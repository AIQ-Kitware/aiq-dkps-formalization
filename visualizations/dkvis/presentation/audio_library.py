"""Repository-backed, page-based speech library for the draft DKPS lectures.

The source of speech is the same extract_narration.py used by the lecture
pipeline. Only audio bytes are generated/cached here; manuscripts are read-only.
"""
from __future__ import annotations

from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import dataclass
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import threading
from urllib.parse import urlparse
import urllib.error
import urllib.request
from uuid import uuid4

from dkvis.presentation.paths import ROOT

SOURCE_DIRECTORY = ROOT / 'draft-stages' / 'tts-lectures'
EXTRACTOR = SOURCE_DIRECTORY / 'extract_narration.py'
AUDIO_PAGE = Path(__file__).with_name('audio_library.html')
LECTURE_NAME = re.compile(r'^(\d{6})-.*\.md$')
VOICE_PATTERN = re.compile(r'^[A-Za-z0-9_.+\-]{1,80}$')
SENTENCE_BREAK = re.compile(r'(?<=[.!?])\s+(?=[A-Z0-9“\"(])')


class SpeechServiceError(Exception):
    pass


@dataclass(frozen=True)
class SpeechSettings:
    model: str
    voice: str
    speed: float


def narration_extractor(path: Path):
    """Call the canonical spoken-region extractor, including future refinements."""
    module_path = path.parent / 'extract_narration.py'
    spec = importlib.util.spec_from_file_location('dkps_staged_narration_extractor', module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot load narration extractor: {module_path}')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.extract(path).strip()


def split_pages(text: str, *, max_chars: int = 850) -> list[str]:
    """Keep paragraphs together when possible; split long ones at sentences/words."""
    if max_chars < 100:
        raise ValueError('max_chars must be at least 100')
    paragraphs = [p.strip() for p in re.split(r'\n\s*\n', text) if p.strip()]
    units = []
    for paragraph in paragraphs:
        if len(paragraph) <= max_chars:
            units.append(paragraph)
            continue
        for sentence in SENTENCE_BREAK.split(paragraph):
            if len(sentence) <= max_chars:
                units.append(sentence)
                continue
            # A long sentence (or formula) is split at whitespace, not dropped.
            words = sentence.split()
            chunk = ''
            for word in words:
                if len(word) > max_chars:
                    raise ValueError('Speech word exceeds the page character limit')
                if chunk and len(chunk) + len(word) + 1 > max_chars:
                    units.append(chunk)
                    chunk = ''
                chunk = f'{chunk} {word}'.strip()
            if chunk:
                units.append(chunk)
    pages = []
    current = ''
    for unit in units:
        if current and len(current) + len(unit) + 2 > max_chars:
            pages.append(current)
            current = ''
        current = f'{current}\n\n{unit}'.strip() if current else unit
    if current:
        pages.append(current)
    return pages


class AudioLectureLibrary:
    def __init__(self, *, sources=SOURCE_DIRECTORY, cache=None, endpoint=None,
                 model=None, voice=None, profile=None, response_format=None, page_chars=None, workers=2,
                 sender=None):
        from dkvis.presentation.tts import load_profiles, resolve_profile

        # The audio reader shares production TTS profiles and private .env.
        # Load .env before collecting audio-specific environment overrides.
        document = load_profiles()
        overrides = {}
        for name, value in (
            ('endpoint', endpoint or os.environ.get('DKVIS_AUDIO_TTS_ENDPOINT')),
            ('model', model or os.environ.get('DKVIS_AUDIO_TTS_MODEL')),
            ('voice', voice or os.environ.get('DKVIS_AUDIO_TTS_VOICE')),
            ('response_format', response_format or os.environ.get('DKVIS_AUDIO_TTS_RESPONSE_FORMAT')),
        ):
            if value:
                overrides[name] = value
        config = resolve_profile(document,
                                 selected=profile or os.environ.get('DKVIS_AUDIO_TTS_PROFILE'),
                                 overrides=overrides)
        self.sources = Path(sources).resolve()
        self.cache = Path(cache or (ROOT / 'audio-cache')).resolve()
        self.profile = config['profile']
        self.endpoint = config['endpoint']
        self.model = config['model']
        self.default_voice = config['voice']
        self.response_format = config['response_format']
        self.request_settings = config.get('request', {})
        self.language = config.get('language')
        self.pronunciation_replacements = config.get('pronunciation_replacements', {})
        self.timeout = config['timeout_seconds']
        if not self.endpoint.startswith(('http://', 'https://')):
            raise ValueError('TTS endpoint must use HTTP or HTTPS')
        self.page_chars = int(page_chars if page_chars is not None else
                              os.environ.get('DKVIS_AUDIO_PAGE_CHARS', '420'))
        if not 250 <= self.page_chars <= 1500:
            raise ValueError('Speech page size must be 250–1500 characters')
        if not VOICE_PATTERN.fullmatch(self.default_voice):
            raise ValueError('Invalid default TTS voice')
        self._sender = sender or self._send_speech
        self._executor = ThreadPoolExecutor(max_workers=workers, thread_name_prefix='dkps-speech')
        self._lock = threading.Lock()
        self._jobs: dict[str, Future] = {}
        self._max_queued = 8

    def connection_status(self):
        """Probe the configured upstream from the *server*, not the browser."""
        parsed = urlparse(self.endpoint)
        port = parsed.port or (443 if parsed.scheme == 'https' else 80)
        try:
            with socket.create_connection((parsed.hostname, port), timeout=1.5):
                return dict(state='reachable', profile=self.profile, model=self.model,
                            voice=self.default_voice, upstream=f'{parsed.hostname}:{port}')
        except (OSError, ValueError) as exc:
            return dict(state='unreachable', profile=self.profile, model=self.model,
                        voice=self.default_voice, upstream=f'{parsed.hostname}:{port}',
                        error=f'{type(exc).__name__}: {exc}')

    def close(self):
        self._executor.shutdown(wait=False, cancel_futures=True)

    def _files(self):
        if not self.sources.is_dir():
            return []
        return sorted(p for p in self.sources.iterdir() if p.is_file() and LECTURE_NAME.fullmatch(p.name))

    def _lecture_path(self, lecture_id):
        if not re.fullmatch(r'\d{6}', lecture_id):
            raise KeyError(lecture_id)
        matches = [path for path in self.sources.glob(f'{lecture_id}-*.md') if LECTURE_NAME.fullmatch(path.name)]
        if len(matches) != 1:
            raise KeyError(lecture_id)
        return matches[0]

    def _record(self, path, include_pages):
        spoken = narration_extractor(path)
        pages = split_pages(spoken, max_chars=self.page_chars)
        heading = path.read_text(encoding='utf-8').splitlines()[0]
        title = heading.removeprefix('# ').strip() if heading.startswith('# ') else path.stem[7:].replace('-', ' ').title()
        record = dict(id=path.name[:6], title=title, words=len(spoken.split()),
                      page_count=len(pages), source_modified=path.stat().st_mtime,
                      estimated_minutes=round(len(spoken.split()) / 145, 1))
        if include_pages:
            record['pages'] = pages
            record['transcript'] = spoken
            record['related_resources'] = self._related_resources(path.name[:6])
        return record

    def _related_resources(self, lecture_id):
        """Optional non-spoken learning links from the existing sidecar catalog."""
        metadata = self.sources / 'metadata'
        try:
            sidecar = json.loads((metadata / f'{lecture_id}.json').read_text(encoding='utf-8'))
            sources = json.loads((metadata / 'sources.json').read_text(encoding='utf-8'))['sources']
        except (OSError, ValueError, KeyError, TypeError):
            return []
        result = []
        for reading in sidecar.get('related_resources', []):
            source = sources.get(reading.get('source_id'))
            if not source or source.get('access') != 'free_no_login':
                continue
            url = source.get('url', '')
            if urlparse(url).scheme != 'https' or not urlparse(url).netloc:
                continue
            result.append(dict(title=source['title'], url=url,
                               reason=reading.get('reason', '')))
        return result

    def catalog(self):
        return [self._record(p, False) for p in self._files()]

    def detail(self, lecture_id):
        return self._record(self._lecture_path(lecture_id), True)

    def settings(self, voice=None, speed=None):
        voice = voice if voice is not None else self.default_voice
        if not isinstance(voice, str) or not VOICE_PATTERN.fullmatch(voice):
            raise ValueError('Voice must be 1–80 letters, digits or name punctuation')
        try:
            rate = float(speed) if speed is not None else 1.0
        except (TypeError, ValueError):
            raise ValueError('TTS speed must be a number') from None
        if not 0.5 <= rate <= 2.0 or not __import__('math').isfinite(rate):
            raise ValueError('TTS speed must be between 0.5 and 2.0')
        return SpeechSettings(self.model, voice, round(rate, 3))

    def _target(self, lecture_id, page_index, settings):
        lecture = self.detail(lecture_id)
        if page_index < 0 or page_index >= lecture['page_count']:
            raise IndexError(page_index)
        text = lecture['pages'][page_index]
        canonical = json.dumps(dict(profile=self.profile, endpoint=self.endpoint,
                                    model=settings.model, voice=settings.voice,
                                    speed=settings.speed, response_format=self.response_format,
                                    request=self.request_settings, language=self.language,
                                    pronunciation=self.pronunciation_replacements,
                                    output='mp3', input=text),
                               sort_keys=True, ensure_ascii=False)
        digest = hashlib.sha256(canonical.encode('utf-8')).hexdigest()
        return self.cache / lecture_id / f'{page_index:03d}-{digest}.mp3', text, digest

    def _send_speech(self, text: str, settings: SpeechSettings, destination: Path):
        from dkvis.presentation.pronunciation import speech_text

        payload = {**self.request_settings, 'model': settings.model,
                   'voice': settings.voice, 'input': speech_text(text, self.pronunciation_replacements),
                   'response_format': self.response_format}
        if self.language:
            payload['language'] = self.language
        # The configured Breeze adapter does not take a speed field. Apply
        # speed in FFmpeg after synthesis; Kokoro accepts the API speed field.
        is_kokoro = settings.model.lower() == 'kokoro'
        if is_kokoro:
            payload.update(speed=settings.speed, stream=False)
        request = urllib.request.Request(self.endpoint, data=json.dumps(payload).encode('utf-8'),
                                         headers={'Content-Type': 'application/json'}, method='POST')
        needs_conversion = self.response_format == 'wav' or (not is_kokoro and settings.speed != 1.0)
        source = destination.with_name(destination.name + f'.source.{self.response_format}') if needs_conversion else destination
        try:
            try:
                with urllib.request.urlopen(request, timeout=min(180, self.timeout)) as response:
                    media_type = response.headers.get('Content-Type', '').lower()
                    if 'json' in media_type or 'text/' in media_type:
                        raise SpeechServiceError('Speech server returned text rather than audio')
                    with source.open('xb') as output:
                        size = 0
                        while True:
                            chunk = response.read(1024 * 256)
                            if not chunk:
                                break
                            size += len(chunk)
                            if size > 16 * 1024 * 1024:
                                raise SpeechServiceError('Speech page exceeded 16 MB')
                            output.write(chunk)
            except urllib.error.HTTPError as exc:
                detail = exc.read(300).decode('utf-8', errors='replace').strip()
                raise SpeechServiceError(f'TTS server HTTP {exc.code}: {detail}') from exc
            except (urllib.error.URLError, TimeoutError) as exc:
                raise SpeechServiceError(f'Cannot connect to speech server at {self.endpoint}: {exc}') from exc
            if size < 256:
                raise SpeechServiceError('Speech server returned an empty or truncated audio page')
            if needs_conversion:
                if not shutil.which('ffmpeg'):
                    raise SpeechServiceError('FFmpeg is required to play the configured WAV speech profile')
                command = ['ffmpeg', '-nostdin', '-y', '-loglevel', 'error', '-i', str(source),
                           '-vn']
                if not is_kokoro and settings.speed != 1.0:
                    command += ['-filter:a', f'atempo={settings.speed:g}']
                command += ['-codec:a', 'libmp3lame', '-q:a', '3', '-f', 'mp3', str(destination)]
                try:
                    result = subprocess.run(command, capture_output=True, text=True, timeout=90)
                except (OSError, subprocess.TimeoutExpired) as exc:
                    raise SpeechServiceError(f'FFmpeg conversion failed: {exc}') from exc
                if result.returncode:
                    raise SpeechServiceError(f'FFmpeg conversion failed: {result.stderr[-300:]}')
        finally:
            if needs_conversion:
                source.unlink(missing_ok=True)

    def _generate(self, target, text, settings):
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_name(f'.{target.stem}-{uuid4().hex}.tmp')
        try:
            self._sender(text, settings, temporary)
            if not temporary.is_file() or temporary.stat().st_size < 256:
                raise SpeechServiceError('Speech endpoint returned incomplete audio')
            os.replace(temporary, target)
        finally:
            temporary.unlink(missing_ok=True)

    def status(self, lecture_id, page_index, settings):
        target, _text, digest = self._target(lecture_id, page_index, settings)
        if target.is_file() and target.stat().st_size >= 256:
            return dict(state='ready', key=digest, bytes=target.stat().st_size)
        with self._lock:
            job = self._jobs.get(digest)
            if job is None:
                return dict(state='missing', key=digest)
            if job.done():
                error = job.exception()
                if error:
                    return dict(state='error', key=digest, error=str(error))
                return dict(state='missing', key=digest)
            return dict(state='rendering' if job.running() else 'queued', key=digest)

    def request(self, lecture_id, page_index, settings):
        target, text, digest = self._target(lecture_id, page_index, settings)
        if target.is_file() and target.stat().st_size >= 256:
            return self.status(lecture_id, page_index, settings)
        with self._lock:
            running = self._jobs.get(digest)
            if running is None or running.done():
                in_flight = sum(1 for job in self._jobs.values() if not job.done())
                if in_flight >= self._max_queued:
                    raise OverflowError('Audio generation queue is full; retry shortly')
                # Retire finished jobs; cached files, not futures, are durable.
                self._jobs = {key: job for key, job in self._jobs.items() if not job.done()}
                self._jobs[digest] = self._executor.submit(self._generate, target, text, settings)
        return self.status(lecture_id, page_index, settings)

    def audio_file(self, lecture_id, page_index, settings):
        target, _text, _digest = self._target(lecture_id, page_index, settings)
        if not target.is_file() or target.stat().st_size < 256:
            raise FileNotFoundError(target)
        return target

    def voices(self):
        base = self.endpoint.removesuffix('/v1/audio/speech')
        for suffix in ('/v1/audio/voices', '/v1/voices'):
            try:
                with urllib.request.urlopen(base + suffix, timeout=3) as response:
                    data = json.load(response)
                items = data.get('voices', data.get('data', data)) if isinstance(data, dict) else data
                names = []
                if isinstance(items, list):
                    for item in items:
                        name = item if isinstance(item, str) else (item.get('id') or item.get('name') if isinstance(item, dict) else None)
                        if isinstance(name, str) and VOICE_PATTERN.fullmatch(name):
                            names.append(name)
                if names:
                    return sorted(set(names) | {self.default_voice})
            except (OSError, ValueError, TypeError, AttributeError, urllib.error.URLError):
                pass
        return [self.default_voice]


class AudioLectureHub:
    """Reader-specific profile selection and persistent voice registrations.

    TTS endpoints are defined by local tts.toml only. A browser may choose a
    profile or voice ID, but never supply an arbitrary upstream URL.
    """

    def __init__(self, *, sources=SOURCE_DIRECTORY, cache=None, profile=None,
                 endpoint=None, sender=None, page_chars=None):
        from dkvis.presentation.tts import load_profiles
        self.document = load_profiles()
        self.sources = Path(sources).resolve()
        self.cache = Path(cache or (ROOT / 'audio-cache')).resolve()
        self.profile = profile or os.environ.get('DKVIS_AUDIO_TTS_PROFILE') or 'kokoro'
        if self.profile not in self.document.get('profiles', {}):
            raise ValueError(f'Unknown audio profile: {self.profile}')
        self._endpoint_override = endpoint
        self._sender = sender
        self._page_chars = page_chars
        self._engines = {}
        self._lock = threading.RLock()
        self._voice_registry = self.cache / 'registered-voices.json'
        self.engine(self.profile)

    @property
    def default_voice(self):
        return self.engine(self.profile).default_voice

    @property
    def model(self):
        return self.engine(self.profile).model

    def engine(self, profile=None):
        profile = profile or self.profile
        if not isinstance(profile, str) or profile not in self.document.get('profiles', {}):
            raise ValueError(f'Unknown TTS profile: {profile}')
        with self._lock:
            if profile not in self._engines:
                self._engines[profile] = AudioLectureLibrary(
                    sources=self.sources, cache=self.cache, profile=profile,
                    endpoint=self._endpoint_override if profile == self.profile else None,
                    page_chars=self._page_chars, sender=self._sender)
            return self._engines[profile]

    def profiles(self):
        names = list(self.document.get('profiles', {}))
        names.sort(key=lambda name: (name != self.profile, name != 'crall-math-dk-v2-breeze-tts2', name))
        labels = {'kokoro': 'Kokoro',
                  'crall-math-dk-v2-breeze-tts2': 'Crall Math DK v2 (Breeze)',
                  'crall': 'Crall Math DK (legacy)'}
        return [dict(id=name,
                     label=self.document['profiles'][name].get('display_name', labels.get(name, name)),
                     model=self.document['profiles'][name].get('model'),
                     default_voice=self.document['profiles'][name].get('voice'))
                for name in names]

    def catalog(self):
        return self.engine(self.profile).catalog()

    def detail(self, lecture_id):
        return self.engine(self.profile).detail(lecture_id)

    def _read_registry(self):
        try:
            data = json.loads(self._voice_registry.read_text(encoding='utf-8'))
        except FileNotFoundError:
            return []
        if not isinstance(data, dict) or not isinstance(data.get('voices'), list):
            raise ValueError('Invalid registered-voices.json')
        return data['voices']

    def registered_voices(self, profile):
        self.engine(profile)
        with self._lock:
            return [dict(item) for item in self._read_registry() if item.get('profile') == profile]

    def voices(self, profile):
        engine = self.engine(profile)
        return sorted(set(engine.voices()) | {item['voice'] for item in self.registered_voices(profile)})

    def register_voice(self, profile, voice, label=None):
        self.engine(profile)
        if not isinstance(voice, str) or not VOICE_PATTERN.fullmatch(voice):
            raise ValueError('Voice ID must use 1-80 letters, digits, _, ., +, or -')
        if label is None:
            label = voice
        if not isinstance(label, str) or not (1 <= len(label.strip()) <= 80):
            raise ValueError('Voice label must contain 1-80 characters')
        with self._lock:
            voices = self._read_registry()
            record = dict(profile=profile, voice=voice, label=label.strip())
            voices = [item for item in voices if (item.get('profile'), item.get('voice')) != (profile, voice)]
            voices.append(record)
            voices.sort(key=lambda item: (item['profile'], item['voice']))
            self.cache.mkdir(parents=True, exist_ok=True)
            temporary = self._voice_registry.with_name(f'.registered-voices-{uuid4().hex}.tmp')
            try:
                with temporary.open('x', encoding='utf-8') as stream:
                    json.dump(dict(version=1, voices=voices), stream, indent=2, ensure_ascii=False)
                    stream.write('\n')
                    stream.flush()
                    os.fsync(stream.fileno())
                os.replace(temporary, self._voice_registry)
            finally:
                temporary.unlink(missing_ok=True)
        return record

    def close(self):
        with self._lock:
            for engine in self._engines.values():
                engine.close()
