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
import tempfile
from urllib.parse import urlparse
import urllib.error
import urllib.request
from uuid import uuid4

from dkvis.presentation.paths import ROOT

SOURCE_DIRECTORY = ROOT / 'draft-stages' / 'tts-lectures'
PAPER_DIRECTORY = ROOT / 'draft-stages' / 'tts-paper'
EXTRACTOR = SOURCE_DIRECTORY / 'extract_narration.py'
AUDIO_PAGE = Path(__file__).with_name('audio_library.html')
LECTURE_NAME = re.compile(r'^(\d{6})-.*\.md$')
VOICE_PATTERN = re.compile(r'^[A-Za-z0-9_.+\-]{1,80}$')
# A pagination revision changes the text of synthesized pages and the reader's
# per-page duration measurements. Include the version in both cache identities.
PAGINATION_VERSION = 'sentence-aware-v2'
# Include terminal quotation marks/brackets when deciding where a sentence ends.
# Unlike an uppercase-only lookahead this also handles sentences intentionally
# followed by lowercase starts (for example, quoted or mathematical text).
SENTENCE_BOUNDARY = re.compile(r'[.!?][\"”’\)\]]*\s+')
NON_TERMINAL_ABBREVIATIONS = frozenset({
    'mr.', 'mrs.', 'ms.', 'dr.', 'prof.', 'fig.', 'eq.', 'sec.',
    'e.g.', 'i.e.', 'etc.', 'vs.', 'cf.', 'no.', 'st.',
})


class SpeechServiceError(Exception):
    pass


@dataclass(frozen=True)
class SpeechSettings:
    model: str
    voice: str
    speed: float


def narration_extractor(path: Path):
    """Call the canonical spoken-region extractor, including future refinements."""
    # Both audio tracks use the same canonical spoken-region extractor.
    module_path = EXTRACTOR
    spec = importlib.util.spec_from_file_location('dkps_staged_narration_extractor', module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot load narration extractor: {module_path}')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.extract(path).strip()


def _sentences(paragraph: str) -> list[str]:
    """Find spoken sentences without losing punctuation or trailing quotes.

    The boundary detector deliberately favors keeping ambiguous abbreviations
    with the following words instead of treating every period as a sentence.
    """
    pieces = []
    start = 0
    for match in SENTENCE_BOUNDARY.finditer(paragraph):
        end = match.start() + len(match.group().rstrip())  # before whitespace
        # match.start() is the first terminal punctuation character. Checking
        # the word ending there avoids a break at Dr., e.g., or initials.
        prefix = paragraph[:match.start()+1]
        word = re.search(r'([A-Za-z]+(?:\.[A-Za-z]+)*\.)$', prefix)
        if word and (word.group(1).lower() in NON_TERMINAL_ABBREVIATIONS
                     or len(word.group(1)) == 2 and word.group(1)[0].isupper()):
            continue
        sentence = paragraph[start:end].strip()
        if sentence:
            pieces.append(sentence)
        start = match.end()
    remainder = paragraph[start:].strip()
    if remainder:
        pieces.append(remainder)
    return pieces


def _split_oversized_sentence(sentence: str, max_chars: int) -> list[str]:
    """Split only unavoidable over-limit sentences, always on word breaks."""
    words = sentence.split()
    result = []
    current = ''
    for word in words:
        if len(word) > max_chars:
            raise ValueError('Speech word exceeds the page character limit')
        candidate = f'{current} {word}' if current else word
        if current and len(candidate) > max_chars:
            result.append(current)
            current = word
        else:
            current = candidate
    if current:
        result.append(current)
    return result


def split_pages(text: str, *, max_chars: int = 600) -> list[str]:
    """Pack complete sentences before splitting any sentence across pages.

    Only a sentence longer than the page limit is fragmented. Sentence and
    paragraph whitespace is normalized when repacking; spoken words, their
    order, and punctuation are preserved. Empty pages are never produced.
    """
    if max_chars < 100:
        raise ValueError('max_chars must be at least 100')
    paragraphs = [p.strip() for p in re.split(r'\n\s*\n', text) if p.strip()]
    pages = []
    current = ''
    for paragraph in paragraphs:
        # Existing paragraph boundaries are the preferred visual separation.
        units = [paragraph] if len(paragraph) <= max_chars else _sentences(paragraph)
        start_of_paragraph = True
        for sentence in units:
            chunks = ([sentence] if len(sentence) <= max_chars
                      else _split_oversized_sentence(sentence, max_chars))
            for fragment in chunks:
                separator = '\n\n' if start_of_paragraph else ' '
                candidate = current + separator + fragment if current else fragment
                if current and len(candidate) > max_chars:
                    pages.append(current)
                    current = fragment
                else:
                    current = candidate
                start_of_paragraph = False
    if current:
        pages.append(current)
    return pages


class AudioLectureLibrary:
    def __init__(self, *, sources=SOURCE_DIRECTORY, cache=None, endpoint=None,
                 model=None, voice=None, profile=None, response_format=None, page_chars=None, workers=2,
                 sender=None, config=None, document=None):
        from dkvis.presentation.tts import load_profiles, resolve_profile

        # The audio reader shares production TTS profiles and private .env.
        # Load .env before collecting audio-specific environment overrides.
        if document is None:
            document = load_profiles(config)
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
        # Keep browser pages independent of the smaller synthesis requests.
        # A local voice may stop speaking before the nominal service limit,
        # returning a valid media file with plausible duration. Make each
        # request short enough to limit the amount of omitted speech.
        # Override these limits if a particular voice needs shorter passages.
        self.speech_max_chars = min(int(config['max_chars']),
                                    int(os.environ.get('DKVIS_AUDIO_SEGMENT_CHARS', '140')))
        self.speech_max_words = min(int(config['max_words']),
                                    int(os.environ.get('DKVIS_AUDIO_SEGMENT_WORDS', '12')))
        if not 40 <= self.speech_max_chars <= 280:
            raise ValueError('Audio speech segment characters must be 40-280')
        if not 2 <= self.speech_max_words <= 24:
            raise ValueError('Audio speech segment words must be 2-24')
        # The synthesis cap is deliberately below the service's configured
        # duration ceiling. An unexpectedly long passage is re-synthesized
        # in smaller pieces rather than trusting a potentially capped WAV.
        service_limit = float(config.get('max_audio_seconds', 0))
        segment_limit = float(os.environ.get('DKVIS_AUDIO_SEGMENT_SECONDS', '12'))
        if segment_limit <= 0 or not __import__('math').isfinite(segment_limit):
            raise ValueError('Audio speech segment seconds must be positive and finite')
        self.max_audio_seconds = min(service_limit, segment_limit) if service_limit > 0 else segment_limit
        configured_wps = float(config.get('max_speech_words_per_second', 0))
        # The production limit of 12 words/s catches severe truncation only.
        # Reader requests are short enough to use a stricter plausibility bound.
        self.max_speech_words_per_second = min(configured_wps, 6.0) if configured_wps else 0
        self.chunk_pause_seconds = float(config.get('chunk_pause_seconds', 0))
        if not self.endpoint.startswith(('http://', 'https://')):
            raise ValueError('TTS endpoint must use HTTP or HTTPS')
        self.page_chars = int(page_chars if page_chars is not None else
                              os.environ.get('DKVIS_AUDIO_PAGE_CHARS', '600'))
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
        """Probe upstream and show effective reader bounds (no private config paths)."""
        parsed = urlparse(self.endpoint)
        port = parsed.port or (443 if parsed.scheme == 'https' else 80)
        details = dict(profile=self.profile, model=self.model, voice=self.default_voice,
                       upstream=f'{parsed.hostname}:{port}', page_chars=self.page_chars,
                       speech_max_chars=self.speech_max_chars,
                       speech_max_words=self.speech_max_words,
                       speech_max_seconds=self.max_audio_seconds)
        try:
            with socket.create_connection((parsed.hostname, port), timeout=1.5):
                return dict(state='reachable', **details)
        except (OSError, ValueError) as exc:
            return dict(state='unreachable', **details,
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
        # Lecture number is already displayed separately in the reader.
        title = re.sub(r'^\d{6}\s*[—–-]\s*', '', title)
        record = dict(id=path.name[:6], title=title, words=len(spoken.split()),
                      page_count=len(pages), page_chars=self.page_chars,
                      pagination_version=PAGINATION_VERSION,
                      source_modified=path.stat().st_mtime,
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
            # G3 reuses the non-spoken G2 source catalog without copying it.
            source_catalog = metadata / 'sources.json'
            if not source_catalog.is_file():
                source_catalog = SOURCE_DIRECTORY / 'metadata' / 'sources.json'
            sources = json.loads(source_catalog.read_text(encoding='utf-8'))['sources']
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
        # Page size and pagination are inputs to the audio artifact, even if
        # a particular page's text happens to be unchanged after a resize.
        # Include the page address to keep in-flight jobs distinct when two
        # different pages contain identical text.
        identity = dict(lecture_id=lecture_id, page_index=page_index,
                        page_chars=self.page_chars, pagination=PAGINATION_VERSION,
                        profile=self.profile, endpoint=self.endpoint,
                        model=settings.model, voice=settings.voice,
                        speed=settings.speed, response_format=self.response_format,
                        request=self.request_settings, language=self.language,
                        pronunciation=self.pronunciation_replacements,
                        output='mp3', input=text)
        if settings.model.lower() != 'kokoro':
            # Breeze-specific synthesis parameters also distinguish recordings
            # made before the bounded-generation safeguards.
            identity.update(synthesis='bounded-v4',
                            synthesis_chars=self.speech_max_chars,
                            synthesis_words=self.speech_max_words,
                            max_audio_seconds=self.max_audio_seconds,
                            min_wps_limit=self.max_speech_words_per_second,
                            chunk_pause_seconds=self.chunk_pause_seconds)
        canonical = json.dumps(identity, sort_keys=True, ensure_ascii=False)
        digest = hashlib.sha256(canonical.encode('utf-8')).hexdigest()
        return self.cache / lecture_id / f'{page_index:03d}-{digest}.mp3', text, digest

    def _send_speech(self, text: str, settings: SpeechSettings, destination: Path):
        if settings.model.lower() != 'kokoro':
            self._send_bounded_speech(text, settings, destination)
            return
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

    def _send_bounded_speech(self, text: str, settings: SpeechSettings, destination: Path):
        """Assemble a whole page from verified, bounded local-TTS requests.

        Breeze's server may return a valid WAV that stops at its duration cap.
        A valid media file alone does not establish that the entire text was
        spoken. We reject capped/implausibly short requests and retry smaller
        passages, then encode one browser-seekable MP3 with chunk timing marks.
        """
        from dkvis.presentation.audio import (
            text_chunks, check_audio_limit, check_audio_minimum,
            AudioLimitError, AudioTooShortError,
        )
        from dkvis.presentation.media import duration
        from dkvis.presentation.pronunciation import speech_text

        if not shutil.which('ffmpeg') or not shutil.which('ffprobe'):
            raise SpeechServiceError('Breeze page synthesis requires FFmpeg and FFprobe')
        # Pronunciation aliases can expand a source token into several words.
        # Enforce the request limits *after* those aliases have been applied.
        def bounded_parts(piece: str) -> list[str]:
            prepared = speech_text(piece, self.pronunciation_replacements)
            if (len(prepared) <= self.speech_max_chars
                    and len(prepared.split()) <= self.speech_max_words):
                return [piece]
            words = piece.split()
            if len(words) < 2:
                raise SpeechServiceError(
                    'A pronunciation-expanded token exceeds the local TTS segment limit')
            middle = len(words) // 2
            return (bounded_parts(' '.join(words[:middle]))
                    + bounded_parts(' '.join(words[middle:])))

        pieces = [safe for part in text_chunks(text, self.speech_max_chars,
                                               self.speech_max_words)
                  for safe in bounded_parts(part)]
        if not pieces:
            raise SpeechServiceError('Cannot synthesize an empty speech page')
        chunks: list[tuple[Path, str, float]] = []
        with tempfile.TemporaryDirectory(prefix='speech-page-', dir=destination.parent) as folder:
            work = Path(folder)
            serial = 0

            def fetch(piece: str) -> tuple[Path, float]:
                nonlocal serial
                serial += 1
                source = work / f'part-{serial:04d}.{self.response_format}'
                payload = {**self.request_settings, 'model': settings.model,
                           'voice': settings.voice,
                           'input': speech_text(piece, self.pronunciation_replacements),
                           'response_format': self.response_format}
                if self.language:
                    payload['language'] = self.language
                request = urllib.request.Request(
                    self.endpoint, data=json.dumps(payload).encode('utf-8'),
                    headers={'Content-Type': 'application/json'}, method='POST')
                try:
                    with urllib.request.urlopen(request, timeout=min(180, self.timeout)) as response:
                        media_type = response.headers.get('Content-Type', '').lower()
                        if 'json' in media_type or 'text/' in media_type:
                            raise SpeechServiceError('Speech server returned text rather than audio')
                        with source.open('xb') as output:
                            size = 0
                            while block := response.read(256 * 1024):
                                size += len(block)
                                if size > 16 * 1024 * 1024:
                                    raise SpeechServiceError('Speech segment exceeded 16 MB')
                                output.write(block)
                        expected = response.headers.get('Content-Length')
                        if expected is not None and int(expected) != size:
                            raise SpeechServiceError(
                                f'Speech response ended early: expected {expected} bytes, got {size}')
                except urllib.error.HTTPError as exc:
                    detail = exc.read(300).decode('utf-8', errors='replace').strip()
                    raise SpeechServiceError(f'TTS server HTTP {exc.code}: {detail}') from exc
                except (urllib.error.URLError, TimeoutError) as exc:
                    raise SpeechServiceError(f'Cannot connect to speech server at {self.endpoint}: {exc}') from exc
                if size < 256:
                    raise SpeechServiceError('Speech server returned an empty audio segment')
                try:
                    seconds = duration(source)
                except (ValueError, OSError, subprocess.CalledProcessError) as exc:
                    raise SpeechServiceError(f'Invalid TTS audio segment: {exc}') from exc
                return source, seconds

            def complete(piece: str, depth: int = 0):
                if depth > 12:
                    raise SpeechServiceError('Speech server repeatedly truncated short passages')
                for attempt in range(2):
                    source, seconds = fetch(piece)
                    try:
                        check_audio_limit(seconds, self.max_audio_seconds)
                    except AudioLimitError:
                        # The WAV may play fine while omitting the last words.
                        words = piece.split()
                        if len(words) < 2:
                            raise SpeechServiceError('Speech server truncated even a one-word request')
                        half = max(1, len(words) // 2)
                        subpieces = text_chunks(piece, self.speech_max_chars, half)
                        if len(subpieces) < 2:
                            subpieces = [' '.join(words[:half]), ' '.join(words[half:])]
                        for subpiece in subpieces:
                            complete(subpiece, depth + 1)
                        return
                    try:
                        check_audio_minimum(piece, seconds, self.max_speech_words_per_second,
                                            min_words=8)
                    except AudioTooShortError as exc:
                        if attempt == 0:
                            continue
                        words = piece.split()
                        if len(words) <= 8:
                            raise SpeechServiceError(f'Breeze returned incomplete speech twice: {exc}') from exc
                        subpieces = text_chunks(piece, self.speech_max_chars, max(1, len(words) // 2))
                        if len(subpieces) < 2:
                            subpieces = [' '.join(words[:len(words)//2]),
                                         ' '.join(words[len(words)//2:]) ]
                        for subpiece in subpieces:
                            complete(subpiece, depth + 1)
                        return
                    chunks.append((source, piece, seconds))
                    return

            for piece in pieces:
                complete(piece)
            # Decode every segment before concatenating; this avoids nested
            # MP3 headers and non-seekable, inconsistent duration metadata.
            args = [arg for source, _, _ in chunks for arg in ('-i', str(source))]
            pause = self.chunk_pause_seconds
            filters = []
            for index in range(len(chunks)):
                pad = f',apad=pad_dur={pause:g}' if index < len(chunks) - 1 and pause else ''
                filters.append(
                    f'[{index}:a]aresample=48000,'
                    f'aformat=sample_fmts=s16:channel_layouts=mono,asetpts=PTS-STARTPTS'
                    f'{pad}[a{index}]')
            filters.append(''.join(f'[a{i}]' for i in range(len(chunks))) +
                           f'concat=n={len(chunks)}:v=0:a=1[joined]')
            filters.append(f'[joined]atempo={settings.speed:g}[out]' if settings.speed != 1.0
                           else '[joined]anull[out]')
            command = ['ffmpeg', '-nostdin', '-y', '-loglevel', 'error', *args,
                       '-filter_complex', ';'.join(filters), '-map', '[out]',
                       '-codec:a', 'libmp3lame', '-q:a', '3', '-f', 'mp3', str(destination)]
            try:
                result = subprocess.run(command, capture_output=True, text=True, timeout=180)
            except (OSError, subprocess.TimeoutExpired) as exc:
                raise SpeechServiceError(f'FFmpeg assembly failed: {exc}') from exc
            if result.returncode:
                raise SpeechServiceError(f'FFmpeg assembly failed: {result.stderr[-400:]}')
            try:
                output_seconds = duration(destination)
            except (ValueError, OSError, subprocess.CalledProcessError) as exc:
                raise SpeechServiceError(f'Invalid assembled page audio: {exc}') from exc
            raw_seconds = sum(seconds for _, _, seconds in chunks) + pause * (len(chunks) - 1)
            expected_seconds = raw_seconds / settings.speed
            # A decoder/conversion failure can otherwise silently publish a
            # syntactically valid MP3 that stops before the last speech chunk.
            tolerance = max(0.35, expected_seconds * 0.015)
            if abs(output_seconds - expected_seconds) > tolerance:
                raise SpeechServiceError(
                    f'Audio assembly lost speech: expected {expected_seconds:.2f}s, '
                    f'got {output_seconds:.2f}s')
            # This sidecar documents audible chunk boundaries, not word-level
            # forced alignment. The browser interpolates only inside a chunk.
            scale = output_seconds / raw_seconds
            cursor = 0.0
            timing_chunks = []
            for index, (_, piece, seconds) in enumerate(chunks):
                end = cursor + seconds * scale
                timing_chunks.append(dict(words=len(piece.split()), start=round(cursor, 4),
                                          end=round(end, 4)))
                cursor = end + (pause * scale if index + 1 < len(chunks) else 0)
            sidecar = destination.with_name(destination.name + '.timings.json')
            sidecar.write_text(json.dumps(dict(version=1, chunks=timing_chunks,
                                               duration=output_seconds), indent=2) + '\n',
                               encoding='utf-8')

    def _generate(self, target, text, settings):
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_name(f'.{target.stem}-{uuid4().hex}.tmp')
        try:
            self._sender(text, settings, temporary)
            if not temporary.is_file() or temporary.stat().st_size < 256:
                raise SpeechServiceError('Speech endpoint returned incomplete audio')
            temporary_timing = temporary.with_name(temporary.name + '.timings.json')
            if temporary_timing.is_file():
                os.replace(temporary_timing, target.with_name(target.name + '.timings.json'))
            os.replace(temporary, target)
        finally:
            temporary.unlink(missing_ok=True)
            temporary.with_name(temporary.name + '.timings.json').unlink(missing_ok=True)

    def status(self, lecture_id, page_index, settings):
        target, _text, digest = self._target(lecture_id, page_index, settings)
        if target.is_file() and target.stat().st_size >= 256:
            result = dict(state='ready', key=digest, bytes=target.stat().st_size)
            timing_file = target.with_name(target.name + '.timings.json')
            try:
                timing = json.loads(timing_file.read_text(encoding='utf-8'))
                if isinstance(timing, dict) and timing.get('version') == 1:
                    result['timings'] = timing
            except (OSError, ValueError):
                pass
            return result
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

    TTS profiles come from the TTS config file: tts.toml by default, or an
    operator-supplied private config. A browser may choose a profile or
    voice ID from that list, but never supply an arbitrary upstream URL or
    config path.
    """

    def __init__(self, *, sources=SOURCE_DIRECTORY, cache=None, profile=None,
                 endpoint=None, sender=None, page_chars=None, config=None):
        from dkvis.presentation.tts import load_profiles
        self.config = config
        self.document = load_profiles(config)
        self.sources = Path(sources).resolve()
        self.cache = Path(cache or (ROOT / 'audio-cache')).resolve()
        # The standard reader default stays Kokoro; a private config without
        # Kokoro falls back to its own declared default profile.
        profiles = self.document.get('profiles', {})
        self.profile = (profile or os.environ.get('DKVIS_AUDIO_TTS_PROFILE')
                        or ('kokoro' if 'kokoro' in profiles
                            else self.document.get('profile', 'kokoro')))
        if self.profile not in profiles:
            raise ValueError(f'Unknown audio profile: {self.profile}')
        self._endpoint_override = endpoint
        self._sender = sender
        self._page_chars = page_chars
        self.tracks = {'g2': self.sources}
        if self.sources == SOURCE_DIRECTORY.resolve() and PAPER_DIRECTORY.is_dir():
            self.tracks['g3'] = PAPER_DIRECTORY.resolve()
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

    def engine(self, profile=None, track='g2'):
        profile = profile or self.profile
        if track not in self.tracks:
            raise ValueError(f'Unknown audio track: {track}')
        if not isinstance(profile, str) or profile not in self.document.get('profiles', {}):
            raise ValueError(f'Unknown TTS profile: {profile}')
        with self._lock:
            key = (profile, track)
            if key not in self._engines:
                # G2 preserves preexisting cache locations; G3 remains isolated.
                cache = self.cache if track == 'g2' else self.cache / track
                self._engines[key] = AudioLectureLibrary(
                    sources=self.tracks[track], cache=cache, profile=profile,
                    endpoint=self._endpoint_override if profile == self.profile else None,
                    page_chars=self._page_chars, sender=self._sender, document=self.document)
            return self._engines[key]

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

    def catalog(self, track='g2'):
        return self.engine(self.profile, track).catalog()

    def detail(self, lecture_id, track='g2'):
        return self.engine(self.profile, track).detail(lecture_id)

    def course_tracks(self):
        return [
            dict(id='g1', label='G1 · Manim', kind='presentation', url='/',
                 summary='Original animated presentations and media'),
            dict(id='g2', label='G2 · Comprehensive audio', kind='audio', url='/audio?track=g2',
                 count=len(self.engine(self.profile, 'g2')._files()),
                 summary='Complete foundations and theorem development'),
            *([dict(id='g3', label='G3 · Paper audio', kind='audio', url='/audio?track=g3',
                    count=len(self.engine(self.profile, 'g3')._files()),
                    summary='Shorter path to four angle theorems, counterexample, and matching theorem')]
              if 'g3' in self.tracks else []),
        ]

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
