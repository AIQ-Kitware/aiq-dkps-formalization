"""Browse rendered lectures and serve seekable media.

    uv run --extra serve python -m dkvis.presentation serve
"""
from __future__ import annotations

import argparse
from contextlib import asynccontextmanager
from datetime import datetime, timezone
import hashlib
import os
from uuid import uuid4
import json
import math
import re
import shutil
import subprocess
from pathlib import Path
from urllib.parse import quote, urlencode

from starlette.concurrency import run_in_threadpool
from starlette.applications import Starlette
from starlette.exceptions import HTTPException
from starlette.responses import FileResponse, JSONResponse, PlainTextResponse, Response
from starlette.routing import Mount, Route
from starlette.staticfiles import StaticFiles

from dkvis.presentation.paths import ROOT

KINDS = {'.mp4': 'video', '.webm': 'video', '.mov': 'video', '.m4v': 'video',
         '.html': 'slides', '.htm': 'slides', '.pdf': 'pdf',
         '.wav': 'audio', '.mp3': 'audio', '.ogg': 'audio'}
PAGE = Path(__file__).with_name('library.html')


def within(root, relative):
    """Resolve catalog and timeline paths within the selected render directory."""
    try:
        path = (root/relative).resolve()
        path.relative_to(root)
    except (ValueError, OSError):
        raise HTTPException(404)
    if any(part.startswith('.') for part in path.relative_to(root).parts):
        raise HTTPException(404)
    return path


def timeline_paths(root, media):
    """Prefer the timeline for this narrator; never borrow another profile's."""
    # An explicitly named output still belongs to its recorded stable deck.
    try:
        sidecar=within(root,Path(str(media.relative_to(root))+'.metadata.json'))
        metadata=json.loads(sidecar.read_text())
        deck=metadata.get('deck');settings=metadata.get('settings',{})
        profile=settings.get('profile')
        if deck and profile and re.fullmatch(r'[A-Za-z0-9_-]+',profile):
            theme='-light' if settings.get('theme')=='light' else ''
            work=root/f'{deck}{theme}-narrated'
            return [work/f'timeline-{profile}{".preview" if settings.get("preview") else ""}.json']
    except (OSError,ValueError,TypeError,HTTPException):
        pass
    candidates = [media.parent/'timeline.json']
    if media.name.endswith('.narrated.mp4'):
        stem = media.name.removesuffix('.narrated.mp4')
        preview = stem.endswith('.preview')
        if preview:
            stem = stem.removesuffix('.preview')
        deck, separator, profile = stem.partition('.')
        deck = re.sub(r'^\d{6}_', '', deck)
        work = media.parent/f'{deck}-narrated'
        candidates = [work/f'timeline-{profile}{".preview" if preview else ""}.json'] if separator else [work/'timeline.json']
    return candidates


def timeline_for(root, media):
    for candidate in timeline_paths(root,media):
        try:
            candidate=within(root,candidate.relative_to(root))
            entries=json.loads(candidate.read_text())
            if isinstance(entries,list):
                return candidate,entries
        except (OSError,ValueError,TypeError,HTTPException):
            continue
    return None,[]


def chapters_for(root, media):
    """Prefer this video's timeline; fall back to chapters embedded in the movie."""
    candidates=timeline_paths(root,media)
    for candidate in candidates:
        # Repair timelines live beside their movie; timeline paths themselves must
        # remain in the served tree, including when a directory is a symlink.
        try:
            candidate = within(root, candidate.relative_to(root))
            entries = json.loads(candidate.read_text())
            chapters = [dict(title=str(row['title']), start=float(row['start'])) for row in entries]
            if any(not math.isfinite(row['start']) or row['start'] < 0 for row in chapters):
                continue
            return chapters
        except (OSError, ValueError, TypeError, KeyError, HTTPException):
            continue
    if media.suffix.lower() in {'.mp4', '.m4v', '.mov', '.webm'} and shutil.which('ffprobe'):
        try:
            result = subprocess.run(['ffprobe', '-v', 'error', '-show_chapters', '-of', 'json', str(media)],
                                    check=True, capture_output=True, text=True, timeout=5)
            return [dict(title=str(c.get('tags', {}).get('title', f'Chapter {i+1}')),
                         start=float(c['start_time'])) for i, c in enumerate(json.loads(result.stdout)['chapters'])]
        except (OSError, ValueError, KeyError, subprocess.SubprocessError):
            pass
    return []


def create_app(directory=ROOT/'renders', *, feedback_directory=None,
               audio_source_directory=None, audio_cache_directory=None,
               audio_tts_endpoint=None, audio_tts_profile=None, audio_tts_config=None,
               audio_library=None, slide_library=None):
    root = Path(directory).resolve()
    if not root.is_dir():
        if root == (ROOT/'renders').resolve():
            root.mkdir(parents=True, exist_ok=True)
        else:
            raise ValueError(f'Render directory does not exist: {root}')

    from dkvis.presentation.audio_library import AudioLectureHub, AUDIO_PAGE
    from dkvis.presentation.course_graph import build_course_graph, connections
    from dkvis.presentation.companion_slides import CompanionSlideLibrary
    companions = slide_library or CompanionSlideLibrary()
    course_graph = build_course_graph()
    slides_by_node = {node_id: [] for node_id in course_graph['nodes']}
    for deck in companions.catalog():
        for node_id in deck['lecture_nodes']:
            if node_id not in slides_by_node:
                raise ValueError(f'Slide deck {deck["id"]} links to missing lecture {node_id}')
            slides_by_node[node_id].append(deck['id'])
    for node_id, node in course_graph['nodes'].items():
        node['companion_slides'] = slides_by_node[node_id]
    COURSE_GRAPH_PAGE = Path(__file__).with_name('course_graph.html')
    speech_library = audio_library or AudioLectureHub(
        sources=audio_source_directory or ROOT/'draft-stages'/'tts-lectures',
        cache=audio_cache_directory or ROOT/'audio-cache',
        endpoint=audio_tts_endpoint, profile=audio_tts_profile, config=audio_tts_config,
    )

    # Viewer feedback is authored data, not a disposable render/cache artifact.
    feedback_root = Path(feedback_directory).resolve() if feedback_directory else root.parent/'feedback'
    if feedback_root.is_relative_to(root):
        raise ValueError('Keep feedback outside the publicly served render directory')

    def save_feedback(payload):
        from dkvis.presentation.library import catalog as deck_catalog
        if not isinstance(payload, dict):
            raise HTTPException(400, 'Expected a feedback object.')
        text = payload.get('text')
        if not isinstance(text, str) or not text.strip() or len(text) > 10000:
            raise HTTPException(400, 'Enter feedback between 1 and 10,000 characters.')
        lecture = next((row for row in deck_catalog(root) if row['id'] == payload.get('deck')), None)
        if lecture is None:
            raise HTTPException(404, 'Lecture not found.')
        record = dict(schema_version=1, id=str(uuid4()), created_at=datetime.now(timezone.utc).isoformat(),
                      deck=lecture['id'], title=lecture['title'], text=text.strip(),
                      current_lecture_provenance=lecture['provenance'], asset=None,
                      playback_seconds=None, chapter=None, timeline=None)
        if payload.get('path') is not None:
            selected = next((a for a in lecture['assets'] if a['path'] == payload['path']), None)
            if selected is None:
                raise HTTPException(404, 'Selected lecture file not found.')
            if payload.get('version') != selected['version']:
                raise HTTPException(409, 'This file has been regenerated. Your text has not been saved; copy it before refreshing the lecture.')
            media = within(root, selected['path'])
            before = media.stat()
            with media.open('rb') as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
            after = media.stat()
            if before.st_mtime_ns != after.st_mtime_ns or before.st_size != after.st_size or str(after.st_mtime_ns) != selected['version']:
                raise HTTPException(409, 'This file changed while saving. Refresh the lecture and try again.')
            record['asset'] = {**selected, 'sha256': digest}
            seconds = payload.get('playback_seconds')
            if seconds is not None:
                if (selected['kind'] not in {'video', 'audio'} or isinstance(seconds, bool)
                        or not isinstance(seconds, (float, int)) or not math.isfinite(seconds) or seconds < 0):
                    raise HTTPException(400, 'Invalid playback timestamp.')
                record['playback_seconds'] = seconds
                timeline, entries = timeline_for(root, media)
                if timeline:
                    raw = timeline.read_bytes()
                    record['timeline'] = dict(path=timeline.relative_to(root).as_posix(),
                                              sha256=hashlib.sha256(raw).hexdigest())
                record['chapter'] = next((dict(scene=e.get('scene'), title=e.get('title'), start=e['start'])
                                          for e in reversed(entries) if e.get('start', math.inf) <= seconds), None)
        feedback_root.mkdir(parents=True, exist_ok=True)
        target = feedback_root/f'{record["id"]}.json'
        temporary = target.with_suffix('.tmp')
        try:
            with temporary.open('x', encoding='utf-8') as stream:
                json.dump(record, stream, indent=2, ensure_ascii=False, allow_nan=False)
                stream.write('\n')
                stream.flush()
                os.fsync(stream.fileno())
            temporary.replace(target)
        finally:
            temporary.unlink(missing_ok=True)
        return dict(id=record['id'], created_at=record['created_at'])

    async def feedback(request):
        if request.headers.get('content-type', '').split(';')[0].strip() != 'application/json':
            raise HTTPException(415, 'Send feedback as JSON.')
        origin = request.headers.get('origin')
        if origin and origin != f'{request.url.scheme}://{request.url.netloc}':
            raise HTTPException(403, 'Submit feedback from this lecture library.')
        body = bytearray()
        async for chunk in request.stream():
            body.extend(chunk)
            if len(body) > 65536:
                raise HTTPException(413, 'Feedback request is too large.')
        try:
            payload = json.loads(body)
        except (ValueError, UnicodeDecodeError):
            raise HTTPException(400, 'Invalid feedback JSON.')
        try:
            receipt = await run_in_threadpool(save_feedback, payload)
        except OSError:
            raise HTTPException(500, 'Could not save feedback on the server. Your text is still in the box; please try again.')
        return JSONResponse(receipt, status_code=201, headers={'Cache-Control':'no-store'})

    async def index(request):
        return FileResponse(PAGE, headers={'Cache-Control': 'no-cache'})

    def catalog(request):
        from dkvis.presentation.library import catalog as deck_catalog
        folder=within(root,request.query_params.get('folder',''))
        if folder!=root:
            raise HTTPException(404)
        return JSONResponse(dict(items=deck_catalog(root)),headers={'Cache-Control':'no-store'})

    def media_data(request):
        from dkvis.presentation.captions import transcript_rows
        media=within(root,request.query_params.get('path',''))
        if not media.is_file():
            raise HTTPException(404)
        timeline,entries=timeline_for(root,media)
        rows=transcript_rows(root,entries)
        parts=[part for row in rows for part in row['parts'] if part.get('text')]
        return dict(chapters=chapters_for(root,media),transcript=rows,
                    transcript_complete=bool(rows) and all(e.get('builds') for e in entries) and len(rows)==sum(len(e.get('builds',[])) for e in entries),
                    captions_available=bool(rows),caption_timing='approximate within TTS chunks',
                    speech_generated=max((p.get('generated',0) for p in parts),default=0) or None,
                    models=sorted({p['model'] for p in parts if p.get('model')}),
                    voices=sorted({p['voice'] for p in parts if p.get('voice')}),
                    timeline_modified=timeline.stat().st_mtime if timeline else None)

    def media_detail(request):
        return JSONResponse(media_data(request),headers={'Cache-Control':'no-store'})

    def captions(request):
        from dkvis.presentation.captions import vtt
        data=media_data(request)
        if not data['captions_available']:
            raise HTTPException(404,'No speech-text snapshot or cache is available for this video.')
        return Response(vtt(data['transcript']),media_type='text/vtt',headers={'Cache-Control':'no-store'})

    def transcript(request):
        data=media_data(request)
        if not data['transcript']:
            raise HTTPException(404,'No rendered transcript is available.')
        text='\n\n'.join(f'{row["title"]} ({row["start"]:.1f}s)\n\n{row["text"]}' for row in data['transcript'])
        return PlainTextResponse(text+'\n',headers={'Cache-Control':'no-store'})

    def source_transcript(request):
        from dkvis.presentation.narration import read_deck_narration
        try:
            scripts=read_deck_narration(request.query_params.get('deck',''))
        except (KeyError,ValueError,FileNotFoundError):
            raise HTTPException(404)
        text='\n\n'.join(f'{i}. {s.title}\n\n{s.text}' for i,s in enumerate(scripts.values(),1))
        return PlainTextResponse(text+'\n',headers={'Cache-Control':'no-store'})

    def learning_companion(request):
        from dkvis.presentation.resources import learning_resources, companion_html
        try:
            data=learning_resources(request.query_params.get('deck',''))
        except KeyError:
            raise HTTPException(404)
        if data is None:
            raise HTTPException(404)
        return Response(companion_html(data),media_type='text/html',headers={'Cache-Control':'no-store'})

    def chapters(request):
        path = within(root, request.query_params.get('path', ''))
        if not path.is_file():
            raise HTTPException(404)
        return JSONResponse(chapters_for(root, path), headers={'Cache-Control': 'no-store'})

    def audio_error(exc):
        if isinstance(exc, (KeyError, IndexError, FileNotFoundError)):
            raise HTTPException(404, 'Lecture or page not found.') from exc
        if isinstance(exc, ValueError):
            raise HTTPException(400, str(exc)) from exc
        if isinstance(exc, OverflowError):
            raise HTTPException(429, str(exc)) from exc
        raise exc

    def audio_engine(profile=None, track='g2'):
        if hasattr(speech_library, 'engine'):
            return speech_library.engine(profile, track)
        if track != 'g2':
            raise ValueError(f'Unknown audio track: {track}')
        if profile and profile != speech_library.profile:
            raise ValueError(f'Unknown TTS profile: {profile}')
        return speech_library

    def audio_settings(request):
        try:
            engine = audio_engine(request.query_params.get('profile'), request.query_params.get('track', 'g2'))
            return engine, engine.settings(request.query_params.get('voice'),
                                           request.query_params.get('speed'))
        except ValueError as exc:
            audio_error(exc)

    def audio_query(engine, settings, *, key=None):
        track = 'g2' if engine.sources == speech_library.sources else 'g3'
        query = dict(profile=engine.profile, voice=settings.voice, speed=settings.speed,
                     track=track)
        # The audio URL must change when a server-side input changes. In
        # particular, pagination, voice-profile settings and synthesis version
        # belong to the cache key, but are not represented by the public query
        # parameters above. Browser caches previously held an outdated MP3 for
        # a year at the same URL after page size changed.
        if key is not None:
            query['key'] = key
        return urlencode(query)

    async def learning_paths(request):
        return FileResponse(COURSE_GRAPH_PAGE, headers={'Cache-Control': 'no-cache'})

    async def course_graph_api(request):
        return JSONResponse(course_graph, headers={'Cache-Control': 'no-store'})

    async def audio_home(request):
        return FileResponse(AUDIO_PAGE, headers={'Cache-Control': 'no-cache'})

    async def audio_catalog(request):
        track = request.query_params.get('track', 'g2')
        try:
            items = await run_in_threadpool(speech_library.catalog, track) if hasattr(speech_library, 'course_tracks') else await run_in_threadpool(speech_library.catalog)
        except ValueError as exc:
            audio_error(exc)
        return JSONResponse({'items': items, 'track': track,
                             'default_voice': speech_library.default_voice,
                             'model': speech_library.model, 'profile': speech_library.profile}, headers={'Cache-Control': 'no-store'})

    async def audio_lecture(request):
        try:
            if hasattr(speech_library, 'course_tracks'):
                row = await run_in_threadpool(speech_library.detail, request.path_params['lecture_id'], request.query_params.get('track', 'g2'))
            else:
                if request.query_params.get('track', 'g2') != 'g2':
                    raise ValueError('Unknown audio track')
                row = await run_in_threadpool(speech_library.detail, request.path_params['lecture_id'])
        except (KeyError, IndexError, ValueError) as exc:
            audio_error(exc)
        track = request.query_params.get('track', 'g2')
        row = dict(row, course_connections=connections(course_graph, f'{track}:{row["id"]}'),
                   companion_slides=companions.list_for_lecture(f'{track}:{row["id"]}'))
        return JSONResponse(row, headers={'Cache-Control': 'no-store'})

    async def audio_plain_transcript(request):
        """Return only spoken narration, for select-all/copy or external TTS."""
        track = request.query_params.get('track', 'g2')
        lecture_id = request.path_params['lecture_id']
        try:
            if hasattr(speech_library, 'course_tracks'):
                row = await run_in_threadpool(speech_library.detail, lecture_id, track)
            else:
                if track != 'g2':
                    raise ValueError('Unknown audio track')
                row = await run_in_threadpool(speech_library.detail, lecture_id)
        except (KeyError, IndexError, ValueError) as exc:
            audio_error(exc)
        return PlainTextResponse(
            row['transcript'], media_type='text/plain; charset=utf-8',
            headers={'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff'})

    def slide_status(request):
        try:
            return JSONResponse(companions.status(request.path_params['deck_id']),
                                headers={'Cache-Control': 'no-store'})
        except KeyError:
            raise HTTPException(404, 'Unknown slide deck.')

    async def slide_build(request):
        origin = request.headers.get('origin')
        if origin and origin != f'{request.url.scheme}://{request.url.netloc}':
            raise HTTPException(403, 'Build slides from this lecture library.')
        if request.headers.get('content-length') and int(request.headers['content-length']) > 1024:
            raise HTTPException(413, 'Build request too large.')
        try:
            result = await run_in_threadpool(companions.build, request.path_params['deck_id'])
        except KeyError:
            raise HTTPException(404, 'Unknown slide deck.')
        return JSONResponse(result, headers={'Cache-Control': 'no-store'})

    def slide_html(request):
        try:
            path = companions.rendered(request.path_params['deck_id'])
        except KeyError:
            raise HTTPException(404, 'Unknown slide deck.')
        except FileNotFoundError:
            raise HTTPException(409, 'Build the companion slides before opening them.')
        return FileResponse(path, media_type='text/html', headers={'Cache-Control':'no-store'})

    def slide_download(request):
        try:
            path = companions.rendered(request.path_params['deck_id'])
        except KeyError:
            raise HTTPException(404, 'Unknown slide deck.')
        except FileNotFoundError:
            raise HTTPException(409, 'Build the companion slides before downloading them.')
        return FileResponse(path, media_type='text/html', filename=path.name,
                            content_disposition_type='attachment', headers={'Cache-Control':'no-store'})

    async def slide_catalog(request):
        return JSONResponse({'items': companions.catalog()},headers={'Cache-Control':'no-store'})

    async def audio_tracks(request):
        tracks = speech_library.course_tracks() if hasattr(speech_library, 'course_tracks') else [
            dict(id='g2', label='G2 · Comprehensive audio', kind='audio', url='/audio?track=g2')]
        tracks = [*tracks, dict(id='g4', label='G4 - YWS population gap', kind='graph',
                                url='/learning-paths?track=g4', status='planned',
                                count=len(next(t['path'] for t in course_graph['tracks'] if t['id'] == 'g4')))]
        return JSONResponse(dict(tracks=tracks, default_track='g2'),
                            headers={'Cache-Control': 'no-store'})

    async def audio_profiles(request):
        if hasattr(speech_library, 'profiles'):
            profiles = speech_library.profiles()
        else:
            profiles = [dict(id=speech_library.profile, label=speech_library.profile,
                             model=speech_library.model, default_voice=speech_library.default_voice)]
        return JSONResponse(dict(default_profile=speech_library.profile, profiles=profiles),
                            headers={'Cache-Control': 'no-store'})

    async def audio_health(request):
        try:
            engine = audio_engine(request.query_params.get('profile'))
        except ValueError as exc:
            audio_error(exc)
        return JSONResponse(await run_in_threadpool(engine.connection_status),
                            headers={'Cache-Control': 'no-store'})

    async def audio_voices(request):
        try:
            engine = audio_engine(request.query_params.get('profile'))
            names = await run_in_threadpool(engine.voices)
            registered = (speech_library.registered_voices(engine.profile)
                          if hasattr(speech_library, 'registered_voices') else [])
            names = sorted(set(names) | {item['voice'] for item in registered})
        except ValueError as exc:
            audio_error(exc)
        return JSONResponse(dict(voices=names, registered=registered,
                                 default_voice=engine.default_voice,
                                 model=engine.model, profile=engine.profile),
                            headers={'Cache-Control': 'no-store'})

    async def audio_register_voice(request):
        if not hasattr(speech_library, 'register_voice'):
            raise HTTPException(501, 'Voice registration is not configured.')
        if request.headers.get('content-type', '').split(';')[0].strip() != 'application/json':
            raise HTTPException(415, 'Send voice registration as JSON.')
        origin = request.headers.get('origin')
        if origin and origin != f'{request.url.scheme}://{request.url.netloc}':
            raise HTTPException(403, 'Register voices from this lecture library.')
        raw = bytearray()
        async for chunk in request.stream():
            raw.extend(chunk)
            if len(raw) > 2048:
                raise HTTPException(413, 'Registration request is too large.')
        try:
            data = json.loads(raw)
            if not isinstance(data, dict) or set(data) - {'profile', 'voice', 'label'}:
                raise ValueError('Only profile, voice, and label may be registered.')
            record = await run_in_threadpool(speech_library.register_voice,
                                             data.get('profile'), data.get('voice'), data.get('label'))
        except (ValueError, TypeError) as exc:
            audio_error(ValueError(str(exc)))
        return JSONResponse(record, status_code=201, headers={'Cache-Control': 'no-store'})

    async def audio_inventory(request):
        try:
            engine, settings = audio_settings(request)
            lecture_id = request.query_params.get('lecture_id')
            if not lecture_id:
                raise ValueError('lecture_id is required')
            result = await run_in_threadpool(engine.inventory, lecture_id, settings)
        except (ValueError, IndexError, KeyError) as exc:
            audio_error(exc)
        return JSONResponse(result, headers={'Cache-Control': 'no-store'})

    async def audio_cache_catalog(request):
        try:
            engine, settings = audio_settings(request)
            result = await run_in_threadpool(engine.catalog_inventory, settings)
        except (ValueError, IndexError, KeyError) as exc:
            audio_error(exc)
        return JSONResponse(dict(items=result), headers={'Cache-Control': 'no-store'})

    async def audio_prepare_lecture(request):
        """Start a bounded server-side cache campaign; independent of browser navigation."""
        if request.headers.get('content-type', '').split(';')[0].strip() != 'application/json':
            raise HTTPException(415, 'Send preparation settings as JSON.')
        origin = request.headers.get('origin')
        if origin and origin != f'{request.url.scheme}://{request.url.netloc}':
            raise HTTPException(403, 'Prepare speech from this lecture library.')
        raw = bytearray()
        async for chunk in request.stream():
            raw.extend(chunk)
            if len(raw) > 2048:
                raise HTTPException(413, 'Preparation settings are too large.')
        try:
            body = json.loads(raw)
            if not isinstance(body, dict) or set(body) - {'profile', 'voice', 'speed', 'track', 'lecture_id'}:
                raise ValueError('Invalid preparation fields')
            engine = audio_engine(body.get('profile'), body.get('track', 'g2'))
            settings = engine.settings(body.get('voice'), body.get('speed'))
            if not isinstance(body.get('lecture_id'), str):
                raise ValueError('lecture_id is required')
            result = await run_in_threadpool(engine.prepare_lecture, body['lecture_id'], settings)
        except (ValueError, IndexError, KeyError, TypeError) as exc:
            audio_error(exc)
        return JSONResponse(result, status_code=202, headers={'Cache-Control': 'no-store'})

    async def audio_cancel_generation(request):
        if request.headers.get('content-type', '').split(';')[0].strip() != 'application/json':
            raise HTTPException(415, 'Send cancellation settings as JSON.')
        origin = request.headers.get('origin')
        if origin and origin != f'{request.url.scheme}://{request.url.netloc}':
            raise HTTPException(403, 'Cancel speech from this lecture library.')
        raw = bytearray()
        async for chunk in request.stream():
            raw.extend(chunk)
            if len(raw) > 2048:
                raise HTTPException(413, 'Cancellation request is too large.')
        try:
            body = json.loads(raw)
            if not isinstance(body, dict) or set(body) - {'profile', 'voice', 'speed', 'track', 'lecture_id'}:
                raise ValueError('Invalid cancellation fields')
            engine = audio_engine(body.get('profile'), body.get('track', 'g2'))
            settings = engine.settings(body.get('voice'), body.get('speed'))
            if not isinstance(body.get('lecture_id'), str):
                raise ValueError('lecture_id is required')
            affected = await run_in_threadpool(engine.cancel, body['lecture_id'], settings)
        except (ValueError, IndexError, KeyError, TypeError) as exc:
            audio_error(exc)
        return JSONResponse(dict(cancelled=affected, count=len(affected)),
                            headers={'Cache-Control': 'no-store'})

    def audio_status_payload(request, result, engine, settings):
        if result['state'] == 'ready':
            result['url'] = (f'/api/audio-lectures/{request.path_params["lecture_id"]}'
                             f'/pages/{request.path_params["page"]}/audio?'
                             f'{audio_query(engine, settings, key=result["key"])}')
        return result

    async def audio_page_status(request):
        try:
            engine, settings = audio_settings(request)
            result = await run_in_threadpool(engine.status,
                request.path_params['lecture_id'], request.path_params['page'], settings)
        except (KeyError, IndexError, ValueError) as exc:
            audio_error(exc)
        return JSONResponse(audio_status_payload(request, result, engine, settings),
                            headers={'Cache-Control': 'no-store'})

    async def audio_page_render(request):
        if request.headers.get('content-type', '').split(';')[0].strip() != 'application/json':
            raise HTTPException(415, 'Send TTS settings as JSON.')
        origin = request.headers.get('origin')
        if origin and origin != f'{request.url.scheme}://{request.url.netloc}':
            raise HTTPException(403, 'Render speech from this lecture library.')
        raw = bytearray()
        async for chunk in request.stream():
            raw.extend(chunk)
            if len(raw) > 2048:
                raise HTTPException(413, 'TTS settings request is too large.')
        try:
            settings_body = json.loads(raw)
            if not isinstance(settings_body, dict) or set(settings_body) - {'profile', 'voice', 'speed', 'track', 'purpose'}:
                raise ValueError('Only track, profile, voice, and speed can be selected.')
            engine = audio_engine(settings_body.get('profile'), settings_body.get('track', 'g2'))
            settings = engine.settings(settings_body.get('voice'), settings_body.get('speed'))
            purpose = settings_body.get('purpose', 'playback')
            if purpose not in ('playback', 'cache', 'prefetch'):
                raise ValueError('Invalid generation purpose')
            result = await run_in_threadpool(engine.request,
                request.path_params['lecture_id'], request.path_params['page'], settings, purpose)
        except (ValueError, IndexError, KeyError, OverflowError, TypeError) as exc:
            audio_error(exc if not isinstance(exc, TypeError) else ValueError('Invalid TTS settings.'))
        if result['state'] == 'ready':
            query = audio_query(engine, settings, key=result['key'])
            result['url'] = (f'/api/audio-lectures/{request.path_params["lecture_id"]}'
                             f'/pages/{request.path_params["page"]}/audio?{query}')
        return JSONResponse(result, status_code=200 if result['state'] == 'ready' else 202,
                            headers={'Cache-Control': 'no-store'})

    async def audio_page_file(request):
        try:
            engine, settings = audio_settings(request)
            supplied_key = request.query_params.get('key')
            if supplied_key is not None:
                # Reject obsolete keyed URLs. An immutable URL must identify
                # exactly one recording, never the current occupant of a page.
                status = await run_in_threadpool(engine.status,
                    request.path_params['lecture_id'], request.path_params['page'], settings)
                if status['key'] != supplied_key:
                    raise HTTPException(404, 'Audio cache identity has changed.')
            path = await run_in_threadpool(engine.audio_file,
                request.path_params['lecture_id'], request.path_params['page'], settings)
        except (KeyError, IndexError, FileNotFoundError, ValueError) as exc:
            audio_error(exc)
        # Legacy URLs without an artifact key must never be cached. Keyed URLs
        # are content-addressed and safe for long-lived browser caching.
        cache_header = ('private, max-age=31536000, immutable' if supplied_key
                        else 'private, no-store')
        return FileResponse(path, media_type='audio/mpeg', filename=path.name,
                            content_disposition_type='inline',
                            headers={'Cache-Control': cache_header})

    @asynccontextmanager
    async def lifespan(_app):
        try:
            yield
        finally:
            speech_library.close()

    app = Starlette(routes=[
        Route('/', index), Route('/audio', audio_home),
        Route('/learning-paths', learning_paths), Route('/api/course-graph', course_graph_api),
        Route('/api/slide-decks', slide_catalog),
        Route('/api/slide-decks/{deck_id}', slide_status),
        Route('/api/slide-decks/{deck_id}/build', slide_build, methods=['POST']),
        Route('/api/slide-decks/{deck_id}/download', slide_download),
        Route('/slide-decks/{deck_id}', slide_html),
        Route('/api/audio-lectures', audio_catalog),
        Route('/api/audio-tracks', audio_tracks),
        Route('/api/audio-voices', audio_voices),
        Route('/api/audio-voices/register', audio_register_voice, methods=['POST']),
        Route('/api/audio-profiles', audio_profiles),
        Route('/api/audio-health', audio_health),
        Route('/api/audio-generation/inventory', audio_inventory),
        Route('/api/audio-generation/catalog', audio_cache_catalog),
        Route('/api/audio-generation/prepare', audio_prepare_lecture, methods=['POST']),
        Route('/api/audio-generation/cancel', audio_cancel_generation, methods=['POST']),
        Route('/api/audio-lectures/{lecture_id}', audio_lecture),
        Route('/api/audio-lectures/{lecture_id}/transcript.txt', audio_plain_transcript),
        Route('/api/audio-lectures/{lecture_id}/pages/{page:int}', audio_page_status),
        Route('/api/audio-lectures/{lecture_id}/pages/{page:int}/render', audio_page_render, methods=['POST']),
        Route('/api/audio-lectures/{lecture_id}/pages/{page:int}/audio', audio_page_file),
        Route('/api/catalog', catalog), Route('/api/chapters', chapters),
        Route('/api/media', media_detail), Route('/api/captions', captions),
        Route('/api/transcript', transcript), Route('/api/source-transcript', source_transcript),
        Route('/api/learning-resources', learning_companion),
        Route('/api/feedback', feedback, methods=['POST']),
        Mount('/files', StaticFiles(directory=root, html=True), name='files'),
    ], lifespan=lifespan)
    return app


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=ROOT/'renders')
    parser.add_argument('--feedback-directory', type=Path, help='saved viewer feedback; defaults to a feedback directory beside renders')
    parser.add_argument('--audio-source-directory', type=Path, help='directory containing the staged Markdown lectures')
    parser.add_argument('--audio-cache-directory', type=Path, help='persistent MP3 page cache')
    parser.add_argument('--audio-tts-endpoint', help='override profile speech URL')
    parser.add_argument('--audio-tts-profile', help='default audio profile (public Breeze; DKVIS_AUDIO_TTS_PROFILE or DKVIS_TTS_PROFILE overrides)')
    parser.add_argument('--tts-config', type=Path,
                        help='TTS profile config for the audio reader (default: tts.toml; DKVIS_AUDIO_TTS_CONFIG overrides)')
    parser.add_argument('--host', default='0.0.0.0')
    parser.add_argument('--port', type=int, default=8001)
    args = parser.parse_args(argv)
    if not 0 < args.port < 65536:
        parser.error('port must be between 1 and 65535')
    import uvicorn
    browser_host = '127.0.0.1' if args.host == '0.0.0.0' else args.host
    print(f'Lecture library: http://{browser_host}:{args.port}/audio (LAN: use this machine\'s IP)', flush=True)
    tts_config = args.tts_config or (Path(os.environ['DKVIS_AUDIO_TTS_CONFIG'])
                                     if os.environ.get('DKVIS_AUDIO_TTS_CONFIG') else None)
    uvicorn.run(create_app(args.directory, feedback_directory=args.feedback_directory,
                           audio_source_directory=args.audio_source_directory,
                           audio_cache_directory=args.audio_cache_directory,
                           audio_tts_endpoint=args.audio_tts_endpoint,
                           audio_tts_profile=args.audio_tts_profile,
                           audio_tts_config=tts_config), host=args.host, port=args.port)


if __name__ == '__main__':
    main()
