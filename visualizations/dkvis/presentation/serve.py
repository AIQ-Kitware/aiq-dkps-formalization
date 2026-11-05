"""Browse rendered lectures and serve seekable media.

    uv run --extra serve python -m dkvis.presentation serve
"""
from __future__ import annotations

import argparse
import json
import math
import re
import shutil
import subprocess
from pathlib import Path
from urllib.parse import quote

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


def create_app(directory=ROOT/'renders'):
    root = Path(directory).resolve()
    if not root.is_dir():
        raise ValueError(f'Render directory does not exist: {root}')

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

    def chapters(request):
        path = within(root, request.query_params.get('path', ''))
        if not path.is_file():
            raise HTTPException(404)
        return JSONResponse(chapters_for(root, path), headers={'Cache-Control': 'no-store'})

    return Starlette(routes=[Route('/', index), Route('/api/catalog', catalog),
                            Route('/api/chapters', chapters), Route('/api/media',media_detail),
                            Route('/api/captions',captions), Route('/api/transcript',transcript),
                            Route('/api/source-transcript',source_transcript),
                            Mount('/files', StaticFiles(directory=root, html=True), name='files')])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=ROOT/'renders')
    parser.add_argument('--host', default='127.0.0.1')
    parser.add_argument('--port', type=int, default=8000)
    args = parser.parse_args(argv)
    if not 0 < args.port < 65536:
        parser.error('port must be between 1 and 65535')
    import uvicorn
    print(f'Lecture library: http://{args.host}:{args.port}/', flush=True)
    uvicorn.run(create_app(args.directory), host=args.host, port=args.port)


if __name__ == '__main__':
    main()
