"""Browse rendered lectures and serve seekable media.

    uv run --extra serve python -m dkvis.presentation serve
"""
from __future__ import annotations

import argparse
import json
import math
import shutil
import subprocess
from pathlib import Path
from urllib.parse import quote

from starlette.applications import Starlette
from starlette.exceptions import HTTPException
from starlette.responses import FileResponse, JSONResponse
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


def chapters_for(root, media):
    """Prefer the timeline for this narrator; never borrow another profile's."""
    candidates = [media.parent/'timeline.json']
    if media.name.endswith('.narrated.mp4'):
        stem = media.name.removesuffix('.narrated.mp4')
        preview = stem.endswith('.preview')
        if preview:
            stem = stem.removesuffix('.preview')
        deck, separator, profile = stem.partition('.')
        work = media.parent/f'{deck}-narrated'
        candidates = [work/f'timeline-{profile}{".preview" if preview else ""}.json'] if separator else [work/'timeline.json']
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
        folder = within(root, request.query_params.get('folder', ''))
        if not folder.is_dir():
            raise HTTPException(404)
        from dkvis.lectures import load_index
        titles = {row['deck']: (i, row['title']) for i, row in enumerate(load_index().values())}
        items = []
        for child in folder.iterdir():
            if child.name.startswith('.'):
                continue
            try:
                path = within(root, child.relative_to(root))
                stat = path.stat()
            except (OSError, HTTPException):
                continue  # a render may replace files while the list is loading
            kind = 'folder' if path.is_dir() else KINDS.get(child.suffix.lower())
            if not kind:
                continue
            relative = child.relative_to(root).as_posix()
            deck = child.name.split('.')[0].removesuffix('-light')
            order, title = titles.get(deck, (1000, child.stem.replace('-', ' ')))
            items.append(dict(path=relative, name=child.name, title=title, kind=kind,
                              order=order, size=stat.st_size, modified=stat.st_mtime,
                              version=str(stat.st_mtime_ns),
                              url='/files/'+quote(relative, safe='/')))
        return JSONResponse(dict(folder=folder.relative_to(root).as_posix(), items=items),
                            headers={'Cache-Control': 'no-store'})

    def chapters(request):
        path = within(root, request.query_params.get('path', ''))
        if not path.is_file():
            raise HTTPException(404)
        return JSONResponse(chapters_for(root, path), headers={'Cache-Control': 'no-store'})

    return Starlette(routes=[Route('/', index), Route('/api/catalog', catalog),
                            Route('/api/chapters', chapters),
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
