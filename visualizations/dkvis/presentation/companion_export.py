"""Build Manim companion-slide frames for PowerPoint and other exporters.

Images are cached by the same source digest as the HTML slide viewer. The CLI
publishes paths as JSON, without rebuilding slide composition in a second
renderer.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from dkvis.presentation.companion_manim import render_slide_png
from dkvis.presentation.companion_slides import CACHE_DIR, CompanionSlideLibrary


def export_companion_frames(source_file: Path, target_dir: Path, *, limit: int | None = None,
                            cache: Path = CACHE_DIR) -> dict:
    source_file = source_file.resolve()
    library = CompanionSlideLibrary(source_file.parent, cache)
    data = json.loads(source_file.read_text(encoding='utf8'))
    validated, revision = library._read(data['id'])
    if validated != data:
        raise ValueError('Source deck disagrees with manifest')
    target_dir.mkdir(parents=True, exist_ok=True)
    count = len(data['slides'])
    selected = min(count, limit) if limit is not None else count
    if selected < 1:
        raise ValueError('At least one frame is required')
    source_cache = cache / 'frames' / revision
    paths = []
    for i, page in enumerate(data['slides'][:selected]):
        image = render_slide_png(data, page, i, count, cache_dir=source_cache)
        frame = target_dir / f'frame-{i + 1:03d}.png'
        frame.write_bytes(image)
        paths.append(str(frame))
    return dict(deck_id=data['id'], slide_count=count, rendered_count=selected, frames=paths)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output_dir', type=Path)
    parser.add_argument('--limit', type=int)
    parser.add_argument('--cache', type=Path, default=CACHE_DIR)
    args = parser.parse_args(argv)
    result = export_companion_frames(args.source, args.output_dir, limit=args.limit, cache=args.cache)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
