"""Render a manim-slides deck and convert it for presenting or sharing.

Run from ``visualizations/``::

    uv run --extra slides python -m dkvis.build_slides sine-theta            # 1080p60 + HTML
    uv run --extra slides python -m dkvis.build_slides sine-theta -q l       # fast draft
    uv run --extra slides python -m dkvis.build_slides sine-theta --pdf      # + one page per build
    uv run --extra slides python -m dkvis.build_slides sine-theta --list     # scene names, in order

``--scenes`` re-renders only the named scenes; conversion always uses the whole
deck.  Set ``DKVIS_THEME=light`` for a light-background deck.
"""

from __future__ import annotations

import argparse
import importlib
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

DECKS = {
    "sine-theta": "dkvis.slides_sine_theta",
}


def scene_names(deck: str) -> list[str]:
    module = importlib.import_module(DECKS[deck])
    return [scene.__name__ for scene in module.SCENES]


def _run(*args: str) -> None:
    cmd = [sys.executable, "-m", "manim_slides", *args]
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=ROOT, check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("deck", choices=sorted(DECKS))
    parser.add_argument("-q", "--quality", default="h", choices=list("lmhpk"), help="manim quality flag (default h = 1080p60)")
    parser.add_argument("--scenes", nargs="+", help="render only these scenes")
    parser.add_argument("--list", action="store_true", help="print scene names in order and exit")
    parser.add_argument("--no-render", action="store_true", help="only convert already-rendered scenes")
    parser.add_argument("--html", type=Path, help="HTML output (default renders/<deck>.html)")
    parser.add_argument("--one-file", action="store_true", help="embed the videos in the HTML file")
    parser.add_argument("--pdf", action="store_true", help="also write renders/<deck>.pdf (last frame of each build)")
    parser.add_argument("--pptx", action="store_true", help="also write renders/<deck>.pptx")
    args = parser.parse_args()

    names = scene_names(args.deck)
    if args.list:
        print(" ".join(names))
        return

    source = Path(importlib.import_module(DECKS[args.deck]).__file__).relative_to(ROOT)
    if not args.no_render:
        _run("render", f"--quality={args.quality}", str(source), *(args.scenes or names))

    renders = ROOT / "renders"
    renders.mkdir(exist_ok=True)
    html = args.html or renders / f"{args.deck}.html"
    convert = ["convert", "--to", "html", *names, str(html)]
    if args.one_file:
        convert.insert(3, "--one-file")
    _run(*convert, "-cslide_number=true", "-ccontrols=true")
    if args.pdf:
        _run("convert", "--to", "pdf", *names, str(renders / f"{args.deck}.pdf"))
    if args.pptx:
        _run("convert", "--to", "pptx", *names, str(renders / f"{args.deck}.pptx"))
    print(f"\nPresent live:  manim-slides present {' '.join(names)}")
    print(f"Or open:       {html}")


if __name__ == "__main__":
    main()
