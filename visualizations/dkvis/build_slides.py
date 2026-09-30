"""Render a manim-slides deck and convert it for presenting or sharing.

Run from ``visualizations/``::

    uv run python -m dkvis.build_slides sine-theta             # 1080p60 + HTML
    uv run python -m dkvis.build_slides sine-theta -q l        # fast draft
    uv run python -m dkvis.build_slides sine-theta-full --pdf  # + one page per build
    uv run python -m dkvis.build_slides sine-theta --list      # scene names, in order

Decks:

* ``sine-theta`` -- the 2D intuition deck (:mod:`dkvis.slides_sine_theta`);
* ``sine-theta-3d`` -- the 3D VTK deck (:mod:`dkvis.slides_sine_theta_3d`);
* ``sine-theta-full`` -- both, with the 3D slides after the payoff slide.

A deck module may define ``prepare(refresh)`` to render assets it needs (the 3D
deck renders its VTK stills and movies); ``--refresh-assets`` forces that.
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

MAIN = "dkvis.slides_sine_theta"
THREE_D = "dkvis.slides_sine_theta_3d"


def _names(module: str) -> list[str]:
    return [scene.__name__ for scene in importlib.import_module(module).SCENES]


def deck(name: str) -> list[tuple[str, list[str]]]:
    """``[(module, [scene, ...]), ...]`` in presentation order."""
    main = _names(MAIN)
    if name == "sine-theta":
        return [(MAIN, main)]
    if name == "sine-theta-3d":
        return [(THREE_D, _names(THREE_D))]
    if name == "sine-theta-full":
        cut = main.index("S12Lean")
        return [(MAIN, main[:cut]), (THREE_D, _names(THREE_D)), (MAIN, main[cut:])]
    raise KeyError(name)


DECKS = ["sine-theta", "sine-theta-3d", "sine-theta-full"]


def _run(*args: str) -> None:
    cmd = [sys.executable, "-m", "manim_slides", *args]
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=ROOT, check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("deck", choices=DECKS)
    parser.add_argument("-q", "--quality", default="h", choices=list("lmhpk"), help="manim quality (default h = 1080p60)")
    parser.add_argument("--scenes", nargs="+", help="render only these scenes")
    parser.add_argument("--list", action="store_true", help="print scene names in order and exit")
    parser.add_argument("--no-render", action="store_true", help="only convert already-rendered scenes")
    parser.add_argument("--refresh-assets", action="store_true", help="re-render assets such as the VTK movies")
    parser.add_argument("--html", type=Path, help="HTML output (default renders/<deck>.html)")
    parser.add_argument("--one-file", action="store_true", help="embed the videos in the HTML file")
    parser.add_argument("--pdf", action="store_true", help="also write renders/<deck>.pdf (last frame of each build)")
    parser.add_argument("--pptx", action="store_true", help="also write renders/<deck>.pptx")
    args = parser.parse_args()

    segments = deck(args.deck)
    names = [n for _, scenes in segments for n in scenes]
    if args.list:
        print(" ".join(names))
        return

    if not args.no_render:
        by_module: dict[str, list[str]] = {}
        for module, scenes in segments:
            by_module.setdefault(module, []).extend(s for s in scenes if not args.scenes or s in args.scenes)
        for module, scenes in by_module.items():
            if not scenes:
                continue
            mod = importlib.import_module(module)
            if hasattr(mod, "prepare"):
                mod.prepare(refresh=args.refresh_assets)
            source = Path(mod.__file__).relative_to(ROOT)
            # ``--quality=h``, not ``-qh``: manim-slides would read ``-qh`` as ``-q -h`` and print help.
            _run("render", f"--quality={args.quality}", str(source), *scenes)

    renders = ROOT / "renders"
    renders.mkdir(exist_ok=True)
    html = args.html or renders / f"{args.deck}.html"
    convert = ["convert", "--to", "html", *names, str(html), "-cslide_number=true", "-ccontrols=true"]
    if args.one_file:
        convert.insert(3, "--one-file")
    _run(*convert)
    if args.pdf:
        _run("convert", "--to", "pdf", *names, str(renders / f"{args.deck}.pdf"))
    if args.pptx:
        _run("convert", "--to", "pptx", *names, str(renders / f"{args.deck}.pptx"))
    print(f"\nPresent live:  manim-slides present {' '.join(names)}")
    print(f"Or open:       {html}")


if __name__ == "__main__":
    main()
