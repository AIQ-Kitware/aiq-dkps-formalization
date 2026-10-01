"""Render a manim-slides deck and convert it for presenting or sharing.

Run from ``visualizations/``::

    uv run python -m dkvis.build_slides sine-theta             # 1080p60 + HTML
    uv run python -m dkvis.build_slides sine-theta -q l        # fast draft
    uv run python -m dkvis.build_slides sine-theta-full --pdf  # + one page per build
    uv run python -m dkvis.build_slides sine-theta-full --handout  # + one page per scene
    uv run python -m dkvis.build_slides sine-theta --list      # scene names, in order

Decks:

* ``sine-theta-short`` -- the 15-minute core talk (intuition, theorem, what was
  formalized, and the Proposition 4.4 counterexample);
* ``sine-theta-full`` -- everything, with optional slides badged ``*`` (technical
  depth) or ``**`` (backup);
* ``sine-theta`` -- the full deck without the VTK scenes;
* ``sine-theta-3d`` and ``prop44`` -- those sections alone.

A deck module may define ``prepare(refresh)`` to render assets it needs (the 3D
deck renders its VTK stills and movies); ``--refresh-assets`` forces that.
Each deck renders into its own ``slides-<deck>/`` folder, and every slide
carries its number in that deck bottom-right ("7 / 16"), the same on all of a
slide's builds.
``--scenes`` re-renders only the named scenes; conversion always uses the whole
deck.

The handout (``--handout``) has one page per scene: the final frame of its last
build, so every scene's last build must hold everything the slide says.  A
build that plays an external video (``src``, e.g. a looping VTK movie) is a
live demo, not a page, so the handout uses the last build before it.  Set ``DKVIS_THEME=light`` for a light-background deck.
"""

from __future__ import annotations

import argparse
import importlib
import os
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

MAIN = "dkvis.slides_sine_theta"
THREE_D = "dkvis.slides_sine_theta_3d"
PROP44 = "dkvis.slides_prop44"

# Presentation order of each deck, by scene name.  Every name must be defined in
# one of MODULES.  Slides with ``depth`` "*" or "**" carry a badge; the short
# deck contains only unmarked (core) slides.
DECK_SCENES = {
    "sine-theta-short": [
        "S00TitleShort", "S00bSetting", "S01Ellipse", "S02Perturb", "S03NoGap", "S03cUnstable", "S03bWanted", "S04Angle", "S05Residual",
        "S06Gap", "S07Theorem", "S08Why", "S11Payoff", "D01Planes", "S12Lean",
        "P01Claim", "P02Counterexample", "S14Summary",
    ],
    "sine-theta-full": [
        "S00Title", "S00bSetting", "S01Ellipse", "S02Perturb", "S03NoGap", "S03cUnstable", "S03bWanted", "S04Angle", "S04bSinThetaOperator",
        "S05Residual", "S06Gap", "S07Theorem", "S08Why", "S08Components", "S09Sylvester",
        "S11Payoff", "S10Sharp", "D01Planes", "D02Tilt", "D03Gap", "D04Perturb", "D05TryIt", "S12Lean",
        "S13Family", "P01Claim", "P02Counterexample", "P03Why", "P04Details", "S14Summary",
    ],
    "sine-theta-3d": ["D01Planes", "D02Tilt", "D03Gap", "D04Perturb", "D05TryIt"],
    "prop44": ["P01Claim", "P02Counterexample", "P03Why", "P04Details"],
}
# The full deck without the VTK scenes, for machines without VTK.
DECK_SCENES["sine-theta"] = [n for n in DECK_SCENES["sine-theta-full"] if not n.startswith("D")]

MODULES = [MAIN, THREE_D, PROP44]
DECKS = list(DECK_SCENES)


def _module_of() -> dict[str, str]:
    owner = {}
    for module in MODULES:
        for name, obj in vars(importlib.import_module(module)).items():
            if isinstance(obj, type) and getattr(obj, "__module__", None) == module and hasattr(obj, "construct"):
                owner[name] = module
    return owner


def deck(name: str) -> list[tuple[str, list[str]]]:
    """``[(module, [scene, ...]), ...]`` grouped by module, in first-use order."""
    owner = _module_of()
    grouped: dict[str, list[str]] = {}
    for scene in DECK_SCENES[name]:
        if scene not in owner:
            raise KeyError(f"deck {name!r} names unknown scene {scene!r}")
        grouped.setdefault(owner[scene], []).append(scene)
    return list(grouped.items())


def _run(*args: str, deck: str | None = None) -> None:
    cmd = [sys.executable, "-m", "manim_slides", *args]
    print("+", " ".join(cmd), flush=True)
    env = dict(os.environ)
    if deck:
        # Read by DeckSlide: render into slides-<deck>/ and number by this deck's order.
        env["DKVIS_DECK"] = deck
    subprocess.run(cmd, cwd=ROOT, check=True, env=env)


def write_handout(deck_name: str, out: Path) -> None:
    """One PDF page per scene: the last frame of its last manim-drawn build."""
    from PIL import Image

    folder = ROOT / f"slides-{deck_name}"
    pages = []
    with tempfile.TemporaryDirectory() as tmp:
        for k, scene in enumerate(DECK_SCENES[deck_name]):
            slides = json.loads((folder / f"{scene}.json").read_text())["slides"]
            drawn = [s for s in slides if not s.get("src")]
            frame = Path(tmp) / f"{k:03d}.png"
            # -sseof seeks near the end; -update keeps overwriting, leaving the last frame.
            subprocess.run(
                ["ffmpeg", "-loglevel", "error", "-sseof", "-0.5", "-i", str(ROOT / drawn[-1]["file"]),
                 "-update", "1", "-y", str(frame)],
                check=True,
            )
            pages.append(Image.open(frame).convert("RGB"))
    first, *rest = pages
    # 13.33 in wide, the size of a 16:9 presentation slide.
    first.save(out, save_all=True, append_images=rest, resolution=first.width / 13.333)
    print(f"wrote {out} ({len(pages)} pages)")


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
    parser.add_argument("--handout", action="store_true", help="also write renders/<deck>.handout.pdf (one page per scene)")
    args = parser.parse_args()

    segments = deck(args.deck)
    names = DECK_SCENES[args.deck]
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
            _run("render", f"--quality={args.quality}", str(source), *scenes, deck=args.deck)

    renders = ROOT / "renders"
    renders.mkdir(exist_ok=True)
    html = args.html or renders / f"{args.deck}.html"
    folder = ["--folder", f"slides-{args.deck}"]
    convert = ["convert", *folder, "--to", "html", *names, str(html), "-cslide_number=true", "-ccontrols=true"]
    if args.one_file:
        convert.insert(1, "--one-file")
    _run(*convert)
    if args.pdf:
        _run("convert", *folder, "--to", "pdf", *names, str(renders / f"{args.deck}.pdf"))
    if args.pptx:
        _run("convert", *folder, "--to", "pptx", *names, str(renders / f"{args.deck}.pptx"))
    if args.handout:
        write_handout(args.deck, renders / f"{args.deck}.handout.pdf")
    print(f"\nPresent live:  manim-slides present --folder slides-{args.deck} {' '.join(names)}")
    print(f"Or open:       {html}")


if __name__ == "__main__":
    main()
