"""Render a manim-slides deck and convert it for presenting or sharing.

Run from ``visualizations/`` (or use the Makefile)::

    uv run --extra vtk --extra slides python -m dkvis.build_slides part3-family -q l    # one part, fast draft
    uv run --extra vtk --extra slides python -m dkvis.build_slides sine-theta-full      # all parts, 1080p60 + HTML
    uv run --extra vtk --extra slides python -m dkvis.build_slides sine-theta-full --pdf --handout
    uv run --extra vtk --extra slides python -m dkvis.build_slides part1-sine-theta --list

Decks:

* ``sine-theta-short`` -- the 15-minute core talk (intuition, theorem, what was
  formalized, and the Proposition 4.4 counterexample), rendered on its own;
* ``part1-sine-theta`` ... ``part7-glossary`` -- the parts of the full talk.  Each
  renders on its own into ``slides-<part>/`` and gets its own HTML, so a part can
  be rebuilt and shared without touching the others.  Slides are numbered within
  their part ("3 / 7"), and the footer names the part;
* ``sine-theta-full`` -- the parts in order.  It is assembled from the parts'
  renders without rendering anything itself, so its slides carry their parts'
  numbers and footers.  Optional slides are badged ``*`` (technical depth) or
  ``**`` (backup).

A deck module may define ``prepare(refresh)`` to render assets it needs (the 3D
part renders its VTK stills and movies); ``--refresh-assets`` forces that.
``--scenes`` re-renders only the named scenes; conversion always uses the whole
deck.

Scenes render in parallel, one process per scene and ``--jobs`` at a time
(default: one per CPU); each scene's manim output goes to
``renders/logs/<deck>--<scene>.log``.  ``--fps`` overrides the quality's frame
rate, e.g. ``-q h --fps 30`` for 1080p at half the frames of the 60 fps default.

The handout (``--handout``) has one page per scene: the final frame of its last
build, so every scene's last build must hold everything the slide says.  A
build that plays an external video (``src``, e.g. a looping VTK movie) is a
live demo, not a page, so the handout uses the last build before it.  Set
``DKVIS_THEME=light`` for a light-background deck; its outputs carry a ``-light``
suffix (``slides-<deck>-light/``, ``renders/<deck>-light.html``) beside the dark ones.
"""

from __future__ import annotations

import argparse
import importlib
import json
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def output_name(deck_name: str) -> str:
    """``deck_name`` plus the theme suffix: the name of its scene folder and renders."""
    from dkvis.palette import OUTPUT_SUFFIX

    return f"{deck_name}{OUTPUT_SUFFIX}"

MAIN = "dkvis.slides_sine_theta"
THREE_D = "dkvis.slides_sine_theta_3d"
PROP44 = "dkvis.slides_prop44"
FAMILY = "dkvis.slides_family"
FAMILY_DETAIL = "dkvis.slides_family_detail"
PROCESS = "dkvis.slides_process"
GLOSSARY = "dkvis.slides_glossary"

# Presentation order of each deck, by scene name.  Every name must be defined in
# one of MODULES.  Slides with ``depth`` "*" or "**" carry a badge; the short
# deck contains only unmarked (core) slides.
SHORT = "sine-theta-short"
FULL = "sine-theta-full"

# The parts of the full talk, in order, with the footer each part's slides carry.
PARTS = {
    "part1-sine-theta": [
        "S00Title", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03dCompute", "S03NoGap",
        "S03cUnstable", "S04Angle", "S04bSinThetaOperator", "S05Residual", "S06Gap", "S07Theorem", "S08Why", "S08Components",
        "S09Sylvester", "S11Payoff", "S10Sharp", "S12Lean",
    ],
    "part2-3d": ["D01Planes", "D02Tilt", "D03Gap", "D04Perturb", "D05TryIt"],
    "part3-family": [
        "F01Setup", "F01bAngles", "F01cTwoByTwo",
        "F02TanTheta", "F02bTanBuys", "F02cTanWhy",
        "F03SinTwoTheta", "F03bReflect", "F03cPrice",
        "F04TanTwoTheta", "F04bJacobi", "F04cRepulsion",
        "F09WhichOne", "S13Family",
    ],
    "part4-prop44": ["P01Claim", "P02Counterexample", "P03Why", "P04Details"],
    "part5-process": ["W01Workflow", "W02TwoChecks", "W03ThreeStatements", "W04Reversals", "W05Scale", "W06Claims"],
    "part6-summary": ["S14Summary"],
    "part7-glossary": ["G01Matrices", "G02Spectra", "G03Other"],
}
PART_TITLES = {
    "part1-sine-theta": r"Part 1 $\cdot$ the Davis--Kahan $\sin\Theta$ theorem",
    "part2-3d": r"Part 2 $\cdot$ $\sin\Theta$ in three dimensions",
    "part3-family": r"Part 3 $\cdot$ the $\tan\Theta$, $\sin2\Theta$ and $\tan2\Theta$ theorems",
    "part4-prop44": r"Part 4 $\cdot$ Proposition 4.4, a printed claim that is false",
    "part5-process": r"Part 5 $\cdot$ how the formalization was built",
    "part6-summary": r"Part 6 $\cdot$ summary",
    "part7-glossary": r"Part 7 $\cdot$ notation",
}

DECK_SCENES = {
    SHORT: [
        "S00TitleShort", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03NoGap", "S03cUnstable", "S04Angle", "S05Residual",
        "S06Gap", "S07Theorem", "S08Why", "S11Payoff", "D01Planes", "S12Lean",
        "P01Claim", "P02Counterexample", "S14Summary",
    ],
    **PARTS,
    FULL: [scene for scenes in PARTS.values() for scene in scenes],
}
# Decks assembled from other decks' renders rather than rendered themselves.
COMPOSITES = {FULL: list(PARTS)}

MODULES = [MAIN, THREE_D, FAMILY, FAMILY_DETAIL, PROP44, PROCESS, GLOSSARY]
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


def _render_scene(deck_name: str, module: str, scene: str, quality: str, fps: float | None) -> float:
    """Render one scene of ``deck_name`` in its own process; return the seconds it took."""
    source = Path(importlib.import_module(module).__file__).relative_to(ROOT)
    # ``--quality=h``, not ``-qh``: manim-slides would read ``-qh`` as ``-q -h`` and print help.
    cmd = [sys.executable, "-m", "manim_slides", "render", f"--quality={quality}"]
    if fps:
        cmd.append(f"--fps={fps:g}")
    cmd += [str(source), scene]
    log = ROOT / "renders" / "logs" / f"{output_name(deck_name)}--{scene}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    # Read by DeckSlide: render into slides-<deck>/ and number by this deck's order.
    env = {**os.environ, "DKVIS_DECK": deck_name}
    start = time.monotonic()
    with open(log, "w") as out:
        result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        tail = "\n".join(log.read_text(errors="replace").splitlines()[-25:])
        raise RuntimeError(f"{deck_name}/{scene} failed (log: {log}):\n{tail}")
    return time.monotonic() - start


def render(
    deck_names: list[str],
    quality: str,
    fps: float | None = None,
    only: list[str] | None = None,
    refresh_assets: bool = False,
    jobs: int | None = None,
) -> None:
    """Render the (non-composite) decks' scenes, or only those in ``only``, ``jobs`` at a time."""
    tasks = [
        (name, module, scene)
        for name in deck_names
        for module, scenes in deck(name)
        for scene in scenes
        if not only or scene in only
    ]
    for module in dict.fromkeys(module for _, module, _ in tasks):
        mod = importlib.import_module(module)
        if hasattr(mod, "prepare"):
            mod.prepare(refresh=refresh_assets)
    jobs = jobs or os.cpu_count() or 1
    print(f"rendering {len(tasks)} scenes, {jobs} at a time", flush=True)
    with ThreadPoolExecutor(jobs) as pool:
        futures = {pool.submit(_render_scene, *task, quality, fps): task for task in tasks}
        try:
            for done, future in enumerate(as_completed(futures), 1):
                name, _, scene = futures[future]
                print(f"[{done}/{len(tasks)}] {name}/{scene} ({future.result():.0f} s)", flush=True)
        except BaseException:
            pool.shutdown(cancel_futures=True)
            raise


def assemble(deck_name: str) -> None:
    """Point ``slides-<deck>/`` at its parts' rendered scenes (the JSON files name the videos)."""
    folder = ROOT / f"slides-{output_name(deck_name)}"
    folder.mkdir(exist_ok=True)
    for stale in folder.glob("*.json"):
        stale.unlink()
    for part in COMPOSITES[deck_name]:
        for scene in DECK_SCENES[part]:
            src = ROOT / f"slides-{output_name(part)}" / f"{scene}.json"
            if not src.exists():
                raise FileNotFoundError(f"{src} is missing; render {part} first")
            (folder / src.name).write_text(src.read_text())


def write_handout(deck_name: str, out: Path) -> None:
    """One PDF page per scene: the last frame of its last manim-drawn build."""
    from PIL import Image

    folder = ROOT / f"slides-{output_name(deck_name)}"
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
    parser.add_argument("--fps", type=float, help="frame rate, overriding the quality's (e.g. 30 with -q h)")
    parser.add_argument("-j", "--jobs", type=int, help="scenes to render at once (default: one per CPU)")
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

    names = DECK_SCENES[args.deck]
    if args.list:
        print(" ".join(names))
        return

    if not args.no_render:
        render(
            COMPOSITES.get(args.deck, [args.deck]),
            args.quality,
            fps=args.fps,
            only=args.scenes,
            refresh_assets=args.refresh_assets,
            jobs=args.jobs,
        )
    if args.deck in COMPOSITES:
        assemble(args.deck)

    renders = ROOT / "renders"
    renders.mkdir(exist_ok=True)
    out = output_name(args.deck)
    html = args.html or renders / f"{out}.html"
    folder = ["--folder", f"slides-{out}"]
    convert = ["convert", *folder, "--to", "html", *names, str(html), "-cslide_number=true", "-ccontrols=true"]
    if args.one_file:
        convert.insert(1, "--one-file")
    _run(*convert)
    if args.pdf:
        _run("convert", *folder, "--to", "pdf", *names, str(renders / f"{out}.pdf"))
    if args.pptx:
        _run("convert", *folder, "--to", "pptx", *names, str(renders / f"{out}.pptx"))
    if args.handout:
        write_handout(args.deck, renders / f"{out}.handout.pdf")
    print(f"\nPresent live:  manim-slides present --folder slides-{out} {' '.join(names)}")
    print(f"Or open:       {html}")


if __name__ == "__main__":
    main()
