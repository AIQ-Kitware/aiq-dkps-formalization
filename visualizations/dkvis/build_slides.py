"""Render a manim-slides deck and convert it for presenting or sharing.

Run from ``visualizations/`` (or use the Makefile)::

    uv run --extra vtk --extra slides python -m dkvis.build_slides part3-family -q l    # one part, fast draft
    uv run --extra vtk --extra slides python -m dkvis.build_slides sine-theta-full      # all parts, 1080p60 + HTML
    uv run --extra vtk --extra slides python -m dkvis.build_slides sine-theta-full --pdf --handout
    uv run --extra vtk --extra slides python -m dkvis.build_slides part1-sine-theta --list
    uv run --extra vtk --extra slides python -m dkvis.build_slides comprehensive --one-file --html renders/comprehensive.standalone.html

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
* ``kitware-talk`` -- the completed, unchanged 21-scene presentation;
* ``comprehensive`` -- an ordered collection of all distinct mathematical
  scenes, including six chapter transitions and a single VTK finale;
* ``study`` -- the previous long-form learning composition using reusable scenes.

Deck composition lives in :mod:`dkvis.decks`; this module only renders and
converts those specifications.  Optional/backup depth is presentation-specific.

A deck module may define ``prepare(refresh)`` to render assets it needs (the 3D
part renders its VTK stills and movies); ``--refresh-assets`` forces that.
``--scenes`` re-renders only the named scenes; conversion always uses the whole
deck.

Scenes render in parallel, one process per scene and ``--jobs`` at a time
(default: one per CPU); each scene's manim output goes to
``renders/logs/<deck>--<scene>.log``.  ``--fps`` overrides the quality's frame
rate, e.g. ``-q h --fps 30`` for 1080p at half the frames of the 60 fps default.

The handout (``--handout``) has one page per scene.  When a scene has ordinary Manim
builds, its last drawn build is used.  For a video-only scene (e.g. the VTK
finale), the handout uses a frame of the external video.  Set
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

from dkvis.decks import DECKS as DECK_REGISTRY, get_deck

ROOT = Path(__file__).resolve().parent.parent


def output_name(deck_name: str) -> str:
    """``deck_name`` plus the theme suffix: the name of its scene folder and renders."""
    from dkvis.palette import OUTPUT_SUFFIX

    return f"{deck_name}{OUTPUT_SUFFIX}"

# Compatibility views for old scripts that imported these names from this
# module.  New code should use ``dkvis.decks`` and ``DeckSpec`` directly.
DECKS = list(DECK_REGISTRY)
DECK_SCENES = {name: get_deck(name).scene_names for name in DECKS}
COMPOSITES = {
    name: list(get_deck(name).composite_parts)
    for name in DECKS
    if get_deck(name).composite_parts
}
PART_TITLES = {
    name: spec.footer
    for name, spec in DECK_REGISTRY.items()
    if spec.footer and name.startswith("part")
}


def deck(name: str) -> list[tuple[str, list[str]]]:
    """``[(module, [scene, ...]), ...]`` grouped in first-use order."""
    return get_deck(name).grouped_by_module()


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
    slide_use = get_deck(deck_name).slide(scene)
    env = {
        **os.environ,
        "DKVIS_DECK": deck_name,
        # Presence of the variable matters: an empty value explicitly makes a
        # historically optional scene core in this particular presentation.
        "DKVIS_DEPTH": slide_use.depth,
    }
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
    for part in get_deck(deck_name).composite_parts:
        for scene in get_deck(part).scene_names:
            src = ROOT / f"slides-{output_name(part)}" / f"{scene}.json"
            if not src.exists():
                raise FileNotFoundError(f"{src} is missing; render {part} first")
            (folder / src.name).write_text(src.read_text())


def handout_frame_file(slides: list[dict]) -> str:
    """Select the last drawn build, or the movie for a video-only scene.

    The external ``src`` is still a genuine slide, with its own generated
    ``file`` in the Manim Slides scene JSON.  We must not add an extra static
    build just to give the handout something to sample.
    """
    if not slides:
        raise ValueError("scene contains no slides")
    last_drawn = next((slide for slide in reversed(slides) if not slide.get("src")), None)
    return (last_drawn or slides[-1])["file"]


def write_handout(deck_name: str, out: Path) -> None:
    """One PDF page per scene; video-only scenes contribute a movie frame."""
    from PIL import Image

    folder = ROOT / f"slides-{output_name(deck_name)}"
    pages = []
    with tempfile.TemporaryDirectory() as tmp:
        for k, scene in enumerate(get_deck(deck_name).scene_names):
            slides = json.loads((folder / f"{scene}.json").read_text())["slides"]
            frame = Path(tmp) / f"{k:03d}.png"
            # -sseof seeks near the end; -update keeps overwriting, leaving the last frame.
            subprocess.run(
                ["ffmpeg", "-loglevel", "error", "-sseof", "-0.5", "-i", str(ROOT / handout_frame_file(slides)),
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

    names = get_deck(args.deck).scene_names
    if args.list:
        print(" ".join(names))
        return

    if not args.no_render:
        render(
            list(get_deck(args.deck).composite_parts) or [args.deck],
            args.quality,
            fps=args.fps,
            only=args.scenes,
            refresh_assets=args.refresh_assets,
            jobs=args.jobs,
        )
    if get_deck(args.deck).composite_parts:
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
