"""Read the authored presentation text and export one TTS-ready file per slide.

Run ``python -m dkvis.presentation text --deck NAME`` from visualizations/. This exports
text and a manifest; it does not invoke a speech model or synthesize audio.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re

from dkvis.decks import DECKS, get_deck
from dkvis.presentation.paths import ROOT


@dataclass(frozen=True)
class Narration:
    title: str
    motivation: str
    reminder: str
    beats: tuple[str, ...]

    @property
    def text(self) -> str:
        return "\n\n".join(self.beats)


def read_narration(path: Path, *, scenes) -> dict[str, Narration]:
    source = path.read_text()
    headings = list(re.finditer(r"^## ([A-Za-z_]\w*): (.+)$", source, re.MULTILINE))
    result = {}
    for i, match in enumerate(headings):
        name, title = match.groups()
        end = headings[i+1].start() if i+1 < len(headings) else len(source)
        body = source[match.end():end].strip()
        why = re.match(r"Why: ([^\n]+)\n", body)
        if not why:
            raise ValueError(f"missing learner motivation: {name}")
        body = body[why.end():].strip()
        recall = re.match(r"Recall: ([^\n]+)\n", body)
        if not recall:
            raise ValueError(f"missing local notation reminder: {name}")
        body = body[recall.end():].strip()
        if name in result or not body:
            raise ValueError(f"duplicate or empty narration section: {name}")
        # Preserve paragraph pauses but join source wrapping within each paragraph.
        beats = tuple("\n\n".join(" ".join(p.split()) for p in beat.split("\n\n") if p.strip())
                      for beat in body.split("<!-- beat -->"))
        if not all(beats):
            raise ValueError(f"empty narration build: {name}")
        result[name] = Narration(title, why.group(1), recall.group(1), beats)
    if list(result) != list(scenes):
        raise ValueError(f"narration sections must follow the deck's scene order: {path}")
    return result


def narrated_decks() -> list[str]:
    return [name for name, deck in DECKS.items() if deck.narration]


def read_deck_narration(deck_name: str) -> dict[str, Narration]:
    deck = get_deck(deck_name)
    if deck.narration is None:
        raise ValueError(f"Deck {deck_name!r} has no authored transcript; set DeckSpec.narration first.")
    return read_narration(ROOT / deck.narration, scenes=deck.scene_names)


def export(out: Path, *, deck_name: str, theme: str = "dark") -> Path:
    if theme not in {"dark", "light"}:
        raise ValueError("theme must be dark or light")
    out.mkdir(parents=True, exist_ok=True)
    scripts = read_deck_narration(deck_name)
    expected = {f"{number:02d}-{scene}.txt" for number, scene in enumerate(scripts, 1)}
    # A scene insertion changes later numbers. Retire only our stale exports.
    for old in out.glob("*.txt"):
        if re.fullmatch(r"\d{2,}-[A-Za-z_]\w*\.txt", old.name) and old.name not in expected:
            old.unlink()
    entries = []
    beat_dir = out / "beats"
    beat_dir.mkdir(exist_ok=True)
    expected_beats = set()
    suffix = "-light" if theme == "light" else ""
    for number, (scene, script) in enumerate(scripts.items(), 1):
        filename = f"{number:02d}-{scene}.txt"
        (out / filename).write_text(script.text + "\n")
        beat_files = []
        for k, text in enumerate(script.beats, 1):
            beat_name = f"{number:02d}-{scene}-{k:02d}.txt"
            expected_beats.add(beat_name)
            (beat_dir / beat_name).write_text(text + "\n")
            beat_files.append(f"beats/{beat_name}")
        entries.append({"number": number, "scene": scene, "title": script.title,
                        "motivation": script.motivation, "text_file": filename,
                        "beat_files": beat_files,
                        "slide_json": f"slides-{deck_name}{suffix}/{scene}.json"})
    for old in beat_dir.glob("*.txt"):
        if re.fullmatch(r"\d{2,}-[A-Za-z_]\w*-\d{2,}\.txt", old.name) and old.name not in expected_beats:
            old.unlink()
    manifest = out / "manifest.json"
    manifest.write_text(json.dumps({"deck": deck_name, "theme": theme,
        "source": get_deck(deck_name).narration, "slides": entries}, indent=2) + "\n")
    (out / "presentation.txt").write_text("\n\n".join(
        f"Slide {i}: {script.title}\n\n{script.text}"
        for i, script in enumerate(scripts.values(), 1)) + "\n")
    return manifest


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--deck', choices=narrated_decks(), required=True)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--theme", choices=["dark", "light"], default="dark")
    args = parser.parse_args(argv)
    suffix = '-light' if args.theme == 'light' else ''
    out = args.out or ROOT / 'renders' / f'{args.deck}{suffix}-narration'
    manifest = export(out, theme=args.theme, deck_name=args.deck)
    print(f"Exported {len(read_deck_narration(args.deck))} narration files, presentation.txt, and {manifest}")


if __name__ == "__main__":
    main()
