"""Read the authored presentation text and export one TTS-ready file per slide.

Run ``python -m dkvis.matching_narration`` from visualizations/. This exports
text and a manifest; it does not invoke a speech model or synthesize audio.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re

from dkvis.decks.matching import SCENES

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "narration" / "matching-proof.md"


@dataclass(frozen=True)
class Narration:
    title: str
    text: str


def read_narration(path: Path = SOURCE) -> dict[str, Narration]:
    source = path.read_text()
    headings = list(re.finditer(r"^## (M\d{2}\w+): (.+)$", source, re.MULTILINE))
    result = {}
    for i, match in enumerate(headings):
        name, title = match.groups()
        end = headings[i+1].start() if i+1 < len(headings) else len(source)
        text = source[match.end():end].strip()
        if name in result or not text:
            raise ValueError(f"duplicate or empty narration section: {name}")
        # Preserve paragraph pauses but join source wrapping within each paragraph.
        text = "\n\n".join(" ".join(p.split()) for p in text.split("\n\n") if p.strip())
        result[name] = Narration(title, text)
    if list(result) != SCENES:
        raise ValueError("narration sections must follow the matching-proof scene order")
    return result


def export(out: Path, *, theme: str = "dark") -> Path:
    if theme not in {"dark", "light"}:
        raise ValueError("theme must be dark or light")
    out.mkdir(parents=True, exist_ok=True)
    scripts = read_narration()
    expected = {f"{number:02d}-{scene}.txt" for number, scene in enumerate(scripts, 1)}
    # A scene insertion changes later numbers. Retire only our stale exports.
    for old in out.glob("*-M*.txt"):
        if re.fullmatch(r"\d{2}-M\d{2}\w+\.txt", old.name) and old.name not in expected:
            old.unlink()
    entries = []
    suffix = "-light" if theme == "light" else ""
    for number, (scene, script) in enumerate(scripts.items(), 1):
        filename = f"{number:02d}-{scene}.txt"
        (out / filename).write_text(script.text + "\n")
        entries.append({"number": number, "scene": scene, "title": script.title,
                        "text_file": filename,
                        "slide_json": f"slides-matching-proof{suffix}/{scene}.json"})
    manifest = out / "manifest.json"
    manifest.write_text(json.dumps({"deck": "matching-proof", "theme": theme,
        "source": str(SOURCE.relative_to(ROOT)), "slides": entries}, indent=2) + "\n")
    (out / "presentation.txt").write_text("\n\n".join(
        f"Slide {i}: {script.title}\n\n{script.text}"
        for i, script in enumerate(scripts.values(), 1)) + "\n")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / "renders" / "matching-proof-narration")
    parser.add_argument("--theme", choices=["dark", "light"], default="dark")
    args = parser.parse_args()
    manifest = export(args.out, theme=args.theme)
    print(f"Exported {len(SCENES)} narration files, presentation.txt, and {manifest}")


if __name__ == "__main__":
    main()
