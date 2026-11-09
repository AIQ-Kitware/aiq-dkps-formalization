"""Build vector LaTeX mathematics for source-controlled slide decks.

MathTex is preferred when Manim is installed. A TeX + Inkscape path renders
the same Computer Modern mathematics when only system TeX is available.
All SVG assets are cached locally, never committed with the source decks.
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import xml.etree.ElementTree as ET

MATH_RENDERER_VERSION = 'vector-math-v7'
TEX_PREAMBLE = r'''\documentclass[border=2pt,varwidth]{standalone}
\usepackage{amsmath,amssymb,mathtools,bm,mathrsfs}
\begin{document}
$\displaystyle %s$
\end{document}
'''


def _run(command: list[str], directory: Path, *, timeout: int = 40) -> None:
    try:
        proc = subprocess.run(command, cwd=directory, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=timeout, check=False)
    except FileNotFoundError as ex:
        raise RuntimeError(f'Missing slide mathematics renderer: {command[0]}') from ex
    if proc.returncode:
        output = proc.stdout.decode('utf8', 'replace')
        raise RuntimeError(f'Slide math rendering failed ({command[0]}):\n{output[-3500:]}')


def _latex_svg(tex: str, directory: Path) -> str:
    # TeX source is repository-authored. It is never accepted from web requests.
    if not (shutil.which('pdflatex') and shutil.which('pdftocairo')):
        raise RuntimeError('Slide math requires Manim MathTex or pdflatex and pdftocairo')
    (directory/'math.tex').write_text(TEX_PREAMBLE % tex, encoding='utf8')
    _run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
          '-no-shell-escape', 'math.tex'], directory)
    # Poppler retains TeX extensible delimiters (e.g. matrix brackets).
    # Inkscape's PDF import can drop those glyphs.
    _run(['pdftocairo', '-svg', 'math.pdf', 'math.svg'], directory)
    return (directory/'math.svg').read_text(encoding='utf8')


def _manim_svg(tex: str, directory: Path) -> str:
    from manim import MathTex
    # Let Manim own its TeX template and vector glyph generation.
    formula = MathTex(tex)
    path = Path(formula.file_name)
    return path.read_text(encoding='utf8')


def _prepare_inline(svg: str, title: str, prefix: str) -> str:
    """Normalize SVG into a self-contained document fragment with unique IDs."""
    # Inkscape may export PDF math glyph control characters in aria-label.
    # Remove those labels; we set a clean accessible label on the root.
    svg = re.sub(r'\saria-label="[^"]*"', '', svg)
    root = ET.fromstring(svg)
    if not root.tag.endswith('svg'):
        raise ValueError('Math renderer returned a non-SVG document')
    # Disallow external links or embedded scripts, even from renderer output.
    for node in root.iter():
        if node.tag.endswith(('script', 'foreignObject')):
            raise ValueError('Unexpected active SVG content in generated math')
        for key, value in list(node.attrib.items()):
            if key.endswith('href') and not value.startswith('#'):
                raise ValueError('Unexpected external reference in generated math SVG')
    replacements = {}
    for node in root.iter():
        if 'id' in node.attrib:
            old = node.attrib['id']
            replacements[old] = prefix + '-' + old
            node.attrib['id'] = replacements[old]
    for node in root.iter():
        for key, value in list(node.attrib.items()):
            for old, new in replacements.items():
                value = value.replace(f'url(#{old})', f'url(#{new})')
                if key.endswith('href') and value == f'#{old}':
                    value = '#' + new
            node.attrib[key] = value
    # Inkscape emits black fills on glyph paths. Match the slide palette.
    for node in root.iter():
        if node.get('fill', '').replace(' ', '') in ('rgb(0%,0%,0%)', '#000', '#000000', 'black'):
            node.set('fill', 'currentColor')
        style = node.get('style')
        if style and ('fill:#000000' in style or 'stroke:#000000' in style):
            node.set('style', style.replace('fill:#000000', 'fill:currentColor')
                     .replace('stroke:#000000', 'stroke:currentColor'))
    root.set('role', 'img')
    root.set('aria-label', title)
    root.set('class', 'math-svg')
    ET.register_namespace('', 'http://www.w3.org/2000/svg')
    ET.register_namespace('xlink', 'http://www.w3.org/1999/xlink')
    return ET.tostring(root, encoding='unicode', method='xml')


class MathSvgRenderer:
    """Cache exact TeX-to-path outputs and embed their vector glyphs into HTML."""
    def __init__(self, cache_dir: Path):
        self.cache_dir = Path(cache_dir)
        self.backend = os.getenv('DKVIS_SLIDE_MATH_RENDERER', 'auto').lower()
        if self.backend not in ('auto', 'manim', 'latex'):
            raise ValueError('DKVIS_SLIDE_MATH_RENDERER must be auto, manim, or latex')

    def svg(self, tex: str) -> str:
        if not isinstance(tex, str) or not tex.strip() or len(tex) > 4000:
            raise ValueError('A LaTeX equation must be a nonempty source string under 4000 characters')
        digest = hashlib.sha256((MATH_RENDERER_VERSION + ':' + self.backend + ':' + tex).encode()).hexdigest()[:24]
        target = self.cache_dir / f'math-{digest}.svg'
        if target.is_file():
            return target.read_text(encoding='utf8')
        with tempfile.TemporaryDirectory(prefix='dkps-slide-math-') as temp:
            directory = Path(temp)
            if self.backend == 'manim':
                rendered = _manim_svg(tex, directory)
            elif self.backend == 'latex':
                rendered = _latex_svg(tex, directory)
            else:
                try:
                    import manim  # noqa: F401
                except ImportError:
                    rendered = _latex_svg(tex, directory)
                else:
                    rendered = _manim_svg(tex, directory)
            result = _prepare_inline(rendered, tex, digest)
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        # A cache race can safely publish identical content.
        tmp = target.with_suffix(f'.{os.getpid()}.tmp')
        try:
            tmp.write_text(result, encoding='utf8')
            tmp.replace(target)
        finally:
            tmp.unlink(missing_ok=True)
        return result


def export_deck_math_assets(deck_file: Path, output_dir: Path) -> dict[str, str]:
    """Export colored MathTex vector assets for the optional PptxGenJS renderer."""
    import json
    deck = json.loads(Path(deck_file).read_text(encoding='utf8'))
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    renderer = MathSvgRenderer(output_dir / 'cache')
    result = {}
    for index, slide in enumerate(deck['slides']):
        if 'mathtex' not in slide:
            continue
        svg = renderer.svg(slide['mathtex'])
        # PowerPoint SVG drawing does not inherit CSS currentColor.
        svg = svg.replace('currentColor', '#F1C88C')
        dest = output_dir / f'slide-{index+1:03d}.svg'
        dest.write_text(svg, encoding='utf8')
        result[str(index)] = str(dest)
    return result


if __name__ == '__main__':
    import argparse
    import json
    parser = argparse.ArgumentParser(description='Render vector math assets for a G3 companion slide deck')
    parser.add_argument('deck_file', type=Path)
    parser.add_argument('output_dir', type=Path)
    args = parser.parse_args()
    print(json.dumps(export_deck_math_assets(args.deck_file, args.output_dir)))
