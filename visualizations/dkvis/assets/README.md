# Embedded slide icons

`robot.svg` is an original, simple vector robot icon used only on the title
slide for the LLM-assistance disclosure. Keep the icon as an SVG and render it
with Manim's `SVGMobject`, next to ordinary `tex()` text. Do not insert the
Unicode emoji directly into `tex()` or `math()`: those are compiled by LaTeX
and the deck's default TeX setup cannot render emoji glyphs.

To use other Unicode symbols that your LaTeX engine cannot draw, add a local
SVG asset and group it with a `Tex`/`MathTex` label in a `VGroup`.
