# G3 slide renderer redesign and speech pagination

## Scope

- Twenty-six G3 companion slide decks (405 slides) use the revised shared standalone presentation system.
- Added 119 curated MathTex formulas across the decks; equations render to SVG paths from local Manim or TeX/Poppler.
- Added `slide_math.py` and updated the optional PptxGenJS exporter to place vector glyphs instead of Unicode approximations.
- Reworked typography, mathematical stage, geometry panels, reading layouts, and embedded/mobile presentation behavior. Generated outputs remain outside Git.
- G2 and G3 audio pagination now packs entire sentences whenever possible. Only sentences longer than the page character limit can cross a page boundary.
- Updated audio and browser duration-cache identities with `sentence-aware-v2` to regenerate pages whose boundaries changed. The Breeze synthesis segment limits and default Kokoro `af_alloy` voice are unchanged.

## Editorial conventions

The `mathtex` field belongs to slide source, not the TTS narration. A deck remains independently readable: explanations and hypotheses stay in slide text, and figures and equations communicate the mathematical structure directly.

## Validation

The 26 decks built to standalone HTML, mathematical SVGs were checked for compilation, the initial presentation was exported to PowerPoint, and representative browser renders were inspected. The browser layout audit found no slide-canvas overflow. Focused server, slide, audio, and graph tests cover the new rendering and pagination behavior.
