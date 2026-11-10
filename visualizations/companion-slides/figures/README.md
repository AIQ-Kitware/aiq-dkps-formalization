# Generated companion figure directory (legacy)

This directory no longer contains source graphics for companion slides. All
companion diagrams are constructed with native Manim shapes in
`visualizations/dkvis/presentation/companion_geometry.py` and composed with
Manim MathTex and text in `companion_manim.py`.

The former SVG files may remain on your local disk after running
`finish_companion_manim_migration.py --write`: that command uses
`git rm --cached` on tracked SVG exports so **local copies are preserved**,
but Git stops tracking them. The existing `.gitignore` prevents re-adding them.

New diagrams must be authored in Python as Manim geometry, rather than by
editing or committing exported SVG files.
