# Deck experiments

Use this directory for materially different presentation compositions that are
worth rendering side by side.  An experiment should primarily change scene
selection/order or choose between alternative reusable components; it should not
fork a whole scene module merely to move slides around.

Give experiments descriptive names such as `friday_math_first.py` or
`friday_process_first.py`.  Do not use `v2`, `new`, or `final` as the main
distinction.

To make an experiment renderable, create a `DeckSpec` and add it explicitly to
`dkvis/decks/__init__.py`.  Keep the reference decks unchanged so comparisons
remain meaningful.
