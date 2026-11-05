"""Lean 4 syntax colors and a bundled mathematical monospace font."""
from contextlib import nullcontext
import os
from pathlib import Path
from xml.sax.saxutils import escape

from manim import MarkupText, register_font
from pygments import lex
from pygments.lexers import get_lexer_by_name
from pygments.token import Comment, Keyword, Literal, Name, Operator

from dkvis.slide_style import FG, GAP, MUTED, RESID, TRIAL, WANTED

FONT_FILE = Path(__file__).with_name('fonts')/'JuliaMono-Regular.ttf'


def lean_markup(source, *, proof=False):
    """Preserve source text while distinguishing syntax and the proof application."""
    spans = []
    # Avoid the lexer's automatic trailing newline: code is displayed verbatim.
    lexer = get_lexer_by_name('lean4', stripnl=False, ensurenl=False)
    for token, value in lex(source, lexer):
        color = RESID if proof else FG
        if token in Comment:
            color = MUTED
        elif token in Keyword:
            color = GAP
        elif token in Literal.Number:
            color = TRIAL
        elif token in Operator or token in Name.Builtin:
            color = WANTED
        spans.append(f'<span foreground="{color}">{escape(value)}</span>')
    return ''.join(spans)


def lean_code(source, *, size=23, proof=False):
    override = os.environ.get('DKVIS_LEAN_FONT')
    with nullcontext() if override else register_font(FONT_FILE):
        return MarkupText(lean_markup(source, proof=proof), font=override or 'JuliaMono',
                          font_size=size, line_spacing=.55, disable_ligatures=True,
                          color=FG)
