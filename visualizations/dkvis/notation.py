"""The notation table: which role, and so which color, every symbol has.

This is the single authority for symbol colors.  :mod:`dkvis.palette` says what
each *role* looks like in each theme; this table says which role each *symbol*
plays.  Slides never pick a color for a symbol themselves: in LaTeX they write

* ``\\sym{Lambda1}`` for the symbol itself (``\\Lambda_1`` in its role color), and
* ``\\like{Lambda1}{\\operatorname{spec}(\\Lambda_1)}`` for an expression that
  takes that symbol's color,

and in Python, ``concept_color("Lambda1")`` gives the color for a label or a
mobject that stands for the symbol.  Plain geometry may use the role constants
of :mod:`dkvis.slide_style`, but anything drawn for a symbol whose role is not
obvious from the picture (``Vperp`` is neutral, not amber) should ask here.  To recolor a symbol, change its role here; to change
what a role looks like, change :mod:`dkvis.palette`.  ``\\cx{role}{...}`` remains
for legend prose that names a role directly ("blue: ...").

Operators (``A``, ``Ã``, ``H``, the projectors) are neutral.  So are the blocks
that belong to no role: ``A1`` (the complementary block of the old ``A``) and
``E1`` (a basis of ``V-perp``).
"""

from __future__ import annotations

import re

from dkvis.palette import PALETTE

#: LaTeX color name of each role, and its palette entry.
ROLES = {
    "fg": "FG",
    "muted": "MUTED",
    "wanted": "WANTED",
    "unwanted": "UNWANTED",
    "trial": "TRIAL",
    "sine": "SINE",
    "resid": "RESID",
    "gap": "GAP",
}

#: key: (LaTeX, role)
SYMBOLS: dict[str, tuple[str, str]] = {
    # Operators and blocks with no role.
    "A": (r"A", "fg"),
    "H": (r"H", "fg"),
    "At": (r"\tilde A", "fg"),
    "A1": (r"A_1", "fg"),
    "P": (r"P", "fg"),
    "Q": (r"Q", "fg"),
    "E1": (r"E_1", "fg"),
    "Vperp": (r"V^{\perp}", "fg"),
    "a1": (r"a_1", "fg"),
    # What we want: the exact invariant subspace and its spectrum.
    "U": (r"U", "wanted"),
    "F0": (r"F_0", "wanted"),
    "Lambda0": (r"\Lambda_0", "wanted"),
    "u": (r"u", "wanted"),
    "lambda0": (r"\lambda_0", "wanted"),
    "lambdau": (r"\lambda_u", "wanted"),
    # The exact part we do not want.
    "Uperp": (r"U^{\perp}", "unwanted"),
    "F1": (r"F_1", "unwanted"),
    "Lambda1": (r"\Lambda_1", "unwanted"),
    "w": (r"w", "unwanted"),
    "lambda1": (r"\lambda_1", "unwanted"),
    "lambdaw": (r"\lambda_w", "unwanted"),
    # What we computed.
    "V": (r"V", "trial"),
    "v": (r"v", "trial"),
    "E0": (r"E_0", "trial"),
    "A0": (r"A_0", "trial"),
    "rho": (r"\rho", "trial"),
    "mu": (r"\mu", "trial"),
    "a0": (r"a_0", "trial"),
    # How far the computation points into what we do not want.
    "theta": (r"\theta", "sine"),
    "Theta": (r"\Theta", "sine"),
    "Theta0": (r"\Theta_0", "sine"),
    "sintheta": (r"\sin\theta", "sine"),
    "sinTheta0": (r"\sin\Theta_0", "sine"),
    "X": (r"X", "sine"),
    "S": (r"S", "sine"),
    # The residual that exposes it.
    "r": (r"r", "resid"),
    "R": (r"R", "resid"),
    # The separation that keeps it from hiding.
    "delta": (r"\delta", "gap"),
    "g": (r"g", "gap"),
}


def role(key: str) -> str:
    return SYMBOLS[key][1]


def concept_color(key: str) -> str:
    """The color of the symbol ``key`` in the current theme."""
    return PALETTE[ROLES[role(key)]]


def latex_preamble() -> str:
    """``\\definecolor`` for every role, and ``\\sym`` / ``\\like`` for every symbol."""
    lines = [rf"\definecolor{{{name}}}{{HTML}}{{{PALETTE[entry].lstrip('#').upper()}}}" for name, entry in ROLES.items()]
    lines += [
        r"\newcommand{\cx}[2]{\textcolor{#1}{#2}}",
        r"\newcommand{\sym}[1]{\csname dksym@#1\endcsname}",
        r"\newcommand{\like}[2]{\textcolor{\csname dkrole@#1\endcsname}{#2}}",
    ]
    for key, (body, name) in SYMBOLS.items():
        lines.append(rf"\expandafter\def\csname dkrole@{key}\endcsname{{{name}}}")
        lines.append(rf"\expandafter\def\csname dksym@{key}\endcsname{{\textcolor{{{name}}}{{{body}}}}}")
    return "\n".join(lines)


_KEY_USE = re.compile(r"\\(?:sym|like)\{([^{}]*)\}")
# ``\sym{key}`` and any sub/superscripts right after it.
_SYM_USE = re.compile(r"\\sym\{(\w+)\}((?:[\^_](?:\{(?:[^{}]|\{[^{}]*\})*\}|\\[A-Za-z]+|[^\\{]))*)")


def check_keys(source: str) -> None:
    """Raise on an unknown ``\\sym``/``\\like`` key; LaTeX would silently drop it."""
    for key in _KEY_USE.findall(source):
        if key not in SYMBOLS:
            raise KeyError(f"unknown notation key {key!r} in {source!r}; see dkvis.notation.SYMBOLS")


def expand(source: str) -> str:
    """Write each ``\\sym{key}`` out as its colored symbol.

    A script after it goes inside the color group, so ``\\sym{F1}^{*}`` sets as
    ``F_1^*`` with the star over the subscript rather than after it.
    """
    check_keys(source)

    def colored(match: re.Match) -> str:
        body, name = SYMBOLS[match.group(1)]
        return rf"\textcolor{{{name}}}{{{body}{match.group(2)}}}"

    return _SYM_USE.sub(colored, source)
