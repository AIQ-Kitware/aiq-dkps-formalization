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

The operators take the quieter second tier of :mod:`dkvis.palette`: the old
``A`` and its blocks are tan (``A0``, the trial block, stays amber), ``A-hat`` is
steel and ``H`` with its blocks and its entry ``b`` is vermilion.  The
projectors and ``E1`` are neutral.  ``U``/``V`` keys remain only for local statements such as Proposition 4.4; the core sine-theta slides name the frames ``E0``, ``F0`` and ``F1`` directly.
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
    "old": "OLD",
    "current": "CURRENT",
    "perturb": "PERTURB",
    "refuted": "REFUTED",
}

#: key: (LaTeX, role)
SYMBOLS: dict[str, tuple[str, str]] = {
    # The operators, each in a muted relative of its eigenvectors' color.
    "A": (r"A", "old"),
    "A1": (r"A_1", "old"),
    "a1": (r"a_1", "old"),
    "Ahat": (r"\widehat A", "current"),
    "H": (r"H", "perturb"),
    "H0": (r"H_0", "perturb"),
    "H1": (r"H_1", "perturb"),
    "B": (r"B", "perturb"),
    "b": (r"b", "perturb"),
    # No role.
    "P": (r"P", "fg"),
    "Q": (r"Q", "fg"),
    "E1": (r"E_1", "fg"),
    "Vperp": (r"V^{\perp}", "fg"),
    # Local named-subspace notation (not used in the core sine-theta exposition).
    "U": (r"U", "wanted"),
    # Exact wanted frame / spectrum.

    "F0": (r"F_0", "wanted"),
    "Lambda0": (r"\Lambda_0", "wanted"),
    "u": (r"u", "wanted"),
    "f0": (r"f_0", "wanted"),
    "lambda0": (r"\lambda_0", "wanted"),
    "lambdau": (r"\lambda_u", "wanted"),
    # Exact unwanted frame / spectrum; Uperp remains for local named-subspace slides.
    "Uperp": (r"U^{\perp}", "unwanted"),
    "F1": (r"F_1", "unwanted"),
    "Lambda1": (r"\Lambda_1", "unwanted"),
    "w": (r"w", "unwanted"),
    "f1": (r"f_1", "unwanted"),
    "lambda1": (r"\lambda_1", "unwanted"),
    "lambdaw": (r"\lambda_w", "unwanted"),
    # Local trial-subspace name V; the core exposition names E0 directly.
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


# Relations, operations and delimiters: the "verbs" of a formula, which stay
# neutral while the symbols around them take their colors.
_NEUTRAL_CMDS = {
    "le", "ge", "leq", "geq", "lt", "gt", "ne", "neq", "approx", "sim", "equiv", "subset", "subseteq",
    "supset", "supseteq", "cap", "cup", "in", "notin", "setminus", "cdot", "times", "pm", "mp", "to",
    "mapsto", "implies", "Longrightarrow", "Rightarrow", "iff", "quad", "qquad", "left", "right", "bigl",
    "bigr", "Bigl", "Bigr", "big", "Big", "lVert", "rVert", "lvert", "rvert", "langle", "rangle", "sum",
    "max", "min", "inf", "sup", "lim", "int", "circ", "mid", "colon", ",", ";", ":", "!", " ", "\\", "&",
}
# Macros whose name is an operation and whose arguments are colored as usual.
_NEUTRAL_ARG_CMDS = {"norm": 1, "frac": 2, "tfrac": 2, "dfrac": 2, "sqrt": 1, "overline": 1}
# Macros that are neutral together with their argument.
_NEUTRAL_WHOLE_CMDS = {"operatorname", "text", "mathrm", "textbf", "texttt", "mathsf"}
# Macros that take the next token as part of the same symbol.
_ACCENTS = {"tilde", "hat", "bar", "vec", "mathcal", "mathbb", "widetilde", "widehat", "dot"}
_NEUTRAL_CHARS = set("+-=<>/|,()[];:!&")


def _group(src: str, i: int) -> int:
    """Index just past the brace group starting at ``src[i] == '{'``."""
    depth = 0
    for j in range(i, len(src)):
        if src[j] == "{":
            depth += 1
        elif src[j] == "}":
            depth -= 1
            if depth == 0:
                return j + 1
    return len(src)


def _token(src: str, i: int) -> int:
    """Index just past the token at ``i``: a macro, a brace group or one character."""
    if src[i] == "{":
        return _group(src, i)
    if src[i] == "\\":
        j = i + 1
        if j < len(src) and src[j].isalpha():
            while j < len(src) and src[j].isalpha():
                j += 1
            return j
        return min(j + 1, len(src))
    return i + 1


def color_nouns(src: str, color: str) -> str:
    """Wrap the symbols of ``src`` in ``\\textcolor{color}``, leaving its verbs neutral.

    ``color`` is a LaTeX color name or ``[HTML]{RRGGBB}``.  Relations, operations,
    delimiters, norm bars, ``\\operatorname{...}`` and text stay in the
    surrounding color; runs of symbols (letters, digits, Greek, accents, and
    their sub- and superscripts) are colored.
    """
    spec = color if color.startswith("[") else "{" + color + "}"
    out, run, i = [], [], 0

    def flush():
        if run:
            body = "".join(run).strip()
            lead = "".join(run)[: len("".join(run)) - len("".join(run).lstrip())]
            out.append(lead + (rf"\textcolor{spec}{{{body}}}" if body else ""))
            run.clear()

    while i < len(src):
        c = src[i]
        if c in "^_" and (run or out):
            # a script belongs to whatever it follows
            j = _token(src, i + 1)
            (run if run else out).append(src[i:j])
            i = j
            continue
        if c.isspace():
            (run if run else out).append(c)
            i += 1
            continue
        j = _token(src, i)
        tok = src[i:j]
        name = tok[1:] if tok.startswith("\\") else None
        if c in _NEUTRAL_CHARS or (name is not None and name in _NEUTRAL_CMDS):
            flush()
            out.append(tok)
            i = j
        elif name in _NEUTRAL_WHOLE_CMDS:
            flush()
            k = _group(src, j) if j < len(src) and src[j] == "{" else j
            out.append(src[i:k])
            i = k
        elif name in _NEUTRAL_ARG_CMDS:
            flush()
            out.append(tok)
            for _ in range(_NEUTRAL_ARG_CMDS[name]):
                if j < len(src) and src[j] == "{":
                    k = _group(src, j)
                    out.append("{" + color_nouns(src[j + 1 : k - 1], color) + "}")
                    j = k
            i = j
        elif name == "textcolor":
            # already colored: keep it whole, as its own symbol
            flush()
            k = j
            while k < len(src) and src[k] == "{":
                k = _group(src, k)
            out.append(src[i:k])
            i = k
        elif name in _ACCENTS:
            k = _token(src, j) if j < len(src) else j
            run.append(src[i:k])
            i = k
        else:
            run.append(tok)
            i = j
    flush()
    return "".join(out)


_LIKE_USE = re.compile(r"\\like\{(\w+)\}\{")


def _expand_likes(source: str) -> str:
    out, i = [], 0
    for m in _LIKE_USE.finditer(source):
        if m.start() < i:
            continue
        end = _group(source, m.end() - 1)
        body = source[m.end() : end - 1]
        out.append(source[i : m.start()])
        out.append(color_nouns(body, SYMBOLS[m.group(1)][1]))
        i = end
    out.append(source[i:])
    return "".join(out)


def expand(source: str) -> str:
    """Write each ``\\sym{key}`` out as its colored symbol.

    A script after it goes inside the color group, so ``\\sym{F1}^{*}`` sets as
    ``F_1^*`` with the star over the subscript rather than after it.
    """
    check_keys(source)

    def colored(match: re.Match) -> str:
        body, name = SYMBOLS[match.group(1)]
        return rf"\textcolor{{{name}}}{{{body}{match.group(2)}}}"

    return _expand_likes(_SYM_USE.sub(colored, source))
