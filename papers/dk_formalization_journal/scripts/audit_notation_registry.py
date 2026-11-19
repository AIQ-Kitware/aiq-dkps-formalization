#!/usr/bin/env python3
"""Exhaustive source-token audit against the DK journal's semantic registry.

The paper's *meaningful notation* is declared in math_symbol_colors.tex.
This independent lexical scan discovers the active manuscript inputs and
PGF figures, inventories math-mode tokens (including direct raw symbols),
and produces a unified printed-glyph index and an occurrence-level CSV.
No printed glyphs or theorem content are changed.

From the journal directory:
    python scripts/audit_notation_registry.py --strict \
        --output docs/NOTATION_CENSUS.md \
        --occurrences docs/NOTATION_OCCURRENCES.csv

Use --require-centralized to fail until direct raw math symbols have been
adjudicated and migrated to the registry. It presently fails intentionally.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
from dataclasses import dataclass
from pathlib import Path
import re
import sys

PAPER = Path(__file__).resolve().parents[1]
SYMBOL_REFERENCE = re.compile(r"\\(sym|like|symglyph|dkSymbolDescription|dkSymbolGlossaryStatus)\{([A-Za-z][A-Za-z0-9]*)\}")
REFERENCE_IN_GLYPH = re.compile(r"\\symglyph\{([A-Za-z][A-Za-z0-9]*)\}")
DECL_START = re.compile(r"^\s*\\dkDeclareSymbol(?=\[|\{|\s)", re.M)

@dataclass(frozen=True)
class Symbol:
    key: str
    glyph: str
    color: str
    glossary: str
    meaning: str
    symbol_type: str
    hover: str
    line: int


def group(src: str, offset: int, opener: str = "{", closer: str = "}") -> tuple[str, int]:
    if src[offset] != opener:
        raise ValueError(f"expected {opener!r} at offset {offset}")
    depth = 1
    i = offset + 1
    while i < len(src):
        if src[i] == "\\" and i + 1 < len(src) and src[i + 1] in (opener, closer):
            i += 2
            continue
        if src[i] == opener:
            depth += 1
        elif src[i] == closer:
            depth -= 1
            if not depth:
                return src[offset + 1:i], i + 1
        i += 1
    raise ValueError(f"unclosed {opener!r} at offset {offset}")


def declarations(src: str) -> list[Symbol]:
    out = []
    for m in DECL_START.finditer(src):
        pos = m.end()
        while pos < len(src) and src[pos].isspace():
            pos += 1
        hover = ""
        if src[pos] == "[":
            hover, pos = group(src, pos, "[", "]")
        args = []
        for _ in range(6):
            while pos < len(src) and src[pos].isspace():
                pos += 1
            arg, pos = group(src, pos)
            args.append(arg)
        out.append(Symbol(*args, hover, src.count("\n", 0, m.start()) + 1))
    return out


# These records are authored in the symbol registry, not inferred from a
# modern-notation preference. Each alternative must cite one named source and
# one actual section, equation, page, or theorem in that source.
SOURCE_START = re.compile(r"^\s*\\dkDeclareNotationSource\{", re.M)
ALTERNATIVE_START = re.compile(r"^\s*\\dkDeclareNotationAlternative\{", re.M)

def named_records(src: str, pattern: re.Pattern[str], arity: int) -> list[tuple[str, ...]]:
    records = []
    for m in pattern.finditer(src):
        pos = m.end() - 1
        fields = []
        for j in range(arity):
            while src[pos].isspace(): pos += 1
            value, pos = group(src, pos)
            fields.append(value)
        records.append(tuple(fields))
    return records

def resolved_glyph(key: str, registry: dict[str, Symbol], stack: tuple[str, ...] = ()) -> str:
    if key in stack:
        raise ValueError("glyph dependency cycle: " + " -> ".join(stack + (key,)))
    entry = registry[key]
    return REFERENCE_IN_GLYPH.sub(
        lambda m: resolved_glyph(m.group(1), registry, stack + (key,)), entry.glyph
    )



REGISTRY_FILE = "math_symbol_colors.tex"
# Active sources are discovered recursively from paper.tex's actual \input commands.
# This avoids silently missing a new included section or figure in the future.
INPUT_CMD = re.compile(r"\\(?:input|include)\s*\{([^}]+)\}")
# Mathematical environments where TeX enters math mode without $ delimiters.
MATH_ENVS = {
    "math", "displaymath", "equation", "equation*", "align", "align*",
    "alignat", "alignat*", "gather", "gather*", "multline", "multline*",
    "flalign", "flalign*", "eqnarray", "eqnarray*", "split", "aligned",
    "alignedat", "gathered", "cases", "dcases",
}
VERBATIM_ENVS = {"lstlisting", "verbatim", "verbatim*", "minted", "comment"}
TOKENS = re.compile(
    r"\\begin\{([A-Za-z*]+)\}|\\end\{([A-Za-z*]+)\}|"
    r"(?<!\\)\$\$|(?<!\\)\$|(?<!\\)\\\(|(?<!\\)\\\)|(?<!\\)\\\[|(?<!\\)\\\]",
    re.M,
)
CONTROL = re.compile(r"\\(?:[A-Za-z@]+|.)")
NUMBER = re.compile(r"[0-9]+(?:\.[0-9]+)?")
# Standard TeX commands used for constructing a formula, rather than naming
# a particular operator or number. They are still individually counted.
LAYOUT_CMDS = set("""left right middle big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr
quad qquad , ; : ! enspace thinspace negthinspace thickspace hspace vspace
hphantom vphantom phantom smash mathclap mathllap mathrlap
frac dfrac tfrac cfrac sqrt overset underset stackrel substack
begin end displaystyle textstyle scriptstyle scriptscriptstyle
notag nonumber label ref eqref tag allowdisplaybreaks displaybreak
text mbox textnormal textrm textsf texttt textbf textit
underbrace overbrace overrightarrow underrightarrow overleftarrow
mathchoice mathbin mathrel mathop mathord mathopen mathclose
cdots ldots vdots ddots limits nolimits hline
hfill hspace textcolor color
""".split())
# These commands are ordinary mathematical relations, set operations, and
# structural operators. They are part of the census but not missing symbols.
STANDARD_MATH_CMDS = set("""Vert lVert rVert binom downarrow Longleftrightarrow infty
cdot times pm mp div ast star circ bullet
le leq ge geq ne neq eq equiv approx sim simeq cong propto
in ni notin subset subseteq supset supseteq sup superset
cup cap bigcup bigcap setminus emptyset varnothing
land lor neg implies iff forall exists nexists
mapsto to rightarrow longrightarrow leftrightarrow hookrightarrow
Longrightarrow Rightarrow Leftarrow Leftrightarrow
oplus otimes oplus circ ominus odot bigoplus bigotimes
ldotp colon colonqq defeq coloneqq
sum prod coprod int iint iiint oint
lim limsup liminf inf sup max min argmax argmin
sin cos tan cot sec csc arcsin arccos arctan
sinh cosh tanh exp log ln det dim tr ker ran
mod bmod pmod gcd lcm deg hom
perp parallel angle measuredangle
langle rangle lvert rvert lVert rVert
lfloor rfloor lceil rceil ulcorner urcorner
lbrace rbrace ldots dots dotsc dotsb
hat bar tilde widehat widetilde vec dot ddot overline underline
prime dagger ddagger top bot
""".split())
FONT_CMDS = {"mathbb", "mathbf", "mathcal", "mathfrak", "mathscr", "mathsf", "mathtt", "mathrm", "mathit", "boldsymbol", "bm", "operatorname", "operatorname*"}
ACCENT_CMDS = {"hat", "widehat", "bar", "overline", "tilde", "widetilde", "vec", "dot", "ddot", "check", "breve", "acute", "grave"}
TEXT_CMDS = {"text", "mbox", "textnormal", "textrm", "textsf", "texttt", "textbf", "textit", "verb"}
SKIP_ARG_CMDS = {"label", "ref", "eqref", "tag", "cite", "Cref", "cref", "hyperref", "hypertarget", "begin", "end", "vspace", "hspace"}
OPERATOR_CHARS = set("+-=*/<>|!,:;&~@")
SYNTAX_CHARS = set("()[]{}_^&\\")
NUMERIC_CONSTANTS = {"0", "1", "2", "3", "4"}
# The formatters below already pass through central semantic declarations.
WRAPPER_MAP = {
    "DKRange": "RangeOperator",
    "DKKernel": "KernelOperator",
    "DKDom": "DomainOperator",
    "dkHilbertSchmidtNorm": "HilbertSchmidtNormNotation",
    "dkSchattenNorm": "SchattenNormNotation",
    "dkOperatorNorm": "OperatorNormNotation",
    "dkFrobeniusNorm": "FrobeniusNormNotation",
    "dkTraceNorm": "TraceNormNotation",
    "dkKyFanNorm": "KyFanNormNotation",
    "dkModulus": "OperatorModulusNotation",
}


@dataclass(frozen=True)
class Span:
    file: str
    start: int
    end: int
    flavor: str


@dataclass(frozen=True)
class Occurrence:
    kind: str
    token: str
    file: str
    line: int
    column: int
    context: str
    role: str = "math"
    match_keys: str = ""


def stripped_tex(text: str, file: str) -> str:
    """Mask comments and verbatim bodies, preserving offsets and line numbers.

    The generated PGF files activate `%` as a TeX character inside labels.
    Those files need a separate comment rule: generated metadata lines start
    with `%%`, whereas `\\def%{...}` in a label is *not* a comment.
    """
    # Detect comments by looking at the number of immediately preceding '\\'.
    seq = list(text)
    if file.endswith(".pgf"):
        for m in re.finditer(r"(?m)^%%.*$", text):
            for k in range(m.start(),m.end()):
                seq[k]=" "
        return "".join(seq)
    for m in re.finditer(r"(?m)^.*$", text):
        line = text[m.start():m.end()]
        n = 0
        for j, c in enumerate(line):
            if c == "%" and n % 2 == 0:
                for k in range(m.start() + j, m.end()):
                    seq[k] = " "
                break
            n = n + 1 if c == "\\" else 0
    cleaned = "".join(seq)
    for env in VERBATIM_ENVS:
        regex = re.compile(r"\\begin\{" + re.escape(env) + r"\}.*?\\end\{" + re.escape(env) + r"\}", re.S)
        cleaned = regex.sub(lambda m: "".join("\n" if c == "\n" else " " for c in m.group()), cleaned)
    return cleaned


def find_math_spans(text: str, file: str) -> tuple[list[Span], list[str]]:
    spans: list[Span] = []
    errors: list[str] = []
    mode: tuple[str, int] | None = None
    # Math env + $ delimiter combinations nested in a math region are rare;
    # process inner begin/end as ordinary TeX when inside the outer region.
    for m in TOKENS.finditer(text):
        token = m.group(0)
        begin, end = m.group(1), m.group(2)
        if begin:
            if begin in MATH_ENVS and mode is None:
                mode = ("env:" + begin, m.end())
            continue
        if end:
            if mode and mode[0] == "env:" + end:
                spans.append(Span(file, mode[1], m.start(), mode[0]))
                mode = None
            continue
        if mode and mode[0].startswith("env:"):
            continue
        if mode is None:
            if token in {"$", "$$", r"\(", r"\["}:
                mode = (token, m.end())
            else:
                errors.append(f"{file}:{text.count(chr(10),0,m.start())+1}: unmatched math closer {token}")
        else:
            expected = {"$": "$", "$$": "$$", r"\(": r"\)", r"\[": r"\]"}[mode[0]]
            if token == expected:
                spans.append(Span(file, mode[1], m.start(), mode[0]))
                mode = None
            # Escape sequences such as dollar not matched here.
    if mode:
        errors.append(f"{file}: unterminated math region {mode[0]} starting at line {text.count(chr(10),0,mode[1])+1}")
    # Explicit \ensuremath{...} expressions outside standard delimiters.
    for m in re.finditer(r"\\ensuremath\s*\{", text):
        offset = m.end() - 1
        if any(s.start <= m.start() < s.end for s in spans):
            continue
        try:
            _, end = group(text, offset)
            spans.append(Span(file, offset+1, end-1, "ensuremath"))
        except ValueError:
            errors.append(f"{file}:{text.count(chr(10),0,m.start())+1}: malformed ensuremath")
    spans.sort(key=lambda s: s.start)
    for a, b in zip(spans, spans[1:]):
        if a.end > b.start:
            errors.append(f"{file}: overlapping math regions at offset {a.end}")
    return spans, errors


def cmd_at(text: str, i: int) -> tuple[str, int] | None:
    m = CONTROL.match(text, i)
    return (m.group(), m.end()) if m else None


def skip_space(src: str, i: int) -> int:
    while i < len(src) and src[i].isspace():
        i += 1
    return i


def argument(src: str, i: int) -> tuple[str, int, int]:
    """Read one mandatory TeX argument. start/end offsets include enclosing braces."""
    start = skip_space(src, i)
    if start >= len(src):
        return "", start, start
    if src[start] == "{":
        _, end = group(src, start)
        return src[start:end], start, end
    if src[start] == "\\":
        m = CONTROL.match(src, start)
        assert m is not None
        return m.group(), start, m.end()
    return src[start], start, start + 1


def scripts_at(src: str, i: int) -> tuple[str, int, list[tuple[str, int]]]:
    """Capture scripts and return content locations for independent index census."""
    current = i
    expr = []
    children = []
    for _ in range(3):  # ^ and _ in either order; tolerate a third for diagnostics
        j = skip_space(src, current)
        if j >= len(src) or src[j] not in "_^":
            break
        arg, _, end = argument(src, j+1)
        expr.append(src[current:end])
        # Bare or braced script content gets an independent token inventory.
        content = arg[1:-1] if arg.startswith("{") else arg
        child_base = j + 1
        child_base = skip_space(src, child_base)
        if arg.startswith("{"):
            child_base += 1
        children.append((content, child_base))
        current = end
    return "".join(expr), current, children


class MathScanner:
    def __init__(self, path: str, text: str, known: dict[str,str]):
        self.file, self.text, self.known = path, text, known
        self.occs: list[Occurrence] = []
        self.errors: list[str] = []
        self.lines = text.splitlines()

    def add(self, kind: str, token: str, offset: int, role: str = "math") -> None:
        line = self.text.count("\n", 0, offset) + 1
        start = self.text.rfind("\n", 0, offset) + 1
        column = offset - start + 1
        snippet = self.lines[line-1].strip()[:260] if 0 < line <= len(self.lines) else ""
        matches = self.known.get(re.sub(r"\s+", "", token), "")
        self.occs.append(Occurrence(kind, token, self.file, line, column, snippet, role, matches))

    def scan(self, fragment: str, base: int, role: str="math") -> None:
        i = 0
        n = len(fragment)
        while i < n:
            ch = fragment[i]
            if ch.isspace():
                i += 1; continue
            if ch == "\\":
                c = cmd_at(fragment, i)
                if c is None:
                    self.add("unclassified", ch, base+i, role); i += 1; continue
                texcmd, end = c
                name = texcmd[1:]
                if name in {"sym", "like", "symglyph", "dkSymbolDescription", "dkSymbolGlossaryStatus"}:
                    try:
                        k, stop = group(fragment, skip_space(fragment, end))
                    except (IndexError, ValueError):
                        self.errors.append(f"{self.file}:{self.text.count(chr(10),0,base+i)+1}: malformed {texcmd}")
                        i = end; continue
                    self.add("registered-key" if name != "symglyph" else "registered-glyph", k, base+i, role)
                    if name == "like":
                        try:
                            expr, expr_end = group(fragment, skip_space(fragment, stop))
                            self.add("semantic-variant", f"{k} :: {expr}", base+i, "like-expression")
                            expr_start = skip_space(fragment, stop)+1
                            self.scan(expr, base+expr_start, "like-variant")
                            stop = expr_end
                        except (ValueError, IndexError):
                            self.errors.append(f"{self.file}:{self.text.count(chr(10),0,base+i)+1}: malformed {texcmd} expression")
                    else:
                        suffix, stop2, children = scripts_at(fragment, stop)
                        if suffix:
                            if not (role == "like-variant" and name == "symglyph"):
                                self.add("semantic-variant", f"{k} :: {suffix.strip()}", base+i, "scripted-symbol")
                            for sub, pos in children:
                                self.scan(sub, base+pos, "script")
                            stop = stop2
                    i = stop; continue
                if name in TEXT_CMDS | SKIP_ARG_CMDS:
                    try:
                        j = skip_space(fragment, end)
                        if j < n and fragment[j] == "{":
                            _, i = group(fragment, j)
                            continue
                    except ValueError:
                        self.errors.append(f"{self.file}:{self.text.count(chr(10),0,base+i)+1}: unbalanced {name} argument")
                    self.add("layout", texcmd, base+i, role)
                    i = end; continue
                if name in FONT_CMDS | ACCENT_CMDS:
                    arg, arg_start, j = argument(fragment, end)
                    glyph = fragment[i:j]
                    suffix, stop, children = scripts_at(fragment, j)
                    self.add("raw-symbol", glyph+suffix, base+i, role)
                    for sub, pos in children:
                        self.scan(sub, base+pos, "script")
                    i = stop; continue
                if name in WRAPPER_MAP:
                    self.add("registered-wrapper", name, base+i, role)
                    i = end; continue
                if name in {"alpha","beta","gamma","delta","varepsilon","epsilon","theta","vartheta","Theta","sigma","Sigma","rho","eta","mu","nu","xi","pi","Pi","tau","lambda","Lambda","omega","Omega","phi","varphi","Phi","psi","Psi","Gamma","Upsilon","ell","infty","partial","nabla","imath","jmath"}:
                    suffix, stop, children = scripts_at(fragment, end)
                    self.add("raw-symbol", texcmd+suffix, base+i, role)
                    for sub, pos in children:
                        self.scan(sub, base+pos, "script")
                    i = stop; continue
                if name in {"|", "{", "}", "\\", " "}:
                    self.add("standard-operator" if name in {"|", "{", "}"} else "layout", texcmd, base+i, role)
                    i = end; continue
                if name in LAYOUT_CMDS:
                    self.add("layout", texcmd, base+i, role)
                    i = end; continue
                if name in STANDARD_MATH_CMDS:
                    self.add("standard-operator", texcmd, base+i, role)
                    suffix, stop, children = scripts_at(fragment, end)
                    for sub, pos in children:
                        self.scan(sub, base+pos, "script")
                    i = stop; continue
                # Every other control sequence is surfaced, even if it is a
                # project macro later determined to be an operator wrapper.
                self.add("raw-control", texcmd, base+i, role)
                suffix, stop, children = scripts_at(fragment, end)
                for sub, pos in children:
                    self.scan(sub, base+pos, "script")
                i = stop; continue
            if ch.isascii() and ch.isalpha():
                suffix, stop, children = scripts_at(fragment, i+1)
                self.add("raw-symbol", ch+suffix, base+i, role)
                for sub, pos in children:
                    self.scan(sub, base+pos, "script")
                i = stop; continue
            if ch.isdigit():
                m = NUMBER.match(fragment, i)
                assert m is not None
                suffix, stop, children = scripts_at(fragment, m.end())
                self.add("number", m.group()+suffix, base+i, role)
                for sub, pos in children:
                    self.scan(sub, base+pos, "script")
                i = stop; continue
            if ch in OPERATOR_CHARS:
                self.add("standard-operator", ch, base+i, role)
                i += 1; continue
            if ch in SYNTAX_CHARS:
                # all TeX structural characters are also counted; no token is
                # silently omitted from the lexical coverage.
                self.add("syntax", ch, base+i, role)
                i += 1; continue
            if ch in "'.`?:":
                self.add("syntax", ch, base+i, role)
                i += 1; continue
            self.add("unclassified", ch, base+i, role)
            i += 1


def safe(value: str) -> str:
    return value.replace("|", r"\|").replace("\n", " ").strip()


def trim_locations(occs: list[Occurrence], limit:int=4) -> str:
    seen = []
    for x in occs:
        ref = f"{x.file}:{x.line}"
        if ref not in seen:
            seen.append(ref)
        if len(seen) >= limit:
            break
    return ", ".join(f"`{s}`" for s in seen)


def discover_sources() -> tuple[list[str], list[str]]:
    """Follow the active manuscript's TeX/PGF input graph, starting at paper.tex.

    Declarations in the preamble of paper.tex (e.g., the symbol registry) are
    tracked separately; they do not count as mathematical prose. Every
    discovered input is included even if it contains no mathematics.
    """
    todo=["paper.tex"]
    found=[]
    errors=[]
    while todo:
        file=todo.pop(0)
        if file in found:
            continue
        fpath=PAPER/file
        if not fpath.is_file():
            errors.append(f"Included file missing: {file}")
            continue
        found.append(file)
        source=stripped_tex(fpath.read_text(),file)
        if file == "paper.tex":
            m=re.search(r"\\begin\{document\}",source)
            if m:
                source="".join("\n" if c == "\n" else " " for c in source[:m.end()]) + source[m.end():]
        for match in INPUT_CMD.finditer(source):
            target=match.group(1).strip()
            if not target.endswith((".tex",".pgf")):
                target += ".tex"
            f=(PAPER/target).resolve()
            try: rel=f.relative_to(PAPER.resolve()).as_posix()
            except ValueError:
                errors.append(f"Included file outside paper root: {file}: {target}")
                continue
            if rel not in found and rel not in todo:
                todo.append(rel)
    return found,errors


def output_report(reg: dict[str,Symbol], occurrences: list[Occurrence], spans: list[Span], errors: list[str], hashes: dict[str,str], sources: dict[str,tuple[str,str]], alternatives: list[tuple[str,str,str,str,str]]) -> str:
    semantic = [o for o in occurrences if o.kind in {"registered-key", "registered-glyph"}]
    raw = [o for o in occurrences if o.kind == "raw-symbol"]
    commands = [o for o in occurrences if o.kind == "raw-control"]
    variants = [o for o in occurrences if o.kind == "semantic-variant"]
    counts=Counter(o.kind for o in occurrences)
    groups: dict[str,list[Occurrence]] = defaultdict(list)
    for o in raw: groups[o.token].append(o)
    cmdgroups: dict[str,list[Occurrence]] = defaultdict(list)
    for o in commands: cmdgroups[o.token].append(o)
    semantic_groups: dict[str,list[Occurrence]] = defaultdict(list)
    for o in semantic: semantic_groups[o.token].append(o)
    matched_raw = sorted(k for k in groups if any(o.match_keys for o in groups[k]))
    total_by_file=Counter(s.file for s in spans)
    raw_by_file=Counter(o.file for o in raw)
    errors=sorted(set(errors))
    # One combined table groups all *registered* and *raw* occurrences by
    # exact TeX glyph, which is the missing holistic view from prior reports.
    glyph_to_keys: dict[str,list[str]] = defaultdict(list)
    for k,r in reg.items():
        glyph_to_keys[re.sub(r"\s+", "", resolved_glyph(k,reg))].append(k)
    glyph_to_raw: dict[str,list[Occurrence]] = defaultdict(list)
    for k, os in groups.items():
        glyph_to_raw[re.sub(r"\s+", "", k)].extend(os)
    combined_glyphs = sorted(set(glyph_to_keys) | set(glyph_to_raw))
    out = [
        "# Full-source notation census (lexical inventory)", "",
        "**Scope:** This is a source-wide *lexical* listing of TeX math-mode tokens in the active manuscript input graph, discovered recursively from `paper.tex`, including generated PGF figure labels. It is not an assertion that every mathematical object is semantically registered. Local proof variables and the meanings of unregistered expressions require editorial classification. The generated figures are inspected as rendered-source inputs; their Python generators remain the source of truth for rebuilding them.", "",
        "The companion `NOTATION_OCCURRENCES.csv` records every detected occurrence with its source file, line, column, and containing line. It includes standard math operators, digits, punctuation, and scripts so there is an evidence trail for *all* math-mode source tokens, not just proposed symbols. Neither report changes the typeset notation.", "",
        "## Coverage and status", "",
        f"- Semantic registry: **{len(reg)} typed entries** ({sum(x.glossary=='glossary' for x in reg.values())} glossary, {sum(x.glossary=='local' for x in reg.values())} local).",
        f"- Documented source alternatives: **{len(alternatives)}** ({sum(a[1]=='DK1970' for a in alternatives)} from DK 1970), across {len({a[0] for a in alternatives})} semantic keys.",
        f"- Math regions scanned: **{len(spans)}** ({', '.join(f'{k}: {v}' for k,v in sorted(total_by_file.items()))}).",
        f"- Occurrence records: **{len(occurrences)}**; category counts: " + ", ".join(f"{k}={n}" for k,n in counts.most_common()) + ".",
        f"- Registered references in math: **{len(semantic)}**, spanning **{len(semantic_groups)} keys**.",
        f"- Raw mathematical atoms: **{len(raw)} occurrences**, **{len(groups)} distinct printed TeX forms** (including indices/superscripts).",
        f"- Derived semantic variants (`\\like` or scripted `\\sym`/`\\symglyph`): **{len(variants)} occurrences**, **{len(set(o.token for o in variants))} distinct source forms**; these may still contain raw indices.",
        f"- Raw commands needing classification: **{len(commands)} occurrences**, **{len(cmdgroups)} distinct commands**.",
        f"- Raw forms exactly matching a registered glyph: **{len(matched_raw)}** distinct forms; **{len(groups)-len(matched_raw)}** have no exact match; all raw occurrences still bypass `\\sym`.",
        f"- Scan errors: **{len(errors)}** (zero is necessary for lexical coverage).",
        "",
        "### Source checksums (SHA-256)", "",
    ]
    out += [f"- `{f}`: `{h}`" for f,h in hashes.items()]
    if errors: out += ["", "### Scanner exceptions", ""] + [f"- {e}" for e in errors]
    else: out += ["", "The scanner encountered no unmatched math delimiters or malformed semantic wrappers."]
    out += ["", "### Census by source file", "", "| Source file | Math regions | Semantic uses | Raw atoms |", "|---|---:|---:|---:|"]
    for f in sorted(total_by_file):
        out.append(f"| `{f}` | {total_by_file[f]} | {sum(o.file==f for o in semantic)} | {raw_by_file[f]} |")
    out += ["", "## Unified printed-glyph index: registered meanings and raw uses together", "",
            "This is the primary holistic table. Every glyph known to the central registry and every raw math atom observed in the manuscript/PGF labels appears here. Multiple registry keys for the same glyph are shown together; these **are not assumed semantically equivalent**. A raw count above zero means the glyph still appears outside central control at those locations. The `glossary` and `local` designations are declarations, not inferred.", "",
            "| Exact TeX glyph | Registered meanings (`key`: glossary status; definition) | Raw occurrences | Sample raw locations |", "|---|---|---:|---|"]
    for glyph in combined_glyphs:
        keys=glyph_to_keys[glyph]
        descriptions="<br>".join(f"`{key}` ({reg[key].glossary}): {safe(reg[key].meaning)}" for key in keys) if keys else "**UNREGISTERED**"
        raws=glyph_to_raw.get(glyph,[])
        out.append(f"| `{safe(glyph)}` | {descriptions} | {len(raws)} | {trim_locations(raws) if raws else '—'} |")
    out += ["", "## Registered semantics, including glossary status", "",
            "The `glossary` column is directly declared in `math_symbol_colors.tex`. Occurrences here count only direct `\\sym`/`\\like`/`\\symglyph` use in math; the older audit separately counts prose and Python figure sources.", "",
            "| Key | Glyph | Mathematical type | Glossary | Color | In-math uses | Description |", "|---|---|---|---|---|---:|---|"]
    for k,r in reg.items():
        glyph=resolved_glyph(k, reg)
        out.append("| " + " | ".join([f"`{safe(k)}`",f"`{safe(glyph)}`",r.symbol_type,r.glossary,r.color,str(len(semantic_groups[k])),safe(r.meaning)]) + " |")
    out += ["", "## Source-attested notation alternatives", "",
            "These rows are explicitly registered in `math_symbol_colors.tex`; they are not inferred by glyph matching. The table at the end of the paper uses the DK1970 rows from the same records.", "",
            "| Semantic key | Our glyph | Type | Cited source | Source glyph | Exact location | Qualification |", "|---|---|---|---|---|---|---|"]
    for key, source_id, glyph, locator, note in alternatives:
        title, url = sources[source_id]
        out.append("| " + " | ".join([f"`{safe(key)}`",f"`{safe(resolved_glyph(key, reg))}`",reg[key].symbol_type,
            f"[{safe(title)}]({url})",f"`{safe(glyph)}`",safe(locator),safe(note)]) + " |")
    out += ["", "## Types and glyph collisions", "",
            "Every registered object has a declared mathematical type. Reused printed glyphs with different registered types deserve particular attention; this is a report, not an automatic rename.", "",
            "| Printed glyph | Keys and types |", "|---|---|"]
    for glyph, keys in sorted(glyph_to_keys.items()):
        if len(keys) < 2: continue
        out.append(f"| `{safe(glyph)}` | " + "; ".join(f"`{key}` ({reg[key].symbol_type})" for key in keys) + " |")
    variant_groups: dict[str, list[Occurrence]] = defaultdict(list)
    for o in variants:
        variant_groups[o.token].append(o)
    out += ["", "## Semantic variants and their handwritten suffixes", "",
            "Even when a base key is registered, `\\like{Key}{...}` may manually spell a different glyph, and `\\sym{Key}_j` may create a new indexed form. These variants are listed separately so the registry owner can decide whether any merit their own declarations. No names are changed here.", "",
            "| Registry key and printed source expression | Occurrences | Sample locations |", "|---|---:|---|"]
    for expression, os in sorted(variant_groups.items(), key=lambda kv:(-len(kv[1]),kv[0])):
        out.append(f"| `{safe(expression)}` | {len(os)} | {trim_locations(os)} |")
    out += ["", "## Raw mathematical atoms: all distinct source forms", "",
            "Every item below was printed directly in math mode rather than supplied by a `\\sym` glyph definition. The `Registered glyph?` column finds exact glyph matches, **not** semantic equivalence. `script` counts indicate uses inside subscripts/superscripts, including `\\like` variants. All locations are in the occurrence CSV.", "",
            "| Raw source form | Occurrences | Script/variant uses | Registered glyph? | Sample locations |", "|---|---:|---:|---|---|"]
    for k, os in sorted(groups.items(), key=lambda v: (-len(v[1]), v[0])):
        match=next((o.match_keys for o in os if o.match_keys), "")
        out.append("| " + " | ".join([f"`{safe(k)}`",str(len(os)),str(sum(o.role!='math' for o in os)),f"`{safe(match)}`" if match else "—",trim_locations(os)]) + " |")
    out += ["", "## Raw TeX commands that bypass the registry", "",
            "These are *not assumed to be mathematical symbols*. They include user-defined helpers, formatting commands, and class-specific macros. Their occurrences are exhaustive for this category; each must be classified before claiming full semantic coverage.", "",
            "| Control sequence | Uses | Sample locations |", "|---|---:|---|"]
    for k, os in sorted(cmdgroups.items(), key=lambda v: (-len(v[1]), v[0])):
        out.append(f"| `{safe(k)}` | {len(os)} | {trim_locations(os)} |")
    others=defaultdict(list)
    for o in occurrences:
        if o.kind not in {"raw-symbol", "raw-control", "registered-key", "registered-glyph", "semantic-variant"}:
            others[o.kind].append(o)
    out += ["", "## Remaining mathematical vocabulary (operators, numerals, and syntax)", "",
            "No glyphs are discarded from the scanner. Standard LaTeX controls and punctuation are tallied here rather than being treated as candidate object names."]
    for kind, os in sorted(others.items()):
        by=Counter(o.token for o in os)
        out += ["", f"### {kind} ({len(os)} occurrences; {len(by)} distinct)", ""]
        out.append(", ".join(f"`{safe(k)}` × {v}" for k,v in by.most_common()))
    out += ["", "## Known limits and required next work", "",
            "1. Lexical coverage is not semantic completeness: a bare `x`, `X`, `A_0`, or `\\Gamma` can have unrelated meanings in different contexts. This file exposes every source use but cannot decide those meanings automatically.",
            "2. The scan follows all direct TeX/PGF `\\input`/`\\include` dependencies of the active `paper.tex` (not hard-coded filenames). It intentionally excludes inactive papers, standalone studies, class files, and bibliography fields. The PGF labels are derived from Python generators: edit those generators, not the generated artifacts, when changing a figure's notation.",
            "3. A fully registry-controlled paper requires assigning roles to the raw atoms and replacing their source occurrences with `\\sym`/derived glyphs; **this pass does neither**, so there is no false claim of 100% centralization.",
            "4. The existing `\\like{Key}{expression}` mechanism permits hand-written glyphs inside `expression`; this census lists those raw constituents. To make every printed variant centrally controllable, introduce explicit registry keys for meaningful variants, or use `\\symglyph{Key}` plus separately registered modifiers.",
            "5. Re-run the census when the TeX changes. Source hashes above identify exactly which version was inspected. `--require-centralized` is an optional failing check for the unfinished source migration; `--strict` checks only parser and registry integrity.", ""]
    return "\n".join(out)


def main() -> int:
    import hashlib
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, default=None, help="Markdown report path")
    p.add_argument("--occurrences", type=Path, default=None, help="CSV occurrence path")
    p.add_argument("--strict", action="store_true", help="fail on malformed source/unknown semantic keys")
    p.add_argument("--require-centralized", action="store_true", help="fail if any raw mathematical atoms bypass \\sym (migration target; not currently satisfied)")
    args=p.parse_args()
    registry_text=(PAPER/REGISTRY_FILE).read_text()
    symbols=declarations(registry_text)
    reg={x.key:x for x in symbols}
    source_records = named_records(registry_text, SOURCE_START, 3)
    alternative_records = named_records(registry_text, ALTERNATIVE_START, 5)
    notation_sources = {sid:(title,url) for sid,title,url in source_records}
    errors=[]
    if len(notation_sources) != len(source_records): errors.append("Duplicate notation source IDs")
    if any(not r.symbol_type.strip() for r in symbols): errors.append("Missing mathematical type")
    if any(r.symbol_type in {"unknown", "unclassified", "unspecified"} for r in symbols):
        errors.append("Unclassified mathematical type")
    alternatives_seen = set()
    for key, source, glyph, locator, note in alternative_records:
        if key not in reg: errors.append(f"Alternative for unknown key: {key}")
        if source not in notation_sources: errors.append(f"Alternative {key} cites unknown source: {source}")
        if not glyph.strip() or not locator.strip() or not note.strip(): errors.append(f"Incomplete source alternative for {key}/{source}")
        if (key, source) in alternatives_seen: errors.append(f"Duplicate alternative for {key}/{source}")
        alternatives_seen.add((key, source))
    if len(reg) != len(symbols): errors.append("Duplicate semantic declaration keys")
    known=defaultdict(list)
    for key in reg:
        known[re.sub(r"\s+", "", resolved_glyph(key,reg))].append(key)
    matches={key:", ".join(vals) for key, vals in known.items()}
    occurrences=[]; spans=[]; hashes={REGISTRY_FILE: hashlib.sha256(registry_text.encode()).hexdigest()}
    sources, discover_errors = discover_sources()
    errors += discover_errors
    for file in sources:
        text=(PAPER/file).read_text()
        hashes[file]=hashlib.sha256(text.encode()).hexdigest()
        cleaned=stripped_tex(text,file)
        if file=="paper.tex":
            m=re.search(r"\\begin\{document\}",cleaned)
            if not m: errors.append("Missing begin{document} in paper.tex")
            else: cleaned="".join("\n" if c == "\n" else " " for c in cleaned[:m.end()]) + cleaned[m.end():]
        regions, errs=find_math_spans(cleaned,file)
        errors += errs; spans += regions
        scanner=MathScanner(file, cleaned, matches)
        for span in regions:
            scanner.scan(cleaned[span.start:span.end], span.start)
        occurrences += scanner.occs; errors += scanner.errors
        # Find semantic uses *outside* math spans; key meanings should not be
        # lost merely because they appear in ordinary running prose.
        for m in SYMBOL_REFERENCE.finditer(cleaned):
            if any(s.start <= m.start() < s.end for s in regions):
                continue
            scanner.add("registered-key",m.group(2),m.start(),"outside-math")
            occurrences.append(scanner.occs[-1])
    unknown=sorted({o.token for o in occurrences if o.kind in {"registered-key", "registered-glyph"} and o.token not in reg})
    if unknown: errors.append("Unknown registered symbol keys: "+", ".join(unknown))
    report=output_report(reg,occurrences,spans,errors,hashes,notation_sources,alternative_records)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(report,encoding="utf-8")
    else: print(report)
    if args.occurrences:
        args.occurrences.parent.mkdir(parents=True,exist_ok=True)
        with args.occurrences.open("w",encoding="utf-8",newline="") as f:
            wr=csv.writer(f)
            wr.writerow(["kind","token","file","line","column","role","registered_glyph_matches","source_line"])
            for o in occurrences:
                wr.writerow([o.kind,o.token,o.file,o.line,o.column,o.role,o.match_keys,o.context])
    raw_count=sum(o.kind == "raw-symbol" for o in occurrences)
    return 1 if (errors and args.strict) or (args.require_centralized and raw_count) else 0

if __name__=="__main__": sys.exit(main())
