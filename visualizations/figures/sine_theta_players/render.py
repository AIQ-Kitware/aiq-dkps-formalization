#!/usr/bin/env python3
"""Build the standalone Davis--Kahan sine-theta geometry diagram.

The SVG is assembled from named, auditable vector primitives. Colors are taken
from papers/dk_formalization_journal/math_symbol_colors.tex. Nothing here is
included in the paper's build or figures.

Run from any working directory:
    python visualizations/figures/sine_theta_players/render.py
    python visualizations/figures/sine_theta_players/render.py --check

The example is a rank-one illustration with a deliberately small 12 degree
angle; the manuscript's separate Figure 1 uses 40 degrees.
"""

from __future__ import annotations

import argparse
import math
import re
from pathlib import Path
from xml.etree import ElementTree as ET

HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "sine_theta_players.svg"
SVG = "http://www.w3.org/2000/svg"
ET.register_namespace("", SVG)

# Auditable numerical example, distinct from the 40-degree manuscript figure.
ANGLE_DEGREES = 12.0
WANTED_EIGENVALUE = 1.9
UNWANTED_EIGENVALUE = 0.7

# Direct transcription of the corresponding semantic roles in
# papers/dk_formalization_journal/math_symbol_colors.tex.
C = {
    "ink": "#1B1F24", "muted": "#6B7280", "edge": "#D7E0EA",
    "background": "#F7F9FC", "paper": "#FFFFFF",
    "ambient": "#36516A", "ambient_light": "#F4F7FB",
    "trial": "#A66705", "trial_light": "#FFF4E5",
    "wanted": "#1F6FD1", "wanted_light": "#EAF2FF",
    "unwanted": "#007C91", "unwanted_light": "#E5F6F9",
    "angle": "#D12A7B", "resid": "#087D43",
    "resid_light": "#E9F6EE", "gap": "#6E4BD8",
    "gap_light": "#EEE9FE",
}

# Prefer local LaTeX-style fonts. Keep text editable; bundle no fonts.
FONT_TEXT = "TeXGyrePagella, 'TeX Gyre Pagella', STIXGeneral, serif"
FONT_MATH = "STIXGeneral, 'STIX Math', TeXGyrePagella, serif"
SCRIPT_TOKENS = re.compile(r"_ex|[₀₁₂₃₄₅₆₇₈₉]+|\*|²")
SUBSCRIPT_DIGITS = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")


def q(name: str) -> str:
    return f"{{{SVG}}}{name}"


def add(parent: ET.Element, name: str, **attrs: object) -> ET.Element:
    return ET.SubElement(parent, q(name), {
        k.replace("_", "-"): str(v) for k, v in attrs.items() if v is not None
    })


def rect(parent: ET.Element, x: float, y: float, w: float, h: float,
         fill: str, stroke: str = "none", radius: float = 15,
         stroke_width: float = 1.3, element_id: str | None = None) -> None:
    add(parent, "rect", x=x, y=y, width=w, height=h, rx=radius,
        fill=fill, stroke=stroke, stroke_width=stroke_width, id=element_id)


def text(parent: ET.Element, x: float, y: float, message: str, size: float = 21,
         color: str | None = None, weight: int = 400, anchor: str = "start",
         math: bool = False, italic: bool = False,
         element_id: str | None = None) -> None:
    node = add(parent, "text", x=f"{x:.2f}", y=f"{y:.2f}",
               fill=color or C["ink"], font_size=size, font_weight=weight,
               text_anchor=anchor, font_family=FONT_MATH if math else FONT_TEXT,
               font_style="italic" if italic else "normal", id=element_id)
    last = 0
    for match in SCRIPT_TOKENS.finditer(message):
        frag = message[last:match.start()]
        if len(node):
            node[-1].tail = (node[-1].tail or "") + frag
        else:
            node.text = (node.text or "") + frag
        raw = match.group()
        if raw == "_ex":
            script, shift = "ex", "sub"
        elif raw == "*":
            script, shift = "∗", "super"
        elif raw == "²":
            script, shift = "2", "super"
        else:
            script, shift = raw.translate(SUBSCRIPT_DIGITS), "sub"
        span = add(node, "tspan", baseline_shift=shift,
                   font_size=f"{size * .73:.2f}", font_style="normal")
        span.text = script
        last = match.end()
    if len(node):
        node[-1].tail = (node[-1].tail or "") + message[last:]
    else:
        node.text = (node.text or "") + message[last:]


def line(parent: ET.Element, x1: float, y1: float, x2: float, y2: float,
         color: str, width: float = 2, arrow: str | None = None,
         dash: str | None = None, element_id: str | None = None) -> None:
    add(parent, "line", x1=f"{x1:.2f}", y1=f"{y1:.2f}",
        x2=f"{x2:.2f}", y2=f"{y2:.2f}", stroke=color,
        stroke_width=width, stroke_linecap="round", stroke_dasharray=dash,
        marker_end=f"url(#{arrow})" if arrow else None, id=element_id)


def circle(parent: ET.Element, x: float, y: float, r: float, color: str) -> None:
    add(parent, "circle", cx=f"{x:.2f}", cy=f"{y:.2f}", r=r, fill=color)


def path(parent: ET.Element, d: str, color: str, width: float = 2) -> None:
    add(parent, "path", d=d, fill="none", stroke=color,
        stroke_width=width, stroke_linecap="round")


def group(parent: ET.Element, identifier: str, description: str) -> ET.Element:
    node = add(parent, "g", id=identifier)
    add(node, "title").text = description
    return node


def panel(parent: ET.Element, identifier: str, title: str,
          x: float, y: float, w: float, h: float) -> ET.Element:
    node = group(parent, identifier, title)
    rect(node, x, y, w, h, C["paper"], C["edge"], radius=20)
    return node


def check_mathematics() -> dict[str, float]:
    theta = math.radians(ANGLE_DEGREES)
    c, s = math.cos(theta), math.sin(theta)
    rho = WANTED_EIGENVALUE * c*c + UNWANTED_EIGENVALUE * s*s
    delta = rho - UNWANTED_EIGENVALUE
    residual = ((WANTED_EIGENVALUE-rho)*c, (UNWANTED_EIGENVALUE-rho)*s)
    lhs = UNWANTED_EIGENVALUE*s - s*rho
    tol = 1e-12
    assert 0 < theta < math.pi/4
    assert math.isclose(c*c+s*s, 1, abs_tol=tol)
    # F0(h)=(h,0) and F1(g)=(0,g) have orthogonal ranges whose
    # direct sum is all of R^2. Every trial v=(c,s) decomposes exactly.
    wanted_part = (c, 0.0)
    unwanted_part = (0.0, s)
    assert math.isclose(wanted_part[0]+unwanted_part[0], c, abs_tol=tol)
    assert math.isclose(wanted_part[1]+unwanted_part[1], s, abs_tol=tol)
    assert math.isclose(wanted_part[0]*unwanted_part[0] +
                        wanted_part[1]*unwanted_part[1], 0, abs_tol=tol)
    # The complementary coordinate readout X=F1* E0 sends 1 to s;
    # the isometric embedding F1 sends s to the vector S(1)=(0,s).
    x_value = s
    assert unwanted_part == (0.0, x_value)
    assert math.isclose(abs(x_value), s, abs_tol=tol)
    assert delta > 0
    assert math.isclose(lhs, residual[1], abs_tol=tol)  # Sylvester identity
    assert math.isclose(c*residual[0]+s*residual[1], 0, abs_tol=tol)
    assert math.isclose(delta*s, abs(residual[1]), abs_tol=tol)
    assert abs(residual[1]) <= math.hypot(*residual)+tol
    return {"theta": theta, "c": c, "s": s, "rho": rho,
            "delta": delta, "residual_norm": math.hypot(*residual)}


def build_svg() -> None:
    values = check_mathematics()
    root = ET.Element(q("svg"), {
        "width": "1800", "height": "1120", "viewBox": "0 0 1800 1120",
        "role": "img", "aria-label": (
            "Sine-theta theorem geometry. Orthogonal wanted and unwanted "
            "subspaces span E; a nearly aligned trial direction decomposes "
            "into their components. Other panels define coordinate maps, "
            "the residual and spectral separation."
        ),
    })
    add(root, "title").text = "Geometry and notation of the sine-theta theorem"
    add(root, "desc").text = (
        "Programmatic, two-dimensional rank-one example with theta=12 degrees. "
        "The blue wanted and cyan complementary axes jointly span the ambient plane. "
        "The amber trial vector lies near the wanted axis and splits into "
        "wanted and complementary projections. Three coordinate systems "
        "map into the same E."
    )
    defs = add(root, "defs")
    for role in ("ink", "trial", "wanted", "unwanted", "gap"):
        marker = add(defs, "marker", id=f"tip-{role}", viewBox="0 0 10 10",
                     refX="8.6", refY="5", markerWidth="6.8",
                     markerHeight="6.8", orient="auto-start-reverse")
        add(marker, "path", d="M0 0 L10 5 L0 10 Z", fill=C[role])
    rect(root, 0, 0, 1800, 1120, C["background"], radius=0)

    # Heading
    text(root, 60, 69, "Geometry and Notation of the Sine-Theta Theorem",
         47, C["ink"], 700)
    text(root, 61, 112, "One ambient space, an exact orthogonal decomposition, and a nearby trial subspace",
         23, C["muted"])
    line(root, 61, 136, 1738, 136, C["edge"], 1.5)

    # 1: Ambient space geometry. Orthogonal axes span the plane (no ambiguous
    #    rectangular 'partition' of E). The 12 degree trial line is consistent
    #    with the scalar example and small enough to show the intended picture.
    geometry = panel(root, "ambient-geometry", "Exact subspaces span E; a trial line is slightly tilted", 55, 158, 1070, 666)
    text(geometry, 84, 207, "1   Ambient geometry and exact decomposition", 28, C["ink"], 700)
    text(geometry, 85, 258, "E = ran(F₀) ⊕ ran(F₁)", 32, C["ambient"], 680, math=True)
    text(geometry, 85, 293, "Every ambient vector has a unique wanted and complementary component.",
         19, C["muted"])
    rect(geometry, 85, 315, 1008, 482, C["ambient_light"], "#DEE7F0", radius=15)
    text(geometry, 106, 353, "E", 30, C["ambient"], 700, math=True, italic=True)
    text(geometry, 145, 351, "rank-one model: E = R²", 17.5, C["muted"])

    ox, oy, length = 346.0, 678.0, 524.0
    vx = ox + length*values["c"]
    vy = oy - length*values["s"]
    # Light, data-independent viewing guide emphasizes this whole plane is E.
    line(geometry, 167, oy, 1032, oy, C["wanted"], 3.6, "tip-wanted", element_id="exact-wanted-axis")
    line(geometry, ox, 761, ox, 382, C["unwanted"], 3.6, "tip-unwanted", element_id="exact-complement-axis")
    # Projections and trial vector; draw the trial ray last.
    line(geometry, ox, oy, vx, oy, C["wanted"], 5.0, element_id="wanted-component")
    line(geometry, vx, oy, vx, vy, C["unwanted"], 4.0, dash="6 5", element_id="unwanted-component")
    line(geometry, ox, oy, vx, vy, C["trial"], 5.0, "tip-trial", element_id="trial-vector")
    circle(geometry, ox, oy, 5.3, C["ambient"])
    circle(geometry, vx, vy, 7, C["trial"])
    circle(geometry, vx, oy, 5.4, C["wanted"])
    path(geometry, f"M {vx-20:.2f} {oy:.2f} v -20 h 20", C["muted"], 1.5)
    radius = 105
    endx, endy = ox+radius*values["c"], oy-radius*values["s"]
    path(geometry, f"M {ox+radius:.2f} {oy:.2f} A {radius} {radius} 0 0 0 {endx:.2f} {endy:.2f}", C["angle"], 3.0)
    text(geometry, 467, 663, "θ = 12°", 22, C["angle"], 650)
    text(geometry, 369, 393, "ran(F₁)", 24, C["unwanted"], 700)
    text(geometry, 371, 421, "exact complement", 17, C["muted"])
    text(geometry, 930, 663, "ran(F₀)", 24, C["wanted"], 700)
    text(geometry, 930, 692, "exact wanted", 17, C["muted"])
    text(geometry, 683, 545, "ran(E₀)", 25, C["trial"], 700)
    text(geometry, 683, 574, "trial direction", 17, C["muted"])
    text(geometry, vx+14, vy-5, "v = E₀(1)", 21, C["trial"], 650)
    text(geometry, vx+18, 627, "S(1)", 22, C["unwanted"], 700)
    text(geometry, vx+18, 651, "unwanted part", 17, C["muted"])
    text(geometry, 695, 718, "P_ex v", 22, C["wanted"], 650)
    text(geometry, 696, 744, "wanted part", 17, C["muted"])
    rect(geometry, 105, 757, 963, 31, C["paper"], radius=7)
    text(geometry, 117, 780, "v = P_ex v + (I − P_ex)v    ;    X = F₁*E₀ reads off the unwanted coordinates.",
         19, C["ink"], 550)

    # 2: Three *coordinate* Hilbert spaces, with mapping images shown in E.
    spaces = panel(root, "coordinate-embeddings", "All frames embed separate abstract coordinate spaces into the same E", 1145, 158, 600, 666)
    text(spaces, 1173, 207, "2   Coordinates and embeddings", 27, C["ink"], 700)
    text(spaces, 1175, 251, "The coordinate spaces need not be subsets of E.",
         19, C["muted"])

    rows = [
        (298, "F_ex", "F₀", "ran(F₀) ⊂ E", "wanted", "wanted exact coordinates"),
        (417, "G", "F₁", "ran(F₁) ⊂ E", "unwanted", "complementary exact coordinates"),
        (536, "F", "E₀", "ran(E₀) ⊂ E", "trial", "chosen trial coordinates"),
    ]
    for y, domain, embed, image, role, desc in rows:
        cell = group(spaces, f"row-{role}", f"{domain} maps via {embed} to {image}")
        rect(cell, 1175, y, 540, 101, C[f"{role}_light"], C[role], radius=13)
        text(cell, 1195, y+42, domain, 30, C[role], 650, math=True, italic=True)
        line(cell, 1295, y+38, 1361, y+38, C[role], 2.6, f"tip-{role}")
        text(cell, 1326, y+28, embed, 20, C[role], 650, anchor="middle", math=True)
        text(cell, 1382, y+44, image, 22, C[role], 660, math=True)
        text(cell, 1196, y+79, desc, 17, C["muted"])

    rect(spaces, 1175, 673, 540, 113, "#F6F8FC", "#E4E9F0", radius=12)
    text(spaces, 1192, 703, "F_ex ⊕ G gives exact coordinates for all of E.",
         20, C["ambient"], 640)
    text(spaces, 1192, 736, "F instead describes the approximate subspace.",
         19, C["ink"])
    text(spaces, 1192, 765, "F need not be the same as F_ex.",
         18, C["muted"])

    # 3: Mechanism, with generous line spacing and no crowding.
    algebra = panel(root, "sylvester-mechanism", "Residual produces the Sylvester equation controlling the unwanted component", 55, 846, 935, 229)
    text(algebra, 85, 895, "3   Residual and the unwanted component", 27, C["ink"], 700)
    text(algebra, 86, 936, "X = F₁*E₀ : F → G", 23, C["unwanted"], 650, math=True)
    text(algebra, 518, 936, "R = ÂE₀ − E₀A₀ : F → E", 22, C["resid"], 650, math=True)
    line(algebra, 85, 957, 962, 957, C["edge"], 1.1)
    text(algebra, 87, 1000, "Λ₁X − XA₀ = F₁*R", 29, C["ink"], 670, math=True)
    text(algebra, 87, 1044, "|X| = sin Θ₀", 23, C["angle"], 630, math=True)
    text(algebra, 408, 1044, "δ N(sin Θ₀) ≤ N(R)", 23, C["ink"], 630, math=True)

    # 4: Scalar ordered gap, consistent with the 12 degree picture above.
    gap = panel(root, "spectral-separation", "Concrete ordered spectral gap of the same rank-one model", 1010, 846, 735, 229)
    text(gap, 1039, 895, "4   Spectral separation", 27, C["ink"], 700)
    text(gap, 1040, 924, "Â = diag(1.9, 0.7),  A₀ = ρ,  Λ₁ = 0.7", 18, C["muted"])
    x0, x1, ay = 1065.0, 1682.0, 1016.0
    domain_min, domain_max = .4, 2.0
    def loc(v: float) -> float:
        return x0 + (v-domain_min)/(domain_max-domain_min)*(x1-x0)
    xl, xr = loc(UNWANTED_EIGENVALUE), loc(values["rho"])
    line(gap, x0, ay, x1, ay, C["ambient"], 2, "tip-ink")
    for x, role in ((xl, "unwanted"), (xr, "trial")):
        line(gap, x, ay-12, x, ay+12, C[role], 4)
        circle(gap, x, ay, 5.6, C[role])
    text(gap, xl, 1047, "λ₁ = 0.7", 18, C["unwanted"], 650, anchor="middle")
    text(gap, xr, 1047, f"ρ ≈ {values['rho']:.3f}", 18, C["trial"], 650, anchor="middle")
    path(gap, f"M {xl:.2f} 974 V 963 H {xr:.2f} V 974", C["gap"], 2.6)
    text(gap, (xl+xr)/2, 953, f"δ ≈ {values['delta']:.3f}", 20, C["gap"], 690, anchor="middle")

    tree = ET.ElementTree(root)
    ET.indent(tree, space="  ")
    tree.write(OUTPUT, encoding="utf-8", xml_declaration=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check scalar identities and SVG XML")
    args = parser.parse_args()
    values = check_mathematics()
    if args.check:
        if not OUTPUT.is_file():
            raise SystemExit(f"Missing SVG: {OUTPUT}")
        parsed = ET.parse(OUTPUT)
        assert parsed.getroot().get("viewBox") == "0 0 1800 1120"
        assert parsed.getroot().find(f".//{q('g')}[@id='ambient-geometry']") is not None
        print("OK: scalar model, SVG XML, ambient geometry group")
    else:
        build_svg()
        print("Wrote", OUTPUT)
    print("theta={:.1f}, rho={:.9f}, delta={:.9f}, sin(theta)={:.9f}, norm(R)={:.9f}".format(
        ANGLE_DEGREES, values["rho"], values["delta"], values["s"], values["residual_norm"]))


if __name__ == "__main__":
    main()
