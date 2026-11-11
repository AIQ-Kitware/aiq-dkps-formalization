#!/usr/bin/env python3
"""Build an auditable, standalone SVG of the DK sine-theta notation.

All objects are drawn from explicit SVG primitives. The rank-one numerical
specialization is the one used in the journal's Figure 1: Ahat=diag(1.9,0.7),
angle=40 degrees, A0=rho=<v,Ahat v>, F0(h)=(h,0), F1(g)=(0,g).

No dependency on Manim, matplotlib, browser rendering, or generated artwork.
Run: python visualizations/figures/sine_theta_players/render.py
     python visualizations/figures/sine_theta_players/render.py --check
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

# These are paper Figure 1 values, not general theorem assumptions.
ANGLE_DEGREES = 40.0
WANTED_EIGENVALUE = 1.9
UNWANTED_EIGENVALUE = 0.7

C = {
    "ink": "#17253a", "muted": "#5c6b7e", "faint": "#e7edf5",
    "background": "#f6f8fc", "paper": "#ffffff", "edge": "#d4deeb",
    "blue": "#235cca", "blue_light": "#eaf2ff",
    "green": "#187a5d", "green_light": "#e9f7f0",
    "violet": "#7954bf", "violet_light": "#f3edfc",
    "orange": "#b65f22", "orange_light": "#fff4e8",
}


def q(name: str) -> str:
    return f"{{{SVG}}}{name}"


def add(parent: ET.Element, name: str, **attributes: object) -> ET.Element:
    return ET.SubElement(parent, q(name), {k.replace("_", "-"): str(v) for k, v in attributes.items() if v is not None})


def rect(parent: ET.Element, x: float, y: float, w: float, h: float,
         fill: str, stroke: str, radius: float = 18, stroke_width: float = 1.5,
         element_id: str | None = None) -> None:
    add(parent, "rect", x=x, y=y, width=w, height=h, rx=radius,
        fill=fill, stroke=stroke, stroke_width=stroke_width, id=element_id)


# TeX-like serif faces, with explicit platform fallbacks.  The source SVG keeps
# real editable text instead of embedding font files or converting glyphs to paths.
# TeXGyrePagella is a TeX-family serif; STIXGeneral has math-oriented glyphs.
# Fonts are not redistributed with the overlay.
FONT_TEXT = "TeXGyrePagella, 'TeX Gyre Pagella', 'STIXGeneral', serif"
FONT_MATH = "STIXGeneral, 'STIX Math', 'TeXGyrePagella', serif"

# Use real SVG baseline shifts for math scripts.  The STIXGeneral text face
# does not include the Unicode subscript digits, so relying on those glyphs
# produces mixed-font formulas.  These spans stay editable SVG text.
SCRIPT_TOKENS = re.compile(r"_ex|[₀₁₂₃₄₅₆₇₈₉]+|\*|²")
SUBSCRIPT_DIGITS = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")


def add_typeset_text(node: ET.Element, message: str, size: float) -> None:
    last = 0
    for match in SCRIPT_TOKENS.finditer(message):
        fragment = message[last:match.start()]
        if len(node):
            node[-1].tail = (node[-1].tail or "") + fragment
        else:
            node.text = (node.text or "") + fragment
        raw = match.group(0)
        if raw == "_ex":
            script, shift = "ex", "sub"
        elif raw == "*":
            script, shift = "∗", "super"
        elif raw == "²":
            script, shift = "2", "super"
        else:
            script, shift = raw.translate(SUBSCRIPT_DIGITS), "sub"
        span = add(node, "tspan", baseline_shift=shift,
                   font_size=f"{size*0.73:.2f}", font_style="normal")
        span.text = script
        last = match.end()
    rest = message[last:]
    if len(node):
        node[-1].tail = (node[-1].tail or "") + rest
    else:
        node.text = rest


def text(parent: ET.Element, x: float, y: float, message: str,
         size: float = 22, color: str | None = None, weight: int = 400,
         anchor: str = "start", element_id: str | None = None,
         italic: bool = False, font: str | None = None,
         math: bool = False) -> None:
    node = add(parent, "text", x=f"{x:.2f}", y=f"{y:.2f}", fill=color or C["ink"],
               font_size=size, font_weight=weight, text_anchor=anchor,
               font_family=font or (FONT_MATH if math else FONT_TEXT),
               font_style="italic" if italic else "normal",
               id=element_id)
    add_typeset_text(node, message, size)


def line(parent: ET.Element, x1: float, y1: float, x2: float, y2: float,
         color: str, width: float = 2, arrow: str | None = None,
         dashed: str | None = None, element_id: str | None = None) -> None:
    add(parent, "line", x1=f"{x1:.2f}", y1=f"{y1:.2f}",
        x2=f"{x2:.2f}", y2=f"{y2:.2f}", stroke=color,
        stroke_width=width, stroke_linecap="round",
        stroke_dasharray=dashed, marker_end=f"url(#{arrow})" if arrow else None,
        id=element_id)


def path(parent: ET.Element, description: str, color: str,
         width: float = 2.0, fill: str = "none", element_id: str | None = None) -> None:
    add(parent, "path", d=description, fill=fill, stroke=color,
        stroke_width=width, stroke_linecap="round", id=element_id)


def circle(parent: ET.Element, x: float, y: float, radius: float,
           color: str, element_id: str | None = None) -> None:
    add(parent, "circle", cx=f"{x:.2f}", cy=f"{y:.2f}", r=radius,
        fill=color, id=element_id)


def group(parent: ET.Element, name: str, explanation: str) -> ET.Element:
    result = add(parent, "g", id=name)
    add(result, "title").text = explanation
    return result


def badge(parent: ET.Element, x: float, y: float, value: str,
          color: str, background: str, width: int = 0, math: bool = False) -> None:
    w = width or max(66, int(len(value) * 12.5 + 30))
    rect(parent, x, y, w, 37, background, background, radius=10, stroke_width=0)
    text(parent, x + 12, y + 26, value, 20, color, 600, math=math, italic=math)


def check_mathematics() -> dict[str, float]:
    """Validate the concrete model using independent scalar computations."""
    theta = math.radians(ANGLE_DEGREES)
    c, s = math.cos(theta), math.sin(theta)
    rho = WANTED_EIGENVALUE * c*c + UNWANTED_EIGENVALUE * s*s
    delta = rho - UNWANTED_EIGENVALUE
    # The displayed rank-one maps are E0(t)=t(c,s), F1(g)=(0,g).
    x = s
    sv = (0.0, s)
    residual = ((WANTED_EIGENVALUE-rho)*c, (UNWANTED_EIGENVALUE-rho)*s)
    adjoint_residual = residual[1]
    sylvester_left = UNWANTED_EIGENVALUE*x - x*rho
    tol = 1e-12
    assert delta > 0
    assert math.isclose(c*c+s*s, 1.0, abs_tol=tol)
    assert math.isclose(sv[0]*sv[0]+sv[1]*sv[1], s*s, abs_tol=tol)
    assert math.isclose(sylvester_left, adjoint_residual, abs_tol=tol)
    assert math.isclose(c*residual[0]+s*residual[1], 0.0, abs_tol=tol)
    assert math.isclose(delta*abs(s), abs(adjoint_residual), abs_tol=tol)
    assert abs(adjoint_residual) <= math.hypot(*residual)+tol
    return {"rho": rho, "delta": delta, "sin_theta": s,
            "residual_norm": math.hypot(*residual)}


def build_svg() -> None:
    values = check_mathematics()
    root = ET.Element(q("svg"), {
        "width": "1800", "height": "1100", "viewBox": "0 0 1800 1100",
        "role": "img", "aria-label": "Sine-theta theorem notation: coordinate maps, rank-one geometry, Sylvester identity and spectral gap",
    })
    add(root, "title").text = "Sine-theta theorem: the players and how they connect"
    add(root, "desc").text = (
        "Deterministically constructed diagram. The coordinate spaces F, F_ex, and G "
        "embed in E through E_0, F_0, and F_1. A rank-one example shows the trial "
        "direction at 40 degrees to the wanted eigenspace and its unwanted component. "
        "The bottom panels give the residual and Sylvester identity and the exact "
        "separation delta between rho and lambda_1."
    )
    defs = add(root, "defs")
    for key in ("blue", "green", "violet", "orange", "ink"):
        marker = add(defs, "marker", id="tip-" + key, viewBox="0 0 10 10",
                     refX=8.5, refY=5, markerWidth=7, markerHeight=7,
                     orient="auto-start-reverse")
        add(marker, "path", d="M 0 0 L 10 5 L 0 10 z", fill=C[key])

    rect(root, 0, 0, 1800, 1100, C["background"], C["background"], radius=0, stroke_width=0)
    head = group(root, "heading", "Names and types match the sine-theta section of the journal manuscript.")
    text(head, 58, 65, "Sine-theta: who is who?", 45, C["ink"], 750)
    text(head, 59, 110, "Trial coordinates, exact spectral coordinates, and the angle between their images", 22, C["muted"])
    badge(head, 1450, 44, "Rank-one example: E = R\u00b2", C["muted"], "#e9edf4", 292)
    text(head, 59, 151, "Key distinction: F, F_ex, and G are coordinate spaces; their images under the frames are subspaces of E.",
         19, C["blue"], 500)

    # A. Typed coordinate map: separate spaces from their images.
    left = group(root, "coordinates-and-embeddings", "The three coordinate Hilbert spaces and the isometries into E.")
    rect(left, 55, 183, 840, 550, C["paper"], C["edge"])
    text(left, 86, 232, "1   Coordinate spaces and embeddings", 26, C["ink"], 700)
    cards = [
        (97, "F", "trial coordinates", "A\u2080: trial operator", "blue"),
        (361, "F_ex", "wanted exact coordinates", "", "green"),
        (625, "G", "unwanted exact coordinates", "\u039b\u2081: complementary block", "violet"),
    ]
    for x, name, subtitle, op, ck in cards:
        section = group(left, "space-" + name.lower().replace("_", "-"), subtitle)
        rect(section, x, 267, 230, 114, C[ck + "_light"], C[ck], radius=14, stroke_width=2)
        text(section, x+15, 304, name, 29, C[ck], 700, math=True, italic=True)
        text(section, x+15, 329, subtitle, 15, C["ink"], 500)
        if op:
            text(section, x+15, 359, op, 15, C[ck], 600)
    # Arrow starts at each card and terminates at ambient space.
    embed = [(212, "E\u2080", "blue"), (476, "F\u2080", "green"), (740, "F\u2081", "violet")]
    for xx, name, ck in embed:
        line(left, xx, 382, xx, 475, C[ck], 3, "tip-" + ck, element_id="embed-"+ck)
        badge(left, xx+13, 399, name, C[ck], C[ck+"_light"], 65, math=True)
    rect(left, 99, 467, 752, 200, "#fcfdff", C["edge"], 17)
    text(left, 119, 500, "E", 33, C["ink"], 750)
    text(left, 160, 498, "ambient Hilbert space", 18, C["muted"])
    strips = [
        (516, "ran(E\u2080)", "trial subspace", "blue"),
        (559, "ran(F\u2080)", "desired exact subspace", "green"),
        (602, "ran(F\u2081)", "exact orthogonal complement", "violet"),
    ]
    for yy, sym, label, ck in strips:
        rect(left, 120, yy, 710, 34, C[ck+"_light"], C[ck+"_light"], radius=9, stroke_width=0)
        text(left, 137, yy+23, sym, 19, C[ck], 700)
        text(left, 294, yy+23, label, 18, C["ink"])
    text(left, 119, 658, "ran(F\u2080) \u22a5 ran(F\u2081)    and    ran(F\u2080) \u2295 ran(F\u2081) = E",
         16, C["muted"])
    text(left, 111, 710, "Readout: X = F\u2081*E\u2080  :  F \u2192 G   (unwanted exact coordinates)",
         19, C["blue"], 600)

    # B. True Euclidean construction: E=R^2 with orthogonal eigendirections.
    geo = group(root, "rank-one-geometry", "Wanted horizontal eigenline, unwanted vertical eigenline, trial vector and its orthogonal projection.")
    rect(geo, 925, 183, 820, 550, C["paper"], C["edge"])
    text(geo, 955, 232, "2   A rank-one geometric slice", 26, C["ink"], 700)
    text(geo, 955, 267, "F\u2080(h) = (h,0)     F\u2081(g) = (0,g)     E\u2080(1) = v", 19, C["muted"])
    ox, oy, length = 1063.0, 639.0, 383.0
    theta = math.radians(ANGLE_DEGREES)
    vx = ox + length * math.cos(theta)
    vy = oy - length * math.sin(theta)
    px = vx
    # Axes visually separated from vector arrows so labels are legible.
    line(geo, ox-17, oy, 1679, oy, C["green"], 3.0, "tip-green", element_id="wanted-axis")
    line(geo, ox, oy+17, ox, 311, C["violet"], 3.0, "tip-violet", element_id="unwanted-axis")
    text(geo, 1512, 620, "ran(F\u2080)  wanted", 19, C["green"], 600)
    text(geo, 1081, 315, "ran(F\u2081)  unwanted", 18, C["violet"], 600)
    # A vector v belongs to the trial line; its perpendicular component is S(1).
    line(geo, ox, oy, vx, vy, C["blue"], 4.5, "tip-blue", element_id="trial-vector")
    line(geo, px, oy, px, vy, C["violet"], 4.0, "tip-violet", element_id="complementary-projection")
    circle(geo, vx, vy, 6.5, C["blue"])
    circle(geo, px, oy, 5, C["green"])
    # Right angle of projection at the wanted axis.
    path(geo, f"M {px-18:.2f} {oy:.2f} v -18 h 18", C["muted"], 1.4)
    # Reference acute angle measured from the horizontal wanted line.
    radius = 89.0
    start_x, start_y = ox+radius, oy
    end_x, end_y = ox+radius*math.cos(theta), oy-radius*math.sin(theta)
    path(geo, f"M {start_x:.2f} {start_y:.2f} A {radius} {radius} 0 0 0 {end_x:.2f} {end_y:.2f}", C["blue"], 2.6)
    text(geo, ox+96, oy-32, "\u03b8 = 40\u00b0", 21, C["blue"], 650)
    text(geo, vx+16, vy-5, "v = E\u2080(1)", 21, C["blue"], 650)
    text(geo, px+16, (vy+oy)/2+1, "S(1)", 21, C["violet"], 700)
    text(geo, px+17, (vy+oy)/2+28, "= (I\u2212P_ex)v", 16, C["violet"])
    text(geo, px+12, oy+31, "P_ex v", 18, C["green"], 650)
    text(geo, 1471, 314, "P_ex = F\u2080F\u2080*", 18, C["green"])
    text(geo, 1471, 342, "I \u2212 P_ex = F\u2081F\u2081*", 18, C["violet"])
    text(geo, 988, 712, "|S| = sin \u0398\u2080; in this slice,  |S| = sin(40\u00b0).", 18, C["muted"])

    # C. The algebraic mechanism, with types and the general bound.
    algebra = group(root, "residual-and-sylvester", "The residual R, unwanted-coordinate map X and their Sylvester identity.")
    rect(algebra, 55, 757, 840, 305, C["paper"], C["edge"])
    text(algebra, 86, 803, "3   Residual \u2192 Sylvester equation \u2192 angle", 25, C["ink"], 700)
    badge(algebra, 86, 824, "R = \u00c2E\u2080 \u2212 E\u2080A\u2080", C["orange"], C["orange_light"], 328)
    text(algebra, 435, 850, ": F \u2192 E  (intertwining residual)", 18, C["muted"])
    badge(algebra, 86, 876, "X = F\u2081*E\u2080", C["blue"], C["blue_light"], 224)
    text(algebra, 334, 903, ": F \u2192 G  (unwanted readout)", 18, C["muted"])
    text(algebra, 88, 957, "\u039b\u2081 X \u2212 X A\u2080 = F\u2081* R", 30, C["ink"], 700)
    line(algebra, 88, 976, 857, 976, C["faint"], 1)
    text(algebra, 88, 1008, "S = F\u2081X;    |S| = sin \u0398\u2080;    \u03b4 N(sin \u0398\u2080) \u2264 N(R)",
         22, C["ink"], 600)
    text(algebra, 88, 1040, "Bound assumes the theorem's spectral separation, domains, and ideal membership.",
         16, C["muted"])

    # D. The scalar gap, intentionally identified as one ordered example.
    gap = group(root, "spectral-separation-example", "A0=rho approximately 1.404, Lambda1=0.7 and delta=rho-0.7.")
    rect(gap, 925, 757, 820, 305, C["paper"], C["edge"])
    text(gap, 956, 803, "4   Spectral separation in this example", 25, C["ink"], 700)
    text(gap, 957, 840, "\u00c2 = diag(1.9, 0.7),     A\u2080 = \u03c1 = \u27e8v, \u00c2v\u27e9,     \u039b\u2081 = 0.7", 20, C["muted"])
    # There is no hidden eigengap substitution: the certified delta in this
    # ordered configuration is rho - Lambda1, not 1.9 - 0.7.
    ymin = 0.4
    ymax = 1.65
    axis_x0, axis_x1, ay = 995.0, 1678.0, 937.0
    def tx(value: float) -> float:
        return axis_x0 + (value-ymin) / (ymax-ymin) * (axis_x1-axis_x0)
    x_lam = tx(UNWANTED_EIGENVALUE)
    x_rho = tx(values["rho"])
    line(gap, axis_x0, ay, axis_x1, ay, C["muted"], 2, "tip-ink")
    for xx, name, ck in [(x_lam, "\u03bb\u2081 = 0.7", "violet"),
                         (x_rho, "\u03c1 \u2248 1.404", "blue")]:
        line(gap, xx, ay-15, xx, ay+15, C[ck], 4)
        circle(gap, xx, ay, 6.5, C[ck])
        text(gap, xx, ay+43, name, 19, C[ck], 650, "middle")
    # A bracket above the two spectral values indicates their separation.
    ybr = 879
    path(gap, f"M {x_lam:.2f} {ybr+19} V {ybr} H {x_rho:.2f} V {ybr+19}", C["ink"], 2)
    text(gap, (x_lam+x_rho)/2, ybr-9, "\u03b4 = \u03c1 \u2212 0.7 \u2248 0.704", 19, C["ink"], 600, "middle")
    text(gap, 957, 1007, "Here \u03b4 separates \u03c3(A\u2080) from \u03c3(\u039b\u2081); it is not the", 18, C["muted"])
    text(gap, 957, 1036, "full 1.2 eigenvalue gap of the ambient operator.", 18, C["muted"])

    tree = ET.ElementTree(root)
    ET.indent(tree, space="  ")
    tree.write(OUTPUT, encoding="utf-8", xml_declaration=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify numerical example and SVG generation")
    args = parser.parse_args()
    vals = check_mathematics()
    if args.check:
        if not OUTPUT.is_file():
            raise SystemExit(f"missing SVG: {OUTPUT}")
        parsed = ET.parse(OUTPUT)
        assert parsed.getroot().get("viewBox") == "0 0 1800 1100"
        print("OK: numerical rank-one identities and SVG XML")
    else:
        build_svg()
        print("Wrote", OUTPUT)
    print("rho={:.9f}, delta={:.9f}, sin(theta)={:.9f}, norm(R)={:.9f}".format(
        vals["rho"], vals["delta"], vals["sin_theta"], vals["residual_norm"]))


if __name__ == "__main__":
    main()
