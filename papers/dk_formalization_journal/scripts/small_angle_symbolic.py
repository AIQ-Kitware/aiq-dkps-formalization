#!/usr/bin/env python3
"""Reproduce the polynomial identities in the small-angle counterexample.

Requires SymPy. This checks matrix identities, not Lean elaboration or source
correspondence. It does not replace the conventional proof in counterexample.tex.
"""
from __future__ import annotations

import json
import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("This optional calculation requires SymPy: python -m pip install sympy") from exc


def main() -> int:
    c, s, lam = sp.symbols("c s lam", real=True)
    i2, i4 = sp.eye(2), sp.eye(4)
    j = sp.Matrix([[0, -1], [1, 0]])
    a, b = c**2 * i2 + s*c*j, -s**2 * i2 + s*c*j
    w = a.row_join(b).col_join(b.row_join(a))
    direct = (c*i2).row_join(s*j).col_join((s*j).row_join(c*i2))
    p = sp.diag(1, 1, 0, 0)
    y = (c*i2).col_join(s*j)
    q = y * y.T
    t = q*p + (i4-q)*(i4-p)
    gram_w = (i4-w).T*(i4-w)
    gram_r = (i4-direct).T*(i4-direct)
    relation = sp.groebner([c**2+s**2-1], c, s, lam)
    passed: list[str] = []

    def zero(name: str, expression: object) -> None:
        entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
        residual = [relation.reduce(sp.expand(value))[1] for value in entries]
        if any(value != 0 for value in residual):
            raise AssertionError(f"{name}: nonzero residual {residual}")
        passed.append(name)

    zero("competitor_orthogonal", w.T*w-i4)
    zero("direct_rotation_orthogonal", direct.T*direct-i4)
    zero("target_frame_orthonormal", y.T*y-i2)
    zero("target_projection", q*q-q)
    zero("source_to_target_intertwining", w*p*w.T-q)
    zero("principal_cosine_matrix", sp.Matrix([[1,0,0,0],[0,1,0,0]])*y-c*i2)
    zero("canonical_intertwiner_is_cosine_times_rotation", t-c*direct)
    zero("intertwiner_gram", t.T*t-c**2*i4)
    zero("direct_displacement_gram", gram_r-(2-2*c)*i4)
    zero("competitor_gram_spectrum", (lam*i4-gram_w).det()-lam**2*(lam-4*s**2)**2)
    zero("direct_gram_spectrum", (lam*i4-gram_r).det()-(lam-(2-2*c))**4)
    fixed = sp.Rational(1,2)*sp.Matrix([[1,-1,-1,-1],[1,1,1,-1],[-1,-1,1,-1],[1,-1,1,1]])
    zero("recovers_original_pi_over_four_matrix", sp.simplify(w.subs({c:sp.sqrt(2)/2,s:sp.sqrt(2)/2})-fixed))
    theta = sp.symbols("theta", real=True)
    if sp.trigsimp(4*sp.sin(theta)-8*sp.sin(theta/2)*sp.cos(theta/2)) != 0:
        raise AssertionError("trace ratio identity")
    passed.append("trace_ratio_trigonometric_identity")
    print(json.dumps({
        "sympy_version": sp.__version__,
        "status": "passed",
        "checks": passed,
        "domain_used_in_mathematical_proof": "0 < theta < pi/2; c=cos(theta), s=sin(theta)",
        "strict_inequality_justification": "sin(theta/2)>0 and cos(theta/2)<1 on the stated interval",
        "lean_compilation": "not performed by this script",
        "scope": "symbolic algebra only; no new source-correspondence or historical-priority certification"
    }, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
