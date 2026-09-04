#!/usr/bin/env python3
"""Merge the current S2 sine-theta semantic review refinements into the census.

The census is an active scientific ledger.  This script therefore edits one
identified review in place instead of shipping a census snapshot.  It preserves
unrelated upstream changes and refuses to overwrite an unfamiliar semantic edit.
"""
from __future__ import annotations

import argparse
import copy
import json
import pathlib
import subprocess
import sys


def repo_root() -> pathlib.Path:
    return pathlib.Path(
        subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
    )


def ensure_tools_importable(root: pathlib.Path) -> None:
    try:
        import aiq_lean_tools  # noqa: F401
        return
    except ImportError:
        src = root / "submodules/aiq-lean-formalization-tools/src"
        if src.is_dir():
            sys.path.insert(0, str(src))
        else:
            raise


def find_row(data: dict, row_id: str) -> dict:
    hits = [
        row for row in data.get("items", [])
        if isinstance(row, dict) and row.get("id") == row_id
    ]
    if len(hits) != 1:
        raise RuntimeError(f"expected one census row {row_id!r}; found {len(hits)}")
    return hits[0]


def find_clause(review: dict, source_clause: str) -> dict:
    hits = [
        c for c in review.get("clause_map", [])
        if isinstance(c, dict) and c.get("source_clause") == source_clause
    ]
    if len(hits) != 1:
        raise RuntimeError(
            f"expected exactly one clause matching {source_clause!r}; found {len(hits)}. "
            "The review changed upstream, so this merge needs re-reading rather than guessing."
        )
    return hits[0]


def merge_unique_dicts(container: dict, key: str, wanted: list[dict]) -> None:
    current = container.get(key)
    if current is None:
        container[key] = copy.deepcopy(wanted)
        return
    if not isinstance(current, list):
        raise RuntimeError(f"{key} exists but is not a list")
    for item in wanted:
        if item not in current:
            current.append(copy.deepcopy(item))


def replace_known_text(
    container: dict,
    key: str,
    wanted: str,
    *,
    stale_needles: tuple[str, ...],
    label: str,
) -> None:
    current = container.get(key)
    if current == wanted:
        return
    if not isinstance(current, str):
        raise RuntimeError(f"{label}.{key} is not text")
    if any(needle in current for needle in stale_needles):
        container[key] = wanted
        return
    raise RuntimeError(
        f"{label}.{key} changed upstream and does not match a known stale form; "
        "refusing to overwrite that semantic edit"
    )


def set_fragment_if_known(clause: dict, wanted: str, allowed_old: tuple[str | None, ...], label: str) -> None:
    current = clause.get("source_fragment")
    if current == wanted:
        return
    if current in allowed_old:
        clause["source_fragment"] = wanted
        return
    raise RuntimeError(
        f"{label} now cites source_fragment={current!r}; refusing to replace an upstream semantic choice"
    )


def upsert_fragment(review: dict, spec: dict) -> None:
    fragments = review.setdefault("source_fragments", [])
    if not isinstance(fragments, list):
        raise RuntimeError("semantic_review.source_fragments is not a list")
    hits = [f for f in fragments if isinstance(f, dict) and f.get("id") == spec["id"]]
    if not hits:
        fragments.append(copy.deepcopy(spec))
        return
    if len(hits) != 1:
        raise RuntimeError(f"duplicate source fragment id {spec['id']!r}")
    existing = hits[0]
    for key in ("role", "locator"):
        if key in existing and existing[key] != spec[key]:
            raise RuntimeError(
                f"source fragment {spec['id']!r} has upstream {key}={existing[key]!r}, "
                f"expected {spec[key]!r}; refusing to overwrite it"
            )
    for key, value in spec.items():
        existing.setdefault(key, copy.deepcopy(value))


def pin_one_source_fragment(root: pathlib.Path, review: dict, fragment_spec: dict) -> None:
    """Refresh only the inherited fragment pin; leave every other source pin intact."""
    ensure_tools_importable(root)
    from aiq_lean_tools.source_model import SourceLibrary
    from aiq_lean_tools.source_pins import make_source_pin

    library = SourceLibrary.discover(root)
    fragment = library.resolve(
        fragment_spec["locator"],
        id=fragment_spec["id"],
        role=fragment_spec.get("role", "primary"),
    )
    if fragment is None:
        raise RuntimeError(
            f"source fragment {fragment_spec['id']!r} does not resolve in the current tree; "
            "the source moved, so the semantic review must be updated explicitly"
        )
    pin = make_source_pin(
        fragment,
        note="Pinned for inherited Section 1 evidence used by S2-sin-theta semantic focus.",
    )
    pins = review.setdefault("source_pins", [])
    if not isinstance(pins, list):
        raise RuntimeError("semantic_review.source_pins is not a list")
    hits = [
        i for i, p in enumerate(pins)
        if isinstance(p, dict) and p.get("fragment") == fragment_spec["id"]
    ]
    if len(hits) > 1:
        raise RuntimeError(f"duplicate source pin for {fragment_spec['id']!r}")
    if hits:
        pins[hits[0]] = pin
    else:
        pins.append(pin)


def update_context_role(review: dict, name: str, wanted: str, stale_needles: tuple[str, ...]) -> None:
    entries = [
        e for e in review.get("context_declarations", [])
        if isinstance(e, dict) and e.get("name") == name
    ]
    if len(entries) != 1:
        raise RuntimeError(f"expected one context declaration {name!r}; found {len(entries)}")
    entry = entries[0]
    current = entry.get("mathematical_role")
    if current == wanted:
        return
    if isinstance(current, str) and any(x in current for x in stale_needles):
        entry["mathematical_role"] = wanted
        return
    raise RuntimeError(
        f"context declaration {name!r} changed upstream; refusing to overwrite its role"
    )


def apply(data: dict, root: pathlib.Path) -> None:
    row = find_row(data, "S2-sin-theta")
    review = row.get("semantic_review")
    if not isinstance(review, dict):
        raise RuntimeError("S2-sin-theta has no semantic_review object")

    clauses = {
        "field": "The scalar field is real or complex.",
        "setup": "A, A0, and Lambda1 are self-adjoint; E0 is the trial coordinate map and F0,F1 are orthogonal exact-space coordinates.",
        "residual": "R = A E0 - E0 A0 on the operator domain, while F1 intertwines Lambda1 with A.",
        "sine": "sin Theta0 is the directed sine block from the trial subspace to the exact subspace.",
        "gap": "For beta <= alpha and delta > 0, one spectrum lies in [beta,alpha] and the other avoids (beta-delta,alpha+delta), with the roles interchangeable.",
        "norm": "The norm is an arbitrary source unitary-invariant norm and R has finite norm.",
        "conclusion": "delta ||sin Theta0|| <= ||R||.",
        "scope": "Infinite-dimensional and unbounded self-adjoint scope.",
    }
    c = {name: find_clause(review, text) for name, text in clauses.items()}

    # Lean focus is structural.  No copy of the pretty-printed theorem is stored.
    targets = {
        "field": [{"kind": "binder_type_dep", "constant": "RCLike"}],
        "setup": [
            {"kind": "binder", "name": "A"},
            {"kind": "binder", "name": "A₀"},
            {"kind": "binder", "name": "Λ₁"},
            {"kind": "binder", "name": "E₀"},
            {"kind": "binder", "name": "F₀"},
            {"kind": "binder", "name": "F₁"},
            {"kind": "binder", "name": "hA"},
            {"kind": "binder", "name": "hA₀"},
            {"kind": "binder", "name": "hΛ₁"},
        ],
        "residual": [
            {"kind": "binder", "name": "htrial"},
            {"kind": "binder", "name": "hexact"},
        ],
        "sine": [{"kind": "result"}],
        "gap": [
            {"kind": "binder", "name": "hδ"},
            {"kind": "binder", "name": "hgap"},
        ],
        "norm": [
            {"kind": "binder", "name": "N"},
            {"kind": "binder", "name": "hR"},
        ],
        "conclusion": [{"kind": "result"}],
        "scope": [
            {"kind": "binder", "name": "A"},
            {"kind": "binder", "name": "A₀"},
            {"kind": "binder", "name": "Λ₁"},
        ],
    }
    for name, wanted in targets.items():
        merge_unique_dicts(c[name], "lean_targets", wanted)

    # Section 1 is where these objects and the scalar scope are actually introduced.
    set_fragment_if_known(c["setup"], "block-residual", (None, "printed"), "setup clause")
    stale_excerpt = "or the same condition with A_0 and \\Lambda_1 interchanged"
    if c["setup"].get("source_excerpt") == stale_excerpt:
        c["setup"].pop("source_excerpt", None)
    elif c["setup"].get("source_excerpt"):
        raise RuntimeError(
            "setup clause has a different upstream source_excerpt; refusing to delete it without review"
        )
    merge_unique_dicts(c["setup"], "source_targets", [
        {"kind": "math", "text": "A"},
        {"kind": "math", "text": "A_0"},
        {"kind": "math", "text": "\\Lambda_1"},
        {"kind": "math", "text": "E_0"},
        {"kind": "math", "text": "F_0"},
        {"kind": "math", "text": "F_1"},
    ])

    set_fragment_if_known(c["field"], "block-residual", (None, "printed"), "scalar-field clause")
    field_excerpt = "Let \\Hsp be a separable Hilbert space, real or complex; finite dimensionality is not assumed."
    current_field_excerpt = c["field"].get("source_excerpt")
    if current_field_excerpt in (None, field_excerpt):
        c["field"]["source_excerpt"] = field_excerpt
    else:
        raise RuntimeError("scalar-field clause has a different upstream source_excerpt")

    # The source identifies ||sin Theta_0|| with the one-sided block norm in Section 1.
    set_fragment_if_known(c["sine"], "ui-norms", (None, "printed"), "sine-object clause")
    merge_unique_dicts(c["sine"], "source_targets", [
        {"kind": "math", "text": "\\sin\\Theta_0"},
        {"kind": "math", "text": "Q^\\perp E_0"},
    ])

    fragment_spec = {
        "id": "block-residual",
        "role": "definition",
        "why": "Section 1 introduces the scalar scope, operator blocks, and coordinate isometries used by the Section 2 theorem.",
        "locator": {
            "document": "DavisKahan1970",
            "marker": "S1-block-residual",
            "section": "1",
            "result": "Block notation, reducing decompositions, and residual",
        },
    }
    upsert_fragment(review, fragment_spec)
    pin_one_source_fragment(root, review, fragment_spec)

    # Refresh prose that described an older presentation declaration rather than
    # the canonical theorem now shown in the Lean pane.
    replace_known_text(
        c["field"], "lean_realization",
        "The canonical theorem quantifies over 𝕜 with [RCLike 𝕜]. The analytic capability classes used by its proof are supplied by unconditional instances and do not appear as theorem hypotheses.",
        stale_needles=("two scalar capability binders", "proved instances for both source scalar fields"),
        label="scalar-field clause",
    )
    replace_known_text(
        c["sine"], "lean_realization",
        "The canonical theorem writes the directed sine representative directly as (I - F₀ F₀†) E₀ inside its result. The presentation specialization introduces an explicit sinTheta₀ parameter and hSinTheta₀ only to make the printed inequality easier to read.",
        stale_needles=("sinTheta₀ is an explicit theorem parameter", "hSinTheta₀ literally states"),
        label="sine-object clause",
    )
    replace_known_text(
        c["gap"], "lean_realization",
        "hδ : 0 < δ and hgap : FormBoundedSylvesterGap A₀ Λ₁ δ appear directly. FormBoundedSylvesterGap packages the source separation configurations, including the interval/exterior branch with the roles interchangeable and the half-infinite ordered cases.",
        stale_needles=("hβα and hδ are explicit", "hspectral is literally"),
        label="gap clause",
    )
    replace_known_text(
        c["norm"], "lean_realization",
        "N : SymmetricNormingFunction and hR : N.Mem R appear directly. SymmetricNormingFunction is the source-facing dimension-coherent normalized unitary-invariant norm structure used by the canonical theorem; N.Mem R says the residual lies in its associated norm ideal.",
        stale_needles=("N : UnitaryInvariantNorm", "public source-facing name"),
        label="norm clause",
    )
    replace_known_text(
        c["conclusion"], "lean_realization",
        "The canonical result is N.Mem ((I - F₀ F₀†) E₀) together with δ * N.gauge ((I - F₀ F₀†) E₀) <= N.gauge R. The second conjunct is the printed factor-one inequality after the Section 1 identification of ||sin Theta₀|| with the directed block norm; the first records ideal membership for the Lean norm representation.",
        stale_needles=("text after the theorem colon is exactly", "supporting sinTheta_unbounded_intervalExterior"),
        label="conclusion clause",
    )

    replace_known_text(
        review, "note",
        "The canonical review declaration is `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike`, re-exported as `TauCeti.DavisKahan1970.SectionTwo.sinTheta`. It is generic over `RCLike`, uses `SymmetricNormingFunction` directly, takes unbounded self-adjoint `LinearPMap` operators with the full `FormBoundedSylvesterGap`, and concludes both ideal membership of the directed sine block and the factor-one bound. `sinTheta_unbounded_intervalExterior_characterizedWitness_rclike` remains a presentation specialization: it introduces an explicit `sinTheta₀` for readability, but covers only the interval/exterior gap branch and states only the inequality, so it is not the canonical source witness. `IsTrialResidual` and `IsExactSpectralDecomposition` are compact hypotheses whose characterization lemmas expose their isometry, domain, residual, orthogonality, completeness, and intertwining content. The proof-capability classes are implementation instances and do not occur as hypotheses of the canonical theorem.",
        stale_needles=(
            "canonical review declaration is also the intended paper-display declaration",
            "two `RCLike` capability classes in the generic signature",
            "Demoted to supporting: DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike",
        ),
        label="S2-sin-theta semantic review",
    )

    update_context_role(
        review,
        "TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction",
        "The source-facing norm structure used directly by the canonical theorem: a dimension-coherent normalized unitary-invariant norm represented by one symmetric norming function across finite singular-value prefixes.",
        ("Implementation structure behind the public theorem spelling UnitaryInvariantNorm",),
    )
    update_context_role(
        review,
        "TauCeti.DavisKahan.Sylvester.HasUnboundedSylvesterKyFan",
        "Internal unbounded Sylvester Ky Fan proof capability. It is supplied by an unconditional instance at every `RCLike` field and does not appear as a hypothesis of the canonical sine-theta theorem.",
        ("Scalar-field proof capability used to keep one theorem generic over RCLike",),
    )
    update_context_role(
        review,
        "ContinuousLinearMap.HasMinMaxLowerBoundEverywhere",
        "Internal approximation-number min--max capability used by the universal norm machinery. It is supplied by an unconditional `RCLike` instance and does not appear as a hypothesis of the canonical sine-theta theorem.",
        ("Approximation-number min--max capability needed by the universal norm machinery",),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "census", nargs="?", default="dev/davis-kahan-1970-full-source-census.json"
    )
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    root = repo_root()
    path = pathlib.Path(args.census)
    if not path.is_absolute():
        path = root / path
    before_text = path.read_text(encoding="utf-8")
    data = json.loads(before_text)
    apply(data, root)
    after_text = json.dumps(data, indent=2, ensure_ascii=False) + "\n"

    if before_text == after_text:
        print(f"already current: {path}")
        return 0
    if args.dry_run:
        import difflib
        sys.stdout.writelines(
            difflib.unified_diff(
                before_text.splitlines(True), after_text.splitlines(True),
                fromfile=str(path), tofile=str(path) + " (merged)",
            )
        )
        return 0
    path.write_text(after_text, encoding="utf-8")
    print(f"merged S2 semantic review refinements into current census: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
