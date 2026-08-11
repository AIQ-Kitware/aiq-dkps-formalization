# Tau Ceti roadmap rules and style

This guide condenses `submodules/TauCetiRoadmap/README.md` § **Writing a roadmap** and the
accepted prose conventions of the operator-theory roadmap. Historical editing observations are
retained in `llm_notes.md` and `reread-brief.md`.

## Mathematical specification

- State the mathematics and public API Tau Ceti should contain.
- Give each introduced object a usable basic theory: constructors, extensionality, structural
  laws, transport lemmas, and the standard consequences expected by downstream users.
- State each target at its natural generality with exact scalar fields, dimensions, topology,
  completeness assumptions, domain hypotheses, and quantitative constants.
- Use `RCLike` for objects and theorems whose formulas and hypotheses are field-uniform. State
  scalar-specific mathematics over its natural scalar field.
- Record a complete dependency path from Mathlib, existing Tau Ceti material, earlier layers in
  the same roadmap, or cited roadmap prerequisites.
- Give each mathematical concept one owner in the roadmap family and express downstream use as a
  dependency on that owner.
- Describe implementation mechanisms as roadmap targets when they are themselves desired public
  mathematics.

## Mathlib and existing formalizations

- Use Mathlib vocabulary, structures, predicates, and API shapes wherever they express the target
  mathematics.
- Treat current Mathlib design as the baseline for names, bundling, coercions, and theorem shape.
- Use existing formalizations as evidence for theorem statements, feasible generality, edge cases,
  and provenance.
- Specify the desired Tau Ceti mathematics independently of donor file structure and proof order.
- Keep acknowledgements concise: source, link, licence, and authorship context.

## Prototypes

- Use `Suggested.lean` for representative names, signatures, structures, and typeclass shape.
- Use `sorry` for prototype bodies.
- Keep the Markdown roadmap definitive for mathematical scope and dependency structure.
- Give prototype objects enough structure for downstream signatures to express their intended API.

## Prose

- Use present-tense declarative sentences.
- Make mathematical objects, hypotheses, constructions, and consequences the subjects of
  sentences.
- Use concrete nouns, exact hypotheses, exact constants, and named dependencies.
- Prefer positive statements describing the completed mathematics.
- Express rationale through mathematical generality, ownership, consequences, and dependency
  structure.
- Use mathematical contrasts when the distinction changes a theorem statement, hypothesis, or
  public API.
- Keep paragraphs focused on one mathematical purpose.
- Vary sentence structure across sibling roadmaps while preserving the shared section order.
- Keep roadmap text stable across implementation progress and review history.

## Edit validation

- Read each changed README sequentially after editing.
- Compare corresponding sections across sibling roadmaps for repeated templates and duplicated
  ownership claims.
- Check relative links, Markdown structure, and line wrapping.
- Compile changed `Suggested.lean` files against the roadmap toolchain.
