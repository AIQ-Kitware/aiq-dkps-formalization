# What Does It Take to Prove Davis--Kahan?

A separate research project investigating the mathematical and historical
foundations of Davis and Kahan's 1970 spectral-subspace perturbation theory.

- [Research plan](RESEARCH_PLAN.md): research questions, evidence requirements,
  ordered work packages, publication criteria, and reproducibility steps.
- [Sine-theta pilot](cases/sine_theta.md): the first theorem-level study,
  including the mathematical reduction and a checklist of open evidence work.

The pilot uses the complete, source-reviewed formalization already maintained
in `DavisKahan/` and `ForTauCeti/`. Its intended output is a readable mathematical
reconstruction with traceable source and Lean evidence. It does not create a
second Davis--Kahan result census or replace the existing journal manuscript.

Related material in the parent repository:

- `dev/davis-kahan-1970-formalization-result-inventory.json`: 29 source targets.
- `dev/davis-kahan-1970-full-source-census.json`: source correspondence and
  supporting proof claims.
- `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`: the selected
  full-scope sine-theta result.
- `papers/dk_formalization_journal/`: the mathematical formalization paper.
- `papers/dk_formalization_journal/scripts/build_formalization_prerequisite_trace.py`:
  an existing compiler-derived declaration-prerequisite analysis.
- `papers/dk_formalization_journal/scripts/build_formalization_theory_graph.py`:
  declaration graphs joined to a curated mathematical taxonomy.
- `semantic-alignment-page.sh` and `leanq graph-index`: source-to-Lean review
  and proof-dependency exploration.

Follow `papers/AGENTS.md` and the shared paper-writing rules before producing
manuscript prose. Keep research planning and editorial decisions in Markdown;
only established mathematical conclusions belong in a submitted article.
