#!/usr/bin/env python3
"""Validate dated evidence and build reproducibility artifacts for the paper."""
from __future__ import annotations

import csv
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent


def git_root() -> Path:
    try:
        out = subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel'],
            cwd=PAPER,
            text=True,
            stderr=subprocess.DEVNULL,
        )
        return Path(out.strip())
    except Exception:
        return PAPER.parents[1]


REPO = git_root()


def git(*args: str) -> str:
    cmd = ['git', '-c', f'safe.directory={REPO}', *args]
    return subprocess.check_output(
        cmd, cwd=REPO, text=True, stderr=subprocess.STDOUT
    ).strip()


def load_csv(path: Path):
    with path.open(newline='', encoding='utf8') as f:
        return list(csv.DictReader(f))


def tex_escape(text: str) -> str:
    repl = {
        '\\': r'\textbackslash{}',
        '&': r'\&',
        '%': r'\%',
        '$': r'\$',
        '#': r'\#',
        '_': r'\_',
        '{': r'\{',
        '}': r'\}',
        '~': r'\textasciitilde{}',
        '^': r'\textasciicircum{}',
    }
    return ''.join(repl.get(c, c) for c in text)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def validate_timeline(rows):
    errors = []
    for i, r in enumerate(rows, 2):
        commit = r['commit']
        try:
            full = git('rev-parse', commit)
            commit_date = git('show', '-s', '--format=%aI', full)
        except Exception as ex:
            errors.append(f'row {i}: cannot resolve commit {commit}: {ex}')
            continue
        if commit_date[:10] != r['datetime'][:10]:
            errors.append(
                f'row {i}: date mismatch for {commit}: '
                f'csv={r["datetime"]} git={commit_date}'
            )
        evidence = REPO / r['evidence_path']
        if not evidence.exists():
            try:
                git('cat-file', '-e', f'{full}:{r["evidence_path"]}')
            except Exception:
                errors.append(
                    f'row {i}: evidence path missing both now and at {commit}: '
                    f'{r["evidence_path"]}'
                )
    if errors:
        raise SystemExit('\n'.join(errors))


def build_timeline_table(rows):
    out = PAPER / 'generated' / 'review_timeline_table.tex'
    labels = {
        'dk_specific_work_visible': 'DK-specific Lean work visible',
        'formalization_literature_note': 'Formalization/literature comparison note',
        'full_paper_faithful_scaffold': 'Full-paper-faithful DK scaffold',
        'dedicated_tree_reorganization': 'Reorganized into dedicated DK tree',
        'source_comparison_finds_mismatch': 'Source comparison finds incomplete coverage',
        'first_29_of_29_checkpoint': 'Result inventory reaches 29/29',
        'same_day_reopen': 'Later review invalidates Proposition 3.5 acceptance',
        'august_17_29_of_29_checkpoint': 'Maintained semantic review reports 29/29',
        'palomar_readiness_reorganization': 'Palomar readiness cleanup begins',
        'coherent_clause_recheck': 'Clause-by-clause check invalidates sin 2Theta acceptance',
        'broad_review': 'Broader source comparison finds remaining gaps',
        'apparent_completion': 'Another 29/29 checkpoint',
        'new_gap_found': 'Follow-up review finds another scope gap',
        'gap_repaired': 'Source-shaped endpoint added',
        'section8_unbounded_source_facades': 'Section 8 promoted to unbounded source facades',
        'source_surface_reopened': 'Signature review identifies source-surface issues',
        'paper_snapshot': 'Workshop-paper repository snapshot',
    }
    lines = []
    for r in rows:
        date = r['datetime'][:10]
        short = r['commit'][:8]
        label = labels.get(r['event'], r['event'].replace('_', ' '))
        lines.append(f'{date} & \\texttt{{{short}}} & {tex_escape(label)} \\\\')
    lines.append('\\bottomrule')
    out.write_text('\n'.join(lines) + '\n', encoding='utf8')


def build_activity_tikz():
    rows = load_csv(PAPER / 'data' / 'lean_publication_activity.csv')
    expected_months = (
        [f'2024-{m:02d}' for m in range(1, 13)]
        + [f'2025-{m:02d}' for m in range(1, 13)]
        + [f'2026-{m:02d}' for m in range(1, 10)]
    )
    months = [r['month'] for r in rows]
    if months != expected_months:
        raise SystemExit('expected Jan 2024--Sep 2026 publication months in order')

    # Keep the longer tracked snapshot for audit provenance, but reproduce only
    # the public Papers With Lean chart period used in the manuscript. September
    # is partial at the paper cutoff, so the figure ends at August 2026.
    figure_rows = [
        r for r in rows
        if '2025-01' <= r['month'] <= '2026-08'
    ]
    expected_figure_months = (
        [f'2025-{m:02d}' for m in range(1, 13)]
        + [f'2026-{m:02d}' for m in range(1, 9)]
    )
    if [r['month'] for r in figure_rows] != expected_figure_months:
        raise SystemExit('expected Jan 2025--Aug 2026 figure months in order')
    values = [int(r['papers_indexed']) for r in figure_rows]
    bars = '\n'.join(
        f'  \\fill[black!18] ({i - 0.34},0) rectangle ({i + 0.34},{v});'
        for i, v in enumerate(values)
    )
    labels = [
        (0, 'Jan 25'),
        (6, 'Jul 25'),
        (12, 'Jan 26'),
        (18, 'Jul 26'),
    ]
    xlabels = '\n'.join(
        f'  \\node[anchor=north, font=\\scriptsize] at ({x},-5) {{{label}}};'
        for x, label in labels
    )
    yticks = '\n'.join(
        f'  \\draw (-0.5,{y}) -- (-0.25,{y}) '
        f'node[left, font=\\scriptsize] {{{y}}};'
        for y in [0, 25, 50, 75, 100]
    )
    text = rf'''% Generated by scripts/build_evidence.py
\begin{{tikzpicture}}[x=0.40cm,y=0.043cm]
{bars}
  \draw[thick] (-0.5,0) -- (19.55,0);
  \draw[thick] (-0.5,0) -- (-0.5,112);
{yticks}
{xlabels}
  \node[rotate=90, anchor=south, font=\scriptsize] at (-2.65,56)
    {{papers / month}};
\end{{tikzpicture}}
'''
    (PAPER / 'generated' / 'lean_activity_timeline_tikz.tex').write_text(
        text, encoding='utf8'
    )

def build_resource_table():
    rows = load_csv(PAPER / 'data' / 'resource_snapshot.csv')
    pretty = {
        'retained_model_turns': 'Retained model turns',
        'output_tokens': 'Output tokens',
        'billable_input_accounting_measure': 'Billable-input accounting measure',
        'exact_commit_attribution': 'Exact commit attribution',
        'api_equivalent_list_price': 'API-equivalent list price',
        'operational_serving_energy': 'Operational serving energy',
    }
    basis = {
        'observed_lower_bound': 'Observed lower bound.',
        'coverage': 'Coverage.',
        'modeled_from_observed': 'Modeled from observed telemetry.',
    }
    lines = []
    for r in rows:
        value = r['value']
        if r['unit'] == 'USD':
            value = r'\$' + f'{int(float(value)):,}'
        elif r['unit'] == 'kWh':
            value = f'{float(value):,.1f} kWh'
        elif r['unit'] == 'tokens' and '/' not in value:
            value = f'{int(value):,}'
        elif r['unit'] == 'turns':
            value = f'{int(value):,}'
        note = f'{basis[r["category"]]} {r["interpretation"]}'
        lines.append(
            f'{tex_escape(pretty.get(r["quantity"], r["quantity"]))} & '
            f'{value} & {tex_escape(note)} \\\\'
        )
    lines.append('\\bottomrule')
    (PAPER / 'generated' / 'resource_snapshot_table.tex').write_text(
        '\n'.join(lines) + '\n', encoding='utf8'
    )



def build_model_tables():
    systems = load_csv(PAPER / 'data' / 'model_systems.csv')
    system_lines = []
    for r in systems:
        system_lines.append(
            f'{tex_escape(r["system"])} & {tex_escape(r["models"])} \\\\'
        )
    system_lines.append('\\bottomrule')
    (PAPER / 'generated' / 'model_systems_table.tex').write_text(
        '\n'.join(system_lines) + '\n', encoding='utf8'
    )

    usage = load_csv(PAPER / 'data' / 'model_usage_snapshot.csv')
    token_lines = [
        '% Generated by scripts/build_evidence.py; do not edit by hand.',
        '\\begin{tabular}{lrrrr}',
        '\\toprule',
        'Model & \\multicolumn{4}{c}{Measured lower-bound tokens} \\\\',
        ' & Input & Cache write & Cache read & Output \\\\',
        '\\midrule',
    ]
    for r in usage:
        vals = [f'{int(r[k]):,}' for k in (
            'input_tokens', 'cache_write_tokens', 'cache_read_tokens', 'output_tokens'
        )]
        token_lines.append(
            f'{tex_escape(r["model"])} & ' + ' & '.join(vals) + ' \\\\'
        )
    token_lines.extend(['\\bottomrule', '\\end{tabular}'])
    (PAPER / 'generated' / 'model_token_table.tex').write_text(
        '\n'.join(token_lines) + '\n', encoding='utf8'
    )


def build_sin_theta_alignment_example():
    """Build the historical/current sine-theta statement comparison."""

    def extract_decl(
        commit: str,
        source_path: str,
        name: str,
        context_prefix: str | None = None,
        context_line_count: int = 1,
    ):
        if commit == 'WORKTREE':
            full_commit = f"WORKTREE@{git('rev-parse', 'HEAD')}"
            raw = (REPO / source_path).read_bytes()
        else:
            full_commit = git('rev-parse', commit)
            raw = subprocess.check_output(
                ['git', '-c', f'safe.directory={REPO}', 'show', f'{full_commit}:{source_path}'],
                cwd=REPO,
            )
        source = raw.decode('utf8')
        lines = source.splitlines()
        decl_start = next(
            i for i, line in enumerate(lines)
            if line.strip().startswith(f'theorem {name}')
        )
        decl_end = decl_start
        while decl_end < len(lines):
            if ':=' in lines[decl_end]:
                decl_end += 1
                break
            decl_end += 1
        signature = '\n'.join(lines[decl_start:decl_end]) + '\n'
        context = ''
        context_start = None
        if context_prefix is not None:
            context_start = next(
                i for i in range(decl_start - 1, -1, -1)
                if lines[i].strip().startswith(context_prefix)
            )
            context = '\n'.join(
                lines[context_start:context_start + context_line_count]
            ) + '\n\n'
        return {
            'name': name,
            'commit': full_commit,
            'source_path': source_path,
            'source_file_sha256': hashlib.sha256(raw).hexdigest(),
            'line_range_1based': [decl_start + 1, decl_end],
            'context_line_1based': None if context_start is None else context_start + 1,
            'signature_sha256': hashlib.sha256(signature.encode('utf8')).hexdigest(),
            'signature': signature,
            'display_source': context + signature,
        }

    historical_review_commit = '489c01c2cc992a20d38415b5f827cdc046fe7236'
    correction_commit = git('rev-parse', 'cb3b330b')
    historical_path = 'DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean'
    historical_name = 'sinTheta_unbounded_intervalExterior_characterizedWitness_rclike'
    historical = extract_decl(
        historical_review_commit,
        historical_path,
        historical_name,
        context_prefix='variable {𝕜 : Type u} [RCLike 𝕜]',
        context_line_count=6,
    )
    current_path = 'DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean'
    current_name = 'sinTheta_unbounded_formGap_whereDefinedUIN_rclike'
    current = extract_decl(
        'WORKTREE',
        current_path,
        current_name,
        context_prefix='variable {𝕜 : Type u} [RCLike 𝕜]',
        context_line_count=6,
    )

    historical_review_path = 'docs/semantic-alignment/dk-headline-review.md'
    historical_review = git(
        'show', f'{historical_review_commit}:{historical_review_path}'
    )
    for needle in (
        '### Canonical Lean declarations',
        f'#### `DavisKahan1970.{historical_name}`',
        '| claimed_exact |',
    ):
        if needle not in historical_review:
            raise RuntimeError(
                f'historical sine-theta review evidence missing {needle!r}'
            )
    corrected_review = git('show', f'{correction_commit}:{historical_review_path}')
    correction_needles = (
        'CANONICAL WITNESS CORRECTED 2026-08-31.',
        f'The row named `{historical_name}` as the exact source match.',
        'That was wrong on two counts: it carries only the bounded interval/exterior branch of the gap, while the source permits half-infinite separating intervals',
    )
    for needle in correction_needles:
        if needle not in corrected_review:
            raise RuntimeError(
                f'corrective sine-theta review evidence missing {needle!r}'
            )

    historical_checks = (
        '[RCLike 𝕜]',
        '[ContinuousLinearMap.HasMinMaxLowerBoundEverywhere',
        '[HasUnboundedSylvesterKyFan',
        '(N : UnitaryInvariantNorm)',
        '(A : E →ₗ.[𝕜] E)',
        '(A₀ : F →ₗ.[𝕜] F)',
        '(Λ₁ : G →ₗ.[𝕜] G)',
        '{β α δ : ℝ}',
        'Set.Icc β α',
        'x ≤ β - δ ∨ α + δ ≤ x',
        'δ * N.gauge sinTheta₀ ≤ N.gauge R',
    )
    for needle in historical_checks:
        if needle not in historical['display_source']:
            raise RuntimeError(
                f'historical sine-theta signature missing {needle!r}'
            )
    current_checks = (
        '[RCLike 𝕜]',
        '[TopologicalSpace.SeparableSpace E]',
        'NormalizedSymmetricOperatorIdealFamily',
        '(A : E →ₗ.[𝕜] E)',
        '(A₀ : F →ₗ.[𝕜] F)',
        '(Λ₁ : G →ₗ.[𝕜] G)',
        'IsTrialResidual A A₀ E₀ R',
        'IsExactSpectralDecomposition A Λ₁ F₀ F₁',
        'FormBoundedSylvesterGap A₀ Λ₁ δ',
        'N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) →',
        'N.Mem R →',
        'δ * N.gaugeReal',
        '≤',
        'N.gaugeReal R',
    )
    for needle in current_checks:
        if needle not in current['display_source']:
            raise RuntimeError(f'current sine-theta signature missing {needle!r}')

    exact_outputs = {
        'historical_sin_theta_gap_mismatch_exact.lean': historical['display_source'],
        'current_sin_theta_exact.lean': current['display_source'],
    }
    for name, text in exact_outputs.items():
        path = PAPER / 'generated' / name
        path.write_text(text, encoding='utf8')
        if path.read_text(encoding='utf8') != text:
            raise RuntimeError(f'exact sine-theta sidecar changed during write: {name}')

    # Replace only display-sensitive Unicode.  The exact sidecars above remain
    # byte-for-byte excerpts from Git/current source.
    literate = [
        ('→ₗ.[𝕜]', r'\LeanLitPMapK'),
        ('→L[𝕜]', r'\LeanLitCLMapK'),
        ('𝕜', r'\LeanLitScalar'),
        ('Λ₁', r'\LeanLitLambda\LeanLitSubOne'),
        ('A₀', r'A\LeanLitSubZero'),
        ('E₀', r'E\LeanLitSubZero'),
        ('F₀', r'F\LeanLitSubZero'),
        ('F₁', r'F\LeanLitSubOne'),
        ('sinTheta₀', r'sinTheta\LeanLitSubZero'),
        ('₀', r'\LeanLitSubZero'),
        ('₁', r'\LeanLitSubOne'),
        ('β', r'\LeanLitBeta'),
        ('α', r'\LeanLitAlpha'),
        ('δ', r'\LeanLitDelta'),
        ('ℝ', r'\LeanLitReal'),
        ('≤', r'\LeanLitLe'),
        ('⊆', r'\LeanLitSubsetEq'),
        ('∀', r'\LeanLitForall'),
        ('∈', r'\LeanLitMem'),
        ('∨', r'\LeanLitDisj'),
        ('∧', r'\LeanLitConj'),
        ('∘L', r'\LeanLitCompL'),
        ('→', r'\LeanLitArrow'),
    ]
    # Longer tokens first so subscripted identifiers are not partially replaced.
    literate.sort(key=lambda pair: len(pair[0]), reverse=True)

    paper_tex = (PAPER / 'paper.tex').read_text(encoding='utf8')
    for _, sentinel in literate:
        # Verify every actual sentinel referenced in the replacement has a mapping.
        import re
        for token in re.findall(r'\\LeanLit[A-Za-z]+', sentinel):
            tex_key = '{' + token.replace('\\', '\\\\') + '}'
            if tex_key not in paper_tex:
                raise RuntimeError(
                    f'paper.tex is missing literate mapping for sentinel {token}'
                )

    def presentation(name: str, exact_name: str, exact_text: str) -> str:
        text = exact_text
        for source_token, sentinel in literate:
            text = text.replace(source_token, sentinel)
        if not text.endswith(':= by\n'):
            raise RuntimeError(f'{name} presentation no longer ends in `:= by`')
        text = text[:-1] + '  -- proof omitted\n'
        if not text.isascii():
            remaining = sorted({c for c in text if ord(c) > 127})
            raise RuntimeError(
                f'{name} presentation contains unmapped Lean Unicode: {remaining!r}'
            )
        header = [
            '-- GENERATED PRESENTATION INPUT; this is not the exact Lean source.',
            f'-- Exact signature/context: generated/{exact_name}',
            '-- ASCII LeanLit... sentinels stand in for display-sensitive Lean notation.',
            '-- paper.tex renders those sentinels with the listings literate= table.',
            '-- Audit the exact sidecar/provenance JSON, not this presentation file.',
        ]
        return '\n'.join(header) + '\n' + text

    historical_presentation = presentation(
        'historical sine-theta',
        'historical_sin_theta_gap_mismatch_exact.lean',
        historical['display_source'],
    )
    current_presentation = presentation(
        'current sine-theta',
        'current_sin_theta_exact.lean',
        current['display_source'],
    )
    (PAPER / 'generated' / 'historical_sin_theta_gap_mismatch_presentation.lean').write_text(
        historical_presentation, encoding='ascii'
    )
    (PAPER / 'generated' / 'current_sin_theta_presentation.lean').write_text(
        current_presentation, encoding='ascii'
    )

    if paper_tex.count('firstline=6,') < 2:
        raise RuntimeError('paper.tex must skip the five-line header for both sine-theta displays')

    payload = {
        'schema_version': 1,
        'case': 'sin-theta-finite-gap-review-misclassification',
        'historical_review_commit': historical_review_commit,
        'correction_commit': correction_commit,
        'historical_declaration': historical,
        'current_declaration': current,
        'review_evidence': {
            'historical_packet_path': historical_review_path,
            'historical_packet_sha256': hashlib.sha256(historical_review.encode('utf8')).hexdigest(),
            'historical_classification': 'canonical / claimed_exact',
            'corrected_packet_sha256': hashlib.sha256(corrected_review.encode('utf8')).hexdigest(),
            'durable_defect_used_in_paper': (
                'The historical declaration inlines only the finite interval/exterior '
                'gap, while Davis--Kahan also permit half-infinite separation.'
            ),
        },
        'presentation_files': {
            'historical': 'generated/historical_sin_theta_gap_mismatch_presentation.lean',
            'current': 'generated/current_sin_theta_presentation.lean',
        },
        'note': (
            'The paper uses the gap-scope defect only. A later review also discussed '
            'an ideal-membership interpretation, but the project subsequently revised '
            'its norm-boundary model; that point is intentionally not used as the '
            'historical misalignment example.'
        ),
    }
    (PAPER / 'generated' / 'sin_theta_alignment_example.json').write_text(
        json.dumps(payload, indent=2, sort_keys=True) + '\n', encoding='utf8'
    )

    # Remove generated files for the superseded sin-2-Theta worked example.
    for stale_name in (
        'historical_scope_mismatch.json',
        'historical_scope_mismatch_table.tex',
        'historical_scope_mismatch_exact.lean',
        'historical_scope_mismatch_presentation.lean',
        'current_sin_two_theta_exact.lean',
        'current_sin_two_theta_presentation.lean',
    ):
        stale = PAPER / 'generated' / stale_name
        if stale.exists():
            stale.unlink()

def build_manifest():
    relpaths = [
        'papers/formalization_process/paper.tex',
        'papers/formalization_process/appendix.tex',
        'papers/formalization_process/references.bib',
        'papers/formalization_process/brainstorm.md',
        'papers/formalization_process/data/practitioner_accounts.csv',
        'papers/formalization_process/data/practitioner_accounts.schema.json',
        'papers/formalization_process/data/lean_publication_activity.csv',
        'papers/formalization_process/data/review_timeline.csv',
        'papers/formalization_process/data/resource_snapshot.csv',
        'papers/formalization_process/data/model_systems.csv',
        'papers/formalization_process/data/model_usage_snapshot.csv',
        'papers/formalization_process/notes/SEMANTIC_ALIGNMENT_CANDIDATES.md',
        'papers/formalization_process/generated/semantic_alignment_candidates.json',
        'papers/formalization_process/figures/formalization_workflow.png',
        'papers/formalization_process/figures/semantic-alignment-sine-theta-row.png',
        'papers/formalization_process/generated/sin_theta_alignment_example.json',
        'papers/formalization_process/generated/historical_sin_theta_gap_mismatch_exact.lean',
        'papers/formalization_process/generated/historical_sin_theta_gap_mismatch_presentation.lean',
        'papers/formalization_process/generated/current_sin_theta_exact.lean',
        'papers/formalization_process/generated/current_sin_theta_presentation.lean',
        'DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean',
        'DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomain.lean',
        'docs/semantic-alignment/dk-headline-review.md',
        'dev/davis-kahan-1970-formalization-result-inventory.json',
        'dev/davis-kahan-1970-full-source-census.json',
        'prose/distilled_literature/DavisKahan1970_part_III.tex',
        'submodules/aiq-lean-formalization-tools/README.md',
    ]
    artifacts = []
    for rel in relpaths:
        path = REPO / rel
        if not path.exists():
            artifacts.append({'path': rel, 'status': 'missing'})
        else:
            artifacts.append(
                {
                    'path': rel,
                    'status': 'present',
                    'bytes': path.stat().st_size,
                    'sha256': sha256(path),
                }
            )

    present_lines = [
        f'{a["path"]}\t{a["sha256"]}\n'
        for a in artifacts
        if a['status'] == 'present'
    ]
    aggregate = hashlib.sha256(
        ''.join(sorted(present_lines)).encode()
    ).hexdigest()
    try:
        head = git('rev-parse', 'HEAD')
    except Exception:
        head = 'unavailable'
    try:
        sub = git(
            'submodule', 'status', '--', 'submodules/aiq-lean-formalization-tools'
        ).split()[0].lstrip('-+U')
    except Exception:
        sub = 'unavailable'
    manifest = {
        'schema_version': 1,
        'worked_semantic_example': {
            'result': 'S2-sin-theta',
            'historical_defect': 'finite_interval_exterior_gap_only',
            'current_endpoint': 'sinTheta_unbounded_formGap_whereDefinedUIN_rclike',
            'fidelity_authority': 'result ledger / source review, not theorem name',
        },
        'repository_head': head,
        'formalization_tools_submodule': sub,
        'aggregate_sha256': aggregate,
        'aggregate_definition': (
            'sha256 of sorted UTF-8 lines path\\tsha256\\n for all present artifacts'
        ),
        'artifacts': artifacts,
    }
    out_json = PAPER / 'generated' / 'materials_manifest.json'
    out_json.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + '\n', encoding='utf8'
    )

    show = {
        'papers/formalization_process/paper.tex': 'workshop paper source',
        'papers/formalization_process/data/practitioner_accounts.csv': 'public-account snapshot',
        'papers/formalization_process/data/practitioner_accounts.schema.json': 'account-field schema',
        'papers/formalization_process/data/review_timeline.csv': 'selected Git chronology',
        'papers/formalization_process/generated/sin_theta_alignment_example.json': 'historical/current sine-theta semantic-alignment evidence',
        'papers/formalization_process/generated/historical_sin_theta_gap_mismatch_exact.lean': 'exact historical sine-theta signature sidecar',
        'papers/formalization_process/generated/current_sin_theta_exact.lean': 'exact current Davis--Kahan Section 2 sine-theta signature',
        'papers/formalization_process/notes/SEMANTIC_ALIGNMENT_CANDIDATES.md': 'semantic-alignment candidate signatures',
        'DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean': 'current sine-theta Lean source',
        'dev/davis-kahan-1970-formalization-result-inventory.json': '29-result tracking data',
        'dev/davis-kahan-1970-full-source-census.json': 'source-comparison data',
        'prose/distilled_literature/DavisKahan1970_part_III.tex': 'Davis--Kahan source reconstruction',
    }
    rows = []
    for a in artifacts:
        label = show.get(a['path'])
        if label is None:
            continue
        if a['status'] == 'present':
            rows.append(
                f'{tex_escape(label)} & '
                f'\\texttt{{{a["sha256"][:16]}}} & {a["bytes"]:,} \\\\'
            )
        else:
            rows.append(f'{tex_escape(label)} & missing & -- \\\\')
    macros = [
        '% Generated by scripts/build_evidence.py',
        f'\\newcommand{{\\EvidenceSnapshotCommit}}{{{head}}}',
        f'\\newcommand{{\\EvidenceSnapshotShort}}{{{head[:8] if head != "unavailable" else head}}}',
        f'\\newcommand{{\\FormalizationToolsCommit}}{{{sub}}}',
        f'\\newcommand{{\\MaterialsAggregateSHA}}{{{aggregate}}}',
        '\\newcommand{\\MaterialHashRows}{%',
        *[r + '%' for r in rows],
        '}',
    ]
    (PAPER / 'generated' / 'evidence_macros.tex').write_text(
        '\n'.join(macros) + '\n', encoding='utf8'
    )


def main():
    (PAPER / 'generated').mkdir(exist_ok=True)
    timeline = load_csv(PAPER / 'data' / 'review_timeline.csv')
    validate_timeline(timeline)
    build_timeline_table(timeline)
    build_activity_tikz()
    build_resource_table()
    build_model_tables()
    build_sin_theta_alignment_example()
    build_manifest()
    print(f'validated {len(timeline)} Git timeline events against {REPO}')
    print('wrote generated evidence, timeline, model, resource, and hash artifacts')


if __name__ == '__main__':
    main()
