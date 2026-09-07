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
        'broad_review': 'Broader source comparison finds remaining gaps',
        'apparent_completion': 'Project checks reach 29/29',
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
            f'{tex_escape(r["system"])} & {tex_escape(r["models"])} & '
            f'{tex_escape(r["typical_use"])} \\\\'
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


def build_historical_scope_mismatch():
    """Extract the historical directed sin-2-Theta scope mismatch from Git."""

    def extract_decl(commit: str, source_path: str, name: str):
        full_commit = git('rev-parse', commit)
        raw = subprocess.check_output(
            ['git', '-c', f'safe.directory={REPO}', 'show', f'{full_commit}:{source_path}'],
            cwd=REPO,
        )
        source = raw.decode('utf8')
        lines = source.splitlines()
        start = next(
            i for i, line in enumerate(lines)
            if line.strip().startswith(f'theorem {name}')
        )
        end = start
        while end < len(lines):
            if ':=' in lines[end]:
                end += 1
                break
            end += 1
        snippet = '\n'.join(lines[start:end]) + '\n'
        return {
            'name': name,
            'commit': full_commit,
            'source_path': source_path,
            'source_file_sha256': hashlib.sha256(raw).hexdigest(),
            'line_range_1based': [start + 1, end],
            'signature_sha256': hashlib.sha256(snippet.encode('utf8')).hexdigest(),
            'signature': snippet,
        }

    historical = extract_decl(
        '7001ed05',
        'DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean',
        'sinTwoTheta_directedResidual_paperUINorm',
    )

    # Presentation-only rename audit. Commit a905bd4c deliberately renamed the
    # dimension-coherent norm structure PaperUnitaryInvariantNorm to
    # SymmetricNormingFunction. Its three fields are unchanged; the same commit
    # also renamed related helper identifiers (for example paperZeroPad ->
    # zeroPad), so this verifies the structure modulo those documented names
    # before the historical theorem is displayed with the later type name.
    norm_path = (
        'DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/'
        'UnitaryInvariantNorm.lean'
    )

    def extract_structure(rev: str, name: str):
        source = git('show', f'{rev}:{norm_path}')
        lines = source.splitlines()
        start = next(
            i for i, line in enumerate(lines)
            if line.startswith(f'structure {name} where')
        )
        end = next(
            i for i in range(start + 1, len(lines))
            if lines[i].startswith('namespace ')
        )
        return '\n'.join(lines[start:end]).strip()

    norm_before = extract_structure('a905bd4c^', 'PaperUnitaryInvariantNorm')
    norm_after = extract_structure('a905bd4c', 'SymmetricNormingFunction')
    normalized_before = (
        norm_before
        .replace('PaperUnitaryInvariantNorm', 'SymmetricNormingFunction')
        .replace('paperZeroPad', 'zeroPad')
    )
    if normalized_before != norm_after:
        raise RuntimeError(
            'PaperUnitaryInvariantNorm -> SymmetricNormingFunction rename '
            'no longer verifies modulo documented helper renames'
        )

    current_complex = extract_decl(
        'HEAD',
        'DavisKahan/Sources/DavisKahan1970/SinTwoThetaDirectedAngle.lean',
        'sinTwoTheta_directed_unboundedResidual_sourceExact_complex',
    )
    current_real = extract_decl(
        'HEAD',
        'DavisKahan/Sources/DavisKahan1970/SinTwoThetaDirectedAngle.lean',
        'sinTwoTheta_directed_unboundedResidual_sourceExact_real',
    )

    current_path = 'DavisKahan/Sources/DavisKahan1970/SinTwoThetaDirectedAngle.lean'
    current_source = git('show', f'HEAD:{current_path}')
    checks = [
        ('historical norm', historical['signature'], '(N : PaperUnitaryInvariantNorm)'),
        ('historical bounded complex operator', historical['signature'], '{A : E →L[ℂ] E}'),
        ('historical trial residual', historical['signature'], 'residual A V.subtypeL M'),
        ('current complex source norm', current_complex['signature'], 'NormalizedUnitaryInvariantNorm'),
        ('current real source norm', current_real['signature'], 'NormalizedUnitaryInvariantNorm'),
        ('current complex unbounded operator context', current_source, '{A : H →ₗ.[ℂ] H}'),
        ('current real unbounded operator context', current_source, '{A : E →ₗ.[ℝ] E}'),
    ]
    for label, text, needle in checks:
        if needle not in text:
            raise RuntimeError(f'{label}: expected {needle!r} in extracted source')

    # Reader-facing presentation. The source checks above are the authority for
    # this example. Commit a905bd4c verifies the type rename
    # PaperUnitaryInvariantNorm -> SymmetricNormingFunction. The displayed code
    # intentionally uses ASCII-safe spellings for Real/Complex, order, set
    # membership/subset, conjunction/disjunction, and orthogonal complement so
    # PDF text extraction does not drop mathematical glyphs. This normalization
    # is for presentation only; it does not alter the historical scope mismatch.
    presentation = '''theorem sinTwoTheta_directedResidual
    (N : SymmetricNormingFunction)
    {A : ContinuousLinearMap Complex E E} (hA : IsSelfAdjoint A)
    {U V : Submodule Complex E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U)
    {a b delta : Real} (hdelta : 0 < delta) (hab : a <= b)
    (hUspec : Set.Subset
      (spectrum Real (compressOperator U A)) (Set.Icc a b))
    (hUspec' : forall x,
      Membership.mem x
        (spectrum Real (compressOperator (Submodule.orthogonal U) A)) ->
      Or (x <= a - delta) (b + delta <= x))
    (M : ContinuousLinearMap Complex V V)
    (hMem : N.Mem (residual A V.subtypeL M)) :
    And (N.Mem (sinTwoThetaIdealBlock U V))
      (delta * N.gauge (sinTwoThetaIdealBlock U V) <=
        2 * N.gauge (residual A V.subtypeL M)) := by
  -- proof omitted
'''
    (
        PAPER / 'generated' / 'historical_scope_mismatch_presentation.lean'
    ).write_text(presentation, encoding='utf8')

    table = '\n'.join([
        r'\begin{tabularx}{\linewidth}{@{}p{0.20\linewidth}>{\raggedright\arraybackslash}X>{\raggedright\arraybackslash}X@{}}',
        r'\toprule',
        r' & Historical checked witness & Source scope / current endpoint \\',
        r'\midrule',
        r'Scalar field & $\mathbb{C}$ only & $\mathbb{R}$ and $\mathbb{C}$ \\',
        r'Ambient operator & bounded \texttt{ContinuousLinearMap} & potentially unbounded self-adjoint \texttt{LinearPMap} \\',
        r'Norm parameter & \texttt{PaperUnitaryInvariantNorm} (now \texttt{SymmetricNormingFunction}) & \texttt{NormalizedUnitaryInvariantNorm} \\',
        r'Right-hand side & printed trial residual $R=AE_0-E_0A_0$ & printed trial residual $R=AE_0-E_0A_0$ \\',
        r'\bottomrule',
        r'\end{tabularx}',
        '',
    ])

    payload = {
        'schema_version': 2,
        'case': 'directed-sin-two-theta-bounded-complex-witness',
        'historical': historical,
        'current_complex': current_complex,
        'current_real': current_real,
        'current_ambient_context': {
            'source_path': current_path,
            'complex': '{A : H →ₗ.[ℂ] H}',
            'real': '{A : E →ₗ.[ℝ] E}',
        },
        'table_sha256': hashlib.sha256(table.encode('utf8')).hexdigest(),
        'note': (
            'The PDF theorem display is derived from the exact historical signature; '
            'The historical theorem used the source trial residual but only bounded '
            'complex scope. Current source-facing endpoints use the source norm class '
            'NormalizedUnitaryInvariantNorm and potentially unbounded ambient operators '
            'over both real and complex Hilbert spaces.'
        ),
    }
    out = PAPER / 'generated' / 'historical_scope_mismatch.json'
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n', encoding='utf8')
    (PAPER / 'generated' / 'historical_scope_mismatch_table.tex').write_text(
        table, encoding='utf8'
    )
    stale = PAPER / 'generated' / 'historical_scope_mismatch.lean'
    if stale.exists():
        stale.unlink()

def build_manifest():
    relpaths = [
        'papers/formalization_process_4page/paper.tex',
        'papers/formalization_process_4page/appendix.tex',
        'papers/formalization_process_4page/references.bib',
        'papers/formalization_process_4page/brainstorm.md',
        'papers/formalization_process_4page/data/practitioner_accounts.csv',
        'papers/formalization_process_4page/data/practitioner_accounts.schema.json',
        'papers/formalization_process_4page/data/lean_publication_activity.csv',
        'papers/formalization_process_4page/data/review_timeline.csv',
        'papers/formalization_process_4page/data/resource_snapshot.csv',
        'papers/formalization_process_4page/data/model_systems.csv',
        'papers/formalization_process_4page/data/model_usage_snapshot.csv',
        'papers/formalization_process_4page/notes/SEMANTIC_ALIGNMENT_CANDIDATES.md',
        'papers/formalization_process_4page/generated/semantic_alignment_candidates.json',
        'papers/formalization_process_4page/figures/formalization_workflow.png',
        'papers/formalization_process_4page/figures/semantic-alignment-sine-theta-row.png',
        'papers/formalization_process_4page/generated/historical_scope_mismatch.json',
        'papers/formalization_process_4page/generated/historical_scope_mismatch_table.tex',
        'papers/formalization_process_4page/generated/historical_scope_mismatch_presentation.lean',
        'DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean',
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
        'papers/formalization_process_4page/paper.tex': 'workshop paper source',
        'papers/formalization_process_4page/data/practitioner_accounts.csv': 'public-account snapshot',
        'papers/formalization_process_4page/data/practitioner_accounts.schema.json': 'account-field schema',
        'papers/formalization_process_4page/data/review_timeline.csv': 'selected Git chronology',
        'papers/formalization_process_4page/generated/historical_scope_mismatch.json': 'historical directed sin-2-Theta scope-mismatch example',
        'papers/formalization_process_4page/notes/SEMANTIC_ALIGNMENT_CANDIDATES.md': 'semantic-alignment candidate signatures',
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
    build_historical_scope_mismatch()
    build_manifest()
    print(f'validated {len(timeline)} Git timeline events against {REPO}')
    print('wrote generated evidence, timeline, model, resource, and hash artifacts')


if __name__ == '__main__':
    main()
