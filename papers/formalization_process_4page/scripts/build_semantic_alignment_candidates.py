#!/usr/bin/env python3
"""Generate auditable semantic-alignment candidate examples from Git history."""
from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent


def repo_root() -> Path:
    out = subprocess.check_output(
        ['git', '-c', f'safe.directory={PAPER.parents[1]}', 'rev-parse', '--show-toplevel'],
        cwd=PAPER, text=True,
    )
    return Path(out.strip())


REPO = repo_root()


def git(*args: str) -> str:
    return subprocess.check_output(
        ['git', '-c', f'safe.directory={REPO}', *args],
        cwd=REPO, text=True, stderr=subprocess.STDOUT,
    ).strip()


def file_at(commit: str, source_path: str):
    full = git('rev-parse', commit)
    raw = subprocess.check_output(
        ['git', '-c', f'safe.directory={REPO}', 'show', f'{full}:{source_path}'],
        cwd=REPO,
    )
    return full, raw.decode('utf8'), raw


def extract_decl(commit: str, source_path: str, name: str, kind: str = 'theorem'):
    full, text, raw = file_at(commit, source_path)
    lines = text.splitlines()
    prefix = f'{kind} {name}'
    try:
        start = next(i for i, line in enumerate(lines) if line.strip().startswith(prefix))
    except StopIteration as ex:
        raise RuntimeError(f'cannot find {prefix} in {commit}:{source_path}') from ex

    if kind == 'class':
        end = start + 1
        while end < len(lines):
            if end > start and lines[end].startswith('/--'):
                break
            end += 1
        while end > start and not lines[end - 1].strip():
            end -= 1
    else:
        end = start
        while end < len(lines):
            if ':=' in lines[end]:
                end += 1
                break
            end += 1
        if end == len(lines) and ':=' not in lines[-1]:
            raise RuntimeError(f'cannot find end of {name} signature')

    snippet = '\n'.join(lines[start:end]) + '\n'
    return {
        'name': name,
        'kind': kind,
        'commit': full,
        'short_commit': full[:8],
        'source_path': source_path,
        'line_range_1based': [start + 1, end],
        'source_file_sha256': hashlib.sha256(raw).hexdigest(),
        'snippet_sha256': hashlib.sha256(snippet.encode()).hexdigest(),
        'snippet': snippet,
    }


def block(title, status, explanation, snippets):
    lines = [f'## {title}', '', f'**Status:** {status}', '', explanation.strip(), '']
    for label, item in snippets:
        lo, hi = item['line_range_1based']
        lines.extend([
            f'### {label}', '',
            f'Git: `{item["short_commit"]}`  ',
            f'Path: `{item["source_path"]}`  ',
            f'Lines: {lo}--{hi}  ',
            f'Snippet SHA-256: `{item["snippet_sha256"]}`', '',
            '```lean', item['snippet'].rstrip(), '```', '',
        ])
    return lines


def main():
    snippets = []

    def ex(commit, path, name, kind='theorem'):
        item = extract_decl(commit, path, name, kind)
        snippets.append(item)
        return item

    cases = []

    pre = ex(
        '59f37a20',
        'DavisKahan/Sources/DavisKahan1970/Section8/Theorem82.lean',
        'theorem8_2_sinTwoTheta_perturbation_sourceExact',
    )
    post = ex(
        '064df8d3',
        'DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceUnbounded.lean',
        'theorem8_2_perturbation_sourceExact_unbounded_complex',
    )
    cases += block(
        '1. Theorem 8.2: bounded canonical witness for an inherited unbounded scope',
        'Repaired on 2026-09-06; strong post-rename candidate.',
        """Section 8 inherits the hypotheses of the earlier sin-2-theta theorem. The repository audit ultimately accepted that inherited operator scope as unbounded. The earlier canonical witness below fixes both `A` and `K` as bounded `ContinuousLinearMap`s. The later source-facing endpoint keeps the perturbation bounded but makes the ambient self-adjoint operator `A` an unbounded `LinearPMap`. This matches the remembered failure mode: the formal theorem proves a useful bounded case, while using it as the canonical source witness narrows the source scope.""",
        [('Earlier bounded witness', pre), ('Later unbounded source-facing endpoint', post)],
    )

    current = ex(
        'e9517c4a',
        'DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceUnbounded.lean',
        'theorem8_2_residual_sourceExact_unbounded_complex',
    )
    cases += block(
        '2. Theorem 8.2 residual branch: caller hypotheses that the source does not add',
        'Open in snapshot e9517c4a; identified by hostile review bcf94e16.',
        """The final signature/context-only review in this snapshot says the source adds residual smallness and the central-spectrum condition to the inherited sin-2-theta context. This facade also asks the caller for `M`, `hPdom`, `hRitz`, and `hres`. The review records that the Ritz block is derivable from the central-spectrum condition, so those assumptions should be constructed internally rather than exposed as source hypotheses. This is the clearest current example of too many hypotheses.""",
        [('Current facade', current)],
    )

    pre = ex(
        '61d1e639',
        'DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean',
        'tanTheta_directed_unboundedTrial_symmetricNorming_complex',
    )
    post = ex(
        '23fc0954',
        'DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean',
        'tanTheta_directed_unboundedRitz_symmetricNorming_exists_complex',
    )
    cases += block(
        '3. Theorem 6.3: extra spectral-gap hypothesis and preselected target subspace',
        'Repaired on 2026-09-05; strong post-rename candidate.',
        """A hostile source-signature review found that the canonical witness asked for `hgap`, a spectral-projection gap around `alpha`, and fixed the target to a particular spectral subspace. The printed Theorem 6.3 does not add that Lambda-zero gap assumption. The repaired endpoint constructs the tangent representative from source-shaped Ritz and unwanted-spectrum data instead of asking the caller for the extra gap and representative.""",
        [('Earlier witness with extra gap', pre), ('Repaired source-shaped endpoint', post)],
    )

    capability = ex(
        '61d1e639',
        'DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean',
        'HasApproximationNumberStrongCutoff', 'class',
    )
    pre = ex(
        '61d1e639',
        'DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean',
        'approximationSingularValue_comp_strongProjection_tendsto',
    )
    post = ex(
        'dd33d00d',
        'DavisKahan/Sources/DavisKahan1970/Section5.lean',
        'lemma5_1_complex',
    )
    cases += block(
        '4. Lemma 5.1: a hidden capability-class assumption that contained the lemma',
        'Repaired on 2026-09-05.',
        """The generic theorem looked like a proof of the printed cutoff-continuity lemma, but its typeclass assumption `HasApproximationNumberStrongCutoff` had a single field that is essentially the same theorem. That makes the generic declaration poor source evidence: the desired result is carried by an inferred assumption. The repaired source-facing complex theorem has no such capability class in its signature.""",
        [('Hidden capability class', capability), ('Earlier generic theorem', pre), ('Repaired complex source theorem', post)],
    )

    pre = ex(
        'c3de4988',
        'DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean',
        'tanTheta_ambient_unboundedRitz_symmetricNorming_complex',
    )
    post = ex(
        '3abcc839',
        'DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean',
        'tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_complex',
    )
    bridge = ex(
        '3abcc839',
        'DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean',
        'crossedDefectsEquivalent_of_hasDefinedAmbientTangent',
    )
    cases += block(
        '5. Section 2 tan-Theta theorem: condition (3.5) exposed as an extra input',
        'Repaired on 2026-09-04; selected for the four-page worked example.',
        """The earlier theorem required `h35 : CrossedDefectsEquivalent U V`. Davis and Kahan introduce condition (3.5) only in Section 3 and say it applies for the remainder of the paper, so it is not a hypothesis of the earlier Section 2 tan-Theta theorem. The repair does not derive `h35` from the ordered gap and Rayleigh--Ritz hypotheses alone. It makes the paper's earlier definedness convention explicit as `hdefined : HasDefinedAmbientTangent U V`; the bridge theorem below then proves `CrossedDefectsEquivalent U V` from `hdefined`, and the repaired endpoint passes that derived fact internally. This isolates the semantic error: a later source condition had been exposed as a caller-supplied hypothesis of an earlier result.""",
        [
            ('Earlier theorem with h35', pre),
            ('Repaired theorem using source definedness', post),
            ('Bridge deriving h35 from definedness', bridge),
        ],
    )

    pre = ex(
        'c3de4988',
        'DavisKahan/Sources/DavisKahan1970/Section3Theorem31Realization.lean',
        'theorem3_1_realization_ofSpectralMultiplicity_complex',
    )
    post = ex(
        'cbaf5895',
        'DavisKahan/Sources/DavisKahan1970/Section3Theorem31Realization.lean',
        'theorem3_1_realization_ofSpectralMultiplicityAwayFromZero_complex',
    )
    cases += block(
        '6. Theorem 3.1 converse: multiplicity equality was too strong at spectral value zero',
        'Repaired on 2026-09-04; strong post-rename candidate.',
        """The printed converse permits the spectral multiplicities of the two angle operators to differ at zero. The earlier theorem required `SameSpectralMultiplicity`, equality everywhere, and therefore proved a narrower converse. The repaired source-facing theorem uses `SameSpectralMultiplicityAwayFromZero`. This is a compact example where a plausible formal predicate was slightly stronger than the source condition.""",
        [('Earlier stronger hypothesis', pre), ('Repaired source hypothesis', post)],
    )

    historical = ex(
        '7001ed05',
        'DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean',
        'sinTwoTheta_directedResidual_paperUINorm',
    )
    cases += block(
        '7. Existing sin-2-Theta false finish: bounded complex trial-residual theorem',
        'Repaired historically; lower preference because the signature predates vocabulary cleanup.',
        """This was an earlier candidate for the four-page paper. It has the source trial residual and factor two but only bounded complex operator scope, while a separate unbounded theorem at the time used a reflection residual. The example remains historically valid, but `PaperUnitaryInvariantNorm` is an older repository name and adds vocabulary that is unrelated to the semantic-alignment point.""",
        [('Historical signature', historical)],
    )

    header = [
        '# Candidate semantic-alignment cases for the workshop paper', '',
        'Generated by `scripts/build_semantic_alignment_candidates.py` from pinned Git revisions.', '',
        '**Snapshot used for open/closed status:** `e9517c4af568` (2026-09-06).', '',
        'Every Lean block below is copied verbatim from `git show`; the generator does not normalize notation or rename declarations. Each block records its exact commit, historical path, 1-based line range, and SHA-256. This file is for choosing and studying a worked example; several listed mismatches were subsequently repaired.', '',
        'The four-page paper currently uses **5 (Section 2 tan-Theta / condition (3.5))** because the mismatch is visible in one hypothesis and the repository contains a direct repair theorem showing how that hypothesis is derived from the source-side definedness condition. Candidates **1**, **2**, **3**, and **6** remain useful alternatives for scope and extra-hypothesis failures.', '',
    ]
    doc = '\n'.join(header + cases).rstrip() + '\n'
    out = PAPER / 'notes' / 'SEMANTIC_ALIGNMENT_CANDIDATES.md'
    out.write_text(doc, encoding='utf8')

    manifest = {
        'schema_version': 1,
        'snapshot': git('rev-parse', 'e9517c4a'),
        'markdown_sha256': hashlib.sha256(doc.encode()).hexdigest(),
        'snippets': [{k: v for k, v in item.items() if k != 'snippet'} for item in snippets],
    }
    jpath = PAPER / 'generated' / 'semantic_alignment_candidates.json'
    jpath.parent.mkdir(exist_ok=True)
    jpath.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n', encoding='utf8')
    print(f'wrote {out} with {len(snippets)} verbatim Lean snippets')


if __name__ == '__main__':
    main()
