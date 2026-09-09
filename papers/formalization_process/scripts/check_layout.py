#!/usr/bin/env python3
"""Check the workshop page budget, display integrity, and author visibility.

Requires pdftotext (Poppler). Run after building both PDFs. This checks the
rendered text and TeX logs; visual inspection is still needed for layout.
"""
from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

PAPER = Path(__file__).resolve().parent.parent
AUTHORS = ('Jonathan Crall', 'Brian Hu', 'Edward Wang', 'Carey E. Priebe')
CONTRACT = 'HR001125CE017'


def validate_pages(pages: list[str], public: bool) -> list[str]:
    """Return failures for extracted, form-feed-separated PDF pages."""
    errors = []
    reference_pages = [
        i + 1 for i, page in enumerate(pages)
        if re.search(r'^\s*(?:\d+\s+)?References\s*(?:\d+\s*)?$', page, re.M)
    ]
    if len(reference_pages) != 1:
        errors.append(f'References heading must appear exactly once; found {reference_pages}')
        return errors
    reference_page = reference_pages[0]
    main_pages = reference_page - 1
    if not public and not (4 <= main_pages <= 9):
        errors.append(f'Anonymous main text must be 4--9 pages; found {main_pages}')
    if not any(re.search(r'\bConclusion\b', page) for page in pages[:main_pages]):
        errors.append('Conclusion must appear before References')
    flat_pages = [' '.join(page.split()) for page in pages]
    display_pages = [
        i for i, page in enumerate(flat_pages)
        if 'theorem sinTwoTheta_ambient' in page
    ]
    if len(display_pages) != 1 or display_pages[0] >= main_pages:
        errors.append('Historical theorem must appear once before References')
    else:
        display = flat_pages[display_pages[0]]
        required = (
            '-- proof omitted', 'Formalization 1:',
            'source scope includes unbounded',
            'SymmetricNormingFunction',
            'variable {A B : E → L[C] E}', '{U V : Submodule C E}',
            'U⊥ A', 'x ≤ a - d ∨ b + d ≤ x',
            '2 * N.gauge (B - A)',
        )
        for token in required:
            if token not in display:
                errors.append(f'Historical display split or text missing: {token}')
    figure1 = [i + 1 for i, page in enumerate(flat_pages) if 'Figure 1:' in page]
    figure2 = [i + 1 for i, page in enumerate(flat_pages) if 'Figure 2:' in page]
    if len(figure1) != 1 or figure1[0] > 2:
        errors.append(f'Workflow Figure 1 must appear by page 2; found {figure1}')
    if len(figure2) != 1 or figure2[0] <= reference_page:
        errors.append(f'Publication Figure 2 must remain after References in the appendix; found {figure2}')
    checklist_pages = [i + 1 for i, page in enumerate(flat_pages) if 'NeurIPS Paper Checklist' in page]
    if len(checklist_pages) != 1 or checklist_pages[0] <= reference_page:
        errors.append(f'NeurIPS checklist must appear once after References; found {checklist_pages}')
    current_pages = [
        i for i, page in enumerate(flat_pages)
        if 'theorem sinTwoTheta_commonDomain_whereDefinedUIN_rclike' in page
    ]
    if len(current_pages) != 1 or current_pages[0] >= main_pages:
        errors.append('Current source-facing sin 2Theta theorem must appear once before References')
    else:
        current = flat_pages[current_pages[0]]
        for token in (
            '-- proof omitted', 'Formalization 2:',
            'NormalizedSymmetricOperatorIdealFamily',
            'RCLike K', 'SeparableSpace E', 'T.domain = A.domain',
            'FormBoundedSylvesterGap', 'ReducesSubspace A P',
            'ReducesSubspace T Q', '∀ R : P', '∀ Hop : E',
            'directedSinTwoAngleOperator P Q', 'sinTwoAngleOperator P Q',
            'N.Mem R', 'N.Mem Hop', '2 * N.gaugeReal R',
            '2 * N.gaugeReal Hop',
        ):
            if token not in current:
                errors.append(f'Current sin 2Theta display split or text missing: {token}')
    main_text = ' '.join(flat_pages[:main_pages])
    for token in ('AI assistance.', 'ChatGPT and Claude were used throughout'):
        if token not in main_text:
            errors.append(f'Main-text AI-assistance statement is missing: {token}')
    text = ' '.join(flat_pages)
    if public:
        for author in AUTHORS:
            if author not in flat_pages[0]:
                errors.append(f'Public first page is missing author: {author}')
        if CONTRACT not in ' '.join(flat_pages[:reference_page]):
            errors.append('Public acknowledgment must appear before References')
    else:
        for identifier in (*AUTHORS, CONTRACT, 'github.com/AIQ-Kitware'):
            if identifier in text:
                errors.append(f'Identifying text in anonymous PDF: {identifier}')
    if '\ufffd' in text or '??' in text:
        errors.append('Replacement glyph or unresolved reference in PDF text')
    return errors


def validate_source_editability() -> list[str]:
    """Catch source characters that make uploaded Overleaf .tex files non-editable."""
    errors = []
    for path in sorted(PAPER.glob('*.tex')):
        text = path.read_text(encoding='utf-8')
        for lineno, line in enumerate(text.splitlines(), 1):
            bad = [(c, ord(c)) for c in line if ord(c) > 0xFFFF]
            if bad:
                rendered = ', '.join(f'U+{code:04X}' for _, code in bad)
                errors.append(
                    f'{path.name}:{lineno}: non-BMP Unicode ({rendered}); '
                    'use ASCII listings sentinels / LaTeX commands instead'
                )
    return errors


def main() -> int:
    executable = shutil.which('pdftotext')
    if executable is None:
        print('ERROR: pdftotext is required (install Poppler utilities).')
        return 1
    failed = False
    source_errors = validate_source_editability()
    for error in source_errors:
        failed = True
        print(f'source: ERROR: {error}')
    for name, public in [('paper', False), ('paper_public', True)]:
        pdf = PAPER / 'build' / f'{name}.pdf'
        log = PAPER / 'build' / f'{name}.log'
        errors = []
        if not pdf.is_file() or not log.is_file():
            errors.append(f'Build {pdf.name} and its TeX log before checking layout')
        else:
            result = subprocess.run(
                [executable, '-layout', str(pdf), '-'],
                text=True, encoding='utf-8', capture_output=True, check=False,
            )
            if result.returncode:
                errors.append(f'pdftotext failed: {result.stderr.strip()}')
            else:
                pages = result.stdout.split('\f')
                while pages and not pages[-1].strip():
                    pages.pop()
                errors.extend(validate_pages(pages, public))
            log_text = log.read_text(encoding='utf-8', errors='replace')
            for pattern in (
                r'Overfull \\[hv]box', r'Missing character:',
                r'(?:Citation|Reference) .+ undefined',
                r'There were undefined (?:references|citations)',
                r'Label\(s\) may have changed', r'Rerun to get',
                r'Token not allowed in a PDF string',
            ):
                if re.search(pattern, log_text):
                    errors.append(f'TeX diagnostic matched: {pattern}')
        if errors:
            failed = True
            for error in errors:
                print(f'{pdf.name}: ERROR: {error}')
        else:
            print(f'{pdf.name}: PASS: workshop page budget/reference boundary, display, '
                  'figures, checklist, author visibility, and TeX diagnostics checked')
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
