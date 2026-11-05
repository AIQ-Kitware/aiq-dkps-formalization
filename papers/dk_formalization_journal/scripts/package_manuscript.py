#!/usr/bin/env python3
"""Export the editable Overleaf project or the publisher's single-TeX sources."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
from zipfile import ZIP_DEFLATED, ZipFile

PAPER = Path(__file__).resolve().parents[1]
SOURCES = (
    'paper.tex', 'math_symbol_colors.tex', 'counterexample.tex',
    'formalization_enabled_extension.tex', 'appendix_notation.tex',
    'appendix_process.tex', 'appendix_result_summaries.tex',
    'references.bib', 'sn-jnl.cls', 'sn-mathphys-num.bst',
    'sn-mathphys-ay.bst', 'latexmkrc', 'README_OVERLEAF.md',
)
INPUT = re.compile(r'^\s*\\input\{([^}]+)\}\s*$', re.MULTILINE)


def flattened_source(path):
    """Expand the article's standalone TeX includes, leaving figures separate."""
    source = path.read_text()
    return INPUT.sub(
        lambda m: flattened_source(PAPER / Path(m[1]).with_suffix('.tex')),
        source,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kind', choices=('overleaf', 'submission'))
    args = parser.parse_args()
    stage = PAPER / 'build' / args.kind
    if stage.exists():
        shutil.rmtree(stage)
    (stage / 'figures').mkdir(parents=True)
    for name in SOURCES:
        shutil.copy2(PAPER / name, stage / name)
    for number in range(1, 4):
        for suffix in ('.pgf', '.pdf'):
            name = f'figures/Fig{number}{suffix}'
            shutil.copy2(PAPER / name, stage / name)

    if args.kind == 'submission':
        source = flattened_source(PAPER / 'paper.tex')
        source = re.sub(r'^\\DKAuthorStyle(?:true|false)$',
                        lambda _: '\\DKAuthorStylefalse', source,
                        count=1, flags=re.MULTILINE)
        source = re.sub(
            r'\\resizebox\{([^{}]+)\}\{!\}\{\\input\{figures/(Fig[123])\.pgf\}\}',
            lambda m: r'\includegraphics[width=' + m[1] + ']{figures/' + m[2] + '.pdf}',
            source,
        )
        (stage / 'paper.tex').write_text(source)
        for name in SOURCES:
            if name.endswith('.tex') and name != 'paper.tex':
                (stage / name).unlink()
        subprocess.run(['latexmk', '-pdf', '-outdir=build', 'paper.tex'],
                       cwd=stage, check=True)
        shutil.copy2(stage / 'build/paper.pdf', stage / 'paper.pdf')
        for number in range(1, 4):
            subprocess.run([
                'pdftops', '-eps', f'figures/Fig{number}.pdf',
                f'figures/Fig{number}.eps',
            ], cwd=stage, check=True)
    else:
        shutil.copy2(PAPER / 'build/paper.pdf', stage / 'paper.pdf')

    archive = PAPER / 'build' / f'dk_formalization_{args.kind}.zip'
    with ZipFile(archive, 'w', compression=ZIP_DEFLATED) as bundle:
        for path in sorted(stage.rglob('*')):
            if path.is_file() and 'build' not in path.relative_to(stage).parts:
                bundle.write(path, path.relative_to(stage))
    print(f'Wrote {archive.relative_to(PAPER)}')


if __name__ == '__main__':
    main()
