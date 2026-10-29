"""Manuscript-native LaTeX lettering for the three numerical diagrams.

PGF keeps labels as live TeX in the paper, so semantic symbol macros retain
font consistency and glossary tooltips. PDF/SVG are standalone vector exports.
"""
from pathlib import Path
import subprocess
import matplotlib.pyplot as plt
from matplotlib.text import Text

PAPER = Path(__file__).resolve().parents[1]


def configure():
    plt.rcParams.update({
        'pgf.texsystem': 'lualatex', 'pgf.rcfonts': False,
        'font.family': 'serif', 'font.size': 18,
        'pgf.preamble': (
            r'\usepackage{lmodern,amsmath,amssymb,xcolor,hyperref}'
            r'\def\DKNoSymbolTooltips{1}\input{'
            + str(PAPER / 'math_symbol_colors.tex') + '}'),
    })


def save(fig, name, description):
    # Semantic macros own label colors; the surrounding formula stays neutral.
    # This also lets the manuscript's monochrome switch affect live labels.
    for label in fig.findobj(Text):
        if r'\sym' in label.get_text() or r'\like' in label.get_text():
            label.set_color('#1B1F24')
    stem = PAPER / 'figures' / name
    fig.savefig(stem.with_suffix('.pgf'))
    # The PGF header records the standalone measurement preamble as a comment.
    # Keep committed sources independent of the build machine's absolute path.
    pgf = stem.with_suffix('.pgf')
    pgf.write_text(pgf.read_text().replace(str(PAPER / 'math_symbol_colors.tex'), 'math_symbol_colors.tex'))
    fig.savefig(stem.with_suffix('.pdf'), metadata={
        'Creator': 'Matplotlib PGF; LuaLaTeX labels; checked dkvis numerical models',
        'Subject': description, 'CreationDate': None, 'ModDate': None})
    subprocess.run(['pdftocairo', '-svg', str(stem.with_suffix('.pdf')),
                    str(stem.with_suffix('.svg'))], check=True)
    svg = stem.with_suffix('.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines()) + '\n')
    preview = PAPER / 'build' / (name + '-preview')
    preview.parent.mkdir(exist_ok=True)
    subprocess.run(['pdftoppm', '-scale-to', '1740', '-png', '-singlefile',
                    str(stem.with_suffix('.pdf')), str(preview)], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    plt.close(fig)
    print(f'Wrote {name}: live PGF, vector PDF/SVG, and preview')
