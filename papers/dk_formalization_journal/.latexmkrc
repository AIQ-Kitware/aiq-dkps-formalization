$pdf_mode = 1;
$out_dir = 'build';
# Let latexmk place both LaTeX and BibTeX products in the same directory.
# A hard-coded -output-directory in $pdflatex leaves BibTeX using stale root aux files.
# LaTeXBox invokes latexmk -pdf, so select LuaLaTeX through this command too.
# The manuscript's emoji comments require LuaTeX.
$pdflatex = 'lualatex -synctex=1 -interaction=nonstopmode -halt-on-error %O %S';

# LuaTeX can truncate/remove the PDF before reporting a source error.
# Keep the last successful PDF available to the editor's viewer on failure.
$compiling_cmd = 'if test -s %D; then cp -p %D %D.last-good; fi';
$failure_cmd = 'if test -f %D.last-good; then mv -f %D.last-good %D; fi';
$success_cmd = 'rm -f %D.last-good';

# The figures are generated and gitignored. Prepare them for direct latexmk
# invocations too, including Vim/LaTeXBox builds that do not call `make paper`.
unless (grep { $_ eq '-c' || $_ eq '-C' || $_ eq '-CA' } @ARGV) {
    system('make', 'paper-figures') == 0
        or die "Could not generate the manuscript figures.\n";
}
