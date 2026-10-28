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
