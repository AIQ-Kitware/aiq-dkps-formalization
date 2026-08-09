
uv pip install git-of-theseus

cd "$HOME/code/aiq-dkps-formalization"

OUTDIR="./git-of-theseus"
WEEK_SECONDS=$((7 * 24 * 60 * 60))

git-of-theseus-analyze . \
    --interval "$WEEK_SECONDS" \
    --procs 4 \
    --ignore-whitespace \
    --outdir "$OUTDIR"

#git-of-theseus-line-plot \
#    "$OUTDIR/authors.json" \
#    --outfile "$OUTDIR/authors-line.png"

#git-of-theseus-line-plot \
#    "$OUTDIR/authors.json" \
#    --normalize \
#    --outfile "$OUTDIR/authors-line-norm.png"

git-of-theseus-stack-plot \
    "$OUTDIR/cohorts.json" \
    --outfile "$OUTDIR/cohorts-stack.png"

#git-of-theseus-stack-plot \
#    "$OUTDIR/authors.json" \
#    --outfile "$OUTDIR/authors-stack.png"

#git-of-theseus-stack-plot \
#    "$OUTDIR/authors.json" \
#    --normalize \
#    --outfile "$OUTDIR/authors-stack-norm.png"

#git-of-theseus-stack-plot \
#    "$OUTDIR/exts.json" \
#    --outfile "$OUTDIR/ext-stack.png"

git-of-theseus-survival-plot \
    "$OUTDIR/survival.json" \
    --outfile "$OUTDIR/survival.png"



cd "$HOME"/code/aiq-dkps-formalization


git-of-theseus-analyze . \
    --interval "86400" \
    --procs 4 \
    --ignore-whitespace \
    --outdir ./git-of-theseus


git-of-theseus-line-plot ./git-of-theseus/authors.json --outfile ./git-of-theseus/authors-line.png
git-of-theseus-line-plot ./git-of-theseus/authors.json --outfile ./git-of-theseus/authors-line-norm.png --normalize

git-of-theseus-stack-plot ./git-of-theseus/cohorts.json --outfile ./git-of-theseus/cohorts-stack.png
git-of-theseus-stack-plot ./git-of-theseus/authors.json --outfile ./git-of-theseus/authors-stack.png
git-of-theseus-stack-plot ./git-of-theseus/authors.json --normalize --outfile ./git-of-theseus/authors-stack-norm.png
git-of-theseus-stack-plot ./git-of-theseus/exts.json --outfile ./git-of-theseus/ext-stack.png

git-of-theseus-survival-plot ./git-of-theseus/survival.json --outfile ./git-of-theseus/survival-survival.png


