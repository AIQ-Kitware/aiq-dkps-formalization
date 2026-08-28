#!/bin/bash
set -euo pipefail

mkdir -p build/leanq

LEAN_NUM_THREADS=3 lake build

leanq graph-index \
    --out build/leanq/project-semantic-graph.json

leanq graph-compare-html \
    build/leanq/project-semantic-graph.json \
    --census dev/davis-kahan-1970-full-source-census.json \
    --census dev/yu-wang-samworth-2015-full-source-census.json \
    --census dev/quench-2026-full-source-census.json \
    --boundary headline \
    --family 'Davis–Kahan' \
    --family 'Quench' \
    --out build/leanq/proof-comparison.html

#leanq graph-html \
#    build/leanq/project-semantic-graph.json \
#    --census dev/davis-kahan-1970-full-source-census.json \
#    --census dev/yu-wang-samworth-2015-full-source-census.json \
#    --census dev/quench-2026-full-source-census.json \
#    --boundary headline \
#    --out build/leanq/project-semantic-graph.html

cat <<'EOF'

HTML proof explorer built:

    build/leanq/project-semantic-graph.html

Open it with, for example:

    google-chrome build/leanq/project-semantic-graph.html

or:

    xdg-open build/leanq/project-semantic-graph.html

EOF
