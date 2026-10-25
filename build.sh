#!/bin/sh
set -e
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex >/dev/null || { grep -A5 "^!" build/main.log; exit 1; }
cp refs.bib build/ && (cd build && bibtex main >/dev/null)
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex >/dev/null || { grep -A5 "^!" build/main.log; exit 1; }
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex >/dev/null || { grep -A5 "^!" build/main.log; exit 1; }
cp build/main.pdf vdv_conjecture.pdf
grep -E "Warning|undefined|Overfull" build/main.log | grep -v "Font shape" || echo "no warnings"
