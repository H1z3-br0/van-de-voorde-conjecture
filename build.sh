#!/bin/sh
set -e
cd "$(dirname "$0")"
mkdir -p build
run() { pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex >/dev/null || { grep -A5 "^!" build/main.log; exit 1; }; }
run
cp refs.bib build/ && (cd build && bibtex main >/dev/null)
for i in 1 2 3 4; do
  run
  grep -q "Rerun to get" build/main.log || break
done
cp build/main.pdf vdv_conjecture.pdf
grep -E "Warning|undefined|Overfull" build/main.log | grep -v "Font shape" || echo "no warnings"
