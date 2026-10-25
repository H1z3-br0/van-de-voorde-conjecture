#!/bin/sh
set -e
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
echo "== Proposition 3.2 (brute force in the plane)";         python3 plane_check.py
echo "== Table 1 and the examples for q = 7, 11 (Section 8)"; python3 examples.py
echo "== Proposition 6.2 (digit combinatorics)";               python3 stickelberger_digits.py
echo "== Other steps of the proof (Section 9.1)";              python3 checks.py
echo "== The data files can be rebuilt by the search program"
tmp=$(mktemp -d)
cp data/q_*.txt "$tmp"/
sh search/make_data.sh > /dev/null
for f in data/q_*.txt; do
  grep -v '^q=' "$f" > "$tmp/new"
  grep -v '^q=' "$tmp/$(basename "$f")" > "$tmp/old"
  if ! cmp -s "$tmp/new" "$tmp/old"; then
    cp "$tmp"/q_*.txt data/; echo "FAILED: $f differs from the stored version"; exit 1
  fi
done
cp "$tmp"/q_*.txt data/
rm -r "$tmp"
echo "   identical (apart from the running time)"
echo "== Everything passed."
