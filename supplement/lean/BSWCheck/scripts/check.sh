#!/bin/sh
set -u
cd "$(dirname "$0")/.."
fail=0
log=$(mktemp)

echo "== 1. forbidden constructs in sources"
if python3 scripts/forbidden.py; then echo "ok"; else echo "FAIL: forbidden construct found"; fail=1; fi

echo "== 2. lake build"
[ "${1:-}" = "--clean" ] && rm -rf .lake/build
if lake build >"$log" 2>&1; then echo "ok"; else echo "FAIL: build failed"; tail -30 "$log"; fail=1; fi
nw=$(grep -c '^warning' "$log"); ne=$(grep -c '^error' "$log")
echo "warnings: $nw, errors: $ne"
[ "$ne" -eq 0 ] || fail=1

echo "== 3. Audit.lean"
total=$(grep -c 'depends on axioms' "$log")
bad=$(grep 'depends on axioms' "$log" | grep -vE 'axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$' || true)
nodep=$(grep -c 'does not depend on any axioms' "$log")
echo "listed results: $total (+ $nodep axiom-free)"
if [ -n "$bad" ]; then echo "FAIL:"; echo "$bad"; fail=1; else echo "ok"; fi

echo "== 4. AuditAll (all constants)"
out=$(lake env lean scripts/AuditAll.lean 2>&1)
echo "$out" | grep -E 'AUDIT|error' | head -5
echo "$out" | grep -q 'AUDIT OK' || fail=1

rm -f "$log"
if [ $fail -eq 0 ]; then echo "== ALL CHECKS PASSED"; else echo "== CHECKS FAILED"; fi
exit $fail
