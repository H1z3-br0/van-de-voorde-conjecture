import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gf import make_field

EXPECTED = {3: 3, 5: 0, 7: 14, 9: 0, 11: 22, 13: 0}


def run(p, k, modpoly):
    if k == 1:
        q = p

        def mul(a, b):
            return a * b % p

        def add(a, b):
            return (a + b) % p
    else:
        q, mul, add, _ = make_field(p, k, modpoly)
    points = [(x, y, 1) for x in range(q) for y in range(q)] + [(x, 1, 0) for x in range(q)] + [(1, 0, 0)]

    def on(line, point):
        return add(add(mul(line[0], point[0]), mul(line[1], point[1])), mul(line[2], point[2])) == 0

    line_points = {i: frozenset(j for j, P in enumerate(points) if on(L, P)) for i, L in enumerate(points)}
    conic = frozenset(i for i, (x, y, z) in enumerate(points) if mul(y, y) == mul(x, z))
    assert len(conic) == q + 1
    tangents = [i for i in line_points if len(line_points[i] & conic) == 1]
    external_lines = {i for i in line_points if not line_points[i] & conic}
    exterior = [i for i in range(len(points)) if i not in conic and sum(i in line_points[t] for t in tangents) == 2]
    assert len(exterior) == q * (q + 1) // 2
    line_through = {}
    for i, pts in line_points.items():
        for a, b in itertools.combinations(sorted(pts), 2):
            line_through[a, b] = i
    m = (q + 1) // 2

    def no_tangents(S):
        U = conic | S
        return all(len(U & pts) != 1 for pts in line_points.values())

    def is_arc(S):
        return all(len(pts & S) <= 2 for pts in line_points.values())

    joined_externally = {a: {b for b in exterior if b != a and line_through[min(a, b), max(a, b)] in external_lines}
                         for a in exterior}
    count = {"sets": 0, "arcs": 0, "no_tangents": 0, "disagree": 0}

    def extend(S, candidates):
        if len(S) == m:
            s = frozenset(S)
            a, b = is_arc(s), no_tangents(s)
            count["sets"] += 1
            count["arcs"] += a
            count["no_tangents"] += b
            count["disagree"] += a != b
            return
        for v in sorted(candidates):
            if not S or v > S[-1]:
                extend(S + [v], candidates & joined_externally[v])

    extend([], set(exterior))
    line = (f"   q = {q:2d}: {count['sets']:3d} complete exterior sets, {count['arcs']:2d} of them arcs, "
            f"{count['no_tangents']:2d} with no tangents, disagreements: {count['disagree']}")
    ok = count["disagree"] == 0 and count["arcs"] == EXPECTED[q]
    if len(exterior) <= 45:
        found = [frozenset(S) for S in itertools.combinations(exterior, m) if no_tangents(frozenset(S))]
        not_exterior = sum(1 for S in found
                           if any(line_through[min(a, b), max(a, b)] not in external_lines
                                  for a, b in itertools.combinations(S, 2)))
        line += f"; among all {m}-sets of exterior points: {len(found)} with no tangents, all exterior sets"
        ok = ok and len(found) == EXPECTED[q] and not_exterior == 0
    print(line)
    return ok


all_ok = True
for args in [(3, 1, None), (5, 1, None), (7, 1, None), (3, 2, [2, 2, 1]), (11, 1, None), (13, 1, None)]:
    all_ok &= run(*args)
if not all_ok:
    sys.exit("FAILED")
print("All checks passed.")
