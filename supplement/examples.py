import sys
from itertools import combinations


def expect(condition, message):
    if not condition:
        sys.exit("FAILED: " + message)


def chi(a, q):
    a %= q
    return 0 if a == 0 else (1 if pow(a, (q - 1) // 2, q) == 1 else -1)


def form(pair, q):
    a, b = pair
    if a is None:
        a, b = b, a
    if b is None:
        return (0, 1, -a % q)
    return (1, -(a + b) % q, a * b % q)


def det3(u, v, w, q):
    return (u[0] * (v[1] * w[2] - v[2] * w[1]) - u[1] * (v[0] * w[2] - v[2] * w[0])
            + u[2] * (v[0] * w[1] - v[1] * w[0])) % q


def compatible(P, Q, q):
    product = 1
    for x in P:
        for y in Q:
            if x is not None and y is not None:
                product *= x - y
    return chi(product, q) == -1


def mobius(g, x, q):
    a, b, c, d = g
    if x is None:
        return None if c == 0 else a * pow(c, -1, q) % q
    num, den = (a * x + b) % q, (c * x + d) % q
    return None if den == 0 else num * pow(den, -1, q) % q


def pgl2(q):
    group = []
    for a in range(q):
        for b in range(q):
            for c in range(q):
                for d in range(q):
                    if (a * d - b * c) % q and next(t for t in (a, b, c, d) if t) == 1:
                        group.append((a, b, c, d))
    return group


def compose(g, h, q):
    a, b, c, d = g
    e, f, k, l = h
    m = ((a * e + b * k) % q, (a * f + b * l) % q, (c * e + d * k) % q, (c * f + d * l) % q)
    first = next(t for t in m if t)
    inverse = pow(first, -1, q)
    return tuple(t * inverse % q for t in m)


def order(g, q):
    x, n = g, 1
    while x != (1, 0, 0, 1):
        x, n = compose(x, g, q), n + 1
    return n


print("1. Table 1: non-squares c != -1 and condition (7.1)")
expected_admissible = {7: [3, 5], 11: [2, 6], 19: []}
for q in (7, 11, 19):
    squares = [t for t in range(1, q) if chi(t, q) == 1]
    admissible, excluded = [], []
    for c in range(1, q - 1):
        if chi(c, q) != -1:
            continue
        witnesses = [t for t in squares if t != 1 and chi((t - c) * (c * t - 1), q) == -1]
        if witnesses:
            excluded.append(f"c = {c} (t = {witnesses[0]})")
        else:
            admissible.append(c)
    print(f"   q = {q:2d}: admissible c = {admissible if admissible else 'none'}; "
          f"excluded: {', '.join(excluded) if excluded else 'none'}")
    expect(admissible == expected_admissible[q], f"Table 1 is wrong for q = {q}")

print("2. The examples and their orbits under PGL(2, q)")
results = {}
for q, c, expected_orbit in ((7, 3, 14), (11, 2, 22)):
    squares = [t for t in range(1, q) if chi(t, q) == 1]
    S = [(0, None)] + [(x, c * x % q) for x in squares]
    points = [form(P, q) for P in S]
    exterior_set = all(compatible(P, Q, q) for P, Q in combinations(S, 2))
    arc = all(det3(u, v, w, q) != 0 for u, v, w in combinations(points, 3))

    def key(pairs):
        return frozenset(frozenset(P) for P in pairs)

    group = pgl2(q)
    orbit, stabiliser = set(), []
    for g in group:
        image = key([(mobius(g, a, q), mobius(g, b, q)) for a, b in S])
        orbit.add(image)
        if image == key(S):
            stabiliser.append(g)
    pairs = ", ".join("{" + ",".join("inf" if t is None else str(t) for t in P) + "}" for P in S)
    print(f"   q = {q:2d}, c = {c}: S = {pairs}")
    print(f"           exterior set: {exterior_set}, no three collinear: {arc}, "
          f"orbit length {len(orbit)}, stabiliser order {len(stabiliser)}")
    expect(exterior_set and arc and len(orbit) == expected_orbit, f"example for q = {q} is wrong")
    results[q] = stabiliser

print("3. The stabilisers")
expected_orders = {7: {1: 1, 2: 9, 3: 8, 4: 6}, 11: {1: 1, 2: 15, 3: 20, 5: 24}}
for q, stabiliser in results.items():
    counts = {}
    for g in stabiliser:
        n = order(g, q)
        counts[n] = counts.get(n, 0) + 1
    in_psl = all(chi(a * d - b * c, q) == 1 for a, b, c, d in stabiliser)
    name = "S4" if q == 7 else "A5"
    print(f"   q = {q:2d}: element orders {dict(sorted(counts.items()))} (as in {name}), inside PSL(2, q): {in_psl}")
    expect(counts == expected_orders[q] and in_psl, f"stabiliser for q = {q} is wrong")

print("All checks passed.")
