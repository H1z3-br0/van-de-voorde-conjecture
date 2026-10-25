import cmath
import os
import random
import re
import sys
from math import sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf import make_field

DATA = os.path.join(HERE, "data")
random.seed(2026)


def expect(condition, message):
    if not condition:
        sys.exit("FAILED: " + message)


class Field:
    def __init__(self, p, k=1, poly=None):
        if k == 1:
            self.q = p
            mul, add, neg = (
                (lambda a, b: a * b % p),
                (lambda a, b: (a + b) % p),
                (lambda a: -a % p),
            )
        else:
            self.q, mul, add, neg = make_field(p, k, poly)
        self.p, self.k = p, k
        q = self.q
        self.M = [[mul(a, b) for b in range(q)] for a in range(q)]
        self.A = [[add(a, b) for b in range(q)] for a in range(q)]
        self.N = [neg(a) for a in range(q)]

        for g in range(2, q):
            x, order = g, 1
            while x != 1 and order < q:
                x, order = self.M[x][g], order + 1
            if order == q - 1:
                break
        else:
            raise ValueError("not a field")
        self.log, self.exp, x = [-1] * q, [0] * (q - 1), 1
        for i in range(q - 1):
            self.exp[i], self.log[x], x = x, i, self.M[x][g]
        expect(len(set(self.exp)) == q - 1, f"no generator found for q = {q}")

    def sub(self, a, b):
        return self.A[a][self.N[b]]

    def inv(self, a):
        return self.exp[-self.log[a] % (self.q - 1)]

    def chi(self, a):
        return 0 if a == 0 else (1 if self.log[a] % 2 == 0 else -1)

    def power(self, a, e):
        return 0 if a == 0 else self.exp[self.log[a] * e % (self.q - 1)]

    def four(self):
        return self.A[self.A[1][1]][self.A[1][1]]


def read_solutions(q):
    result = []
    with open(os.path.join(DATA, f"q_{q}.txt")) as f:
        for line in f:
            if line.startswith("NON-ELLIPTIC"):
                psi = {}
                for a, b in re.findall(r"\{(\d+),(\d+)\}", line):
                    psi[int(a)], psi[int(b)] = int(b), int(a)
                result.append(psi)
    return result


def form(F, a, b):
    if a is None:
        a, b = b, a
    if b is None:
        return (0, 1, F.N[a])
    return (1, F.N[F.A[a][b]], F.M[a][b])


def det3(F, u, v, w):
    m, s = F.M, F.sub
    t1 = m[u[0]][s(m[v[1]][w[2]], m[v[2]][w[1]])]
    t2 = m[u[1]][s(m[v[0]][w[2]], m[v[2]][w[0]])]
    t3 = m[u[2]][s(m[v[0]][w[1]], m[v[1]][w[0]])]
    return F.A[s(t1, t2)][t3]


def is_arc(F, psi):
    points, seen = [(0, 1, 0)], set()
    for x in range(1, F.q):
        if x not in seen:
            seen |= {x, psi[x]}
            points.append(form(F, x, psi[x]))
    n = len(points)
    return all(
        det3(F, points[i], points[j], points[l]) != 0
        for i in range(n)
        for j in range(i + 1, n)
        for l in range(j + 1, n)
    )


FIELDS = {
    7: Field(7),
    11: Field(11),
    19: Field(19),
    23: Field(23),
    27: Field(3, 3, [1, 2, 0, 1]),
    31: Field(31),
}

print("1. Arcs among all complete exterior sets containing {0, inf}")
expected_arcs = {7: 2, 11: 2, 19: 0, 23: 0, 27: 0, 31: 0}
for q, F in FIELDS.items():
    solutions = read_solutions(q)
    for psi in solutions:
        expect(
            all(F.chi(x) * F.chi(psi[x]) == -1 for x in range(1, q)),
            f"bad data for q = {q}",
        )
    linear = [
        {x: F.M[n][F.inv(x)] for x in range(1, q)}
        for n in range(1, q)
        if F.chi(n) == -1
    ]
    arcs = sum(is_arc(F, psi) for psi in solutions)
    linear_arcs = sum(is_arc(F, psi) for psi in linear)
    print(
        f"   q = {q:2d}: {len(solutions) + len(linear):3d} sets ({len(linear)} linear), arcs among them: {arcs}"
    )
    expect(
        arcs == expected_arcs[q] and linear_arcs == 0,
        f"unexpected number of arcs for q = {q}",
    )

print(
    "2. Proposition 7.3: non-squares c with chi((t-c)(ct-1)) = 1 for all squares t != 1"
)
expected_c = {7: [3, 5], 11: [2, 6]}
for q in [7, 11, 19, 23, 27, 31, 43]:
    F = FIELDS.get(q) or Field(q)
    squares = [t for t in range(1, q) if F.chi(t) == 1]
    admissible = [
        c
        for c in range(1, q)
        if F.chi(c) == -1
        and all(
            F.chi(F.M[F.sub(t, c)][F.sub(F.M[c][t], 1)]) == 1 for t in squares if t != 1
        )
    ]
    for c in admissible:
        if c != F.N[1]:
            total = sum(
                F.chi(F.M[F.sub(F.M[r][r], c)][F.sub(F.M[c][F.M[r][r]], 1)])
                for r in range(q)
            )
            expect(total == q - 6, f"character sum is not q - 6 for q = {q}, c = {c}")
    print(f"   q = {q:2d}: admissible c = {admissible if admissible else 'none'}")
    expect(admissible == expected_c.get(q, []), f"unexpected admissible c for q = {q}")

print(
    "3. Lemma 4.2: Pi_P * Pi_Q * Pi_R = -eps(P, Q, R) for random pairwise compatible, non-collinear P, Q, R"
)


def segre_mismatches(F, trials):
    q, chi = F.q, F.chi

    def compatible(P, Q):
        (a, b), (c, d) = P, Q
        return (
            chi(F.M[F.M[F.sub(a, c)][F.sub(a, d)]][F.M[F.sub(b, c)][F.sub(b, d)]]) == -1
        )

    def disc(f):
        return F.sub(F.M[f[1]][f[1]], F.M[F.four()][F.M[f[0]][f[2]]])

    def combo(f, g, s, u):
        return tuple(F.A[F.M[s][f[i]]][F.M[u][g[i]]] for i in range(3))

    def passant(f, g):
        return disc(g) != 0 and all(disc(combo(f, g, 1, u)) != 0 for u in range(q))

    def orientation(a, b, c):
        return chi(F.sub(a, b)) * chi(F.sub(b, c)) * chi(F.sub(c, a))

    def slope_product(
        FP, FQ, FR
    ):
        r = 1
        for y in range(1, q):
            if passant(FP, combo(FQ, FR, y, 1)):
                r = F.M[r][F.inv(y)]
        return r

    bad = done = 0
    while done < trials:
        e = random.sample(range(q), 6)
        P, Q, R = (e[0], e[1]), (e[2], e[3]), (e[4], e[5])
        if not (compatible(P, Q) and compatible(Q, R) and compatible(P, R)):
            continue
        FP, FQ, FR = form(F, *P), form(F, *Q), form(F, *R)
        expect(
            passant(FP, FQ) and passant(FQ, FR) and passant(FP, FR),
            "Lemma 3.1(v) fails",
        )
        if det3(F, FP, FQ, FR) == 0:
            continue
        lhs = F.M[F.M[slope_product(FP, FQ, FR)][slope_product(FQ, FR, FP)]][
            slope_product(FR, FP, FQ)
        ]
        eps = orientation(P[0], Q[0], R[0]) * orientation(P[1], Q[1], R[1])
        bad += lhs != (F.N[1] if eps == 1 else 1)
        done += 1
    return bad


for q in [7, 11, 19, 23, 27, 31, 43, 47]:
    F = FIELDS.get(q) or Field(q)
    bad = segre_mismatches(F, 60)
    print(f"   q = {q:2d}: 60 triples, mismatches: {bad}")
    expect(bad == 0, f"Lemma 4.2 fails for q = {q}")

print("4. Lemmas 5.1 and 5.2 on the arcs for q = 7 and q = 11")
for q in [7, 11]:
    F = FIELDS[q]
    chi, n, h = F.chi, q - 1, (q - 1) // 2
    w = cmath.exp(2j * cmath.pi / n)
    for psi in read_solutions(q):
        if not is_arc(F, psi):
            continue
        cond_A = all(
            chi(F.sub(psi[z], psi[y])) == -chi(F.sub(z, y)) * chi(F.M[y][z])
            for y in range(1, q)
            for z in range(1, q)
            if z not in (y, psi[y])
        )
        cond_B = all(chi(F.M[x][F.sub(x, psi[x])]) == -1 for x in range(1, q))
        cond_C = all(
            chi(F.M[F.sub(x, psi[x])][F.sub(z, psi[x])])
            == -chi(F.M[F.sub(x, psi[z])][F.sub(z, psi[z])])
            for x in range(1, q)
            for z in range(1, q)
            if z not in (x, psi[x])
        )

        def eta(a, x):
            return w ** (a * F.log[x]) if x else 0

        def jacobi(a):
            return sum(chi(F.sub(1, t)) * eta(a, t) for t in range(1, q))

        def matrix_m(b, a):
            return sum(eta(b, x).conjugate() * eta(a, psi[x]) for x in range(1, q))

        error = max(
            abs(
                (jacobi(a) + jacobi(b).conjugate()) * matrix_m(b, a)
                + 2 * (q - 1) * (a == b)
            )
            for a in range(n)
            for b in range(n)
            if a not in (0, h) and b not in (0, h)
        )
        pairs = sorted({tuple(sorted((x, psi[x]))) for x in psi})
        print(
            f"   q = {q:2d}, pairs {pairs}: (A), (B), (C) hold; Lemma 5.2 error {error:.0e}"
        )
        expect(
            cond_A and cond_B and cond_C and error < 1e-9,
            f"Lemma 5.1/5.2 fails for q = {q}",
        )

print("5. Lemma 2.1 and |J(chi, eta)| = sqrt(q)")
for p, k, poly in [(3, 3, [1, 2, 0, 1]), (7, 3, [4, 0, 0, 1])]:
    F = Field(p, k, poly)
    q, n = F.q, F.q - 1
    w = cmath.exp(2j * cmath.pi / n)

    def jacobi_sum(a):
        return sum(F.chi(F.sub(1, t)) * w ** (a * F.log[t]) for t in range(1, q))

    values = {a: jacobi_sum(a) for a in range(1, n) if a != n // 2}
    frob_error = max(abs(values[a] - values[a * p % n]) for a in values)
    abs_error = max(abs(abs(v) - sqrt(q)) for v in values.values())
    print(
        f"   q = {q:3d}: max |J(eta^a) - J(eta^(pa))| = {frob_error:.0e}, max ||J| - sqrt(q)| = {abs_error:.0e}"
    )
    expect(frob_error < 1e-6 and abs_error < 1e-6, f"Lemma 2.1 fails for q = {q}")

print(
    "6. Proposition 7.4: no non-square c with chi(1 - c y^(2(p^j - 1))) = -1 for all y != 0, 0 < j < k"
)
for p, k, poly in [
    (3, 3, [1, 2, 0, 1]),
    (7, 3, [4, 0, 0, 1]),
    (3, 5, [1, 2, 0, 0, 0, 1]),
]:
    F = Field(p, k, poly)
    q = F.q
    hits = [
        (j, c)
        for j in range(1, k)
        for c in range(1, q)
        if F.chi(c) == -1
        and all(
            F.chi(F.sub(1, F.M[c][F.power(y, 2 * (p**j - 1))])) == -1
            for y in range(1, q)
        )
    ]
    print(f"   q = {q:3d}: solutions found: {len(hits)}")
    expect(not hits, f"Proposition 7.4 fails for q = {q}")

print("All checks passed.")
