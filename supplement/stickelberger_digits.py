import sys
from math import gcd


def digit_sum(x, p, k):
    s = 0
    for _ in range(k):
        s += x % p
        x //= p
    return s


def check(p, k):
    q = p ** k
    n, h = q - 1, (q - 1) // 2
    units = [t for t in range(n) if gcd(t, n) == 1]
    units_h = [u for u in range(h) if gcd(u, h) == 1]

    def s(x):
        return digit_sum(x % n, p, k)

    def E(y):
        return sum((-1) ** (p ** j * y % h) for j in range(k))

    for x in range(n):
        gamma = sum(1 for j in range(k) if p ** j * x % n >= h)
        if s(x) + s(h) - s(x + h) != (p - 1) * gamma:
            return f"digit-sum formula fails at x = {x}"

    solutions = []
    for b in range(n):
        if b in (0, h):
            continue
        digits = all(s(t) + s(t * (h - b)) == s(t * (1 + h)) + s(-t * b) for t in units)
        parity = all(E(u * b % h) == (-1) ** b * E(u) for u in units_h)
        if digits != parity:
            return f"the equivalence fails at b = {b}"
        if digits:
            solutions.append(b)
    expected = sorted({p ** j * (1 + h) % n for j in range(k)} | {-p ** j % n for j in range(k)})
    if solutions != expected:
        return f"solutions {solutions}, expected {expected}"
    return None


cases = [(p, 1) for p in [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107]]
cases += [(3, 3), (3, 5), (7, 3), (11, 3), (3, 7)]
for p, k in cases:
    error = check(p, k)
    label = f"q = {p}" if k == 1 else f"q = {p}^{k} = {p ** k}"
    if error:
        sys.exit(f"FAILED for {label}: {error}")
    print(f"   {label}: OK")
print("All checks passed.")
