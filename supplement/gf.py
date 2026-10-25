def make_field(p, k, modpoly):
    q = p ** k

    def to_digits(a):
        return [(a // p ** i) % p for i in range(k)]

    def from_digits(digits):
        return sum((c % p) * p ** i for i, c in enumerate(digits))

    def mul(a, b):
        x, y, r = to_digits(a), to_digits(b), [0] * (2 * k)
        for i in range(k):
            for j in range(k):
                r[i + j] += x[i] * y[j]
        for d in range(2 * k - 1, k - 1, -1):
            c = r[d] % p
            if c:
                for i in range(k + 1):
                    r[d - k + i] -= c * modpoly[i]
        return from_digits(r[:k])

    def add(a, b):
        return from_digits([x + y for x, y in zip(to_digits(a), to_digits(b))])

    def neg(a):
        return from_digits([-x for x in to_digits(a)])

    return q, mul, add, neg
