# Supplementary material

Everything here can be re-run in under a minute on an ordinary laptop. You need Python 3.8 or newer
(standard library only) and, for the search program, a C compiler.

```sh
sh run_all.sh
```

runs all checks one after another and stops with `FAILED: …` as soon as a result differs from what
the paper states. Each script also works on its own.

## What each file does

| File | What it checks | Paper |
|---|---|---|
| `plane_check.py` | Brute force in the plane PG(2, q) for q = 3, 5, 7, 9, 11, 13, independent of the "pairs" model: for every complete exterior set S, "no three points collinear" holds exactly when "C ∪ S has no tangents". For q ≤ 9 it runs through all sets of (q+1)/2 exterior points. | Proposition 3.2 |
| `examples.py` | Table 1 (which constants c survive for q = 7, 11, 19); the examples for q = 7 and 11 are complete exterior sets with no three collinear points; their orbits have 14 and 22 elements; the stabilisers are S4 and A5. | Table 1, Section 8 |
| `stickelberger_digits.py` | The combinatorial core of Proposition 6.2, for every b, in 19 fields up to q = 2187. This is the only step of the proof that is neither formalised in Lean nor a cited classical theorem. | Proposition 6.2 |
| `checks.py` | The remaining steps on concrete fields: no arcs among all complete exterior sets for q = 19…31; Proposition 7.3; Lemma 4.2 on random triples; Lemmas 5.1, 5.2 on the examples; Lemma 2.1; Proposition 7.4. | Section 9.1 |
| `gf.py` | Arithmetic in F_{p^k}, shared by the scripts above. | — |
| `search/bsw_search.c` | Exhaustive search for all complete exterior sets containing the point {0, ∞}. Its pruning rule is proved in Lean (`main_balance`). | Section 9.1 |
| `search/make_data.sh` | Compiles the search program and rebuilds `data/`. | — |
| `data/` | The output of the search for q = 7, 11, 19, 23, 27, 31; format in `data/README.md`. | — |
| `lean/BSWCheck/` | The Lean 4 formalisation; see its own README. | Section 9.2 |
| `run_all.sh` | Runs everything above except Lean, and checks that the search program reproduces `data/`. | — |

The Lean part needs a separate setup (about 3 minutes to check once Mathlib is downloaded); see
`lean/BSWCheck/README.md`.
