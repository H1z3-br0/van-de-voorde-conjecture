# Lean 4 formalisation

This folder is a Lean 4 project that machine-checks the main line of the proof in the paper.

## What is proved

The theorem `BSW.Main.main_vdv` (file `BSWCheck/MainTheorems.lean`) says:

> Let F be a finite field of odd order q, with q not 3, 7 or 11. Then no complete exterior set of the conic is an arc.

In Lean a complete exterior set is a fixed-point-free involution `Ψ` of the projective line over F
whose 2-cycles are pairwise compatible (`BSW.Proj.Solution Ψ`). "No three points collinear"
(`BSW.Plane.ArcLikeP Ψ`) means that no three of the corresponding binary quadratic forms have zero
determinant. Lemma 3.1 of the paper, which links these formulas to the geometry, is formalised as well.

## What is assumed

Mathlib does not yet contain Stickelberger's theorem, Weil's bound or McConnel's theorem. These
enter as **explicit hypotheses** of the theorem, never as axioms:

| Hypothesis | Meaning | Used for |
|---|---|---|
| `StickelHyp p` | Proposition 6.2 for a prime field, in a slightly stronger form (any η, not only a generator) | q = p ≡ 3 (mod 4) |
| `StickelPKHyp F p k` | Proposition 6.2 for every generator η₁ (equivalent to the paper's version, by Galois conjugation) | q = p^k ≡ 3 (mod 4), k ≥ 3 |
| `WeilHyp F` | Weil's bound (W) for square-free polynomials | q = p^k ≡ 3 (mod 4), k ≥ 3 |
| `McConnelHyp F p k` | McConnel's theorem (it contains Carlitz's theorem) | q ≡ 1 (mod 4): from it Lean derives the Blokhuis–Seress–Wilbrink theorem |

In the paper, Proposition 6.2 is derived from Stickelberger's theorem by hand. That derivation is not
formalised; its combinatorial core is checked by `supplement/stickelberger_digits.py`. We also tested
the hypotheses numerically, for sanity only: `StickelHyp` for all primes p < 260, `StickelPKHyp` for
q = 27, 243, 343, McConnel for q = 9, 25, and Weil on random polynomials over F_9 and F_27.

Apart from these hypotheses, every result depends only on the three standard axioms of Lean's
mathematics library (`propext`, `Classical.choice`, `Quot.sound`). The project contains no
`sorry` and no `native_decide`.

## How to check it

You need [elan](https://github.com/leanprover/elan), the Lean version manager. The Lean version
(`v4.35.0`) and the Mathlib revision (`56a0058…`) are pinned in `lean-toolchain` and
`lake-manifest.json`.

```sh
lake exe cache get      # download the compiled Mathlib (a few GB, needed only once)
sh scripts/check.sh     # about 3 minutes
```

`check.sh` does four things and prints `ALL CHECKS PASSED` at the end:

1. scans the sources for forbidden commands (`sorry`, `axiom`, `native_decide`, `implemented_by`, …);
2. builds the project;
3. prints the axioms of the main results (`BSWCheck/Audit.lean`) and checks that only the three
   standard ones occur;
4. does the same automatically for **every** constant of the project (`scripts/AuditAll.lean`),
   not only the listed ones.

## Where each step of the paper is

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 (exterior points = pairs, compatibility = passant) | `external_iff`, `compat_iff_passant`, `det3_eq_zero_iff` | `Plane.lean` |
| Normal form with {0, ∞} ∈ S | `isMob_iff_elliptic`, `arcLikeP_conj` | `FrameParity.lean`, `Plane.lean` |
| Corollary 4.3, condition (A) | `arc_A` (by a different route: determinants and Ceva's theorem instead of Lemma 4.2) | `Segre.lean` |
| Lemma 5.1, (B) and (C) | `autocorr_B`, `autocorr_SS` | `JacobiArc.lean` |
| Lemma 5.2 | `jacobi_id` | `JacobiArc.lean` |
| Lemma 6.1 | `lemmaL` | `LemmaL.lean` |
| Lemma 7.1 | `nt_diff`, `three_aux` | `VdVPK.lean` |
| Proposition 7.2 | `psi_linear` (q prime), `psi_power` (q = p^k) | `JacobiArc.lean`, `VdVPK.lean` |
| Proposition 7.3 | `powermap_admissible` (q prime: an elementary argument without Weil's bound), `endgame_lin` (q = p^k) | `Bridge.lean`, `VdVPK.lean` |
| Proposition 7.4 | `endgame_frob`, `three_gcd_le`, `final_ineq` | `VdVPK.lean` |
| Theorem 7.5 and the case q ≡ 1 (mod 4) | `vdv_all` | `Unified.lean` |
| The examples for q = 7, 11 are arcs | `arc7`, `arc11`, `arcP7` (checked by the Lean kernel) | `TheoremV.lean`, `Plane.lean` |
| Pruning rule of the search program `supplement/search/bsw_search.c` | `balance_admissible` (`main_balance`) | `Basics.lean` |

Not formalised: Stickelberger's theorem and the derivation of Proposition 6.2 from it,
Proposition 3.2 (sets without tangents = exterior arcs), and part (c) of Theorem A. These are
checked by the Python scripts in `supplement/`.

## Other files

The project grew out of a wider study of the Blokhuis–Seress–Wilbrink conjecture, so it also contains
results that the paper does not use: power maps (`PowerMap*.lean`, `PowerSums.lean`,
`Exponents.lean`, `Identities.lean`, `Theorem.lean`), parity (`Parity.lean`), the sporadic
solutions for q ≤ 31 (`Sporadic.lean`; the paper uses only the two examples for q = 7, 11), and consistency checks showing that the hypotheses of the theorems can be
satisfied (`Sanity.lean`). They are checked by the same script.
