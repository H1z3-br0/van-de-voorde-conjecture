module

public import Mathlib
public import BSWCheck.Unified
public import BSWCheck.Sporadic

@[expose] public section

/-!
# Main theorems of the BSWCheck project (the statements a reader should check)

Every theorem below restates, with its full hypotheses, a result proved elsewhere in the project; the
proof term is just a reference, so Lean checks that the statement here is exactly what was proved.

## Conventions
* `F` — a finite field; `χ = quadraticChar F`; `PG(1,q) = Option F` (`none = ∞`).
* `BSW.Basic.Admissible ψ` — a solution in the frame `P₀ = {0, ∞}` (conditions (H1)–(H3) of the paper).
* `BSW.Proj.Solution Ψ` — a solution on `PG(1,q)`: a fixed-point-free involution with pairwise
  compatible pairs (`CompatP`), i.e. `(q+1)/2` external points of the conic pairwise joined by passants
  (`main_dictionary`).
* `BSW.Plane.ArcLikeP Ψ` — no three of these points are collinear.

## Classical theorems taken as hypotheses (not in Mathlib)
* `BSW.Jacobi.StickelHyp p` — Proposition 6.2 (Stickelberger), prime field;
* `BSW.VdVPK.StickelPKHyp F p k` — Proposition 6.2 (Stickelberger + Lemma 6.1), `q = p^k`;
* `BSW.BSW1.CarlitzHyp p`, `BSW.VdVPK.McConnelHyp F p k` — Carlitz / McConnel;
* `BSW.VdVPK.WeilHyp F` — Weil's bound for squarefree polynomials.
They appear only as explicit hypotheses; the project has no axioms beyond `propext`,
`Classical.choice`, `Quot.sound` (`scripts/check.sh`).
-/

namespace BSW.Main

open BSW.Basic BSW.Segre BSW.Proj BSW.Plane BSW.BSW1 BSW.VdVPK

/-! ## 1. The geometric dictionary (any finite field of odd characteristic) -/

/-- Three points (binary quadratic forms) are collinear iff their determinant vanishes. -/
theorem main_collinear {F : Type*} [Field F] [Fintype F] [DecidableEq F] (u v w : V3 F) :
    det3 u v w = 0 ↔ ∃ a b c : F, ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧
      a * u.a + b * v.a + c * w.a = 0 ∧ a * u.b + b * v.b + c * w.b = 0 ∧
      a * u.c + b * v.c + c * w.c = 0 :=
  det3_eq_zero_iff u v w

/-- External points of the conic are exactly the pairs `{A, B}` of points of `PG(1,q)`. -/
theorem main_external {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (u : V3 F) :
    (∃ d : F, d ≠ 0 ∧ disc u = d ^ 2) ↔
      ∃ A B : Option F, A ≠ B ∧ ∃ k : F, k ≠ 0 ∧ u = smul3 k (pformP A B) :=
  external_iff hF u

/-- **The dictionary**: two pairs are compatible (H3) iff the line through the two external points
is a passant. -/
theorem main_dictionary {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (A B C D : Option F) : CompatP A B C D ↔ Passant (pformP A B) (pformP C D) :=
  compat_iff_passant hF A B C D

/-! ## 2. Structure of solutions -/

/-- **Frame independence**: in the frame `P₀`, a solution is a Möbius involution iff it
is elliptic, `ψ(x) = n/x`. -/
theorem main_frame {F : Type*} [Field F] [Fintype F] [DecidableEq F] {Ψ : Option F → Option F}
    (h : Solution Ψ) (h0 : Ψ (some 0) = none) :
    IsMob Ψ ↔ ∃ n : F, ∀ x : F, x ≠ 0 → toPsi Ψ x = n / x :=
  isMob_iff_elliptic h h0

/-- **Balance lemma** — the pruning rule of the computer search. -/
theorem main_balance {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ψ : F → F}
    (h : Admissible ψ) (xs : Finset F) (hxs : ∀ x ∈ xs, x ≠ 0) (ε : Option xs → ℤ) :
    ((Uncovered ψ xs).filter (fun w => signature ψ xs w = ε)).card
      = ((Uncovered ψ xs).filter (fun w => signature ψ xs w = -ε)).card :=
  balance_admissible h xs hxs ε

/-- **Power-map theorem for prime `q`**: an admissible power map on the squares is elliptic
(no hypotheses beyond `p ≡ 3 mod 4`, `p ≠ 7, 11`). -/
theorem main_powermap {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (hp7 : p ≠ 7) (hp11 : p ≠ 11)
    {ψ : ZMod p → ZMod p} (h : Admissible ψ) (c : ZMod p) (e : ℕ)
    (hpow : ∀ x : ZMod p, x ^ ((p - 1) / 2) = 1 → ψ x = c * x ^ e) :
    ∀ x : ZMod p, x ≠ 0 → ψ x = c / x :=
  BSW.Bridge.powermap_admissible hp4 hp7 hp11 h c e hpow

/-- **Blokhuis–Seress–Wilbrink theorem for `q ≡ 1 (mod 4)`** (any `q = p^k`), modulo McConnel's theorem: every solution in
the frame `P₀` is elliptic. -/
theorem main_bsw1 {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n p k : ℕ} [Fact p.Prime]
    (hq : Fintype.card F = p ^ k) (hpn : Fintype.card F = 2 * n + 1) (heven : Even n) (hn : 0 < n)
    (hmc : McConnelHyp F p k) {Ψ : Option F → Option F} (hS : Solution Ψ)
    (h0 : Ψ (some 0) = none) : ∀ x : F, x ≠ 0 → toPsi Ψ x = toPsi Ψ 1 / x :=
  bsw1_pk_frame hq hpn heven hn hmc hS h0

/-! ## 3. Van de Voorde's conjecture -/

/-- **Theorem 7.5** (prime `q`), modulo Proposition 6.2. -/
theorem main_theoremV {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    (hp11 : p ≠ 11) (hst : BSW.Jacobi.StickelHyp p) {Ψ : Option (ZMod p) → Option (ZMod p)}
    (hS : Solution Ψ) : ¬ ArcLikeP Ψ :=
  theoremV_proj hp4 hp3 hp7 hp11 hst hS

/-- **Van de Voorde's conjecture for every finite field of odd order `q ∉ {3, 7, 11}`**: no solution
is arc-like — every complete exterior set of `(q+1)/2` points contains three collinear points. -/
theorem main_vdv {F : Type*} [Field F] [Fintype F] [DecidableEq F] {p k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hq : Fintype.card F = p ^ k) (hk : 1 ≤ k) (h3 : Fintype.card F ≠ 3)
    (h7 : Fintype.card F ≠ 7) (h11 : Fintype.card F ≠ 11)
    (hmc : Fintype.card F % 4 = 1 → McConnelHyp F p k)
    (hst1 : Fintype.card F % 4 = 3 → k = 1 → BSW.Jacobi.StickelHyp p)
    (hst : Fintype.card F % 4 = 3 → 3 ≤ k → StickelPKHyp F p k ∧ WeilHyp F)
    {Ψ : Option F → Option F} (hS : Solution Ψ) : ¬ ArcLikeP Ψ :=
  BSW.Unified.vdv_all hp2 hq hk h3 h7 h11 hmc hst1 hst hS

/-- The exceptions are genuine: at `q = 7` there is an arc-like solution (kernel check). -/
theorem main_exception7 :
    Solution (ofPsi BSW.Sporadic.psi7) ∧ ArcLikeP (ofPsi BSW.Sporadic.psi7) := arcP7

/-- **Lemma 6.1**, proved without hypotheses. -/
theorem main_lemmaL {h : ℕ} [NeZero h] (hh : Odd h) (hh1 : 1 < h) {p k : ℕ} (hp3 : 3 ≤ p)
    (hk : Odd k) (hpk : p ^ k = 2 * h + 1) (β : ZMod h) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hc : ∀ τ : ZMod h, IsUnit τ → BSW.LemmaL.Pi p k (τ * β) = ε * BSW.LemmaL.Pi p k τ) :
    ∃ j, j < k ∧ β = (ε : ZMod h) * (p : ZMod h) ^ j :=
  BSW.LemmaL.lemmaL hh hh1 hp3 hk hpk β ε hε hc

end BSW.Main
