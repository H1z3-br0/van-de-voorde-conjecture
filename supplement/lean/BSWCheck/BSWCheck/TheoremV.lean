module

public import Mathlib
public import BSWCheck.Segre
public import BSWCheck.JacobiArc
public import BSWCheck.Bridge
public import BSWCheck.Sporadic

@[expose] public section

/-!
# Theorem 7.5 (Van de Voorde's conjecture for prime `q ≡ 3 mod 4`), with Stickelberger as hypothesis

`BSW.TheoremV.theoremV`: let `p ≡ 3 (mod 4)` be a prime, `p ∉ {3, 7, 11}`.  Assuming `StickelHyp p`
(Proposition 6.2 of the paper, a consequence of Stickelberger's theorem on Gauss sums, which is not in
Mathlib), **no solution is arc-like**: every solution (admissible `ψ`, frame `P₀ = {0, ∞}`) contains
three collinear points.

Chain of the proof (all formal):
* `BSW.Segre.arc_A` — Segre–Paley identity + Ceva ⇒ condition (A);
* `BSW.Jacobi.psi_linear` — (B), (⋆⋆), the Jacobi-sum identity, `StickelHyp` and Fourier inversion
  ⇒ `ψ(x) = c·x` on the squares;
* `BSW.Bridge.powermap_admissible` (the power-map theorem, no Weil bound) ⇒ `ψ(x) = c/x`;
  both together are impossible (evaluate at `x = 4`).

`arc7`, `arc11` show that the hypothesis `ArcLike` is satisfiable (the multiplicative starters at
`q = 7, 11`), so the exceptions `p = 7, 11` are genuine.
-/

namespace BSW.TheoremV

open BSW.Basic BSW.Segre BSW.Jacobi

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Theorem 7.5** (prime case of Van de Voorde's conjecture), modulo `StickelHyp`. -/
theorem theoremV (hp4 : p % 4 = 3) (hp3 : p ≠ 3) (hp7 : p ≠ 7) (hp11 : p ≠ 11)
    (hst : StickelHyp p) {ψ : ZMod p → ZMod p} (h : Admissible ψ) : ¬ ArcLike ψ := by
  intro harc
  set n := p / 2 with hn
  have hpn : p = 2 * n + 1 := by omega
  have hodd : Odd n := ⟨p / 4, by omega⟩
  have hp2 := hp.out.two_le
  have hn3 : 3 ≤ n := by omega
  have hcard : Fintype.card (ZMod p) = 2 * n + 1 := by rw [ZMod.card]; exact hpn
  have hA : CondA ψ := fun y z hy hz hzy hzψ => arc_A hcard hodd hn3 h harc hy hz hzy hzψ
  have hlin := psi_linear hcard hodd hst h hA
  have hell := BSW.Bridge.powermap_admissible hp4 hp7 hp11 h (ψ 1) 1
    (fun x hx => by rw [pow_one]; exact hlin x (by rwa [show (p - 1) / 2 = n by omega] at hx))
  have h2 : (2 : ZMod p) ≠ 0 := BSW.Bridge.two_ne_zero_zmod (by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h4sq : (4 : ZMod p) ^ n = 1 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * n = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one h2
  have e1 := hlin 4 h4sq
  have e2 := hell 4 h4
  have hψ1 := h.ne_zero 1 one_ne_zero
  rw [e1] at e2
  have h15 : (15 : ZMod p) = 0 := by
    have e3 : ψ 1 * 15 = 0 := by
      rw [div_eq_mul_inv] at e2
      have h44 : (4 : ZMod p) * 4⁻¹ = 1 := mul_inv_cancel₀ h4
      linear_combination 4 * e2 + ψ 1 * h44
    exact (mul_eq_zero.mp e3).resolve_left hψ1
  have hdvd : p ∣ 3 * 5 := by
    have : ((15 : ℕ) : ZMod p) = 0 := by exact_mod_cast h15
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with h3 | h5
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h3)
  · have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_five).mp h5
    omega

/-- Equivalently: every solution contains three collinear points (`P₀` and two pairs, or three
pairs). -/
theorem three_collinear (hp4 : p % 4 = 3) (hp3 : p ≠ 3) (hp7 : p ≠ 7) (hp11 : p ≠ 11)
    (hst : StickelHyp p) {ψ : ZMod p → ZMod p} (h : Admissible ψ) :
    (∃ x y : ZMod p, x ≠ 0 ∧ y ≠ 0 ∧ y ≠ x ∧ y ≠ ψ x ∧
        det3 p0 (pf x (ψ x)) (pf y (ψ y)) = 0) ∨
      (∃ x y z : ZMod p, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ y ≠ x ∧ y ≠ ψ x ∧ z ≠ x ∧ z ≠ ψ x ∧ z ≠ y ∧
        z ≠ ψ y ∧ det3 (pf x (ψ x)) (pf y (ψ y)) (pf z (ψ z)) = 0) := by
  by_contra hc
  apply theoremV hp4 hp3 hp7 hp11 hst h
  exact ⟨fun x y hx hy h1 h2 hd => hc (Or.inl ⟨x, y, hx, hy, h1, h2, hd⟩),
    fun x y z hx hy hz h1 h2 h3 h4 h5 h6 hd =>
      hc (Or.inr ⟨x, y, z, hx, hy, hz, h1, h2, h3, h4, h5, h6, hd⟩)⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 10000 in
/-- Non-vacuity: at `q = 7` the multiplicative starter `ψ(x) = 3x` (on squares) is an admissible
arc-like solution (kernel check). -/
theorem arc7 : Admissible BSW.Sporadic.psi7 ∧ ArcLike BSW.Sporadic.psi7 := by
  refine ⟨BSW.Sporadic.sporadic_7.1, ?_⟩
  unfold ArcLike
  decide +kernel

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 10000 in
/-- The same at `q = 11` for the starter `ψ(x) = 2x` (on squares). -/
theorem arc11 : Admissible BSW.Sporadic.psi11 ∧ ArcLike BSW.Sporadic.psi11 := by
  refine ⟨BSW.Sporadic.sporadic_11.1, ?_⟩
  unfold ArcLike
  decide +kernel

end BSW.TheoremV
