module

public import Mathlib

/-!
# Exact quadratic character sums (fact (W0) of the paper)

* `BSW.CharSums.sum_comp_sq` — `∑ₓ f(x²) = ∑ₜ (χ(t) + 1) f(t)`.
* `BSW.CharSums.sum_sq_sub` — `∑ₓ χ(x² - d) = -1` for `d ≠ 0`.
* `BSW.CharSums.sum_quadratic` — **(W0)**: `∑ₓ χ(ax² + bx + c) = -χ(a)` if `a ≠ 0`, `b² - 4ac ≠ 0`.
* `BSW.CharSums.sum_chord` — for a pair `{a,b}` (`a ≠ b`): `∑_{w ∈ F} χ((w-a)(w-b)) = -1`,
  so `f_P` takes the values `±1` equally often on `PG(1,q) \ P` (with `f_P(∞) = 1`).
-/

@[expose] public section

open Finset

namespace BSW.CharSums

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_comp_sq (hF : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ x : F, f (x ^ 2) = ∑ t : F, (quadraticChar F t + 1) * f t := by
  rw [← Finset.sum_fiberwise univ (fun x : F => x ^ 2) (fun x => f (x ^ 2))]
  apply Finset.sum_congr rfl
  intro t _
  have hcard : ((univ.filter (fun x : F => x ^ 2 = t)).card : ℤ) = quadraticChar F t + 1 := by
    rw [← quadraticChar_card_sqrts hF t]
    congr 2
    ext x; simp
  rw [Finset.sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), sum_const, nsmul_eq_mul,
    hcard]

omit [DecidableEq F] in
theorem sum_shift (g : F → ℤ) (d : F) : ∑ t : F, g (t - d) = ∑ s : F, g s :=
  Fintype.sum_equiv (Equiv.subRight d) _ _ (fun _ => rfl)

theorem sum_chi_ne_one (hF : ringChar F ≠ 2) :
    ∑ u ∈ univ.erase (1 : F), quadraticChar F u = -1 := by
  rw [sum_erase_eq_sub (mem_univ _), quadraticChar_sum_zero hF, map_one]; ring

theorem sum_chi_mul_sub (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ t : F, quadraticChar F (t * (t - d)) = -1 := by
  rw [← sum_erase_add _ _ (mem_univ (0 : F)), zero_mul, MulChar.map_zero, add_zero,
    ← sum_chi_ne_one hF]
  have hterm : ∀ t ∈ univ.erase (0 : F),
      quadraticChar F (t * (t - d)) = quadraticChar F (1 - d / t) := by
    intro t ht
    have ht0 : t ≠ 0 := (mem_erase.mp ht).1
    have e : t * (t - d) = t ^ 2 * (1 - d / t) := by field_simp
    rw [e, map_mul, quadraticChar_sq_one' ht0, one_mul]
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' (fun t => 1 - d / t) (fun u => d / (1 - u)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have ht0 : t ≠ 0 := (mem_erase.mp ht).1
    rw [mem_erase]
    refine ⟨?_, mem_univ _⟩
    intro h
    have : d / t = 0 := by linear_combination -h
    exact div_ne_zero hd ht0 this
  · intro u hu
    have hu1 : u ≠ 1 := (mem_erase.mp hu).1
    rw [mem_erase]
    refine ⟨div_ne_zero hd (sub_ne_zero.mpr (Ne.symm hu1)), mem_univ _⟩
  · intro t ht
    show d / (1 - (1 - d / t)) = t
    rw [sub_sub_cancel, div_div_cancel₀ hd]
  · intro u hu
    have hu1 : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm (mem_erase.mp hu).1)
    field_simp
    ring
  · intro t _; rfl

/-- `∑ₓ χ(x² - d) = -1` for `d ≠ 0`. -/
theorem sum_sq_sub (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ x : F, quadraticChar F (x ^ 2 - d) = -1 := by
  have := sum_comp_sq hF (fun t => quadraticChar F (t - d))
  rw [this]
  have e : ∀ t : F, (quadraticChar F t + 1) * quadraticChar F (t - d)
      = quadraticChar F (t * (t - d)) + quadraticChar F (t - d) := by
    intro t; rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun t _ => e t), sum_add_distrib, sum_chi_mul_sub hF hd,
    sum_shift (fun s => quadraticChar F s) d, quadraticChar_sum_zero hF, add_zero]

/-- **(W0).** If `a ≠ 0` and `b² - 4ac ≠ 0` then `∑ₓ χ(ax² + bx + c) = -χ(a)`. -/
theorem sum_quadratic (hF : ringChar F ≠ 2) {a b c : F} (ha : a ≠ 0) (hD : b ^ 2 - 4 * a * c ≠ 0) :
    ∑ x : F, quadraticChar F (a * x ^ 2 + b * x + c) = -quadraticChar F a := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set d : F := (b ^ 2 - 4 * a * c) / (4 * a ^ 2) with hd
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hd0 : d ≠ 0 := div_ne_zero hD (mul_ne_zero h4 (pow_ne_zero 2 ha))
  have e : ∀ x : F, a * x ^ 2 + b * x + c = a * ((x + b / (2 * a)) ^ 2 - d) := by
    intro x; rw [hd]; field_simp; ring
  rw [Finset.sum_congr rfl (fun x _ => by rw [e x, map_mul])]
  rw [← Finset.mul_sum]
  have hshift : ∑ x : F, quadraticChar F ((x + b / (2 * a)) ^ 2 - d)
      = ∑ y : F, quadraticChar F (y ^ 2 - d) :=
    Fintype.sum_equiv (Equiv.addRight (b / (2 * a))) _ _ (fun _ => rfl)
  rw [hshift, sum_sq_sub hF hd0]; ring

/-- For a pair `{a, b}` (`a ≠ b`): `∑_{w ∈ F} χ((w-a)(w-b)) = -1`. -/
theorem sum_chord (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ w : F, quadraticChar F ((w - a) * (w - b)) = -1 := by
  have e : ∀ w : F, (w - a) * (w - b) = 1 * w ^ 2 + (-(a + b)) * w + a * b := by
    intro w; ring
  rw [Finset.sum_congr rfl (fun w _ => by rw [e w]), sum_quadratic hF one_ne_zero, map_one]
  intro h
  apply hab
  have : (a - b) ^ 2 = 0 := by linear_combination h
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

end BSW.CharSums
