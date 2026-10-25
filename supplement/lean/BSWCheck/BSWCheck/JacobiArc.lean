module

public import Mathlib
public import BSWCheck.Basics
public import BSWCheck.CharSums
public import BSWCheck.Segre

@[expose] public section

/-!
# The analytic part of Theorem 7.5 (Lemma 5.1, Lemma 5.2, Fourier inversion)

Setting: a finite field `F` with `|F| = 2n+1`, `n` odd, `ψ` admissible over `F` and satisfying the conclusion of
`BSW.Segre.arc_A` (hypothesis `hA`).

* `A2`          — condition (A) in the form `χ(ψ y - ψ z) = χ(y z) χ(z - y)`.
* `autocorr_B`  — (B): `χ(x (x - ψ x)) = -1`.
* `autocorr_SS` — (⋆⋆): `χ((x-ψx)(z-ψx)) = -χ((x-ψz)(z-ψz))` for `z ∉ {x, ψ x}`.
* `jacobi_id`   — Lemma 5.2: `(J(χ,η) + J(χ,η'⁻¹)) · M(η',η) = -2 ∑ₓ η'⁻¹(x) η(x)`.
* `StickelHyp`  — Proposition 6.2 (Stickelberger), **taken as a hypothesis**.
* `psi_linear`  — under `StickelHyp`: `ψ x = ψ 1 · x` for every square `x`.
-/

open Finset

namespace BSW.Jacobi

open BSW.Basic BSW.Segre

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- `ψ` extended by `0 ↦ 0` (an involution of the whole field). -/
def psiT (ψ : F → F) (y : F) : F := if y = 0 then 0 else ψ y

theorem psiT_of_ne {ψ : F → F} {y : F} (hy : y ≠ 0) : psiT ψ y = ψ y := by
  unfold psiT; rw [ite_eq_right hy]

theorem psiT_zero (ψ : F → F) : psiT ψ 0 = 0 := by unfold psiT; simp

theorem psiT_invol {ψ : F → F} (h : Admissible ψ) : Function.Involutive (psiT ψ) := by
  intro y
  by_cases hy : y = 0
  · rw [hy, psiT_zero, psiT_zero]
  · rw [psiT_of_ne hy, psiT_of_ne (h.ne_zero y hy), h.invol y hy]

theorem sum_psiT {R : Type*} [AddCommMonoid R] {ψ : F → F} (h : Admissible ψ)
    (f : F → R) : ∑ y, f (psiT ψ y) = ∑ c, f c :=
  Fintype.sum_bijective _ (psiT_invol h).bijective _ _ (fun _ => rfl)

theorem ringChar_ne (hpn : Fintype.card F = 2 * n + 1) : ringChar F ≠ 2 :=
  BSW.FB.ringChar_ne_two hpn

theorem chi_neg_one (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) : quadraticChar F (-1) = -1 :=
  (chi_neg_iff hpn (-1)).2 hodd.neg_one_pow

theorem chi_sub_swap (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (a b : F) :
    quadraticChar F (a - b) = -quadraticChar F (b - a) := by
  rw [show a - b = -1 * (b - a) by ring, map_mul, chi_neg_one hpn hodd]; ring

/-- The conclusion of `BSW.Segre.arc_A`, used as the hypothesis of the analytic part. -/
def CondA (ψ : F → F) : Prop :=
  ∀ y z : F, y ≠ 0 → z ≠ 0 → z ≠ y → z ≠ ψ y →
    quadraticChar F ((ψ y - z) * (ψ z - y)) = -quadraticChar F (ψ y * ψ z)

/-- Condition (A): `χ(ψ y - ψ z) = χ(y z) χ(z - y)` for `y, z` in different pairs. -/
theorem A2 {ψ : F → F} (h : Admissible ψ) (hA : CondA ψ) {y z : F}
    (hy : y ≠ 0) (hz : z ≠ 0) (hzy : z ≠ y) (hzψ : z ≠ ψ y) :
    quadraticChar F (ψ y - ψ z) =
      quadraticChar F (y * z) * quadraticChar F (z - y) := by
  have hz'0 := h.ne_zero z hz
  have h1 : ψ z ≠ y := by intro he; apply hzψ; rw [← he, h.invol z hz]
  have h2 : ψ z ≠ ψ y := fun he => hzy (psi_inj h hz hy he)
  have e := hA y (ψ z) hy hz'0 h1 h2
  rw [h.invol z hz, map_mul, map_mul, h.swap y hy] at e
  have hc := chi_sq_one (sub_ne_zero.mpr hzy)
  rw [map_mul]
  linear_combination quadraticChar F (z - y) * e -
    quadraticChar F (ψ y - ψ z) * hc

/-- **(B)**: `χ(x (x - ψ x)) = -1`. -/
theorem autocorr_B (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) {ψ : F → F} (h : Admissible ψ)
    (hA : CondA ψ) {x : F} (hx : x ≠ 0) :
    quadraticChar F (x * (x - ψ x)) = -1 := by
  have hn : 0 < n := hodd.pos
  have hF := ringChar_ne hpn
  have hψx := h.ne_zero x hx
  -- (W0): `∑_c χ(c (ψx - c)) = 1`
  have hW : ∑ c : F, quadraticChar F (c * (ψ x - c)) = 1 := by
    have e := BSW.CharSums.sum_quadratic hF (a := -1) (b := ψ x) (c := 0) (by norm_num)
      (by rw [mul_zero, sub_zero]; exact pow_ne_zero 2 hψx)
    rw [chi_neg_one hpn hodd, neg_neg] at e
    rw [← e]; apply sum_congr rfl; intro c _; congr 1; ring
  rw [← sum_psiT h] at hW
  -- the generic term
  have hgen : ∑ y : F, quadraticChar F x * quadraticChar F (x - y) = 0 := by
    rw [← mul_sum]
    have : ∑ y : F, quadraticChar F (x - y) = ∑ y : F, quadraticChar F y :=
      Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)
    rw [this, quadraticChar_sum_zero hF, mul_zero]
  set d : F → ℤ := fun y => quadraticChar F (psiT ψ y * (ψ x - psiT ψ y)) -
    quadraticChar F x * quadraticChar F (x - y) with hd
  have hsum : ∑ y, d y = 1 := by rw [hd, sum_sub_distrib, hW, hgen, sub_zero]
  have hvan : ∀ y, y ≠ 0 ∧ y ≠ ψ x → d y = 0 := by
    rintro y ⟨hy0, hyψ⟩
    rw [hd]; simp only
    rw [psiT_of_ne hy0]
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [map_mul, h.swap y hy0, A2 h hA hx hy0 hyx hyψ, map_mul, chi_sub_swap hpn hodd y x]
      have := chi_sq_one hy0
      linear_combination (quadraticChar F x * quadraticChar F (x - y)) * this
  rw [Fintype.sum_eq_add 0 (ψ x) (Ne.symm hψx) hvan] at hsum
  simp only [hd, psiT_zero, zero_mul, MulChar.map_zero, sub_zero, psiT_of_ne hψx,
    h.invol x hx] at hsum
  rw [map_mul, chi_sub_swap hpn hodd (ψ x) x, chi_sq_one hx] at hsum
  rw [map_mul]
  linarith

/-- **(⋆⋆)**: `χ((x-ψx)(z-ψx)) = -χ((x-ψz)(z-ψz))` for `z ∉ {x, ψ x}`. -/
theorem autocorr_SS (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) {ψ : F → F} (h : Admissible ψ)
    (hA : CondA ψ) {x z : F} (hx : x ≠ 0) (hz : z ≠ 0) (hzx : z ≠ x) (hzψ : z ≠ ψ x) :
    quadraticChar F ((x - ψ x) * (z - ψ x)) =
      -quadraticChar F ((x - ψ z) * (z - ψ z)) := by
  have hn : 0 < n := hodd.pos
  have hF := ringChar_ne hpn
  have hψx := h.ne_zero x hx
  have hψz := h.ne_zero z hz
  have hψxz : ψ x ≠ ψ z := fun he => hzx (psi_inj h hz hx he.symm)
  have hxψz : x ≠ ψ z := by intro he; apply hzψ; rw [he, h.invol z hz]
  -- the two chord sums
  have hW : ∑ c : F, quadraticChar F ((c - ψ x) * (c - ψ z)) = -1 :=
    BSW.CharSums.sum_chord hF hψxz
  rw [← sum_psiT h] at hW
  have hgen : ∑ y : F, quadraticChar F (x * z) *
      quadraticChar F ((y - x) * (y - z)) = -quadraticChar F (x * z) := by
    rw [← mul_sum, BSW.CharSums.sum_chord hF (Ne.symm hzx)]; ring
  set d : F → ℤ := fun y => quadraticChar F ((psiT ψ y - ψ x) * (psiT ψ y - ψ z)) -
    quadraticChar F (x * z) * quadraticChar F ((y - x) * (y - z)) with hd
  have hsum : ∑ y, d y = -1 + quadraticChar F (x * z) := by
    rw [hd, sum_sub_distrib, hW, hgen]; ring
  set S3 : Finset F := insert 0 (insert (ψ x) ({ψ z} : Finset F)) with hS3
  have hvan : ∀ y ∈ univ, y ∉ S3 → d y = 0 := by
    intro y _ hyS
    simp only [hS3, mem_insert, mem_singleton, not_or] at hyS
    obtain ⟨hy0, hyψx, hyψz⟩ := hyS
    rw [hd]; simp only
    rw [psiT_of_ne hy0]
    by_cases hyx : y = x
    · subst hyx; simp
    by_cases hyz : y = z
    · subst hyz; simp
    have hxy : x ≠ ψ y := by intro he; apply hyψx; rw [he, h.invol y hy0]
    have hzy : z ≠ ψ y := by intro he; apply hyψz; rw [he, h.invol y hy0]
    rw [map_mul, A2 h hA hy0 hx (Ne.symm hyx) hxy, A2 h hA hy0 hz (Ne.symm hyz) hzy,
      map_mul (quadraticChar F) (y - x) (y - z), chi_sub_swap hpn hodd y x, chi_sub_swap hpn hodd y z, map_mul (quadraticChar F) y x,
      map_mul (quadraticChar F) y z, map_mul (quadraticChar F) x z]
    have := chi_sq_one hy0
    linear_combination (quadraticChar F x * quadraticChar F z *
      quadraticChar F (x - y) * quadraticChar F (z - y)) * this
  rw [← sum_subset (subset_univ S3) hvan] at hsum
  have h0S : (0 : F) ∉ insert (ψ x) ({ψ z} : Finset F) := by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hψx, Ne.symm hψz⟩
  have hxS : ψ x ∉ ({ψ z} : Finset F) := by simpa using hψxz
  rw [hS3, sum_insert h0S, sum_insert hxS, sum_singleton] at hsum
  simp only [hd, psiT_zero, psiT_of_ne hψx, psiT_of_ne hψz, h.invol x hx, h.invol z hz,
    zero_sub] at hsum
  -- the quantity `K = χ((z - ψx)(x - ψz)) = -χ(xz)`
  have hK := hA x z hx hz hzx hzψ
  rw [map_mul (quadraticChar F) (ψ x) (ψ z), h.swap x hx, h.swap z hz,
    show (ψ x - z) * (ψ z - x) = (z - ψ x) * (x - ψ z) by ring] at hK
  have e1 : (-ψ x) * (-ψ z) = ψ x * ψ z := by ring
  have e2 : (-x) * (-z) = x * z := by ring
  have e3 : (ψ x - x) * (ψ x - z) = (x - ψ x) * (z - ψ x) := by ring
  have e4 : (ψ z - x) * (ψ z - z) = (x - ψ z) * (z - ψ z) := by ring
  rw [e1, e2, e3, e4] at hsum
  simp only [map_mul, h.swap x hx, h.swap z hz] at hsum hK ⊢
  set a1 := quadraticChar F (x - ψ x)
  set a2 := quadraticChar F (x - ψ z)
  set b1 := quadraticChar F (z - ψ x)
  set b2 := quadraticChar F (z - ψ z)
  set cx := quadraticChar F x
  set cz := quadraticChar F z
  have ha2 : a2 * a2 = 1 := chi_sq_one (sub_ne_zero.mpr hxψz)
  have hb1 : b1 * b1 = 1 := chi_sq_one (sub_ne_zero.mpr hzψ)
  have hcx : cx * cx = 1 := chi_sq_one hx
  have hcz : cz * cz = 1 := chi_sq_one hz
  have E : a1 * a2 + b1 * b2 = cx * cz * (a1 * b1 + a2 * b2) := by
    linear_combination hsum + cz * cz * hcx + hcz
  have f1 : a1 * a2 = -(cx * cz) * (a1 * b1) := by
    linear_combination a1 * b1 * hK - a1 * a2 * hb1
  have f2 : b1 * b2 = -(cx * cz) * (a2 * b2) := by
    linear_combination a2 * b2 * hK - b1 * b2 * ha2
  have h2c : 2 * (cx * cz * (a1 * b1 + a2 * b2)) = 0 := by
    linear_combination -E + f1 + f2
  have h1c := (mul_eq_zero.mp h2c).resolve_left (by norm_num)
  linear_combination cx * cz * h1c - (a1 * b1 + a2 * b2) * cz * cz * hcx -
    (a1 * b1 + a2 * b2) * hcz


/-- The kernel identity `NC + CN = -2I` entrywise (for `x, z ≠ 0`). -/
theorem kernel (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) {ψ : F → F} (h : Admissible ψ)
    (hA : CondA ψ) {x z : F} (hx : x ≠ 0) (hz : z ≠ 0) :
    quadraticChar F (x - ψ x) * quadraticChar F (ψ x - z) +
      quadraticChar F (x - ψ z) * quadraticChar F (ψ z - z) =
      if x = z then -2 else 0 := by
  split_ifs with hxz
  · subst hxz
    rw [chi_sub_swap hpn hodd (ψ x) x]
    have := chi_sq_one (sub_ne_zero.mpr (Ne.symm (psi_ne_self h hx)))
    linear_combination -2 * this
  · by_cases hzψ : z = ψ x
    · subst hzψ
      rw [h.invol x hx, sub_self, sub_self, MulChar.map_zero]; ring
    · have e := autocorr_SS hpn hodd h hA hx hz (Ne.symm hxz) hzψ
      rw [map_mul, map_mul] at e
      rw [chi_sub_swap hpn hodd (ψ x) z, chi_sub_swap hpn hodd (ψ z) z]
      linear_combination -e

/-- `χ(x - ψ x) χ(ψ x) = 1` (from (B)). -/
theorem chi_B (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) {ψ : F → F} (h : Admissible ψ)
    (hA : CondA ψ) {x : F} (hx : x ≠ 0) :
    quadraticChar F (x - ψ x) * quadraticChar F (ψ x) = 1 := by
  have e := autocorr_B hpn hodd h hA hx
  rw [map_mul] at e
  rw [h.swap x hx]
  linear_combination -e

/-! ## Characters with complex values -/

/-- The quadratic character with values in `ℂ`. -/
noncomputable def chiC : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem chiC_apply (a : F) : chiC a = ((quadraticChar F a : ℤ) : ℂ) := by
  simp [chiC, MulChar.ringHomComp_apply]

/-- The Jacobi sum `J(χ, η) = ∑ₜ χ(1 - t) η(t)`. -/
noncomputable def J (η : MulChar F ℂ) : ℂ := ∑ t, chiC (1 - t) * η t

/-- `M(η', η) = ∑ₓ η'⁻¹(x) η(ψ x)` (`η'⁻¹ = conj η'`). -/
noncomputable def M (ψ : F → F) (η' η : MulChar F ℂ) : ℂ :=
  ∑ x, η'⁻¹ x * η (ψ x)

/-- **Proposition 6.2 (a consequence of Stickelberger's theorem), taken as a hypothesis**:
for `η, η' ∉ {1, χ}`, `J(χ,η) + conj J(χ,η') = 0` only if `η' = χ η`. -/
def StickelHypF (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ η η' : MulChar F ℂ, η ≠ 1 → η ≠ chiC → η' ≠ 1 → η' ≠ chiC →
    J η + star (J η') = 0 → η' = chiC * η

theorem star_J (η : MulChar F ℂ) : star (J η) = J η⁻¹ := by
  unfold J
  rw [star_sum]
  refine sum_congr rfl (fun t _ => ?_)
  rw [star_mul', MulChar.star_apply' η t, chiC_apply]
  simp

theorem chiC_neg_one (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) : chiC (-1 : F) = -1 := by
  rw [chiC_apply, chi_neg_one hpn hodd]; push_cast; ring

theorem chiC_ne_one (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) : (chiC : MulChar F ℂ) ≠ 1 := by
  intro he
  have h1 := chiC_neg_one hpn hodd
  rw [he, MulChar.one_apply (isUnit_one.neg)] at h1
  norm_num at h1

theorem chiC_inv : (chiC : MulChar F ℂ)⁻¹ = chiC := by
  refine MulChar.ext' (fun a => ?_)
  rw [MulChar.inv_apply_eq_inv', chiC_apply]
  by_cases ha : a = 0
  · subst ha; simp
  · rcases quadraticChar_dichotomy ha with h1 | h1 <;> rw [h1] <;> norm_num

theorem inner1 (η : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    ∑ z, chiC (a - z) * η z = chiC a * η a * J η := by
  unfold J
  rw [mul_sum, ← Fintype.sum_equiv (Equiv.mulLeft₀ a ha)
    (fun t => chiC (a - a * t) * η (a * t)) _ (fun t => by simp)]
  refine sum_congr rfl (fun t _ => ?_)
  rw [show a - a * t = a * (1 - t) by ring, map_mul, map_mul]; ring

theorem inner2 (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (η : MulChar F ℂ) {b : F}
    (hb : b ≠ 0) : ∑ x, η x * chiC (x - b) = -(chiC b * η b * J η) := by
  rw [← inner1 η hb, ← sum_neg_distrib]
  refine sum_congr rfl (fun x _ => ?_)
  rw [show x - b = -1 * (b - x) by ring, map_mul, chiC_neg_one hpn hodd]; ring

/-- **Lemma 5.2**: `(J(χ,η) + J(χ,η'⁻¹)) M(η',η) = -2 ∑ₓ η'⁻¹(x) η(x)`. -/
theorem jacobi_id (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) {ψ : F → F} (h : Admissible ψ)
    (hA : CondA ψ) (η' η : MulChar F ℂ) :
    (J η + J η'⁻¹) * M ψ η' η = -2 * ∑ x, η'⁻¹ x * η x := by
  set K : F → F → ℂ := fun x z =>
    chiC (x - ψ x) * chiC (ψ x - z) + chiC (x - ψ z) * chiC (ψ z - z) with hK
  -- first evaluation: the kernel is `-2 I`
  have ev1 : ∑ x, ∑ z, η'⁻¹ x * η z * K x z = -2 * ∑ x, η'⁻¹ x * η x := by
    rw [mul_sum]
    refine sum_congr rfl (fun x _ => ?_)
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero]
    rw [sum_eq_single x]
    · have e := kernel hpn hodd h hA hx hx
      rw [ite_eq_left rfl] at e
      have e' : K x x = -2 := by
        rw [hK]; simp only [chiC_apply]; exact_mod_cast e
      rw [e']; ring
    · intro z _ hzx
      by_cases hz : z = 0
      · subst hz; simp [MulChar.map_zero]
      have e := kernel hpn hodd h hA hx hz
      rw [ite_eq_right (Ne.symm hzx)] at e
      have e' : K x z = 0 := by
        rw [hK]; simp only [chiC_apply]; exact_mod_cast e
      rw [e', mul_zero]
    · intro hx'; exact absurd (mem_univ x) hx'
  -- second evaluation
  have part1 : ∑ x, ∑ z, η'⁻¹ x * η z * (chiC (x - ψ x) * chiC (ψ x - z)) = J η * M ψ η' η := by
    unfold M
    rw [mul_sum]
    refine sum_congr rfl (fun x _ => ?_)
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero]
    have e : ∑ z, η'⁻¹ x * η z * (chiC (x - ψ x) * chiC (ψ x - z))
        = η'⁻¹ x * chiC (x - ψ x) * ∑ z, chiC (ψ x - z) * η z := by
      rw [mul_sum]; refine sum_congr rfl (fun z _ => ?_); ring
    rw [e, inner1 η (h.ne_zero x hx)]
    have hB : chiC (x - ψ x) * chiC (ψ x) = 1 := by
      simp only [chiC_apply]; exact_mod_cast chi_B hpn hodd h hA hx
    linear_combination (η'⁻¹ x * η (ψ x) * J η) * hB
  have part2 : ∑ x, ∑ z, η'⁻¹ x * η z * (chiC (x - ψ z) * chiC (ψ z - z)) =
      J η'⁻¹ * M ψ η' η := by
    rw [sum_comm]
    have e : ∀ z, ∑ x, η'⁻¹ x * η z * (chiC (x - ψ z) * chiC (ψ z - z)) =
        η z * η'⁻¹ (psiT ψ z) * J η'⁻¹ := by
      intro z
      by_cases hz : z = 0
      · subst hz; simp [MulChar.map_zero]
      have e1 : ∑ x, η'⁻¹ x * η z * (chiC (x - ψ z) * chiC (ψ z - z))
          = η z * chiC (ψ z - z) * ∑ x, η'⁻¹ x * chiC (x - ψ z) := by
        rw [mul_sum]; refine sum_congr rfl (fun x _ => ?_); ring
      rw [e1, inner2 hpn hodd η'⁻¹ (h.ne_zero z hz), psiT_of_ne hz]
      have hB : chiC (z - ψ z) * chiC (ψ z) = 1 := by
        simp only [chiC_apply]; exact_mod_cast chi_B hpn hodd h hA hz
      have hs : chiC (ψ z - z) = -chiC (z - ψ z) := by
        rw [show ψ z - z = -1 * (z - ψ z) by ring, map_mul, chiC_neg_one hpn hodd]; ring
      rw [hs]
      linear_combination (η z * η'⁻¹ (ψ z) * J η'⁻¹) * hB
    rw [sum_congr rfl (fun z _ => e z), ← sum_mul, mul_comm]
    congr 1
    unfold M
    rw [← sum_psiT h]
    refine sum_congr rfl (fun x _ => ?_)
    by_cases hx : x = 0
    · subst hx; simp [psiT_zero, MulChar.map_zero]
    rw [psiT_of_ne hx, psiT_of_ne (h.ne_zero x hx), h.invol x hx, mul_comm]
  have ev2 : ∑ x, ∑ z, η'⁻¹ x * η z * K x z = (J η + J η'⁻¹) * M ψ η' η := by
    rw [hK]
    simp only [mul_add, sum_add_distrib]
    rw [part1, part2]; ring
  rw [← ev2, ev1]


theorem chiC_mul_ne (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (η : MulChar F ℂ) :
    chiC * η ≠ η := by
  intro he
  apply chiC_ne_one hpn hodd
  have : chiC * η * η⁻¹ = η * η⁻¹ := by rw [he]
  rwa [mul_assoc, mul_inv_cancel, mul_one] at this

theorem M_one {ψ : F → F} (h : Admissible ψ) {η : MulChar F ℂ} (hη : η ≠ 1) :
    M ψ 1 η = 0 := by
  unfold M
  rw [inv_one]
  have e : ∀ x, (1 : MulChar F ℂ) x * η (ψ x) = η (psiT ψ x) := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [psiT_zero, MulChar.map_zero]
    · rw [MulChar.one_apply (Ne.isUnit hx), one_mul, psiT_of_ne hx]
  rw [sum_congr rfl (fun x _ => e x), sum_psiT h (fun c => η c)]
  exact MulChar.sum_eq_zero_of_ne_one hη

theorem M_chi {ψ : F → F} (h : Admissible ψ)
    {η : MulChar F ℂ} (hη : η ≠ chiC) : M ψ chiC η = 0 := by
  unfold M
  rw [chiC_inv]
  have e : ∀ y, chiC (psiT ψ y) * η (ψ (psiT ψ y)) = -((chiC * η : MulChar F ℂ) y) := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [psiT_zero, MulChar.map_zero]
    · rw [psiT_of_ne hy, h.invol y hy, MulChar.mul_apply, chiC_apply, chiC_apply, h.swap y hy]
      push_cast; ring
  have hne : chiC * η ≠ 1 := by
    intro he; apply hη
    rw [eq_inv_of_mul_eq_one_right he, chiC_inv]
  calc ∑ x, chiC x * η (ψ x) = ∑ y, chiC (psiT ψ y) * η (ψ (psiT ψ y)) :=
        (sum_psiT h (fun x => chiC x * η (ψ x))).symm
    _ = ∑ y, -((chiC * η : MulChar F ℂ) y) := sum_congr rfl (fun y _ => e y)
    _ = 0 := by rw [sum_neg_distrib, MulChar.sum_eq_zero_of_ne_one hne, neg_zero]

/-- Under `StickelHyp`, `M(η', η) = 0` unless `η' ∈ {η, χη}` (`η ∉ {1, χ}`). -/
theorem M_vanish (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) {ψ : F → F} (h : Admissible ψ)
    (hA : CondA ψ) (hst : StickelHypF F) {η η' : MulChar F ℂ} (h1 : η ≠ 1)
    (h2 : η ≠ chiC) (h3 : η' ≠ η) (h4 : η' ≠ chiC * η) : M ψ η' η = 0 := by
  by_cases e1 : η' = 1
  · subst e1; exact M_one h h1
  by_cases e2 : η' = chiC
  · subst e2; exact M_chi h h2
  have hJ : J η + J η'⁻¹ ≠ 0 := by
    intro hz; apply h4; apply hst η η' h1 h2 e1 e2; rw [star_J]; exact hz
  have hid := jacobi_id hpn hodd h hA η' η
  have hs : ∑ x, η'⁻¹ x * η x = 0 := by
    have hne : η'⁻¹ * η ≠ 1 := by
      intro he; apply h3; exact (inv_mul_eq_one.mp he)
    rw [← MulChar.sum_eq_zero_of_ne_one hne]
    exact sum_congr rfl (fun x _ => (MulChar.mul_apply _ _ _).symm)
  rw [hs, mul_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left hJ

noncomputable instance instFintypeMulChar : Fintype (MulChar F ℂ) := Fintype.ofFinite _

theorem sum_chars_eq_zero {c : F} (hc : c ≠ 1) : ∑ η : MulChar F ℂ, η c = 0 := by
  obtain ⟨η0, h0⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity F ℂ hc
  refine eq_zero_of_mul_eq_self_left h0 ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective η0) _ _ fun η ↦ rfl

theorem card_chars : (Fintype.card (MulChar F ℂ) : ℂ) = ((Fintype.card F - 1 : ℕ) : ℂ) := by
  rw [← Nat.card_eq_fintype_card, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity,
    Nat.card_eq_fintype_card, Fintype.card_units]

/-- Orthogonality of the characters of `F^*`. -/
theorem sum_char_inv_mul {a : F} (ha : a ≠ 0) (b : F) :
    ∑ η : MulChar F ℂ, η a⁻¹ * η b = if a = b then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
  simp_rw [← map_mul]
  split_ifs with hab
  · subst hab
    rw [inv_mul_cancel₀ ha]
    simp only [map_one, sum_const, card_univ, nsmul_eq_mul, mul_one]
    exact card_chars
  · apply sum_chars_eq_zero
    intro h; apply hab
    have := congrArg (a * ·) h
    rwa [← mul_assoc, mul_inv_cancel₀ ha, one_mul, mul_one, eq_comm] at this

/-- Fourier inversion over the characters of `F^*`. -/
theorem fourier {ψ : F → F} (η : MulChar F ℂ) {x : F} (hx : x ≠ 0) :
    ∑ η' : MulChar F ℂ, η' x * M ψ η' η = ((Fintype.card F - 1 : ℕ) : ℂ) * η (ψ x) := by
  unfold M
  simp_rw [mul_sum]
  rw [sum_comm]
  have e : ∀ y : F, ∑ η' : MulChar F ℂ, η' x * (η'⁻¹ y * η (ψ y)) =
      (if y = x then ((Fintype.card F - 1 : ℕ) : ℂ) else 0) * η (ψ y) := by
    intro y
    have e1 : ∑ η' : MulChar F ℂ, η' x * (η'⁻¹ y * η (ψ y)) =
        (∑ η' : MulChar F ℂ, η' y⁻¹ * η' x) * η (ψ y) := by
      rw [sum_mul]
      refine sum_congr rfl (fun η' _ => ?_)
      rw [MulChar.inv_apply']; ring
    rw [e1]
    by_cases hy : y = 0
    · subst hy
      rw [ite_eq_right (Ne.symm hx)]
      simp [MulChar.map_zero]
    · rw [sum_char_inv_mul hy x]
  rw [sum_congr rfl (fun y _ => e y), sum_eq_single x]
  · rw [ite_eq_left rfl]
  · intro y _ hyx; rw [ite_eq_right hyx, zero_mul]
  · intro hx'; exact absurd (mem_univ x) hx'

theorem map_ne_zero_of_ne {η : MulChar F ℂ} {u : F} (hu : u ≠ 0) : η u ≠ 0 := by
  intro h0
  have e := map_mul η u u⁻¹
  rw [mul_inv_cancel₀ hu, map_one, h0, zero_mul] at e
  exact one_ne_zero e

/-- **Analytic part of Theorem 7.5.** Under `StickelHyp`, an admissible `ψ` satisfying (A) is linear on
the squares: `ψ x = ψ 1 · x`. -/
theorem psi_linear (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (hst : StickelHypF F)
    {ψ : F → F} (h : Admissible ψ) (hA : CondA ψ) :
    ∀ x : F, x ^ n = 1 → ψ x = ψ 1 * x := by
  intro x hxn
  have hx : x ≠ 0 := pow_ne_zero_of hodd.pos one_ne_zero hxn
  have hchix : quadraticChar F x = 1 := (chi_one_iff hpn x).2 hxn
  have hψ1 := h.ne_zero 1 one_ne_zero
  have hu : ψ 1 * x ≠ 0 := mul_ne_zero hψ1 hx
  have key : ∀ η : MulChar F ℂ, η (ψ x) = η (ψ 1 * x) := by
    intro η
    by_cases e1 : η = 1
    · subst e1
      rw [MulChar.one_apply (Ne.isUnit (h.ne_zero x hx)), MulChar.one_apply (Ne.isUnit hu)]
    by_cases e2 : η = chiC
    · subst e2
      rw [chiC_apply, chiC_apply, map_mul, h.swap x hx, h.swap 1 one_ne_zero, hchix, map_one]
      push_cast; ring
    have hne : η ≠ chiC * η := Ne.symm (chiC_mul_ne hpn hodd η)
    have hF : ∀ y : F, y ≠ 0 → ((Fintype.card F - 1 : ℕ) : ℂ) * η (ψ y) =
        η y * M ψ η η + (chiC * η : MulChar F ℂ) y * M ψ (chiC * η) η := by
      intro y hy
      rw [← fourier η hy, Fintype.sum_eq_add η (chiC * η) hne]
      rintro η' ⟨h3, h4⟩
      rw [M_vanish hpn hodd h hA hst e1 e2 h3 h4, mul_zero]
    have hFx := hF x hx
    have hF1 := hF 1 one_ne_zero
    rw [MulChar.mul_apply, chiC_apply, hchix] at hFx
    rw [MulChar.mul_apply, map_one, chiC_apply, map_one] at hF1
    have hT : ((Fintype.card F - 1 : ℕ) : ℂ) ≠ 0 := by
      have : 1 < Fintype.card F := Fintype.one_lt_card
      exact_mod_cast (show Fintype.card F - 1 ≠ 0 by omega)
    rw [map_mul]
    apply mul_left_cancel₀ hT
    push_cast at hFx hF1
    linear_combination hFx - η x * hF1
  by_contra hne
  set a := ψ x / (ψ 1 * x) with ha_def
  have e : a * (ψ 1 * x) = ψ x := div_mul_cancel₀ _ hu
  have ha : a ≠ 1 := by
    intro h1; apply hne; rw [← e, h1, one_mul]
  obtain ⟨η, hη⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity F ℂ ha
  apply hη
  have h1 := key η
  rw [← e, map_mul] at h1
  have hw := map_ne_zero_of_ne (η := η) hu
  apply mul_right_cancel₀ hw
  rw [one_mul]
  exact h1

/-- `StickelHyp p` = `StickelHypF (ZMod p)` (Proposition 6.2 for the prime field). -/
abbrev StickelHyp (p : ℕ) [Fact p.Prime] : Prop := StickelHypF (ZMod p)

end BSW.Jacobi
