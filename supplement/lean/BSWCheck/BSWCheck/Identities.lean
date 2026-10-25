module

/-
  Algebraic identities behind the power-map theorem.
  All statements are over an arbitrary field; `T z = z + z⁻¹`.
-/
public import Mathlib

@[expose] public section

namespace BSW

variable {F : Type*} [Field F]

/-- `T z = z + 1/z`. -/
def T (z : F) : F := z + z⁻¹

/-- Compatibility of power maps. For `ψ x = c x^e` (`e ≥ 1`), `x' = x u` and `w = c x^(e-1)`:
`(x-x')(ψx-ψx')(x-ψx')(x'-ψx) = c x^(e+3) (1-u)(1-u^e)(1-w u^e)(u-w)`. -/
theorem powercomp (c x u : F) (e : ℕ) (he : 1 ≤ e) :
    let w := c * x ^ (e - 1)
    (x - x * u) * (c * x ^ e - c * (x * u) ^ e) * (x - c * (x * u) ^ e) * (x * u - c * x ^ e)
      = c * x ^ (e + 3) * ((1 - u) * (1 - u ^ e) * (1 - w * u ^ e) * (u - w)) := by
  intro w
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  simp only [w, Nat.add_sub_cancel]
  ring

/-- Same identity in the normalisation used in the Lean proof of the main theorem:
`y = x U`, `ψ x = w x`, `ψ y = w x V`. -/
theorem compat_factor (x w U V : F) :
    (x - x * U) * (w * x - w * x * V) * (x - w * x * V) * (w * x - x * U)
      = w * x ^ 4 * ((1 - U) * (1 - V) * (1 - w * V) * (w - U)) := by
  ring

/-- `(1 - wV)(w - U) = -U (wV - 1)(w/U - 1)` (for `U ≠ 0`). -/
theorem factor_h (w U V : F) (hU : U ≠ 0) :
    (1 - w * V) * (w - U) = -U * ((w * V - 1) * (w / U - 1)) := by
  field_simp
  ring

/-- T-form, first factor: if `u = s/t`, `u^e = s t` then `(1-u)(1-u^e) = s (T s - T t)`. -/
theorem Tform_first (s t : F) (hs : s ≠ 0) (ht : t ≠ 0) :
    (1 - s / t) * (1 - s * t) = s * (T s - T t) := by
  unfold T
  field_simp
  ring

/-- T-form, second factor: `(1 - w u^e)(u - w) = s w (T(w t) - T s)`. -/
theorem Tform_second (s t w : F) (hs : s ≠ 0) (ht : t ≠ 0) (hw : w ≠ 0) :
    (1 - w * (s * t)) * (s / t - w) = s * w * (T (w * t) - T s) := by
  unfold T
  field_simp
  ring

/-- T-form, last formula: `T a - T b = (ab-1)(a-b)/(ab)`. -/
theorem T_sub (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    T a - T b = (a * b - 1) * (a - b) / (a * b) := by
  unfold T
  field_simp
  ring

/-- Used for `κ = 1` on `μ_f`: `T s - 2 = (s-1)^2/s`. -/
theorem T_sub_two (s : F) (hs : s ≠ 0) : T s - 2 = (s - 1) ^ 2 / s := by
  unfold T
  field_simp
  ring

/-- Power-map theorem, case `ρ = -1`: `(1 - ρu)(u - ρ) = (1+u)^2`. -/
theorem circle_neg_one (u : F) : (1 - (-1) * u) * (u - (-1)) = (1 + u) ^ 2 := by
  ring

/-- Sign rule of the T-form: for a multiplicative `χ` with `χ(-1) = -1`, `χ w = -1`, `χ s = 1`:
`χ(T w - T s) = -h(ws) h(w/s)` where `h z = χ(z-1)`. -/
theorem Tform_sign {R : Type*} [Field R] (χ : F →*₀ R)
    (w s : F) (hw : w ≠ 0) (hs : s ≠ 0) (hχw : χ w = -1) (hχs : χ s = 1) :
    χ (T w - T s) = -(χ (w * s - 1) * χ (w / s - 1)) := by
  have key : T w - T s = (w * s - 1) * (w / s - 1) * s * (w * s)⁻¹ := by
    unfold T
    field_simp
    ring
  have hinv : χ (w * s)⁻¹ = -1 := by
    rw [map_inv₀, map_mul, hχw, hχs]
    norm_num
  rw [key, map_mul, map_mul, map_mul, hinv, hχs]
  ring

end BSW
