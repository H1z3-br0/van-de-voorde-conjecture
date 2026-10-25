module

public import Mathlib
public import BSWCheck.Basics
public import BSWCheck.Theorem

@[expose] public section

/-!
# Bridge: the paper's definitions (quadratic character) ↔ the power form used in `PowerMap*`

* `BSW.Bridge.chi_eq_neg_one_iff`, `chi_eq_one_iff` — Euler's criterion in `ZMod p`.
* `BSW.Bridge.compat_iff` — `Basic.Compat` (via `quadraticChar`) ↔ `BSW.Compat` (power form).
* `BSW.Bridge.powermap_admissible` — **the power-map theorem for prime `q`, stated for admissible maps**:
  if an admissible `ψ` is a power map `ψ(x) = c·x^e` on squares (`p ≡ 3 mod 4` prime, `p ≠ 7, 11`),
  then `ψ(x) = c/x` for every `x ≠ 0` (elliptic solution).
-/

namespace BSW.Bridge

open BSW.Basic

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hle := Nat.le_of_dvd (by norm_num) h'
  have hge := hp.out.two_le
  omega

theorem neg_one_ne_one_zmod (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  apply two_ne_zero_zmod hp2
  linear_combination -h

theorem key_pow (hp2 : p ≠ 2) (a : ZMod p) :
    ((quadraticChar (ZMod p) a : ℤ) : ZMod p) = a ^ (p / 2) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have key := quadraticChar_eq_pow_of_char_ne_two' hchar a
  rwa [ZMod.card] at key

/-- Euler's criterion: `χ(a) = -1 ↔ a^((p-1)/2) = -1` (here `p/2 = (p-1)/2`). -/
theorem chi_eq_neg_one_iff (hp2 : p ≠ 2) (a : ZMod p) :
    quadraticChar (ZMod p) a = -1 ↔ a ^ (p / 2) = -1 := by
  have key := key_pow hp2 a
  constructor
  · intro h; rw [h] at key; push_cast at key; exact key.symm
  · intro h
    by_cases ha : a = 0
    · exfalso
      rw [ha, zero_pow] at h
      · exact (neg_ne_zero.mpr one_ne_zero) h.symm
      · have := hp.out.two_le; omega
    · rcases quadraticChar_dichotomy ha with h1 | h1
      · exfalso
        rw [h1, h] at key
        push_cast at key
        exact neg_one_ne_one_zmod hp2 key.symm
      · exact h1

/-- Euler's criterion: `χ(a) = 1 ↔ a^((p-1)/2) = 1`. -/
theorem chi_eq_one_iff (hp2 : p ≠ 2) (a : ZMod p) :
    quadraticChar (ZMod p) a = 1 ↔ a ^ (p / 2) = 1 := by
  have key := key_pow hp2 a
  constructor
  · intro h; rw [h] at key; push_cast at key; exact key.symm
  · intro h
    by_cases ha : a = 0
    · exfalso
      rw [ha, zero_pow] at h
      · exact zero_ne_one h
      · have := hp.out.two_le; omega
    · rcases quadraticChar_dichotomy ha with h1 | h1
      · exact h1
      · exfalso
        rw [h1, h] at key
        push_cast at key
        exact neg_one_ne_one_zmod hp2 key

/-- The two definitions of compatibility agree. -/
theorem compat_iff (hp2 : p ≠ 2) (a b c d : ZMod p) :
    Basic.Compat a b c d ↔ BSW.Compat (p / 2) a b c d := by
  unfold Basic.Compat BSW.Compat
  rw [chi_eq_neg_one_iff hp2]
  have : (a - c) * (a - d) * (b - c) * (b - d) = (a - c) * (b - d) * (a - d) * (b - c) := by ring
  rw [this]

theorem sq_or_nonsq (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    x ^ (p / 2) = 1 ∨ x ^ (p / 2) = -1 := by
  rcases quadraticChar_dichotomy hx with h | h
  · exact Or.inl ((chi_eq_one_iff hp2 x).1 h)
  · exact Or.inr ((chi_eq_neg_one_iff hp2 x).1 h)

/-- **Power-map theorem for prime `q`, stated for admissible maps.**  Let `p ≡ 3 (mod 4)` be a prime,
`p ≠ 7, 11`, and let `ψ` be admissible.  If `ψ(x) = c·x^e` for all squares `x`, then `ψ(x) = c/x` for
all `x ≠ 0`: the solution is elliptic. -/
theorem powermap_admissible (hp4 : p % 4 = 3) (hp7 : p ≠ 7) (hp11 : p ≠ 11) {ψ : ZMod p → ZMod p}
    (h : Admissible ψ) (c : ZMod p) (e : ℕ)
    (hpow : ∀ x : ZMod p, x ^ ((p - 1) / 2) = 1 → ψ x = c * x ^ e) :
    ∀ x : ZMod p, x ≠ 0 → ψ x = c / x := by
  have hp2 : p ≠ 2 := by omega
  have hn : (p - 1) / 2 = p / 2 := by omega
  rw [hn] at hpow
  -- `c = ψ 1` is a nonsquare
  have hc1 : ψ 1 = c := by rw [hpow 1 (one_pow _), one_pow, mul_one]
  have hcχ : quadraticChar (ZMod p) c = -1 := by
    have := h.swap 1 one_ne_zero
    rw [hc1, map_one] at this; exact this
  have hc : c ^ ((p - 1) / 2) = -1 := by rw [hn]; exact (chi_eq_neg_one_iff hp2 c).1 hcχ
  -- the hypothesis of `powermap_elliptic`
  have hsol : ∀ x y : ZMod p, x ^ ((p - 1) / 2) = 1 → y ^ ((p - 1) / 2) = 1 → x ≠ y →
      BSW.Compat ((p - 1) / 2) x (c * x ^ e) y (c * y ^ e) := by
    intro x y hx hy hxy
    rw [hn] at hx hy ⊢
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, zero_pow (by have := hp.out.two_le; omega)] at hx; exact zero_ne_one hx
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0, zero_pow (by have := hp.out.two_le; omega)] at hy; exact zero_ne_one hy
    have hyψ : y ≠ ψ x := by
      intro he
      have h1 := h.swap x hx0
      rw [← he, (chi_eq_one_iff hp2 y).2 hy, (chi_eq_one_iff hp2 x).2 hx] at h1
      norm_num at h1
    have hcr := h.cross x y hx0 hy0 (Ne.symm hxy) hyψ
    rw [compat_iff hp2, hpow x hx, hpow y hy] at hcr
    exact hcr
  have hdiv := BSW.powermap_elliptic hp4 hp7 hp11 c hc e hsol
  rw [hn] at hdiv
  -- on squares: `x^e = x⁻¹`
  have hsq : ∀ x : ZMod p, x ^ (p / 2) = 1 → ψ x = c / x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, zero_pow (by have := hp.out.two_le; omega)] at hx; exact zero_ne_one hx
    obtain ⟨k, hk⟩ := hdiv
    have hxe : x ^ e * x = 1 := by
      rw [← pow_succ, hk, pow_mul, hx, one_pow]
    rw [hpow x hx, div_eq_mul_inv]
    congr 1
    exact (eq_inv_of_mul_eq_one_left hxe)
  intro x hx0
  rcases sq_or_nonsq hp2 hx0 with hx | hx
  · exact hsq x hx
  · -- `y = ψ x` is a square, and `ψ y = x`
    have hy0 := h.ne_zero x hx0
    have hysq : (ψ x) ^ (p / 2) = 1 := by
      apply (chi_eq_one_iff hp2 _).1
      rw [h.swap x hx0, (chi_eq_neg_one_iff hp2 x).2 hx, neg_neg]
    have h1 := hsq (ψ x) hysq
    rw [h.invol x hx0] at h1
    -- `x = c / ψ x` ⇒ `ψ x = c / x`
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, MulChar.map_zero] at hcχ; norm_num at hcχ
    field_simp at h1 ⊢
    linear_combination h1

end BSW.Bridge
