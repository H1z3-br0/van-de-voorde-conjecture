module

/-
  Exponent model of `𝔽_p^*` for `p = 2n+1`: squares are `E i = ρ^i` and nonsquares are `c·E i`,
  `i ∈ ZMod n`, where `ρ` is a primitive `n`-th root of unity and `c` a fixed nonsquare.
-/
public import Mathlib
public import BSWCheck.PowerSums

@[expose] public section

open Finset

namespace BSW

variable {p n : ℕ} [hp : Fact p.Prime] [NeZero n]

/-- `E i = ρ^i` for `i ∈ ZMod n`. -/
def E (ρ : ZMod p) (i : ZMod n) : ZMod p := ρ ^ i.val

section
variable {ρ : ZMod p} (hρ : IsPrimitiveRoot ρ n)
include hρ

omit [NeZero n] in
theorem pow_mod_n (k : ℕ) : ρ ^ (k % n) = ρ ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, hρ.pow_eq_one, one_pow, mul_one]

omit [NeZero n] in
theorem E_natCast (k : ℕ) : E ρ (k : ZMod n) = ρ ^ k := by
  rw [E, ZMod.val_natCast, pow_mod_n hρ]

omit [NeZero n] hρ in
theorem E_eq_pow_val (i : ZMod n) : E ρ i = ρ ^ i.val := rfl

theorem E_add (i j : ZMod n) : E ρ (i + j) = E ρ i * E ρ j := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, ← Nat.cast_add]
  rw [E_natCast hρ, pow_add, E, E]

omit [NeZero n] hρ in
theorem E_zero : E ρ (0 : ZMod n) = 1 := by
  rw [E, ZMod.val_zero, pow_zero]

theorem E_mul_E_neg (i : ZMod n) : E ρ i * E ρ (-i) = 1 := by
  rw [← E_add hρ, add_neg_cancel, E_zero]

theorem E_pow (i : ZMod n) (m : ℕ) : E ρ i ^ m = E ρ (i * (m : ZMod n)) := by
  conv_rhs => rw [← ZMod.natCast_zmod_val i, ← Nat.cast_mul]
  rw [E_natCast hρ, E, pow_mul]

omit [NeZero n] in
theorem E_pow_n (i : ZMod n) : E ρ i ^ n = 1 := by
  rw [E, ← pow_mul, mul_comm, pow_mul, hρ.pow_eq_one, one_pow]

theorem E_ne_zero (i : ZMod n) : E ρ i ≠ 0 := by
  intro h
  have := E_pow_n hρ i
  rw [h, zero_pow (NeZero.ne n)] at this
  exact zero_ne_one this

theorem E_inj {i j : ZMod n} (h : E ρ i = E ρ j) : i = j :=
  ZMod.val_injective n (hρ.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) h)

theorem E_eq_one_iff (i : ZMod n) : E ρ i = 1 ↔ i = 0 := by
  constructor
  · intro h
    exact E_inj hρ (h.trans (E_zero).symm)
  · rintro rfl
    exact E_zero

/-- Every `x` with `x^n = 1` is some `E i`. -/
theorem exists_E {x : ZMod p} (hx : x ^ n = 1) : ∃ i : ZMod n, E ρ i = x := by
  obtain ⟨k, -, hk⟩ := hρ.eq_pow_of_pow_eq_one hx
  exact ⟨k, by rw [E_natCast hρ, hk]⟩

/-- Sum over squares. -/
theorem sum_sq {R : Type*} [AddCommMonoid R] (F : ZMod p → R) :
    ∑ z ∈ univ.filter (fun z : ZMod p => z ^ n = 1), F z = ∑ i : ZMod n, F (E ρ i) := by
  symm
  refine Finset.sum_bij (fun i _ => E ρ i) ?_ ?_ ?_ ?_
  · intro i _
    simp [E_pow_n hρ]
  · intro i _ j _ h
    exact E_inj hρ h
  · intro z hz
    obtain ⟨i, hi⟩ := exists_E hρ (Finset.mem_filter.mp hz).2
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i _
    rfl

/-- Sum over nonsquares. -/
theorem sum_nonsq {R : Type*} [AddCommMonoid R] {c : ZMod p} (hc : c ^ n = -1) (F : ZMod p → R) :
    ∑ z ∈ univ.filter (fun z : ZMod p => z ^ n = -1), F z = ∑ i : ZMod n, F (c * E ρ i) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hc
    have : (1 : ZMod p) = 0 := by linear_combination hc
    exact one_ne_zero this
  symm
  refine Finset.sum_bij (fun i _ => c * E ρ i) ?_ ?_ ?_ ?_
  · intro i _
    simp [mul_pow, E_pow_n hρ, hc]
  · intro i _ j _ h
    exact E_inj hρ (mul_left_cancel₀ hc0 h)
  · intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    have : (z / c) ^ n = 1 := by
      rw [div_pow, hz', hc]
      exact div_self (by
        intro h
        have : (1 : ZMod p) = 0 := by linear_combination -h
        exact one_ne_zero this)
    obtain ⟨i, hi⟩ := exists_E hρ this
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hi]
    field_simp
  · intro i _
    rfl

end

/-- `𝔽_p^* = squares ⊔ nonsquares`. -/
theorem sum_erase_zero_split (hpn : p = 2 * n + 1) {R : Type*} [AddCommMonoid R] (F : ZMod p → R) :
    ∑ z ∈ univ.erase (0 : ZMod p), F z
      = ∑ z ∈ univ.filter (fun z : ZMod p => z ^ n = 1), F z
        + ∑ z ∈ univ.filter (fun z : ZMod p => z ^ n = -1), F z := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero' hpn hn
  rw [← Finset.sum_filter_add_sum_filter_not (univ.erase (0 : ZMod p)) (fun z => z ^ n = 1)]
  congr 1
  · congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rw [zero_pow hn.ne'] at h
      exact zero_ne_one h
  · congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨hz, h⟩
      rcases pow_half_eq hpn hz with h' | h'
      · exact absurd h' h
      · exact h'
    · intro h
      refine ⟨?_, ?_⟩
      · rintro rfl
        rw [zero_pow hn.ne'] at h
        have : (1 : ZMod p) = 0 := by linear_combination h
        exact one_ne_zero this
      · intro h'
        rw [h'] at h
        exact h2 (by linear_combination h)

omit [NeZero n] in
/-- A primitive `n`-th root of unity exists in `ZMod p` when `p = 2n+1`. -/
theorem exists_primitive (hpn : p = 2 * n + 1) : ∃ ρ : ZMod p, IsPrimitiveRoot ρ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = 2 * n := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    omega
  have h1 : IsPrimitiveRoot (g : ZMod p) (2 * n) := by
    rw [← hcard, ← hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  refine ⟨(g : ZMod p) ^ 2, ?_⟩
  have := h1.pow_of_dvd (p := 2) two_ne_zero (dvd_mul_right 2 n)
  simpa using this

end BSW
