module

public import Mathlib

@[expose] public section

/-!
# Basic facts over an arbitrary finite field of odd order `q = 2n + 1`

Generalisations of the `ZMod p` helpers (`Exponents.exists_primitive`, `Parity.prod_coset_erase`,
`Bridge.chi_eq_*_iff`) to any finite field `F` with `|F| = 2n + 1`.
-/

open Finset

namespace BSW.FB

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

theorem ringChar_ne_two (hpn : Fintype.card F = 2 * n + 1) : ringChar F ≠ 2 := by
  intro h
  have := FiniteField.even_card_iff_char_two.mp h
  omega

theorem two_ne_zero' (hpn : Fintype.card F = 2 * n + 1) : (2 : F) ≠ 0 :=
  Ring.two_ne_zero (ringChar_ne_two hpn)

theorem neg_one_ne_one (hpn : Fintype.card F = 2 * n + 1) : (-1 : F) ≠ 1 := by
  intro h; apply two_ne_zero' hpn; linear_combination -h

theorem card_div_two (hpn : Fintype.card F = 2 * n + 1) : Fintype.card F / 2 = n := by omega

/-- Euler's criterion: `χ(a) = a^n` in `F`. -/
theorem chi_eq_pow (hpn : Fintype.card F = 2 * n + 1) (a : F) :
    ((quadraticChar F a : ℤ) : F) = a ^ n := by
  rw [quadraticChar_eq_pow_of_char_ne_two' (ringChar_ne_two hpn), card_div_two hpn]

theorem chi_neg_iff (hpn : Fintype.card F = 2 * n + 1) (a : F) :
    quadraticChar F a = -1 ↔ a ^ n = -1 := by
  have key := chi_eq_pow hpn a
  constructor
  · intro h; rw [h] at key; push_cast at key; exact key.symm
  · intro h
    by_cases ha : a = 0
    · exfalso
      have hn : n ≠ 0 := by
        rintro rfl; rw [pow_zero] at h; exact neg_one_ne_one hpn h.symm
      rw [ha, zero_pow hn] at h; exact (neg_ne_zero.mpr one_ne_zero) h.symm
    · rcases quadraticChar_dichotomy ha with h1 | h1
      · exfalso; rw [h1, h] at key; push_cast at key; exact neg_one_ne_one hpn key.symm
      · exact h1

theorem chi_one_iff (hpn : Fintype.card F = 2 * n + 1) (a : F) :
    quadraticChar F a = 1 ↔ a ^ n = 1 := by
  have key := chi_eq_pow hpn a
  constructor
  · intro h; rw [h] at key; push_cast at key; exact key.symm
  · intro h
    by_cases ha : a = 0
    · exfalso
      have hn : n ≠ 0 := by
        rintro rfl
        have h1 : 1 < Fintype.card F := Fintype.one_lt_card
        omega
      rw [ha, zero_pow hn] at h; exact zero_ne_one h
    · rcases quadraticChar_dichotomy ha with h1 | h1
      · exact h1
      · exfalso; rw [h1, h] at key; push_cast at key; exact neg_one_ne_one hpn key

theorem pow_card_sub_one (hpn : Fintype.card F = 2 * n + 1) {a : F} (ha : a ≠ 0) :
    a ^ (2 * n) = 1 := by
  have := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [hpn, Nat.add_sub_cancel] at this

/-- `(n : F) ≠ 0` (indeed `2n = q - 1 = -1` in `F`). -/
theorem n_ne_zero (hpn : Fintype.card F = 2 * n + 1) : (n : F) ≠ 0 := by
  intro h
  have hq : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [hpn] at hq
  push_cast at hq
  rw [h] at hq
  simp at hq

theorem exists_primitive (hpn : Fintype.card F = 2 * n + 1) : ∃ ρ : F, IsPrimitiveRoot ρ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = 2 * n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]; omega
  have h1 : IsPrimitiveRoot (g : F) (2 * n) := by
    rw [← hcard, ← hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  refine ⟨(g : F) ^ 2, ?_⟩
  have := h1.pow_of_dvd (p := 2) two_ne_zero (dvd_mul_right 2 n)
  simpa using this

variable [NeZero n]

theorem prod_one_sub_sq {ρ : F} (hρ : IsPrimitiveRoot ρ n) :
    ∏ u ∈ (univ.filter (fun u : F => u ^ n = 1)).erase 1, (1 - u) = (n : F) := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  subst hm
  have key := hρ.prod_one_sub_pow_eq_order
  push_cast
  rw [← key]
  symm
  refine Finset.prod_bij (fun k _ => ρ ^ (k + 1)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_erase, mem_filter]
    refine ⟨?_, mem_univ _, ?_⟩
    · intro h1
      have := hρ.pow_eq_one_iff_dvd (k + 1) |>.1 h1
      have hk' := mem_range.mp hk
      have := Nat.le_of_dvd (by omega) this
      omega
    · rw [← pow_mul, mul_comm, pow_mul, hρ.pow_eq_one, one_pow]
  · intro a ha b hb hab
    have ha' := mem_range.mp ha; have hb' := mem_range.mp hb
    have := hρ.pow_inj (by omega : a + 1 < m + 1) (by omega : b + 1 < m + 1) hab
    omega
  · intro u hu
    rw [mem_erase, mem_filter] at hu
    obtain ⟨hu1, -, hun⟩ := hu
    obtain ⟨k, hk, rfl⟩ := hρ.eq_pow_of_pow_eq_one hun
    have hk0 : k ≠ 0 := by rintro rfl; exact hu1 (pow_zero ρ)
    exact ⟨k - 1, mem_range.mpr (by omega), by congr 1; omega⟩
  · intro k _; rfl

theorem card_sq_erase {ρ : F} (hρ : IsPrimitiveRoot ρ n) :
    ((univ.filter (fun u : F => u ^ n = 1)).erase 1).card = n - 1 := by
  have hmem : (1 : F) ∈ univ.filter (fun u : F => u ^ n = 1) := by simp
  rw [card_erase_of_mem hmem]
  congr 1
  have : univ.filter (fun u : F => u ^ n = 1) = Polynomial.nthRootsFinset n (1 : F) := by
    ext u
    rw [mem_filter, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero (NeZero.ne n))]
    simp
  rw [this, hρ.card_nthRootsFinset]

/-- Wilson-type product over a coset of the squares: `∏_{z ≠ w, z^n = w^n} (w - z) = w^(n-1) n`. -/
theorem prod_coset_erase {ρ : F} (hρ : IsPrimitiveRoot ρ n) {w : F} (hw : w ≠ 0) :
    ∏ z ∈ (univ.filter (fun z : F => z ^ n = w ^ n)).erase w, (w - z) = w ^ (n - 1) * (n : F) := by
  rw [← prod_one_sub_sq hρ, ← card_sq_erase hρ, ← prod_const, ← prod_mul_distrib]
  symm
  refine Finset.prod_bij (fun u _ => w * u) ?_ ?_ ?_ ?_
  · intro u hu
    rw [mem_erase, mem_filter] at hu ⊢
    obtain ⟨hu1, -, hun⟩ := hu
    refine ⟨?_, mem_univ _, by rw [mul_pow, hun, mul_one]⟩
    intro h; apply hu1
    have : w * u = w * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hw this
  · intro a _ b _ hab; exact mul_left_cancel₀ hw hab
  · intro z hz
    rw [mem_erase, mem_filter] at hz
    obtain ⟨hzw, -, hzn⟩ := hz
    refine ⟨z / w, ?_, by field_simp⟩
    rw [mem_erase, mem_filter]
    refine ⟨?_, mem_univ _, ?_⟩
    · intro h; apply hzw; field_simp at h; exact h
    · rw [div_pow, hzn, div_self (pow_ne_zero n hw)]
  · intro u _; ring

end BSW.FB
