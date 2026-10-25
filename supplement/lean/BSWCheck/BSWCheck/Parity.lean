module

public import Mathlib
public import BSWCheck.Basics
public import BSWCheck.Exponents

@[expose] public section

/-!
# The parity theorem: the bad graph of a solution is Eulerian (prime `q`, frame `P₀ = {0,∞}`)

For an admissible `ψ` over `ZMod p`, `p = 2n+1` with `n` odd (`p ≡ 3 mod 4`), and a square `x`,
`∏_{y square, y ≠ x} χ((x-y)(ψx-ψy)) = 1`; equivalently the number of squares `y ≠ x` with
`χ((x-y)(ψx-ψy)) = -1` (bad pairs of chords in the frame of `P₀`) is even.

The proof is a Wilson-type product: for every `w ≠ 0`,
`∏_{z ≠ w, z^n = w^n} (w - z) = n · w^(n-1)` (`prod_coset_erase`).
-/

open Finset

namespace BSW.Parity

open BSW.Basic

variable {p n : ℕ} [hp : Fact p.Prime] [NeZero n]

/-- `∏_{u ≠ 1, u^n = 1} (1 - u) = n` (cyclotomic product over the squares). -/
theorem prod_one_sub_sq {ρ : ZMod p} (hρ : IsPrimitiveRoot ρ n) :
    ∏ u ∈ (univ.filter (fun u : ZMod p => u ^ n = 1)).erase 1, (1 - u) = (n : ZMod p) := by
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

/-- Number of nonzero `u` with `u ^ n = 1` minus one. -/
theorem card_sq_erase {ρ : ZMod p} (hρ : IsPrimitiveRoot ρ n) :
    ((univ.filter (fun u : ZMod p => u ^ n = 1)).erase 1).card = n - 1 := by
  have hmem : (1 : ZMod p) ∈ univ.filter (fun u : ZMod p => u ^ n = 1) := by simp
  rw [card_erase_of_mem hmem]
  congr 1
  have : univ.filter (fun u : ZMod p => u ^ n = 1) = Polynomial.nthRootsFinset n (1 : ZMod p) := by
    ext u
    rw [mem_filter, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero (NeZero.ne n))]
    simp
  rw [this, hρ.card_nthRootsFinset]

/-- **Wilson-type product over a coset of the squares.** For `w ≠ 0`:
`∏_{z ≠ w, z^n = w^n} (w - z) = w^(n-1) · n`. -/
theorem prod_coset_erase {ρ : ZMod p} (hρ : IsPrimitiveRoot ρ n) {w : ZMod p} (hw : w ≠ 0) :
    ∏ z ∈ (univ.filter (fun z : ZMod p => z ^ n = w ^ n)).erase w, (w - z)
      = w ^ (n - 1) * (n : ZMod p) := by
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

/-- **The parity theorem, product form.**  `p = 2n+1`, `n` odd, `ψ` admissible, `x` a square:
`∏_{y square, y ≠ x} χ((x-y)(ψx-ψy)) = 1`. -/
theorem parity_prod (hpn : p = 2 * n + 1) (hodd : Odd n) {ψ : ZMod p → ZMod p}
    (h : Admissible ψ) {x : ZMod p} (hx : x ^ n = 1) :
    ∏ y ∈ (univ.filter (fun y : ZMod p => y ^ n = 1)).erase x,
        quadraticChar (ZMod p) ((x - y) * (ψ x - ψ y)) = 1 := by
  obtain ⟨ρ, hρ⟩ := BSW.exists_primitive (p := p) (n := n) hpn
  have hp2 : p ≠ 2 := by have := NeZero.ne n; omega
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [zero_pow (NeZero.ne n)] at hx; exact zero_ne_one hx
  have hψx0 := h.ne_zero x hx0
  -- Euler: z^n = ±1 ↔ χ z = ±1 (here n = p/2)
  have hn2 : p / 2 = n := by omega
  have euler1 : ∀ z : ZMod p, quadraticChar (ZMod p) z = 1 ↔ z ^ n = 1 := by
    intro z
    have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    have key := quadraticChar_eq_pow_of_char_ne_two' hchar z
    rw [ZMod.card, hn2] at key
    have hne : (-1 : ZMod p) ≠ 1 := by
      intro h1
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -h1
      rw [ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by norm_num) h2; have := hp.out.two_le; omega
    constructor
    · intro hz; rw [hz] at key; push_cast at key; exact key.symm
    · intro hz
      by_cases hz0 : z = 0
      · rw [hz0, zero_pow (NeZero.ne n)] at hz; exact (zero_ne_one hz).elim
      rcases quadraticChar_dichotomy hz0 with h1 | h1
      · exact h1
      · rw [h1, hz] at key; push_cast at key; exact (hne key).elim
  have hψxn : (ψ x) ^ n = -1 := by
    have hχ : quadraticChar (ZMod p) (ψ x) = -1 := by
      rw [h.swap x hx0, (euler1 x).2 hx]
    rcases BSW.pow_half_eq hpn (h.ne_zero x hx0) with h1 | h1
    · rw [← euler1] at h1; rw [h1] at hχ; norm_num at hχ
    · exact h1
  -- the two products
  have hP1 : ∏ y ∈ (univ.filter (fun y : ZMod p => y ^ n = 1)).erase x, (x - y)
      = x ^ (n - 1) * (n : ZMod p) := by
    have := prod_coset_erase hρ hx0
    rw [hx] at this; exact this
  have hP2 : ∏ y ∈ (univ.filter (fun y : ZMod p => y ^ n = 1)).erase x, (ψ x - ψ y)
      = (ψ x) ^ (n - 1) * (n : ZMod p) := by
    rw [← prod_coset_erase hρ hψx0, hψxn]
    refine Finset.prod_bij (fun y _ => ψ y) ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_erase, mem_filter] at hy ⊢
      obtain ⟨hyx, -, hyn⟩ := hy
      have hy0 : y ≠ 0 := by
        rintro rfl; rw [zero_pow (NeZero.ne n)] at hyn; exact zero_ne_one hyn
      refine ⟨?_, mem_univ _, ?_⟩
      · intro he; apply hyx
        rw [← h.invol y hy0, he, h.invol x hx0]
      · have hχ : quadraticChar (ZMod p) (ψ y) = -1 := by
          rw [h.swap y hy0, (euler1 y).2 hyn]
        rcases BSW.pow_half_eq hpn (h.ne_zero y hy0) with h1 | h1
        · rw [← euler1] at h1; rw [h1] at hχ; norm_num at hχ
        · exact h1
    · intro a ha b hb hab
      rw [mem_erase, mem_filter] at ha hb
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [zero_pow (NeZero.ne n)] at ha; exact zero_ne_one ha.2.2
      have hb0 : b ≠ 0 := by
        rintro rfl; rw [zero_pow (NeZero.ne n)] at hb; exact zero_ne_one hb.2.2
      rw [← h.invol a ha0, hab, h.invol b hb0]
    · intro z hz
      rw [mem_erase, mem_filter] at hz
      obtain ⟨hzw, -, hzn⟩ := hz
      have hz0 : z ≠ 0 := by
        rintro rfl; rw [zero_pow (NeZero.ne n)] at hzn
        have : (1 : ZMod p) = 0 := by linear_combination hzn
        exact one_ne_zero this
      refine ⟨ψ z, ?_, h.invol z hz0⟩
      rw [mem_erase, mem_filter]
      refine ⟨?_, mem_univ _, ?_⟩
      · intro he; apply hzw; rw [← h.invol z hz0, he]
      · apply (euler1 _).1
        rw [h.swap z hz0]
        have : quadraticChar (ZMod p) z = -1 := by
          rcases quadraticChar_dichotomy hz0 with h1 | h1
          · rw [euler1] at h1; rw [h1] at hzn
            exfalso
            have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hzn
            rw [ZMod.natCast_eq_zero_iff] at h2
            have := Nat.le_of_dvd (by norm_num) h2; have := hp.out.two_le; omega
          · exact h1
        rw [this, neg_neg]
    · intro y _; rfl
  -- combine
  rw [← map_prod, prod_mul_distrib, hP1, hP2]
  have hn0 : (n : ZMod p) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) h0
    omega
  obtain ⟨k, hk⟩ := hodd
  have hn1 : n - 1 = 2 * k := by omega
  have e : x ^ (n - 1) * (n : ZMod p) * ((ψ x) ^ (n - 1) * (n : ZMod p))
      = ((x * ψ x) ^ k * (n : ZMod p)) ^ 2 := by
    rw [hn1]; ring
  rw [e, quadraticChar_sq_one']
  exact mul_ne_zero (pow_ne_zero k (mul_ne_zero hx0 hψx0)) hn0

/-- A product of `±1` values equals `(-1)^(number of -1's)`. -/
theorem prod_pm_one {α : Type*} [DecidableEq α] (s : Finset α) (v : α → ℤ)
    (hv : ∀ a ∈ s, v a = 1 ∨ v a = -1) :
    ∏ a ∈ s, v a = (-1) ^ (s.filter (fun a => v a = -1)).card := by
  rw [← prod_filter_mul_prod_filter_not s (fun a => v a = -1)]
  have h1 : ∏ a ∈ s.filter (fun a => v a = -1), v a = (-1) ^ (s.filter (fun a => v a = -1)).card := by
    rw [← prod_const]; exact prod_congr rfl (fun a ha => (mem_filter.mp ha).2)
  have h2 : ∏ a ∈ s.filter (fun a => ¬ v a = -1), v a = 1 := by
    apply prod_eq_one
    intro a ha
    rw [mem_filter] at ha
    rcases hv a ha.1 with h | h
    · exact h
    · exact (ha.2 h).elim
  rw [h1, h2, mul_one]

/-- **The parity theorem.** The number of squares `y ≠ x` forming a bad pair with `x` in the frame of
`P₀` (`χ((x-y)(ψx-ψy)) = -1`) is even: the descendant of the two-graph at `P₀` is Eulerian. -/
theorem parity_even (hpn : p = 2 * n + 1) (hodd : Odd n) {ψ : ZMod p → ZMod p}
    (h : Admissible ψ) {x : ZMod p} (hx : x ^ n = 1) :
    Even (((univ.filter (fun y : ZMod p => y ^ n = 1)).erase x).filter
      (fun y => quadraticChar (ZMod p) ((x - y) * (ψ x - ψ y)) = -1)).card := by
  have hprod := parity_prod hpn hodd h hx
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [zero_pow (NeZero.ne n)] at hx; exact zero_ne_one hx
  rw [prod_pm_one] at hprod
  · rcases Nat.even_or_odd ((((univ.filter (fun y : ZMod p => y ^ n = 1)).erase x).filter
      (fun y => quadraticChar (ZMod p) ((x - y) * (ψ x - ψ y)) = -1)).card) with he | ho
    · exact he
    · rw [ho.neg_one_pow] at hprod; norm_num at hprod
  · intro y hy
    rw [mem_erase, mem_filter] at hy
    obtain ⟨hyx, -, hyn⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl; rw [zero_pow (NeZero.ne n)] at hyn; exact zero_ne_one hyn
    have hne : ψ x - ψ y ≠ 0 := by
      intro h0; apply hyx
      rw [← h.invol y hy0, ← sub_eq_zero.mp h0, h.invol x hx0]
    exact quadraticChar_dichotomy (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyx)) hne)

end BSW.Parity
