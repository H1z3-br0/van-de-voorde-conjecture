module

/-
  Power sums in `ZMod p` used in the elementary (F_p-valued) proof of the power-map theorem.
  Notation: `p = 2n+1` prime, `h z = (z-1)^n` (the Legendre symbol of `z-1`, read in `ZMod p`),
  `X A = ∑_{z nonsquare} z^A (z-1)^n`.
  Main results:
    * `two_mul_X_lt`     : `2 X_A = (-1)^A C(n,A)`            for `0 < A < n`;
    * `two_mul_X_mirror` : `2 X_(2n-A) = (-1)^A C(n,A)`       for `0 < A < n`;
    * `X_zero`           : `X_0 = 1`;
    * `autocorr`         : `∑_{z ≠ 0} (z-1)^n (αz-1)^n = -2`  for squares `α`.
-/
public import Mathlib

@[expose] public section

open Finset

namespace BSW

variable {p : ℕ} [hp : Fact p.Prime]

/-- `∑_{x ∈ 𝔽_p} x^k`. -/
theorem sum_pow_eq (k : ℕ) :
    ∑ x : ZMod p, x ^ k = (if k = 0 then 1 else 0) + (if p - 1 ∣ k then -1 else 0) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
  congr 1
  · exact zero_pow_eq k
  · have h := FiniteField.sum_pow_units (ZMod p) k
    rw [ZMod.card] at h
    rw [← h]
    symm
    refine Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p)) ?_ ?_ ?_ ?_
    · intro u _
      simp [Units.ne_zero]
    · intro u _ v _ huv
      exact Units.ext huv
    · intro b hb
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
      exact ⟨Units.mk0 b hb0, Finset.mem_univ _, rfl⟩
    · intro u _
      rfl

/-- The only multiple of `N` in `(0, 2N)` is `N`. -/
theorem dvd_window_eq {N x : ℕ} (hd : N ∣ x) (hpos : 0 < x) (hlt : x < 2 * N) : x = N := by
  obtain ⟨t, rfl⟩ := hd
  rcases t with _ | _ | t
  · simp at hpos
  · ring
  · nlinarith

theorem not_dvd_small {N x : ℕ} (hpos : 0 < x) (hlt : x < N) : ¬ N ∣ x :=
  fun h => absurd (Nat.le_of_dvd hpos h) (by omega)

variable {n : ℕ}

/-- For `0 < k`, `∑ x^k = -1` if `2n ∣ k`, else `0`. -/
theorem sum_pow_pos (hpn : p = 2 * n + 1) {k : ℕ} (hk : 0 < k) :
    ∑ x : ZMod p, x ^ k = if 2 * n ∣ k then -1 else 0 := by
  rw [sum_pow_eq, ite_eq_right (by omega), zero_add, show p - 1 = 2 * n by omega]

/-- Binomial expansion of `(z-1)^n`. -/
theorem sub_one_pow_expand (z : ZMod p) (n : ℕ) :
    (z - 1) ^ n = ∑ m ∈ range (n + 1), z ^ m * (-1) ^ (n - m) * (n.choose m : ZMod p) := by
  rw [sub_eq_add_neg, add_pow]

/-- `∑_z z^B (z-1)^n = ∑_m C(n,m) (-1)^(n-m) ∑_z z^(B+m)`. -/
theorem sum_mul_sub_one_pow (B n : ℕ) :
    ∑ z : ZMod p, z ^ B * (z - 1) ^ n
      = ∑ m ∈ range (n + 1), (-1) ^ (n - m) * (n.choose m : ZMod p) * ∑ z : ZMod p, z ^ (B + m) := by
  simp_rw [sub_one_pow_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun z _ => ?_
  rw [pow_add]
  ring

/-- If exactly one `m ∈ [0,n]` has `2n ∣ B+m`, the sum picks that term. -/
theorem sum_mul_sub_one_pow_single (hpn : p = 2 * n + 1) {B : ℕ} (hB : 0 < B) (m₀ : ℕ)
    (hm₀ : m₀ ≤ n) (hdiv : 2 * n ∣ B + m₀) (huniq : ∀ m ≤ n, 2 * n ∣ B + m → m = m₀) :
    ∑ z : ZMod p, z ^ B * (z - 1) ^ n = -((-1) ^ (n - m₀) * (n.choose m₀ : ZMod p)) := by
  rw [sum_mul_sub_one_pow, Finset.sum_eq_single m₀]
  · rw [sum_pow_pos hpn (by omega), ite_eq_left hdiv]
    ring
  · intro m hm hne
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [sum_pow_pos hpn (by omega), ite_eq_right (fun h => hne (huniq m hm' h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hm₀)) h

/-- If no `m ∈ [0,n]` has `2n ∣ B+m`, the sum vanishes. -/
theorem sum_mul_sub_one_pow_zero (hpn : p = 2 * n + 1) {B : ℕ} (hB : 0 < B)
    (hnone : ∀ m ≤ n, ¬ 2 * n ∣ B + m) :
    ∑ z : ZMod p, z ^ B * (z - 1) ^ n = 0 := by
  rw [sum_mul_sub_one_pow]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [sum_pow_pos hpn (by omega), ite_eq_right (hnone m hm'), mul_zero]

/-- Euler: for `z ≠ 0`, `z^n = 1 ∨ z^n = -1`. -/
theorem pow_half_eq (hpn : p = 2 * n + 1) {z : ZMod p} (hz : z ≠ 0) : z ^ n = 1 ∨ z ^ n = -1 := by
  have h := ZMod.pow_div_two_eq_neg_one_or_one p hz
  rw [show p / 2 = n by omega] at h
  tauto

/-- `X A = ∑_{z^n = -1} z^A (z-1)^n`. -/
noncomputable def X (n A : ℕ) : ZMod p :=
  ∑ z ∈ univ.filter (fun z : ZMod p => z ^ n = -1), z ^ A * (z - 1) ^ n

theorem two_ne_zero' (hpn : p = 2 * n + 1) (hn : 0 < n) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- `2 X A = ∑_z (1 - z^n) z^A (z-1)^n` for `A > 0`. -/
theorem two_mul_X (hpn : p = 2 * n + 1) (hn : 0 < n) {A : ℕ} (hA : 0 < A) :
    2 * X (p := p) n A = ∑ z : ZMod p, z ^ A * (z - 1) ^ n - ∑ z : ZMod p, z ^ (A + n) * (z - 1) ^ n := by
  rw [X, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z = 0
  · subst hz
    have h1 : (0 : ZMod p) ^ n = 0 := zero_pow (by omega)
    simp [h1, zero_pow (Nat.pos_iff_ne_zero.mp hA), zero_pow (show A + n ≠ 0 by omega)]
  · rw [pow_add]
    rcases pow_half_eq hpn hz with h | h
    · have : ¬ (z ^ n = -1) := by
        rw [h]
        intro h'
        have : (2 : ZMod p) = 0 := by linear_combination h'
        exact two_ne_zero' hpn hn this
      rw [ite_eq_right this, h]
      ring
    · rw [ite_eq_left h, h]
      ring

/-- `2 X_A = (-1)^A C(n,A)` for `0 < A < n`. -/
theorem two_mul_X_lt (hpn : p = 2 * n + 1) {A : ℕ} (hA : 0 < A) (hAn : A < n) :
    2 * X (p := p) n A = (-1) ^ A * (n.choose A : ZMod p) := by
  rw [two_mul_X hpn (by omega) hA]
  rw [sum_mul_sub_one_pow_zero hpn hA (fun m hm h => not_dvd_small (by omega) (by omega) h)]
  rw [sum_mul_sub_one_pow_single hpn (by omega) (n - A) (by omega) ⟨1, by omega⟩ (fun m hm h => by
        have := dvd_window_eq h (by omega) (by omega); omega)]
  rw [show n - (n - A) = A by omega, Nat.choose_symm (by omega)]
  ring

/-- `2 X_(2n-A) = (-1)^A C(n,A)` for `0 < A < n` (`n` odd). -/
theorem two_mul_X_mirror (hpn : p = 2 * n + 1) (hodd : Odd n) {A : ℕ} (hA : 0 < A) (hAn : A < n) :
    2 * X (p := p) n (2 * n - A) = (-1) ^ A * (n.choose A : ZMod p) := by
  rw [two_mul_X hpn (by omega) (by omega)]
  rw [sum_mul_sub_one_pow_single hpn (by omega) A (by omega) ⟨1, by omega⟩ (fun m hm h => by
        have := dvd_window_eq h (by omega) (by omega); omega)]
  rw [sum_mul_sub_one_pow_zero hpn (by omega) (fun m hm h => by
        have := dvd_window_eq h (by omega) (by omega); omega)]
  obtain ⟨k, rfl⟩ := hodd
  have : (-1 : ZMod p) ^ (2 * k + 1 - A) = -(-1) ^ A := by
    have h2 : (-1 : ZMod p) ^ (2 * k + 1 - A) * (-1) ^ A = -1 := by
      rw [← pow_add, show 2 * k + 1 - A + A = 2 * k + 1 by omega, pow_succ, pow_mul]
      simp
    have h3 : ((-1 : ZMod p) ^ A) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (-1 : ZMod p) ^ A * h2 - (-1 : ZMod p) ^ (2 * k + 1 - A) * h3
  rw [this]
  ring

/-- `X_0 = 1`. -/
theorem X_zero (hpn : p = 2 * n + 1) (hodd : Odd n) : X (p := p) n 0 = 1 := by
  have hn : 0 < n := hodd.pos
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero' hpn hn
  -- 2 X_0 = ∑_{z ≠ 0} (1 - z^n)(z-1)^n
  have key : 2 * X (p := p) n 0
      = ∑ z : ZMod p, (z - 1) ^ n - ∑ z : ZMod p, z ^ n * (z - 1) ^ n - (0 - 1) ^ n * (1 - 0 ^ n) := by
    rw [X, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    rw [← Finset.add_sum_erase (univ : Finset (ZMod p)) _ (Finset.mem_univ (0 : ZMod p))]
    have hz0 : ¬ ((0 : ZMod p) ^ n = -1) := by
      rw [zero_pow (by omega)]
      intro h
      have : (1 : ZMod p) = 0 := by linear_combination h
      exact one_ne_zero this
    rw [ite_eq_right hz0]
    have rest : ∀ z ∈ univ.erase (0 : ZMod p),
        (if z ^ n = -1 then 2 * (z ^ 0 * (z - 1) ^ n) else 0) = (z - 1) ^ n - z ^ n * (z - 1) ^ n := by
      intro z hz
      have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
      rcases pow_half_eq hpn hz0 with h | h
      · have : ¬ (z ^ n = -1) := by
          rw [h]; intro h'; exact h2 (by linear_combination h')
        rw [ite_eq_right this, h]; ring
      · rw [ite_eq_left h, h]; ring
    rw [Finset.sum_congr rfl rest, zero_pow (by omega : n ≠ 0)]
    ring
  have s1 : ∑ z : ZMod p, (z - 1) ^ n = 0 := by
    have := sum_mul_sub_one_pow (p := p) 0 n
    simp only [pow_zero, one_mul, zero_add] at this
    rw [this]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [sum_pow_eq, show p - 1 = 2 * n by omega]
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · rw [ite_eq_right hm0, ite_eq_right (fun h => by have := Nat.le_of_dvd (by omega) h; omega)]
      simp
  have s2 : ∑ z : ZMod p, z ^ n * (z - 1) ^ n = -1 := by
    rw [sum_mul_sub_one_pow_single hpn hn n le_rfl ⟨1, by omega⟩ (fun m hm h => by
        have := dvd_window_eq h (by omega) (by omega); omega)]
    simp
  rw [s1, s2, zero_pow (by omega : n ≠ 0)] at key
  obtain ⟨k, rfl⟩ := hodd
  have hm1 : (0 - 1 : ZMod p) ^ (2 * k + 1) = -1 := by
    rw [zero_sub, pow_succ, pow_mul]; simp
  rw [hm1] at key
  have : 2 * X (p := p) (2 * k + 1) 0 = 2 * 1 := by rw [key]; ring
  exact mul_left_cancel₀ h2 this

/-- Autocorrelation: for `α^n = 1`, `∑_{z ≠ 0} (z-1)^n (αz-1)^n = -2`. -/
theorem autocorr (hpn : p = 2 * n + 1) (hodd : Odd n) {α : ZMod p} (hα : α ^ n = 1) :
    ∑ z ∈ univ.erase (0 : ZMod p), (z - 1) ^ n * (α * z - 1) ^ n = -2 := by
  have hn : 0 < n := hodd.pos
  have full : ∑ z : ZMod p, (z - 1) ^ n * (α * z - 1) ^ n = -1 := by
    have e1 : ∀ z : ZMod p, (z - 1) ^ n * (α * z - 1) ^ n
        = ∑ m' ∈ range (n + 1), ∑ m ∈ range (n + 1),
            ((-1) ^ (n - m') * (n.choose m' : ZMod p) * (α ^ m * (-1) ^ (n - m) * (n.choose m : ZMod p)))
              * z ^ (m' + m) := by
      intro z
      rw [sub_one_pow_expand z, sub_one_pow_expand (α * z), Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun m _ => ?_
      rw [mul_pow, pow_add]
      ring
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (univ : Finset (ZMod p))), ← Finset.mul_sum]
    rw [Finset.sum_eq_single n, Finset.sum_eq_single n]
    · rw [sum_pow_pos hpn (by omega), ite_eq_left ⟨1, by ring⟩, hα]
      simp
    · intro m hm hne
      have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hpos : 0 < n + m := by omega
      rw [sum_pow_pos hpn hpos, ite_eq_right (fun h => by
          have := dvd_window_eq h hpos (by omega); omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
    · intro m' hm' hne
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm1 : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hm2 : m' ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm')
      by_cases h0 : m' + m = 0
      · rw [h0, sum_pow_eq, ite_eq_left rfl, ite_eq_left (dvd_zero _)]
        simp
      · rw [sum_pow_pos hpn (Nat.pos_of_ne_zero h0), ite_eq_right (fun h => by
          have := dvd_window_eq h (Nat.pos_of_ne_zero h0) (by omega); omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))] at full
  obtain ⟨k, rfl⟩ := hodd
  have h0 : ((0 : ZMod p) - 1) ^ (2 * k + 1) * (α * 0 - 1) ^ (2 * k + 1) = 1 := by
    rw [mul_zero, zero_sub, ← mul_pow]; simp
  rw [h0] at full
  linear_combination full

end BSW
