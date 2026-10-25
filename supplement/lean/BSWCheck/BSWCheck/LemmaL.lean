module

public import Mathlib

@[expose] public section

/-!
# Lemma 6.1 of the paper: digit combinatorics behind Theorem 7.5 for prime powers

Let `p ≥ 3` be odd, `k` odd, `p^k = 2h + 1` with `h` odd, `h > 1` (so `q = p^k ≡ 3 mod 4`).
For `y ∈ ℤ/h` put `Π(y) = ∑_{j<k} (-1)^{⟨p^j y⟩_h}` (`⟨·⟩_h` = least nonnegative residue).

`BSW.LemmaL.lemmaL`: if `Π(τ β) = ε Π(τ)` for all units `τ` (`ε = ±1`), then `β = ε p^j` for some
`j < k`.  Primality of `p` is not needed.

Proof (as in the paper, with the final digit comparison replaced by a `p`-adic valuation argument):
* binary digits: `2⟨z⟩ = ⟨2z⟩ + h·bit(2z)` (`two_val`), iterated `m = φ(h)` times, give
  `(2^m - 1) Ψ(y) = h ∑_ℓ 2^{m-1-ℓ} col_ℓ(y)`; the hypothesis says `col_ℓ(β) = col_ℓ(1)`, hence
  `Ψ(β) = Ψ(1)` (`Psi_eq_of_Adm`), where `Ψ(y) = ∑_j ⟨p^j y⟩`;
* the cycle `y_{j+1} = p y_j - n_j h` gives `∑ n_j = 2` and `2⟨β⟩ = ∑ n_j p^{k-1-j}`, so
  `2⟨β⟩ = p^a + p^b` (`C_of_Adm`);
* admissible multipliers form a monoid containing `p`; if `β ≡ (1+p^c)/2` then `β²` is admissible,
  and `4⟨β²⟩` equals `(1+p^c)²` or `p^k + 2p^c + p^{2c-k}`, which never equals `2(p^a + p^b)`
  (`no_eq`).
-/

open Finset

namespace BSW.LemmaL

variable {h : ℕ} [NeZero h]

/-- `Π(y) = ∑_{j<k} (-1)^{⟨p^j y⟩_h}`. -/
def Pi (p k : ℕ) (y : ZMod h) : ℤ := ∑ j ∈ range k, (-1) ^ ((p : ZMod h) ^ j * y).val

/-- `Ψ(y) = ∑_{j<k} ⟨p^j y⟩_h`. -/
def Psi (p k : ℕ) (y : ZMod h) : ℕ := ∑ j ∈ range k, ((p : ZMod h) ^ j * y).val

/-- Parity of the least residue. -/
def bit (y : ZMod h) : ℕ := y.val % 2

/-- Admissible multipliers (the case `ε = 1`). -/
def Adm (p k : ℕ) (β : ZMod h) : Prop := ∀ τ : ZMod h, IsUnit τ → Pi p k (τ * β) = Pi p k τ

theorem neg_one_pow_eq (n : ℕ) : (-1 : ℤ) ^ n = 1 - 2 * ((n % 2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [← two_mul, pow_mul]; norm_num
  · rw [pow_succ, pow_mul]; norm_num

omit [NeZero h] in
theorem Pi_eq (p k : ℕ) (y : ZMod h) :
    Pi p k y = k - 2 * ((∑ j ∈ range k, bit ((p : ZMod h) ^ j * y) : ℕ) : ℤ) := by
  unfold Pi bit
  simp only [neg_one_pow_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one,
    ← mul_sum]
  push_cast; ring

omit [NeZero h] in
theorem bit_le (y : ZMod h) : bit y ≤ 1 := by unfold bit; omega

theorem two_val (hh : Odd h) (z : ZMod h) : 2 * z.val = (2 * z).val + h * bit (2 * z) := by
  have hv : (2 * z).val = (2 * z.val) % h := by
    rw [ZMod.val_mul, show (2 : ZMod h) = ((2 : ℕ) : ZMod h) by norm_num, ZMod.val_natCast,
      Nat.mod_mul_mod]
  unfold bit
  rw [hv]
  have hz := ZMod.val_lt z
  obtain ⟨t, ht⟩ := hh
  have hd := Nat.mod_add_div (2 * z.val) h
  have hq : 2 * z.val / h < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  generalize hr : 2 * z.val % h = r at *
  interval_cases hq' : 2 * z.val / h
  · have h0 : r % 2 = 0 := by omega
    rw [h0]; omega
  · have h1 : r % 2 = 1 := by omega
    rw [h1]; omega

/-- `S m y = ∑_{ℓ<m} 2^{m-1-ℓ} bit(2^{ℓ+1} y)`. -/
def S (m : ℕ) (y : ZMod h) : ℕ := ∑ ℓ ∈ range m, 2 ^ (m - 1 - ℓ) * bit ((2 : ZMod h) ^ (ℓ + 1) * y)

omit [NeZero h] in
theorem S_succ (m : ℕ) (y : ZMod h) :
    S (m + 1) y = 2 * S m y + bit ((2 : ZMod h) ^ (m + 1) * y) := by
  unfold S
  rw [sum_range_succ, show m + 1 - 1 - m = 0 by omega, pow_zero, one_mul, mul_sum]
  congr 1
  refine sum_congr rfl (fun ℓ hℓ => ?_)
  have := mem_range.mp hℓ
  rw [show m + 1 - 1 - ℓ = (m - 1 - ℓ) + 1 by omega, pow_succ]; ring

theorem iter (hh : Odd h) (m : ℕ) (y : ZMod h) :
    2 ^ m * y.val = ((2 : ZMod h) ^ m * y).val + h * S m y := by
  induction m with
  | zero => simp [S]
  | succ m ih =>
    rw [S_succ, pow_succ, mul_comm (2 ^ m) 2, mul_assoc, ih, mul_add,
      two_val hh ((2 : ZMod h) ^ m * y)]
    rw [show (2 : ZMod h) * (2 ^ m * y) = 2 ^ (m + 1) * y by ring]
    ring

omit [NeZero h] in
theorem two_unit (hh : Odd h) : IsUnit (2 : ZMod h) := by
  have hc : Nat.Coprime 2 h := Nat.coprime_two_left.mpr hh
  have := (ZMod.unitOfCoprime 2 hc).isUnit
  rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this

omit [NeZero h] in
theorem two_pow_totient (hh : Odd h) : (2 : ZMod h) ^ h.totient = 1 := by
  obtain ⟨u, hu⟩ := two_unit hh
  have := ZMod.pow_totient u
  rw [← hu, ← Units.val_pow_eq_pow_val, this, Units.val_one]

/-- `Ψ(β) = Ψ(1)` for admissible `β`. -/
theorem Psi_eq_of_Adm (hh : Odd h) (p k : ℕ) {β : ZMod h} (hA : Adm p k β) :
    Psi p k β = Psi p k (1 : ZMod h) := by
  set m := h.totient with hm
  have hm1 : 1 ≤ m := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne h))
  have h2m := two_pow_totient hh
  -- `(2^m - 1) ⟨y⟩ = h S_m(y)`
  have key : ∀ y : ZMod h, (2 ^ m - 1) * y.val = h * S m y := by
    intro y
    have e := iter hh m y
    rw [show (2 : ZMod h) ^ m = 1 from h2m, one_mul] at e
    rw [Nat.sub_mul, one_mul, e]; omega
  -- columns agree
  have hcol : ∀ ℓ, ∑ j ∈ range k, bit ((2 : ZMod h) ^ (ℓ + 1) * ((p : ZMod h) ^ j * β)) =
      ∑ j ∈ range k, bit ((2 : ZMod h) ^ (ℓ + 1) * ((p : ZMod h) ^ j * 1)) := by
    intro ℓ
    have hu : IsUnit ((2 : ZMod h) ^ (ℓ + 1)) := (two_unit hh).pow _
    have e := hA _ hu
    rw [Pi_eq, Pi_eq] at e
    have e' : ∑ j ∈ range k, bit ((p : ZMod h) ^ j * ((2 : ZMod h) ^ (ℓ + 1) * β)) =
        ∑ j ∈ range k, bit ((p : ZMod h) ^ j * (2 : ZMod h) ^ (ℓ + 1)) := by omega
    calc ∑ j ∈ range k, bit ((2 : ZMod h) ^ (ℓ + 1) * ((p : ZMod h) ^ j * β))
        = ∑ j ∈ range k, bit ((p : ZMod h) ^ j * ((2 : ZMod h) ^ (ℓ + 1) * β)) :=
          sum_congr rfl (fun j _ => by ring_nf)
      _ = ∑ j ∈ range k, bit ((p : ZMod h) ^ j * (2 : ZMod h) ^ (ℓ + 1)) := e'
      _ = _ := sum_congr rfl (fun j _ => by ring_nf)
  have hsum : ∀ y : ZMod h, (2 ^ m - 1) * Psi p k y =
      h * ∑ ℓ ∈ range m, 2 ^ (m - 1 - ℓ) *
        ∑ j ∈ range k, bit ((2 : ZMod h) ^ (ℓ + 1) * ((p : ZMod h) ^ j * y)) := by
    intro y
    unfold Psi
    rw [mul_sum, sum_congr rfl (fun j _ => key ((p : ZMod h) ^ j * y)), ← mul_sum]
    congr 1
    unfold S
    rw [sum_comm]
    refine sum_congr rfl (fun ℓ _ => ?_)
    rw [mul_sum]
  have e1 := hsum β
  have e2 := hsum 1
  rw [sum_congr rfl (fun ℓ _ => by rw [hcol ℓ])] at e1
  rw [← e2] at e1
  have hpos : 0 < 2 ^ m - 1 := by
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    omega
  exact Nat.eq_of_mul_eq_mul_left hpos e1


/-! ## The cycle `y_{j+1} = p y_j - n_j h` -/

theorem sum_two (k : ℕ) (f g : ℕ → ℕ) :
    (∑ j ∈ range k, f j = 2 → ∃ a b, a < k ∧ b < k ∧ ∑ j ∈ range k, f j * g j = g a + g b) ∧
    (∑ j ∈ range k, f j = 1 → ∃ a, a < k ∧ ∑ j ∈ range k, f j * g j = g a) ∧
    (∑ j ∈ range k, f j = 0 → ∑ j ∈ range k, f j * g j = 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨ih2, ih1, ih0⟩ := ih
    simp only [sum_range_succ]
    refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
    · have : f k = 0 ∨ f k = 1 ∨ f k = 2 := by omega
      rcases this with h0 | h1 | h2
      · obtain ⟨a, b, ha, hb, e⟩ := ih2 (by omega)
        exact ⟨a, b, by omega, by omega, by rw [e, h0]; ring⟩
      · obtain ⟨a, ha, e⟩ := ih1 (by omega)
        exact ⟨a, k, by omega, by omega, by rw [e, h1]; ring⟩
      · have e := ih0 (by omega)
        exact ⟨k, k, by omega, by omega, by rw [e, h2]; ring⟩
    · have : f k = 0 ∨ f k = 1 := by omega
      rcases this with h0 | h1
      · obtain ⟨a, ha, e⟩ := ih1 (by omega)
        exact ⟨a, by omega, by rw [e, h0]; ring⟩
      · have e := ih0 (by omega)
        exact ⟨k, by omega, by rw [e, h1]; ring⟩
    · have e := ih0 (by omega)
      rw [e, show f k = 0 by omega]; ring

omit [NeZero h] in
theorem p_pow_k {p k : ℕ} (hpk : p ^ k = 2 * h + 1) : (p : ZMod h) ^ k = 1 := by
  rw [← Nat.cast_pow, hpk]; push_cast; rw [ZMod.natCast_self]; ring

omit [NeZero h] in
theorem val_mul_p (p : ℕ) (x : ZMod h) : ((p : ZMod h) * x).val = (p * x.val) % h := by
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]

omit [NeZero h] in
theorem pow_lt_h {p k : ℕ} (hp3 : 3 ≤ p) (hk1 : 1 ≤ k) (hpk : p ^ k = 2 * h + 1) (hh1 : 1 < h)
    {j : ℕ} (hj : j < k) : p ^ j < h := by
  have e : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hle : p ^ j ≤ p ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

theorem geom (p k : ℕ) (hp : 1 ≤ p) : (p - 1) * ∑ j ∈ range k, p ^ j = p ^ k - 1 := by
  have e := geom_sum_mul (p : ℤ) k
  have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp
  zify [hp, h1]
  linarith

/-- **Step 4.** For admissible `β`: `2⟨β⟩ = p^a + p^b` with `a, b < k`. -/
theorem C_of_Adm (hh : Odd h) (hh1 : 1 < h) {p k : ℕ} (hp3 : 3 ≤ p) (hk1 : 1 ≤ k)
    (hpk : p ^ k = 2 * h + 1) {β : ZMod h} (hA : Adm p k β) :
    ∃ a b, a < k ∧ b < k ∧ 2 * β.val = p ^ a + p ^ b := by
  set y : ℕ → ℕ := fun j => ((p : ZMod h) ^ j * β).val with hy
  set n : ℕ → ℕ := fun j => p * y j / h with hn
  have step : ∀ j, p * y j = y (j + 1) + h * n j := by
    intro j
    have : y (j + 1) = (p * y j) % h := by
      simp only [hy]; rw [pow_succ', mul_assoc, val_mul_p]
    rw [this]; exact (Nat.mod_add_div _ _).symm
  have unroll : ∀ j, p ^ j * y 0 = y j + h * ∑ i ∈ range j, n i * p ^ (j - 1 - i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_assoc, ih, mul_add, step j, sum_range_succ,
        show j + 1 - 1 - j = 0 by omega, pow_zero, mul_one, mul_add, mul_sum, mul_sum, mul_sum]
      have : ∑ i ∈ range j, h * (n i * p ^ (j + 1 - 1 - i)) =
          ∑ i ∈ range j, p * (h * (n i * p ^ (j - 1 - i))) := by
        refine sum_congr rfl (fun i hi => ?_)
        have := mem_range.mp hi
        rw [show j + 1 - 1 - i = (j - 1 - i) + 1 by omega, pow_succ]; ring
      rw [this]; ring
  have hyk : y k = y 0 := by simp only [hy]; rw [p_pow_k hpk, pow_zero]
  -- `(p - 1) Ψ(β) = h ∑ n_j`
  have hsum : p * Psi p k β = Psi p k β + h * ∑ j ∈ range k, n j := by
    unfold Psi
    rw [mul_sum, sum_congr rfl (fun j _ => step j), sum_add_distrib, ← mul_sum]
    congr 1
    have e1 := sum_range_succ' y k
    have e2 := sum_range_succ y k
    rw [hyk] at e2
    simp only [hy] at e1 e2 ⊢
    omega
  have hPsi1 : Psi p k (1 : ZMod h) = ∑ j ∈ range k, p ^ j := by
    unfold Psi
    refine sum_congr rfl (fun j hj => ?_)
    rw [mul_one, ← Nat.cast_pow, ZMod.val_natCast, Nat.mod_eq_of_lt (pow_lt_h hp3 hk1 hpk hh1
      (mem_range.mp hj))]
  have hgeom := geom p k (by omega)
  rw [Psi_eq_of_Adm hh p k hA, hPsi1] at hsum
  have hn2 : ∑ j ∈ range k, n j = 2 := by
    have e : h * ∑ j ∈ range k, n j = h * 2 := by
      have : (p - 1) * ∑ j ∈ range k, p ^ j = h * ∑ j ∈ range k, n j := by
        rw [Nat.sub_mul, one_mul]; omega
      rw [← this, hgeom, hpk]; omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) e
  -- `2 ⟨β⟩ = ∑ n_j p^{k-1-j}`
  have hN : 2 * y 0 = ∑ j ∈ range k, n j * p ^ (k - 1 - j) := by
    have e := unroll k
    rw [hyk, hpk] at e
    have e' : h * (2 * y 0) = h * ∑ i ∈ range k, n i * p ^ (k - 1 - i) := by
      rw [add_mul, one_mul] at e; linarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) e'
  obtain ⟨a, b, ha, hb, e⟩ := (sum_two k n (fun j => p ^ (k - 1 - j))).1 hn2
  refine ⟨k - 1 - a, k - 1 - b, by omega, by omega, ?_⟩
  have : y 0 = β.val := by simp [hy]
  rw [← this, hN, e]


/-! ## Admissible multipliers form a monoid containing `p` -/

omit [NeZero h] in
theorem Pi_mul_p {p k : ℕ} (hpk : p ^ k = 2 * h + 1) (y : ZMod h) :
    Pi p k ((p : ZMod h) * y) = Pi p k y := by
  unfold Pi
  set F : ℕ → ℤ := fun j => (-1) ^ ((p : ZMod h) ^ j * y).val with hF
  have e : ∀ j, (-1 : ℤ) ^ ((p : ZMod h) ^ j * ((p : ZMod h) * y)).val = F (j + 1) := by
    intro j; simp only [hF]; rw [pow_succ, mul_assoc]
  rw [sum_congr rfl (fun j _ => e j)]
  have e1 := sum_range_succ' F k
  have e2 := sum_range_succ F k
  have hk : F k = F 0 := by simp only [hF]; rw [p_pow_k hpk, pow_zero]
  show ∑ j ∈ range k, F (j + 1) = ∑ j ∈ range k, F j
  linarith

omit [NeZero h] in
theorem adm_one (p k : ℕ) : Adm p k (1 : ZMod h) := fun τ _ => by rw [mul_one]

omit [NeZero h] in
theorem adm_mul {p k : ℕ} {β₁ β₂ : ZMod h} (h1 : Adm p k β₁) (h2 : Adm p k β₂) (hu : IsUnit β₁) :
    Adm p k (β₁ * β₂) := fun τ hτ => by rw [← mul_assoc, h2 _ (hτ.mul hu), h1 τ hτ]

theorem p_unit {p k : ℕ} (hk1 : 1 ≤ k) (hpk : p ^ k = 2 * h + 1) : IsUnit (p : ZMod h) := by
  refine IsUnit.of_mul_eq_one ((p : ZMod h) ^ (k - 1)) ?_
  rw [← pow_succ', Nat.sub_add_cancel hk1, p_pow_k hpk]

theorem adm_ppow {p k : ℕ} (hk1 : 1 ≤ k) (hpk : p ^ k = 2 * h + 1) (j : ℕ) :
    Adm p k ((p : ZMod h) ^ j) := by
  induction j with
  | zero => rw [pow_zero]; exact adm_one p k
  | succ j ih =>
    rw [pow_succ]
    exact adm_mul ih (fun τ _ => by rw [mul_comm, Pi_mul_p hpk]) ((p_unit hk1 hpk).pow j)

/-- `1 + p^c` is a unit modulo `h` (`k` odd). -/
theorem one_add_unit (hh : Odd h) {p k : ℕ} (hk : Odd k) (hpk : p ^ k = 2 * h + 1) (c : ℕ) :
    IsUnit (1 + (p : ZMod h) ^ c) := by
  set w := (p : ZMod h) ^ c
  have hw : w ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, p_pow_k hpk, one_pow]
  have e := mul_neg_geom_sum (-w) k
  rw [sub_neg_eq_add, hk.neg_pow, hw] at e
  obtain ⟨u, hu⟩ := two_unit hh
  refine IsUnit.of_mul_eq_one ((∑ i ∈ range k, (-w) ^ i) * ↑u⁻¹) ?_
  rw [← mul_assoc, e, show (1 : ZMod h) - -1 = 2 by ring, ← hu, Units.mul_inv]

/-! ## The final contradiction: a `p`-adic comparison -/

theorem not_dvd_U {p s t : ℕ} (hp3 : 3 ≤ p) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    (1 + 2 * p ^ s + p ^ t) % p = 1 := by
  have e : 1 + 2 * p ^ s + p ^ t = 1 + p * (2 * p ^ (s - 1) + p ^ (t - 1)) := by
    rw [mul_add, ← mul_assoc, mul_comm p 2, mul_assoc, ← pow_succ', ← pow_succ',
      Nat.sub_add_cancel hs, Nat.sub_add_cancel ht]; ring
  rw [e, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)

theorem pow_mul_inj {p d a U V : ℕ} (hp : 2 ≤ p) (hU : ¬ p ∣ U) (hV : ¬ p ∣ V)
    (e : p ^ d * U = p ^ a * V) : d = a ∧ U = V := by
  have hp0 : 0 < p := by omega
  rcases lt_trichotomy d a with hlt | heq | hgt
  · exfalso; apply hU
    have : p ^ a = p ^ d * p ^ (a - d) := by rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc] at e
    have e' := Nat.eq_of_mul_eq_mul_left (pow_pos hp0 d) e
    rw [e']
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  · subst heq; exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hp0 d) e⟩
  · exfalso; apply hV
    have : p ^ d = p ^ a * p ^ (d - a) := by rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc] at e
    have e' := Nat.eq_of_mul_eq_mul_left (pow_pos hp0 a) e
    rw [← e']
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _

/-- `p^d (1 + 2p^s + p^t) ≠ 2 (p^a + p^b)` for odd `p ≥ 3`, `s, t ≥ 1`. -/
theorem no_eq {p d s t a b : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    p ^ d * (1 + 2 * p ^ s + p ^ t) ≠ 2 * (p ^ a + p ^ b) := by
  wlog hab : a ≤ b generalizing a b
  · intro e; exact this (a := b) (b := a) (by omega) (by rw [e]; ring)
  intro e
  set m := b - a with hm
  have hpb : p ^ b = p ^ a * p ^ m := by rw [← pow_add]; congr 1; omega
  have e' : p ^ d * (1 + 2 * p ^ s + p ^ t) = p ^ a * (2 * (1 + p ^ m)) := by rw [e, hpb]; ring
  have hU := not_dvd_U hp3 hs ht
  have hUd : ¬ p ∣ (1 + 2 * p ^ s + p ^ t) := by
    intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega
  have hps : p ≤ p ^ s := Nat.le_self_pow (by omega) p
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · -- `V = 4`
    rw [hm0, pow_zero] at e'
    have hV : ¬ p ∣ 2 * (1 + 1) := by
      intro hd
      have hc : Nat.Coprime p (2 ^ 2) := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hpodd)
      have := Nat.Coprime.eq_one_of_dvd hc (by simpa using hd)
      omega
    obtain ⟨-, hUV⟩ := pow_mul_inj (by omega) hUd hV e'
    omega
  · have hV2 : (2 * (1 + p ^ m)) % p = 2 := by
      have : 2 * (1 + p ^ m) = 2 + p * (2 * p ^ (m - 1)) := by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm p 2, mul_assoc, ← pow_succ',
          Nat.sub_add_cancel hm0]
      rw [this, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    have hV : ¬ p ∣ 2 * (1 + p ^ m) := by
      intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega
    obtain ⟨-, hUV⟩ := pow_mul_inj (by omega) hUd hV e'
    rw [hUV] at hU; omega


/-! ## Lemma 6.1 -/

/-- **Lemma 6.1, case `ε = 1`.** -/
theorem main_adm (hh : Odd h) (hh1 : 1 < h) {p k : ℕ} (hp3 : 3 ≤ p) (hk : Odd k)
    (hpk : p ^ k = 2 * h + 1) {β : ZMod h} (hA : Adm p k β) :
    ∃ j, j < k ∧ β = (p : ZMod h) ^ j := by
  have hk1 : 1 ≤ k := hk.pos
  have hpodd : Odd p := by
    rcases Nat.even_or_odd p with he | ho
    · exfalso
      obtain ⟨r, hr⟩ := (Nat.even_pow.mpr ⟨he, by omega⟩ : Even (p ^ k))
      omega
    · exact ho
  obtain ⟨a, b, ha, hb, e⟩ := C_of_Adm hh hh1 hp3 hk1 hpk hA
  wlog hab : a ≤ b generalizing a b
  · exact this b a hb ha (by rw [e]; ring) (by omega)
  rcases eq_or_lt_of_le hab with rfl | hlt
  · refine ⟨a, ha, ?_⟩
    have : β.val = p ^ a := by omega
    rw [← ZMod.natCast_zmod_val β, this, Nat.cast_pow]
  exfalso
  set c := b - a with hc
  have hc1 : 1 ≤ c := by omega
  have hck : c < k := by omega
  set β' := (p : ZMod h) ^ (k - a) * β with hβ'
  have hA' : Adm p k β' := adm_mul (adm_ppow hk1 hpk _) hA ((p_unit hk1 hpk).pow _)
  have h2β : (2 : ZMod h) * β = (p : ZMod h) ^ a + (p : ZMod h) ^ b := by
    have := congrArg (Nat.cast : ℕ → ZMod h) e
    push_cast at this; rwa [ZMod.natCast_zmod_val] at this
  have h2β' : (2 : ZMod h) * β' = 1 + (p : ZMod h) ^ c := by
    rw [hβ', show (2 : ZMod h) * ((p : ZMod h) ^ (k - a) * β) =
      (p : ZMod h) ^ (k - a) * (2 * β) by ring, h2β, mul_add, ← pow_add, ← pow_add,
      show k - a + a = k by omega, show k - a + b = k + c by omega, pow_add, p_pow_k hpk, one_mul]
  obtain ⟨B, hB⟩ : ∃ B, 2 * B = 1 + p ^ c := by
    obtain ⟨r, hr⟩ := Odd.add_odd odd_one (hpodd.pow (n := c))
    exact ⟨r, by omega⟩
  have hβB : β' = (B : ZMod h) := by
    apply (two_unit hh).mul_left_cancel
    rw [h2β']
    have := congrArg (Nat.cast : ℕ → ZMod h) hB
    push_cast at this; rw [this]
  have hβu : IsUnit β' := by
    have h1 := one_add_unit hh hk hpk c
    rw [← h2β'] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hA2 := adm_mul hA' hA' hβu
  obtain ⟨e1, e2, -, -, e'⟩ := C_of_Adm hh hh1 hp3 hk1 hpk hA2
  rw [hβB, ← Nat.cast_mul, ZMod.val_natCast] at e'
  have hck2 : 2 * c ≠ k := by obtain ⟨t, ht⟩ := hk; omega
  have hp1 : 1 ≤ p := by omega
  -- `(2B)² = 1 + 2p^c + p^{2c}`
  have hsq : (2 * B) * (2 * B) = 1 + 2 * p ^ c + p ^ (2 * c) := by
    rw [hB, pow_mul]; ring
  rcases lt_or_gt_of_ne hck2 with hlt2 | hgt2
  · -- `2c < k`: `⟨β'²⟩ = B²`
    have hBB : B * B < h := by
      set Q := p ^ (k - 1) with hQ
      have h1 : p ^ c ≤ Q := Nat.pow_le_pow_right hp1 (by omega)
      have h2 : p ^ (2 * c) ≤ Q := Nat.pow_le_pow_right hp1 (by omega)
      have h3 : p ^ k = p * Q := by rw [hQ, ← pow_succ']; congr 1; omega
      have h4 : 3 ≤ Q := by
        calc 3 ≤ p := hp3
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ Q := Nat.pow_le_pow_right hp1 (by omega)
      have h5 : 3 * Q ≤ p * Q := Nat.mul_le_mul_right _ hp3
      have h6 : 4 * (B * B) = 1 + 2 * p ^ c + p ^ (2 * c) := by rw [← hsq]; ring
      linarith
    rw [Nat.mod_eq_of_lt hBB] at e'
    apply no_eq (d := 0) (a := e1) (b := e2) hp3 hpodd hc1 (show 1 ≤ 2 * c by omega)
    rw [pow_zero, one_mul, ← hsq, ← e']; ring
  · -- `2c > k`
    set d := 2 * c - k with hd
    obtain ⟨D, hD⟩ : ∃ D, 2 * D + 1 = p ^ d := by
      obtain ⟨r, hr⟩ := hpodd.pow (n := d); exact ⟨r, hr.symm⟩
    have e2c : p ^ (2 * c) = p ^ k * p ^ d := by rw [← pow_add]; congr 1; omega
    have key : (p ^ k + 2 * p ^ c + p ^ d) + 4 * (h * D) = 4 * (B * B) := by
      have : 4 * (B * B) = (2 * B) * (2 * B) := by ring
      rw [this, hsq, e2c, hpk, ← hD]; ring
    have hle : h * D ≤ B * B := by omega
    set R := B * B - h * D with hR
    have h4R : 4 * R = p ^ k + 2 * p ^ c + p ^ d := by omega
    have hRcast : ((B * B : ℕ) : ZMod h) = (R : ZMod h) := by
      rw [hR, Nat.cast_sub hle, Nat.cast_mul (h : ℕ), ZMod.natCast_self, zero_mul, sub_zero]
    have hRlt : R < h := by
      have hk3 : 3 ≤ k := by omega
      set P := p ^ (k - 2) with hP
      have h1 : p ^ k = p * (p * P) := by rw [hP, ← pow_succ', ← pow_succ']; congr 1; omega
      have h2 : p ^ c ≤ p * P := by
        rw [hP, ← pow_succ']; exact Nat.pow_le_pow_right hp1 (by omega)
      have h3 : p ^ d ≤ P := Nat.pow_le_pow_right hp1 (by omega)
      have h4 : 3 ≤ P := by
        calc 3 ≤ p := hp3
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ P := Nat.pow_le_pow_right hp1 (by omega)
      have h5 : 3 * (p * P) ≤ p * (p * P) := Nat.mul_le_mul_right _ hp3
      have h6 : 3 * P ≤ p * P := Nat.mul_le_mul_right _ hp3
      linarith
    have hval : B * B % h = R := by
      have := congrArg ZMod.val hRcast
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hRlt] at this
    rw [hval] at e'
    apply no_eq (d := d) (s := c - d) (t := k - d) (a := e1) (b := e2) hp3 hpodd (by omega)
      (by omega)
    have : p ^ d * (1 + 2 * p ^ (c - d) + p ^ (k - d)) = p ^ k + 2 * p ^ c + p ^ d := by
      rw [mul_add, mul_add, mul_one, ← mul_assoc, mul_comm (p ^ d) 2, mul_assoc, ← pow_add,
        ← pow_add, show d + (c - d) = c by omega, show d + (k - d) = k by omega]; ring
    rw [this, ← h4R, ← e']; ring

omit [NeZero h] in
theorem Pi_zero (p k : ℕ) : Pi p k (0 : ZMod h) = k := by simp [Pi]

theorem Pi_neg (hh : Odd h) {p k : ℕ} (hk1 : 1 ≤ k) (hpk : p ^ k = 2 * h + 1) {y : ZMod h}
    (hy : y ≠ 0) : Pi p k (-y) = -Pi p k y := by
  unfold Pi
  rw [← sum_neg_distrib]
  refine sum_congr rfl (fun j _ => ?_)
  have hz : (p : ZMod h) ^ j * y ≠ 0 := by
    intro h0
    exact hy (((p_unit hk1 hpk).pow j).mul_right_eq_zero.mp h0)
  have : NeZero ((p : ZMod h) ^ j * y) := ⟨hz⟩
  rw [show (p : ZMod h) ^ j * -y = -((p : ZMod h) ^ j * y) by ring, ZMod.val_neg_of_ne_zero,
    neg_one_pow_eq, neg_one_pow_eq]
  have hlt := ZMod.val_lt ((p : ZMod h) ^ j * y)
  obtain ⟨t, ht⟩ := hh
  have : (h - ((p : ZMod h) ^ j * y).val) % 2 = 1 - ((p : ZMod h) ^ j * y).val % 2 := by omega
  rw [this]
  have : ((p : ZMod h) ^ j * y).val % 2 ≤ 1 := by omega
  push_cast [this]
  ring

omit [NeZero h] in
theorem Pi_two_ne (hh : Odd h) (hh1 : 1 < h) {p k : ℕ} (hk1 : 1 ≤ k) :
    Pi p k (2 : ZMod h) ≠ -k := by
  have hh3 : 3 ≤ h := by obtain ⟨t, ht⟩ := hh; omega
  rw [Pi_eq]
  have hb0 : bit ((p : ZMod h) ^ 0 * 2) = 0 := by
    unfold bit
    rw [pow_zero, one_mul, show (2 : ZMod h) = ((2 : ℕ) : ZMod h) by norm_num, ZMod.val_natCast,
      Nat.mod_eq_of_lt (show 2 < h by omega)]
  have hle : ∑ j ∈ range k, bit ((p : ZMod h) ^ j * 2) ≤ k - 1 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [sum_range_succ', hb0, add_zero]
    calc ∑ j ∈ range k', bit ((p : ZMod h) ^ (j + 1) * 2) ≤ ∑ j ∈ range k', 1 :=
          sum_le_sum (fun j _ => bit_le _)
      _ = k' + 1 - 1 := by simp
  intro he
  have : (∑ j ∈ range k, bit ((p : ZMod h) ^ j * 2) : ℤ) ≤ k - 1 := by
    have := hle; zify [hk1] at this; exact this
  push_cast at he
  linarith

/-- **Lemma 6.1**.  Let `p ≥ 3`, `k` odd, `p^k = 2h + 1` with `h > 1` odd, and `ε = ±1`.
If `Π(τ β) = ε Π(τ)` for every unit `τ` of `ℤ/h`, then `β = ε p^j` for some `j < k`. -/
theorem lemmaL (hh : Odd h) (hh1 : 1 < h) {p k : ℕ} (hp3 : 3 ≤ p) (hk : Odd k)
    (hpk : p ^ k = 2 * h + 1) (β : ZMod h) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hc : ∀ τ : ZMod h, IsUnit τ → Pi p k (τ * β) = ε * Pi p k τ) :
    ∃ j, j < k ∧ β = (ε : ZMod h) * (p : ZMod h) ^ j := by
  have hk1 : 1 ≤ k := hk.pos
  rcases hε with rfl | rfl
  · obtain ⟨j, hj, e⟩ := main_adm hh hh1 hp3 hk hpk (fun τ hτ => by rw [hc τ hτ, one_mul])
    exact ⟨j, hj, by rw [e]; push_cast; ring⟩
  · have hβ : β ≠ 0 := by
      rintro rfl
      have e := hc 2 (two_unit hh)
      rw [mul_zero, Pi_zero] at e
      apply Pi_two_ne hh hh1 (p := p) hk1
      linarith
    have hA : Adm p k (-β) := by
      intro τ hτ
      have hτβ : τ * β ≠ 0 := fun h0 => hβ (hτ.mul_right_eq_zero.mp h0)
      rw [show τ * -β = -(τ * β) by ring, Pi_neg hh hk1 hpk hτβ, hc τ hτ]; ring
    obtain ⟨j, hj, e⟩ := main_adm hh hh1 hp3 hk hpk hA
    exact ⟨j, hj, by rw [← e]; push_cast; ring⟩


/-- Instance `q = 27` (`p = 3`, `k = 3`, `h = 13`): the admissible multipliers are exactly
`1, 3, 9` (the converse direction is `adm_ppow`). -/
theorem lemmaL_27 (β : ZMod 13) (hA : Adm 3 3 β) : β = 1 ∨ β = 3 ∨ β = 9 := by
  obtain ⟨j, hj, rfl⟩ := main_adm (h := 13) (by decide) (by norm_num) (p := 3) (k := 3) le_rfl
    (by decide) (by norm_num) hA
  interval_cases j <;> norm_num

end BSW.LemmaL
