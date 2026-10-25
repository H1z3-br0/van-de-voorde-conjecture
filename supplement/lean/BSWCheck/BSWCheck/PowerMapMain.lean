module

/-
  Main theorem, stage 2: arithmetic of `f = gcd(e-1,n)`, `d = n/f`; decomposition `ZMod n = P ⊕ Q`
  (`P = fℤ/n`, `Q = dℤ/n`); class sums; the three cases (non-hybrid / hybrid / `e ≡ 1`); final theorem.
-/
public import Mathlib
public import BSWCheck.PowerMap

@[expose] public section

open Finset

namespace BSW

/-! ### Elementary arithmetic -/

/-- With `e - 1 = f x`, `n = f d`, `f = gcd(e-1,n)`: `gcd(x,d) = 1`. -/
theorem coprime_x_d {e n f d x : ℕ} (hf : f = Nat.gcd (e - 1) n) (hfd : n = f * d)
    (hx : e - 1 = f * x) (hfpos : 0 < f) : Nat.Coprime x d := by
  have : f = f * Nat.gcd x d := by
    conv_lhs => rw [hf, hx, hfd]
    rw [Nat.gcd_mul_left]
  have : Nat.gcd x d = 1 := by
    have h := this
    nlinarith [Nat.pos_of_ne_zero (show Nat.gcd x d ≠ 0 from fun h0 => by rw [h0] at h; omega)]
  exact this

/-- (б) arithmetic: if `G = gcd(f,d) > 1`, then `a* = (e-1)(e+1)(d/G)` satisfies `n ∣ (e-1) a*`
but `n ∤ a*`. -/
theorem nt_coprime {e n f d : ℕ} (he : 1 ≤ e) (hodd : Odd n) (hf : f = Nat.gcd (e - 1) n)
    (hfd : n = f * d) (hfpos : 0 < f) (hG : 1 < Nat.gcd f d) :
    n ∣ (e - 1) * ((e - 1) * (e + 1) * (d / Nat.gcd f d)) ∧
      ¬ n ∣ (e - 1) * (e + 1) * (d / Nat.gcd f d) := by
  set G := Nat.gcd f d with hGdef
  obtain ⟨x, hx⟩ : f ∣ e - 1 := hf ▸ Nat.gcd_dvd_left _ _
  obtain ⟨f', hf'⟩ : G ∣ f := Nat.gcd_dvd_left _ _
  obtain ⟨d', hd'⟩ : G ∣ d := Nat.gcd_dvd_right _ _
  have hGpos : 0 < G := by omega
  have hdG : d / G = d' := by rw [hd', Nat.mul_div_cancel_left _ hGpos]
  rw [hdG]
  constructor
  · refine ⟨f' * x * x * (e + 1), ?_⟩
    rw [hx, hfd, hd', hf']
    ring
  · intro hdiv
    have hcop := coprime_x_d hf hfd hx hfpos
    -- n = f * G * d'
    have h1 : f * (G * d') ∣ f * (x * (e + 1) * d') := by
      have : (e - 1) * (e + 1) * d' = f * (x * (e + 1) * d') := by rw [hx]; ring
      rw [← hd', ← hfd, ← this]
      exact hdiv
    have h2 : G * d' ∣ x * (e + 1) * d' := Nat.dvd_of_mul_dvd_mul_left hfpos h1
    have hd'pos : 0 < d' := by
      rcases Nat.eq_zero_or_pos d' with h | h
      · exfalso
        rw [h, mul_zero] at hd'
        rw [hd', mul_zero] at hfd
        exact absurd hfd (by have := hodd.pos; omega)
      · exact h
    have h3 : G ∣ x * (e + 1) := Nat.dvd_of_mul_dvd_mul_right hd'pos h2
    have hGx : Nat.Coprime G x :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right f d) (Nat.Coprime.symm hcop)
    have h4 : G ∣ e + 1 := hGx.dvd_of_dvd_mul_left h3
    have h5 : G ∣ e - 1 := dvd_trans (Nat.gcd_dvd_left f d) ⟨x, hx⟩
    have h6 : G ∣ (e + 1) - (e - 1) := Nat.dvd_sub h4 h5
    rw [show e + 1 - (e - 1) = 2 by omega] at h6
    have hGodd : Odd G := Odd.of_dvd_nat hodd (dvd_trans (Nat.gcd_dvd_right f d) ⟨f, by rw [hfd]; ring⟩)
    have : G ≤ 2 := Nat.le_of_dvd (by norm_num) h6
    have hG2 : G = 2 := by omega
    obtain ⟨k, hk⟩ := hGodd
    omega

/-- Non-hybrid arithmetic: `gcd(f,d) = 1`, `d ∤ e+1` ⟹ `n ∤ (e-1)(e+1) f`. -/
theorem nt_nonhybrid {e n f d : ℕ} (hf : f = Nat.gcd (e - 1) n) (hfd : n = f * d) (hfpos : 0 < f)
    (hcop : Nat.Coprime f d) (hnh : ¬ d ∣ e + 1) : ¬ n ∣ (e - 1) * (e + 1) * f := by
  intro hdiv
  obtain ⟨x, hx⟩ : f ∣ e - 1 := hf ▸ Nat.gcd_dvd_left _ _
  have hxd := coprime_x_d hf hfd hx hfpos
  have h1 : f * d ∣ f * (x * (e + 1) * f) := by
    rw [← hfd, show f * (x * (e + 1) * f) = (e - 1) * (e + 1) * f by rw [hx]; ring]
    exact hdiv
  have h2 : d ∣ x * (e + 1) * f := Nat.dvd_of_mul_dvd_mul_left hfpos h1
  have h3 : d ∣ x * (e + 1) := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right h2
  exact hnh ((Nat.Coprime.symm hxd).dvd_of_dvd_mul_left h3)

/-- `C(n,k) ≢ 0 (mod p)` for `k ≤ n < p`. -/
theorem choose_ne_zero {p n k : ℕ} [hp : Fact p.Prime] (hpn : p = 2 * n + 1) (hk : k ≤ n) :
    (n.choose k : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h1 : p ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  rw [hp.out.dvd_factorial] at h1
  omega

/-! ### Decomposition `ZMod n = P ⊕ Q` -/

section Decomp
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Bezout in `ZMod n`. -/
theorem bezout_zmod (a b : ℕ) : ∃ u v : ZMod n,
    ((Nat.gcd a b : ℕ) : ZMod n) = (a : ZMod n) * u + (b : ZMod n) * v := by
  refine ⟨(Nat.gcdA a b : ZMod n), (Nat.gcdB a b : ZMod n), ?_⟩
  have h := Nat.gcd_eq_gcd_ab a b
  have h2 : (((Nat.gcd a b : ℕ) : ℤ) : ZMod n)
      = (((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b : ℤ) : ZMod n) := by rw [h]
  push_cast at h2
  exact h2

/-- `P = f·ZMod n`. -/
def Pset (f : ℕ) : Finset (ZMod n) := univ.image (fun j : ZMod n => (f : ZMod n) * j)

theorem mem_Pset {f : ℕ} {b : ZMod n} : b ∈ Pset f ↔ ∃ j, b = (f : ZMod n) * j := by
  simp [Pset, eq_comm]

theorem Pset_add {f : ℕ} {b b' : ZMod n} (hb : b ∈ Pset f) (hb' : b' ∈ Pset f) :
    b + b' ∈ Pset f := by
  obtain ⟨j, rfl⟩ := mem_Pset.mp hb
  obtain ⟨j', rfl⟩ := mem_Pset.mp hb'
  exact mem_Pset.mpr ⟨j + j', by ring⟩

theorem Pset_neg {f : ℕ} {b : ZMod n} (hb : b ∈ Pset f) : -b ∈ Pset f := by
  obtain ⟨j, rfl⟩ := mem_Pset.mp hb
  exact mem_Pset.mpr ⟨-j, by ring⟩

theorem zero_mem_Pset (f : ℕ) : (0 : ZMod n) ∈ Pset f := mem_Pset.mpr ⟨0, by ring⟩

variable {f d : ℕ} (hfd : n = f * d) (hcop : Nat.Coprime f d)
include hfd hcop

omit hfd in
theorem decomp_exists (i : ZMod n) : ∃ b ∈ Pset (n := n) f, ∃ a ∈ Pset (n := n) d, b + a = i := by
  obtain ⟨u, v, huv⟩ := bezout_zmod (n := n) f d
  rw [hcop, Nat.cast_one] at huv
  refine ⟨(f : ZMod n) * (u * i), mem_Pset.mpr ⟨_, rfl⟩, (d : ZMod n) * (v * i), mem_Pset.mpr ⟨_, rfl⟩, ?_⟩
  linear_combination -i * huv

theorem decomp_unique {b₁ a₁ b₂ a₂ : ZMod n} (hb₁ : b₁ ∈ Pset (n := n) f) (ha₁ : a₁ ∈ Pset (n := n) d)
    (hb₂ : b₂ ∈ Pset (n := n) f) (ha₂ : a₂ ∈ Pset (n := n) d) (h : b₁ + a₁ = b₂ + a₂) :
    b₁ = b₂ ∧ a₁ = a₂ := by
  obtain ⟨j₁, rfl⟩ := mem_Pset.mp hb₁
  obtain ⟨k₁, rfl⟩ := mem_Pset.mp ha₁
  obtain ⟨j₂, rfl⟩ := mem_Pset.mp hb₂
  obtain ⟨k₂, rfl⟩ := mem_Pset.mp ha₂
  obtain ⟨u, v, huv⟩ := bezout_zmod (n := n) f d
  rw [hcop, Nat.cast_one] at huv
  have hn0 : ((f : ZMod n) * (d : ZMod n)) = 0 := by
    rw [← Nat.cast_mul, ← hfd, ZMod.natCast_self]
  -- z = f(j₁ - j₂) = d(k₂ - k₁) is killed by both f and d
  have hz : (f : ZMod n) * (j₁ - j₂) = 0 := by
    have e1 : (f : ZMod n) * (j₁ - j₂) = (d : ZMod n) * (k₂ - k₁) := by linear_combination h
    linear_combination ((f : ZMod n) * (j₁ - j₂)) * huv + (u * (f : ZMod n)) * e1
      + (u * (k₂ - k₁) + v * (j₁ - j₂)) * hn0
  constructor
  · linear_combination hz
  · linear_combination h - hz

/-- Sum over `ZMod n` as a double sum over `P × Q`. -/
theorem sum_decomp {R : Type*} [AddCommMonoid R] (F : ZMod n → R) :
    ∑ i : ZMod n, F i = ∑ b ∈ Pset (n := n) f, ∑ a ∈ Pset (n := n) d, F (b + a) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun ba _ => ba.1 + ba.2) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨b₁, a₁⟩ h₁ ⟨b₂, a₂⟩ h₂ heq
    rw [Finset.mem_product] at h₁ h₂
    obtain ⟨e1, e2⟩ := decomp_unique hfd hcop h₁.1 h₁.2 h₂.1 h₂.2 heq
    exact Prod.ext e1 e2
  · intro i _
    obtain ⟨b, hb, a, ha, rfl⟩ := decomp_exists hcop i
    exact ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, rfl⟩

theorem card_P_mul_card_Q : (Pset (n := n) f).card * (Pset (n := n) d).card = n := by
  rw [← Finset.card_product]
  have : (Pset (n := n) f ×ˢ Pset (n := n) d).card = (univ : Finset (ZMod n)).card := by
    refine Finset.card_bij (fun ba _ => ba.1 + ba.2) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · rintro ⟨b₁, a₁⟩ h₁ ⟨b₂, a₂⟩ h₂ heq
      rw [Finset.mem_product] at h₁ h₂
      obtain ⟨e1, e2⟩ := decomp_unique hfd hcop h₁.1 h₁.2 h₂.1 h₂.2 heq
      exact Prod.ext e1 e2
    · intro i _
      obtain ⟨b, hb, a, ha, rfl⟩ := decomp_exists hcop i
      exact ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, rfl⟩
  rw [this, Finset.card_univ, ZMod.card]

end Decomp

/-- Odd class sums: if `G(-a) = -G(a)` for nonzero `a ∈ Q` (char ≠ 2), then `∑_{a∈Q} G a = G 0`. -/
theorem class_sum {n p : ℕ} [NeZero n] [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (d : ℕ)
    (G : ZMod n → ZMod p) (hodd : ∀ a ∈ Pset (n := n) d, a ≠ 0 → G (-a) = -G a) :
    ∑ a ∈ Pset (n := n) d, G a = G 0 := by
  rw [← Finset.add_sum_erase _ _ (zero_mem_Pset d)]
  suffices hT : ∑ a ∈ (Pset (n := n) d).erase 0, G a = 0 by rw [hT, add_zero]
  set T := ∑ a ∈ (Pset (n := n) d).erase 0, G a with hTdef
  have hneg : T = ∑ a ∈ (Pset (n := n) d).erase 0, G (-a) := by
    refine Finset.sum_nbij' (fun a => -a) (fun a => -a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_erase] at ha ⊢
      exact ⟨neg_ne_zero.mpr ha.1, Pset_neg ha.2⟩
    · intro a ha
      simp only [Finset.mem_erase] at ha ⊢
      exact ⟨neg_ne_zero.mpr ha.1, Pset_neg ha.2⟩
    · intro a _; simp
    · intro a _; simp
    · intro a _; simp
  have hT2 : T = -T := by
    calc T = ∑ a ∈ (Pset (n := n) d).erase 0, G (-a) := hneg
      _ = ∑ a ∈ (Pset (n := n) d).erase 0, -G a :=
          Finset.sum_congr rfl (fun a ha => by
            have ha' := Finset.mem_erase.mp ha
            exact hodd a ha'.2 ha'.1)
      _ = -T := by rw [Finset.sum_neg_distrib]
  have : (2 : ZMod p) * T = 0 := by linear_combination hT2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2
  · exact h

/-- Shift invariance of a sum over `P` by an element of `P`. -/
theorem sum_P_shift {n : ℕ} [NeZero n] {R : Type*} [AddCommMonoid R] (f : ℕ) {s : ZMod n}
    (hs : s ∈ Pset (n := n) f) (F : ZMod n → R) :
    ∑ b ∈ Pset (n := n) f, F b = ∑ b ∈ Pset (n := n) f, F (b + s) := by
  symm
  refine Finset.sum_nbij' (fun b => b + s) (fun b => b - s) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact Pset_add hb hs
  · intro b hb
    rw [sub_eq_add_neg]
    exact Pset_add hb (Pset_neg hs)
  · intro b _; simp
  · intro b _; simp
  · intro b _; rfl

theorem sum_Q_shift {n : ℕ} [NeZero n] {R : Type*} [AddCommMonoid R] (d : ℕ) {s : ZMod n}
    (hs : s ∈ Pset (n := n) d) (F : ZMod n → R) :
    ∑ b ∈ Pset (n := n) d, F b = ∑ b ∈ Pset (n := n) d, F (b + s) :=
  sum_P_shift d hs F

end BSW
