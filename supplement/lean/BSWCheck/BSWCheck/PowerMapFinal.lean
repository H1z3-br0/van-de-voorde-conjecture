module

/-
  Main theorem, stage 3: the three cases and the final statement.
-/
public import Mathlib
public import BSWCheck.PowerMapMain

@[expose] public section

open Finset

namespace BSW

theorem two_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

namespace PMSetup

variable {p n : ℕ} [hp : Fact p.Prime] [NeZero n] (S : PMSetup p n)
include S

/-- `f = gcd(e-1, n)`, `d = n/f`. -/
def f : ℕ := Nat.gcd (S.e - 1) n
def d : ℕ := n / S.f

theorem f_pos : 0 < S.f := Nat.gcd_pos_of_pos_right _ S.n_pos

theorem n_eq_fd : n = S.f * S.d := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm

theorem f_dvd : S.f ∣ S.e - 1 := Nat.gcd_dvd_left _ _

/-- Every element of `P = f·ZMod n` is a center `iη`. -/
theorem center_of_P {b : ZMod n} (hb : b ∈ Pset (n := n) S.f) : ∃ i, b = i * S.η := by
  obtain ⟨j, rfl⟩ := mem_Pset.mp hb
  obtain ⟨u, v, huv⟩ := bezout_zmod (n := n) (S.e - 1) n
  rw [ZMod.natCast_self, zero_mul, add_zero] at huv
  refine ⟨u * j, ?_⟩
  unfold f
  rw [huv, η]
  ring

/-- Elements of `Q = d·ZMod n` are killed by `η`. -/
theorem Q_kills {a : ZMod n} (ha : a ∈ Pset (n := n) S.d) : a * S.η = 0 := by
  obtain ⟨j, rfl⟩ := mem_Pset.mp ha
  obtain ⟨x, hx⟩ := S.f_dvd
  have : (S.d : ZMod n) * j * S.η = ((S.f * S.d : ℕ) : ZMod n) * (j * x) := by
    rw [η, hx]; push_cast; ring
  rw [this, ← S.n_eq_fd, ZMod.natCast_self, zero_mul]

theorem fd_zero : (S.f : ZMod n) * (S.d : ZMod n) = 0 := by
  rw [← Nat.cast_mul, ← S.n_eq_fd, ZMod.natCast_self]

theorem s_mem_P : S.η * (S.ε + 1) ∈ Pset (n := n) S.f := by
  obtain ⟨x, hx⟩ := S.f_dvd
  refine mem_Pset.mpr ⟨(x : ZMod n) * (S.ε + 1), ?_⟩
  rw [η, hx]; push_cast; ring

theorem s_eq_cast : S.η * (S.ε + 1) = (((S.e - 1) * (S.e + 1) : ℕ) : ZMod n) := by
  rw [η, ε]; push_cast; ring

/-- Iterated periodicity. -/
theorem periodic_iter (hη : S.η ≠ 0) (m : ℕ) (j : ZMod n) :
    S.H (j * S.η + (m : ZMod n) * (S.η * (S.ε + 1))) = S.H (j * S.η) := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    have h1 := S.periodic hη (j + (m : ZMod n) * (S.ε + 1))
    have e1 : (j + (m : ZMod n) * (S.ε + 1)) * S.η + S.η * (S.ε + 1)
        = j * S.η + ((m + 1 : ℕ) : ZMod n) * (S.η * (S.ε + 1)) := by push_cast; ring
    have e2 : (j + (m : ZMod n) * (S.ε + 1)) * S.η = j * S.η + (m : ZMod n) * (S.η * (S.ε + 1)) := by
      ring
    rw [e1, e2, ih j] at h1
    exact h1

/-- (б): `gcd(f,d) = 1`. -/
theorem coprime_fd (hη : S.η ≠ 0) : Nat.Coprime S.f S.d := by
  by_contra hG
  have hG1 : 1 < Nat.gcd S.f S.d := by
    have : 0 < Nat.gcd S.f S.d := Nat.gcd_pos_of_pos_left _ S.f_pos
    unfold Nat.Coprime at hG
    omega
  obtain ⟨h1, h2⟩ := nt_coprime S.he S.hodd rfl S.n_eq_fd S.f_pos hG1
  set m := S.d / Nat.gcd S.f S.d
  set a : ZMod n := (((S.e - 1) * (S.e + 1) * m : ℕ) : ZMod n) with ha_def
  have ha0 : a ≠ 0 := by
    rw [ha_def, Ne, ZMod.natCast_eq_zero_iff]
    exact h2
  have hK : a * S.η = 0 := by
    rw [ha_def, η, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rw [mul_comm]
    exact h1
  have ha_s : a = (m : ZMod n) * (S.η * (S.ε + 1)) := by
    rw [ha_def, S.s_eq_cast]; push_cast; ring
  have hodd := S.odd_rel 0 a ha0 hK
  have hp1 : S.H (0 * S.η + a) = S.H (0 * S.η) := by
    rw [ha_s]; exact S.periodic_iter hη m 0
  have hp2 : S.H (0 * S.η - a) = S.H (0 * S.η) := by
    have := S.periodic_iter hη m (-(m : ZMod n) * (S.ε + 1))
    have e1 : -(m : ZMod n) * (S.ε + 1) * S.η + (m : ZMod n) * (S.η * (S.ε + 1)) = 0 * S.η := by ring
    have e2 : -(m : ZMod n) * (S.ε + 1) * S.η = 0 * S.η - a := by rw [ha_s]; ring
    rw [e1, e2] at this
    exact this.symm
  rw [hp1, hp2, ← sq, S.H_sq] at hodd
  exact S.two_ne (by linear_combination hodd)

/-- Oddness at any `b ∈ P` in the form needed for class sums. -/
theorem H_odd_P {b : ZMod n} (hb : b ∈ Pset (n := n) S.f) :
    ∀ a ∈ Pset (n := n) S.d, a ≠ 0 → S.H (b + -a) = -S.H (b + a) := by
  intro a ha ha0
  obtain ⟨i, rfl⟩ := S.center_of_P hb
  rw [← sub_eq_add_neg]
  exact S.H_neg_of_odd i a ha0 (S.Q_kills ha)

/-- Class sums over `Q` on the nonsquare side. -/
theorem class_sum_H {b : ZMod n} (hb : b ∈ Pset (n := n) S.f) :
    ∑ a ∈ Pset (n := n) S.d, S.H (b + a) = S.H b := by
  have := class_sum S.two_ne S.d (fun a => S.H (b + a)) (fun a ha ha0 => S.H_odd_P hb a ha ha0)
  simpa using this

/-! #### Non-hybrid case -/

theorem nonhybrid_false (hη : S.η ≠ 0) (hcop : Nat.Coprime S.f S.d) (hnh : ¬ S.d ∣ S.e + 1) :
    False := by
  have hρ := S.hρ
  have hfd := S.n_eq_fd
  -- 0 < f < n
  have hd1 : S.d ≠ 1 := by intro h; apply hnh; rw [h]; exact one_dvd _
  have hdpos : 0 < S.d := by
    rcases Nat.eq_zero_or_pos S.d with h | h
    · rw [h, mul_zero] at hfd; exact absurd hfd (NeZero.ne n)
    · exact h
  have hfn : S.f < n := by
    have : 2 ≤ S.d := by omega
    nlinarith [S.f_pos]
  -- X_f as an exponent sum
  have hX : X (p := p) n S.f = ∑ i : ZMod n, (S.c * E S.ρ i) ^ S.f * S.H i := by
    unfold X
    rw [sum_nonsq hρ S.hc]
    rfl
  set Y := ∑ b ∈ Pset (n := n) S.f, (S.c * E S.ρ b) ^ S.f * S.H b with hY
  have hXY : X (p := p) n S.f = Y := by
    rw [hX, sum_decomp hfd hcop]
    refine Finset.sum_congr rfl fun b hb => ?_
    have : ∀ a ∈ Pset (n := n) S.d,
        (S.c * E S.ρ (b + a)) ^ S.f * S.H (b + a) = (S.c * E S.ρ b) ^ S.f * S.H (b + a) := by
      intro a ha
      obtain ⟨j, rfl⟩ := mem_Pset.mp ha
      have hEa : E S.ρ ((S.d : ZMod n) * j) ^ S.f = 1 := by
        rw [E_pow hρ, show (S.d : ZMod n) * j * (S.f : ZMod n) = ((S.f : ZMod n) * (S.d : ZMod n)) * j by ring,
          S.fd_zero, zero_mul, E_zero]
      rw [E_add hρ, show S.c * (E S.ρ b * E S.ρ ((S.d : ZMod n) * j)) = (S.c * E S.ρ b) * E S.ρ ((S.d : ZMod n) * j) by ring,
        mul_pow, hEa, mul_one]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, S.class_sum_H hb]
  -- shift invariance of Y
  have hshift : Y = E S.ρ (S.η * (S.ε + 1)) ^ S.f * Y := by
    calc Y = ∑ b ∈ Pset (n := n) S.f, (S.c * E S.ρ (b + S.η * (S.ε + 1))) ^ S.f * S.H (b + S.η * (S.ε + 1)) := by
          rw [hY]; exact sum_P_shift S.f S.s_mem_P _
      _ = ∑ b ∈ Pset (n := n) S.f, E S.ρ (S.η * (S.ε + 1)) ^ S.f * ((S.c * E S.ρ b) ^ S.f * S.H b) := by
          refine Finset.sum_congr rfl fun b hb => ?_
          obtain ⟨i, rfl⟩ := S.center_of_P hb
          rw [S.periodic hη i, E_add hρ]
          ring
      _ = E S.ρ (S.η * (S.ε + 1)) ^ S.f * Y := by rw [hY, Finset.mul_sum]
  have hne : E S.ρ (S.η * (S.ε + 1)) ^ S.f ≠ 1 := by
    rw [E_pow hρ, Ne, E_eq_one_iff hρ, S.s_eq_cast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact nt_nonhybrid rfl hfd S.f_pos hcop hnh
  have hY0 : Y = 0 := by
    have : (E S.ρ (S.η * (S.ε + 1)) ^ S.f - 1) * Y = 0 := by linear_combination -hshift
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have h2X := two_mul_X_lt (p := p) S.hpn S.f_pos hfn
  rw [hXY, hY0, mul_zero] at h2X
  have hc := choose_ne_zero (p := p) S.hpn hfn.le
  have : ((-1 : ZMod p) ^ S.f) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact (mul_ne_zero this hc) h2X.symm

/-! #### Hybrid case -/

theorem b_mul_eps {b : ZMod n} (hb : b ∈ Pset (n := n) S.f) (hh : S.d ∣ S.e + 1) :
    b * S.ε = -b := by
  obtain ⟨j, rfl⟩ := mem_Pset.mp hb
  obtain ⟨t, ht⟩ := hh
  have : (S.f : ZMod n) * j * (S.ε + 1) = 0 := by
    have : (S.f : ZMod n) * j * (S.ε + 1) = ((S.f : ZMod n) * (S.d : ZMod n)) * (t * j) := by
      rw [ε]
      have : ((S.e : ℕ) : ZMod n) + 1 = ((S.e + 1 : ℕ) : ZMod n) := by push_cast; ring
      rw [this, ht]; push_cast; ring
    rw [this, S.fd_zero, zero_mul]
  linear_combination this

theorem Hs_odd_P (hcop : Nat.Coprime S.f S.d) (hh : S.d ∣ S.e + 1) {b : ZMod n}
    (hb : b ∈ Pset (n := n) S.f) :
    ∀ a ∈ Pset (n := n) S.d, a ≠ 0 → S.Hs (b + -a) = -S.Hs (b + a) := by
  intro a ha ha0
  have hρ := S.hρ
  have hfd := S.n_eq_fd
  have ha' : a + b ≠ 0 := by
    intro h
    have := decomp_unique hfd hcop hb ha (zero_mem_Pset S.f) (zero_mem_Pset S.d)
      (by rw [add_comm]; simpa using h)
    exact ha0 this.2
  obtain ⟨i, hi⟩ := S.center_of_P hb
  have hm := S.master i (a + b) ha'
  have haε : a * S.ε = a := by rw [← S.η_add_one, mul_add, S.Q_kills ha, mul_one, zero_add]
  have hbε := S.b_mul_eps hb hh
  have e1 : i * S.η + (a + b) * S.ε = 0 * S.η + a := by rw [add_mul, haε, hbε, ← hi]; ring
  have e2 : i * S.η - (a + b) = 0 * S.η - a := by rw [← hi]; ring
  rw [e1, e2] at hm
  have hodd := S.odd_rel 0 a ha0 (S.Q_kills ha)
  have hA : S.A (a + b) = 1 := by linear_combination -hm + S.A (a + b) * hodd
  -- A(a+b) = Hs(a+b) Hs(a-b)
  have hA' : S.A (a + b) = S.Hs (a + b) * S.Hs (a - b) := by
    unfold A
    rw [mul_pow, S.one_sub_pow, add_mul, haε, hbε, ← sub_eq_add_neg, S.one_sub_pow]
    ring
  have hneg : S.Hs (a - b) = -S.Hs (b + -a) := by
    rw [show a - b = -(b + -a) by ring, S.Hs_neg]
  rw [hA, hneg, add_comm a b] at hA'
  have hsq := S.Hs_sq (show b + a ≠ 0 by rwa [add_comm])
  linear_combination (S.Hs (b + a)) * hA' - S.Hs (b + -a) * hsq

theorem class_sum_Hs (hcop : Nat.Coprime S.f S.d) (hh : S.d ∣ S.e + 1) {b : ZMod n}
    (hb : b ∈ Pset (n := n) S.f) :
    ∑ a ∈ Pset (n := n) S.d, S.Hs (b + a) = S.Hs b := by
  have := class_sum S.two_ne S.d (fun a => S.Hs (b + a)) (fun a ha ha0 => S.Hs_odd_P hcop hh hb a ha ha0)
  simpa using this

/-- `∑_i [Hs(i)Hs(i+δ) + H(i)H(i+δ)] = -2`. -/
theorem autocorr_exp (δ : ZMod n) :
    ∑ i : ZMod n, (S.Hs i * S.Hs (i + δ) + S.H i * S.H (i + δ)) = -2 := by
  have hρ := S.hρ
  have h := autocorr (p := p) S.hpn S.hodd (E_pow_n hρ δ)
  rw [sum_erase_zero_split S.hpn, sum_sq hρ, sum_nonsq hρ S.hc] at h
  rw [Finset.sum_add_distrib, ← h]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold Hs
    rw [E_add hρ, mul_comm (E S.ρ i) (E S.ρ δ)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold H
    rw [E_add hρ]
    ring_nf

theorem hybrid_false (hη : S.η ≠ 0) (hcop : Nat.Coprime S.f S.d) (hh : S.d ∣ S.e + 1)
    (hf1 : S.f ≠ 1) : False := by
  have hρ := S.hρ
  have hfd := S.n_eq_fd
  set P := Pset (n := n) S.f
  set Q := Pset (n := n) S.d
  -- d ≥ 2 (else η = 0) and f ≥ 2
  have hd1 : S.d ≠ 1 := by
    intro h
    apply hη
    obtain ⟨x, hx⟩ := S.f_dvd
    rw [η, hx, Nat.cast_mul]
    have hfn : S.f = n := by
      have := hfd
      rw [h, mul_one] at this
      exact this.symm
    have : (S.f : ZMod n) = 0 := by
      rw [hfn, ZMod.natCast_self]
    rw [this, zero_mul]
  have hdpos : 0 < S.d := by
    rcases Nat.eq_zero_or_pos S.d with h | h
    · rw [h, mul_zero] at hfd; exact absurd hfd (NeZero.ne n)
    · exact h
  have hf2 : 2 ≤ S.f := by have := S.f_pos; omega
  have hd2 : 2 ≤ S.d := by omega
  -- the two ways of computing T
  set T := ∑ b ∈ P, ((∑ a ∈ Q, S.Hs (b + a)) ^ 2 + (∑ a ∈ Q, S.H (b + a)) ^ 2) with hT
  have way1 : T = 2 * (P.card : ZMod p) - 1 := by
    rw [hT]
    rw [Finset.sum_congr rfl fun b hb => by rw [S.class_sum_Hs hcop hh hb, S.class_sum_H hb]]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ b ∈ P, S.H b ^ 2 = P.card := by
      rw [Finset.sum_congr rfl fun b _ => S.H_sq b, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ b ∈ P, S.Hs b ^ 2 = (P.card : ZMod p) - 1 := by
      rw [← Finset.add_sum_erase _ _ (zero_mem_Pset S.f), S.Hs_zero,
        Finset.sum_congr rfl fun b hb => S.Hs_sq (Finset.mem_erase.mp hb).1, Finset.sum_const,
        nsmul_eq_mul, mul_one, Finset.card_erase_of_mem (zero_mem_Pset S.f),
        Nat.cast_sub (Finset.card_pos.mpr ⟨0, zero_mem_Pset S.f⟩)]
      push_cast
      ring
    rw [h1, h2]; ring
  have way2 : T = -2 * (Q.card : ZMod p) := by
    have sq_expand : ∀ (G : ZMod n → ZMod p) (b : ZMod n),
        (∑ a ∈ Q, G (b + a)) ^ 2 = ∑ a ∈ Q, ∑ δ ∈ Q, G (b + a) * G (b + a + δ) := by
      intro G b
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mul_sum, sum_Q_shift S.d ha]
      refine Finset.sum_congr rfl fun δ _ => ?_
      congr 2
      ring
    let F : ZMod n → ZMod n → ZMod p := fun i δ => S.Hs i * S.Hs (i + δ) + S.H i * S.H (i + δ)
    have hT' : T = ∑ b ∈ P, ∑ a ∈ Q, ∑ δ ∈ Q, F (b + a) δ := by
      rw [hT]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [sq_expand (fun i => S.Hs i) b, sq_expand (fun i => S.H i) b, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
    rw [hT']
    calc ∑ b ∈ P, ∑ a ∈ Q, ∑ δ ∈ Q, F (b + a) δ
        = ∑ b ∈ P, ∑ δ ∈ Q, ∑ a ∈ Q, F (b + a) δ :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ δ ∈ Q, ∑ b ∈ P, ∑ a ∈ Q, F (b + a) δ := Finset.sum_comm
      _ = ∑ δ ∈ Q, ∑ i : ZMod n, F i δ :=
          Finset.sum_congr rfl fun δ _ => (sum_decomp hfd hcop (fun i => F i δ)).symm
      _ = ∑ δ ∈ Q, (-2 : ZMod p) := Finset.sum_congr rfl fun δ _ => S.autocorr_exp δ
      _ = -2 * (Q.card : ZMod p) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : P.card * Q.card = n := card_P_mul_card_Q hfd hcop
  have hfn : S.f < n := by nlinarith
  have hdn : S.d < n := by nlinarith
  have hP2 : 2 ≤ P.card := by
    have : 1 < P.card := by
      refine Finset.one_lt_card.mpr ⟨0, zero_mem_Pset S.f, (S.f : ZMod n), mem_Pset.mpr ⟨1, by ring⟩, ?_⟩
      intro h
      have := (ZMod.natCast_eq_zero_iff S.f n).mp h.symm
      exact absurd (Nat.le_of_dvd S.f_pos this) (by omega)
    omega
  have hQ2 : 2 ≤ Q.card := by
    have : 1 < Q.card := by
      refine Finset.one_lt_card.mpr ⟨0, zero_mem_Pset S.d, (S.d : ZMod n), mem_Pset.mpr ⟨1, by ring⟩, ?_⟩
      intro h
      have := (ZMod.natCast_eq_zero_iff S.d n).mp h.symm
      exact absurd (Nat.le_of_dvd hdpos this) (by omega)
    omega
  have heq : ((2 * P.card + 2 * Q.card - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    linear_combination way1.symm.trans way2
  rw [ZMod.natCast_eq_zero_iff] at heq
  have hle := Nat.le_of_dvd (by omega) heq
  have hpq : P.card + Q.card ≤ P.card * Q.card := by nlinarith
  have := S.hpn
  omega

/-! #### The case `e ≡ 1 (mod n)` -/

theorem e1_462 (hη : S.η = 0) (hn3 : 3 ≤ n) : (462 : ZMod p) = 0 := by
  have hρ := S.hρ
  have hK : ∀ a : ZMod n, a * S.η = 0 := by intro a; rw [hη, mul_zero]
  have Hneg : ∀ a : ZMod n, a ≠ 0 → S.H (-a) = -S.H a := by
    intro a ha
    have := S.H_neg_of_odd 0 a ha (hK a)
    simpa using this
  set L : ℕ → ZMod p := fun m => ∑ i : ZMod n, E S.ρ i ^ m * S.H i with hL
  have hXm : ∀ m, X (p := p) n m = S.c ^ m * L m := by
    intro m
    unfold X
    rw [sum_nonsq hρ S.hc, hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold H
    ring
  have hrefl : ∀ m, ∑ i : ZMod n, E S.ρ i ^ m * S.H (-i) = 2 * S.H 0 - L m := by
    intro m
    have : ∑ i : ZMod n, (E S.ρ i ^ m * S.H (-i) + E S.ρ i ^ m * S.H i) = 2 * S.H 0 := by
      rw [Finset.sum_eq_single 0]
      · simp [E_zero]; ring
      · intro i _ hi; rw [Hneg i hi]; ring
      · simp
    rw [Finset.sum_add_distrib] at this
    rw [hL]
    linear_combination this
  have hEm : ∀ (i : ZMod n) (m : ℕ), m ≤ 2 * n → E S.ρ i ^ (2 * n - m) = E S.ρ (-i) ^ m := by
    intro i m hm
    have h1 := E_mul_E_neg hρ i
    have h2 : E S.ρ i ^ (2 * n) = 1 := by rw [pow_mul', E_pow_n hρ, one_pow]
    calc E S.ρ i ^ (2 * n - m) = E S.ρ i ^ (2 * n - m) * (E S.ρ i * E S.ρ (-i)) ^ m := by rw [h1, one_pow, mul_one]
      _ = E S.ρ i ^ (2 * n - m + m) * E S.ρ (-i) ^ m := by rw [mul_pow, pow_add]; ring
      _ = E S.ρ (-i) ^ m := by rw [Nat.sub_add_cancel hm, h2, one_mul]
  have hmir : ∀ m ≤ 2 * n, X (p := p) n (2 * n - m) = S.c ^ (2 * n - m) * (2 * S.H 0 - L m) := by
    intro m hm
    unfold X
    rw [sum_nonsq hρ S.hc, ← hrefl m, Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.neg (ZMod n)) (fun i => S.c ^ (2 * n - m) * (E S.ρ i ^ m * S.H (-i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.neg_apply, neg_neg]
    rw [mul_pow, hEm i m hm]
    unfold H
    ring
  -- H(0) = 1
  have hH0 : S.H 0 = 1 := by
    have h0 := hrefl 0
    have hL0 : L 0 = 1 := by
      have := hXm 0
      rw [X_zero S.hpn S.hodd, pow_zero, one_mul] at this
      exact this.symm
    have hsym : ∑ i : ZMod n, E S.ρ i ^ 0 * S.H (-i) = L 0 := by
      rw [hL]
      simp only [pow_zero, one_mul]
      exact Equiv.sum_comp (Equiv.neg (ZMod n)) (fun i => S.H i)
    rw [hsym, hL0] at h0
    have : (2 : ZMod p) * (S.H 0 - 1) = 0 := by linear_combination -h0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h S.two_ne
    · exact sub_eq_zero.mp h
  have hcpow : S.c ^ (2 * n) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one S.c_ne_zero
    rwa [show p - 1 = 2 * n by have := S.hpn; omega] at this
  -- relations for m = 1, 2
  have rel : ∀ m, 0 < m → m < n → (1 + S.c ^ (2 * m)) * L m = 2 ∧
      2 * S.c ^ m * L m = (-1) ^ m * (n.choose m : ZMod p) := by
    intro m hm0 hmn
    have hA := two_mul_X_lt (p := p) S.hpn hm0 hmn
    have hB := two_mul_X_mirror (p := p) S.hpn S.hodd hm0 hmn
    rw [hXm] at hA
    rw [hmir m (by omega), hH0] at hB
    refine ⟨?_, by linear_combination hA⟩
    -- c^(2n-m) (2 - L) = c^m L  ⟹  (2 - L) = c^(2m) L
    have hsplit : S.c ^ (2 * n - m) * S.c ^ m = 1 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega), hcpow]
    have e1 : S.c ^ (2 * n - m) * (2 * 1 - L m) = S.c ^ m * L m := by
      have : (2 : ZMod p) * (S.c ^ (2 * n - m) * (2 * 1 - L m) - S.c ^ m * L m) = 0 := by
        linear_combination hB - hA
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h S.two_ne
      · exact sub_eq_zero.mp h
    have : (2 - L m) = S.c ^ (2 * m) * L m := by
      linear_combination (S.c ^ m) * e1 - (2 * 1 - L m) * hsplit
    linear_combination -this
  obtain ⟨h1, h2⟩ := rel 1 (by norm_num) (by omega)
  obtain ⟨h3, h4⟩ := rel 2 (by norm_num) (by omega)
  have h5 : 2 * (n.choose 2 : ZMod p) = (n : ZMod p) * ((n : ZMod p) - 1) := by
    have := two_choose_two n
    have h' : ((2 * n.choose 2 : ℕ) : ZMod p) = ((n * (n - 1) : ℕ) : ZMod p) := by rw [this]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at h'
    exact h'
  have h6 : 2 * (n : ZMod p) + 1 = 0 := by
    have : ((2 * n + 1 : ℕ) : ZMod p) = 0 := by rw [← S.hpn, ZMod.natCast_self]
    push_cast at this
    exact this
  rw [Nat.choose_one_right] at h2
  simp only [pow_one, mul_one] at h1 h2
  rw [show 2 * 2 = 4 by norm_num] at h3
  generalize S.c = c at h1 h2 h3 h4
  generalize L 1 = L1 at h1 h2
  generalize L 2 = L2 at h3 h4
  generalize (n.choose 2 : ZMod p) = C2 at h4 h5
  generalize (n : ZMod p) = N at h2 h5 h6
  linear_combination
    (6144*c*L1*L2 + 1024*c*L2^2 - 2240*c*L2 + 8192*L2^2 - 17920*L2) * h1
    + (-3072*c^2*L1*L2 - 512*c^2*L2^2 + 1120*c^2*L2 - 4096*c*L2^2 + 8960*c*L2 - 3072*L1*L2
        - 512*L2^2 + 7264*L2) * h2
    + (-8192*L1*L2 + 16128*L2) * h3
    + (4096*c^2*L1*L2 - 8064*c^2*L2 - 128*L2 - 1232) * h4
    + (2048*c^2*L1*L2 - 4032*c^2*L2 - 64*L2 - 616) * h5
    + (1024*c^2*L1*L2*N + 256*c^2*L2^2 - 2016*c^2*L2*N + 2464*c^2*L2 + 2048*c*L2^2 - 4480*c*L2
        + 1536*L1*L2 + 256*L2^2 - 32*L2*N - 3584*L2 - 308*N + 462) * h6

end PMSetup

end BSW
