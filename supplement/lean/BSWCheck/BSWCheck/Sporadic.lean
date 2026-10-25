module

public import Mathlib
public import BSWCheck.Basics
public import BSWCheck.Bridge

@[expose] public section

/-!
# Sporadic solutions: the bound `q > 31` cannot be lowered (kernel-checked witnesses)

For `p = 7, 11, 19, 23, 31` an explicit **non-elliptic admissible map** (the first stored solution of
`artifacts/small/q_p.txt`) is verified by the kernel (`decide +kernel`, no `native_decide`):
`BSW.Sporadic.sporadic_p` states `Admissible ψ ∧ ¬ ∃ n, ∀ x ≠ 0, ψ x = n / x`.
-/

namespace BSW.Sporadic

open BSW.Basic BSW.Bridge

/-- Decidable power form of admissibility in `ZMod p` (Euler's criterion). -/
def AdmPow (p : ℕ) (ψ : ZMod p → ZMod p) : Prop :=
  (∀ x : ZMod p, x ≠ 0 → ψ x ≠ 0 ∧ ψ (ψ x) = x ∧ (x * ψ x) ^ (p / 2) = -1) ∧
  (∀ x y : ZMod p, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ ψ x →
      ((x - y) * (x - ψ y) * (ψ x - y) * (ψ x - ψ y)) ^ (p / 2) = -1)

theorem admissible_of_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ψ : ZMod p → ZMod p}
    (h : AdmPow p ψ) : Admissible ψ := by
  refine ⟨fun x hx => (h.1 x hx).1, fun x hx => (h.1 x hx).2.1, fun x hx => ?_, ?_⟩
  · have hm := (chi_eq_neg_one_iff hp2 _).2 (h.1 x hx).2.2
    rw [map_mul] at hm
    exact (neg_iff_mul (chi_sq_one hx)).2 hm
  · intro x y hx hy hyx hyψ
    unfold BSW.Basic.Compat
    exact (chi_eq_neg_one_iff hp2 _).2 (h.2 x y hx hy hyx hyψ)

theorem not_elliptic_of {p : ℕ} [Fact p.Prime] {ψ : ZMod p → ZMod p} (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * ψ a ≠ b * ψ b) :
    ¬ ∃ n : ZMod p, ∀ x : ZMod p, x ≠ 0 → ψ x = n / x := by
  rintro ⟨n, hn⟩
  apply hab
  rw [hn a ha, hn b hb]
  field_simp

/-- The first stored sporadic solution for `q = 7`. -/
def psi7 (x : ZMod 7) : ZMod 7 :=
  match x.val with
  | 1 => 3
  | 2 => 6
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 2
  | _ => 0

instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem sporadic_7 : Admissible psi7 ∧ ¬ ∃ n : ZMod 7, ∀ x : ZMod 7, x ≠ 0 → psi7 x = n / x := by
  refine ⟨admissible_of_pow (by norm_num) ?_, not_elliptic_of 1 2 (by decide) (by decide) (by decide +kernel)⟩
  unfold AdmPow psi7
  decide +kernel

/-- The first stored sporadic solution for `q = 11`. -/
def psi11 (x : ZMod 11) : ZMod 11 :=
  match x.val with
  | 1 => 2
  | 2 => 1
  | 3 => 6
  | 4 => 8
  | 5 => 10
  | 6 => 3
  | 7 => 9
  | 8 => 4
  | 9 => 7
  | 10 => 5
  | _ => 0

instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem sporadic_11 : Admissible psi11 ∧ ¬ ∃ n : ZMod 11, ∀ x : ZMod 11, x ≠ 0 → psi11 x = n / x := by
  refine ⟨admissible_of_pow (by norm_num) ?_, not_elliptic_of 1 3 (by decide) (by decide) (by decide +kernel)⟩
  unfold AdmPow psi11
  decide +kernel

/-- The first stored sporadic solution for `q = 19`. -/
def psi19 (x : ZMod 19) : ZMod 19 :=
  match x.val with
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | 5 => 8
  | 6 => 13
  | 7 => 10
  | 8 => 5
  | 9 => 15
  | 10 => 7
  | 11 => 18
  | 12 => 16
  | 13 => 6
  | 14 => 17
  | 15 => 9
  | 16 => 12
  | 17 => 14
  | 18 => 11
  | _ => 0

instance fact_prime_19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩

theorem sporadic_19 : Admissible psi19 ∧ ¬ ∃ n : ZMod 19, ∀ x : ZMod 19, x ≠ 0 → psi19 x = n / x := by
  refine ⟨admissible_of_pow (by norm_num) ?_, not_elliptic_of 1 3 (by decide) (by decide) (by decide +kernel)⟩
  unfold AdmPow psi19
  decide +kernel

/-- The first stored sporadic solution for `q = 23`. -/
def psi23 (x : ZMod 23) : ZMod 23 :=
  match x.val with
  | 1 => 5
  | 2 => 7
  | 3 => 22
  | 4 => 20
  | 5 => 1
  | 6 => 15
  | 7 => 2
  | 8 => 14
  | 9 => 10
  | 10 => 9
  | 11 => 16
  | 12 => 19
  | 13 => 21
  | 14 => 8
  | 15 => 6
  | 16 => 11
  | 17 => 18
  | 18 => 17
  | 19 => 12
  | 20 => 4
  | 21 => 13
  | 22 => 3
  | _ => 0

instance fact_prime_23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩

theorem sporadic_23 : Admissible psi23 ∧ ¬ ∃ n : ZMod 23, ∀ x : ZMod 23, x ≠ 0 → psi23 x = n / x := by
  refine ⟨admissible_of_pow (by norm_num) ?_, not_elliptic_of 1 2 (by decide) (by decide) (by decide +kernel)⟩
  unfold AdmPow psi23
  decide +kernel

/-- The first stored sporadic solution for `q = 31`. -/
def psi31 (x : ZMod 31) : ZMod 31 :=
  match x.val with
  | 1 => 3
  | 2 => 30
  | 3 => 1
  | 4 => 24
  | 5 => 15
  | 6 => 19
  | 7 => 11
  | 8 => 29
  | 9 => 21
  | 10 => 26
  | 11 => 7
  | 12 => 14
  | 13 => 25
  | 14 => 12
  | 15 => 5
  | 16 => 23
  | 17 => 28
  | 18 => 22
  | 19 => 6
  | 20 => 27
  | 21 => 9
  | 22 => 18
  | 23 => 16
  | 24 => 4
  | 25 => 13
  | 26 => 10
  | 27 => 20
  | 28 => 17
  | 29 => 8
  | 30 => 2
  | _ => 0

instance fact_prime_31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

theorem sporadic_31 : Admissible psi31 ∧ ¬ ∃ n : ZMod 31, ∀ x : ZMod 31, x ≠ 0 → psi31 x = n / x := by
  refine ⟨admissible_of_pow (by norm_num) ?_, not_elliptic_of 1 2 (by decide) (by decide) (by decide +kernel)⟩
  unfold AdmPow psi31
  decide +kernel

end BSW.Sporadic
