module

/-
  Main theorem (power-map theorem, elementary F_p version): for a prime `p ≡ 3 (mod 4)`, `p ≠ 7, 11`,
  every power-map solution `ψ(x) = c x^e` (x square, c nonsquare) is elliptic: `n ∣ e + 1`.
  Stage 1: setup, the master relation, oddness and periodicity.
-/
public import Mathlib
public import BSWCheck.Identities
public import BSWCheck.PowerSums
public import BSWCheck.Exponents

@[expose] public section

open Finset

namespace BSW

/-- Compatibility of the pairs `{a,b}` and `{c,d}`: `χ((a-c)(b-d)(a-d)(b-c)) = -1`. -/
def Compat {p : ℕ} (n : ℕ) (a b c d : ZMod p) : Prop :=
  ((a - c) * (b - d) * (a - d) * (b - c)) ^ n = -1

variable {p n : ℕ} [hp : Fact p.Prime] [NeZero n]

/-- If `A X Y = -1` with `X² = Y² = 1`, then `X = -A Y` and `A² = 1`. -/
theorem pm_rel {R : Type*} [CommRing R] {A X Y : R} (h : A * X * Y = -1) (hX : X ^ 2 = 1)
    (hY : Y ^ 2 = 1) : X * Y = -A ∧ X = -A * Y ∧ A ^ 2 = 1 := by
  have hxy : X * Y = -A := by linear_combination (X * Y) * h - A * hX - A * X ^ 2 * hY
  refine ⟨hxy, ?_, ?_⟩
  · linear_combination -X * hY + Y * hxy
  · linear_combination (A - X * Y) * hxy + Y ^ 2 * hX + hY

/-- The data of a power-map solution, in exponent coordinates. -/
structure PMSetup (p n : ℕ) [Fact p.Prime] [NeZero n] where
  hpn : p = 2 * n + 1
  hodd : Odd n
  ρ : ZMod p
  hρ : IsPrimitiveRoot ρ n
  c : ZMod p
  hc : c ^ n = -1
  e : ℕ
  he : 1 ≤ e
  hsol : ∀ x y : ZMod p, x ^ n = 1 → y ^ n = 1 → x ≠ y → Compat n x (c * x ^ e) y (c * y ^ e)

namespace PMSetup

variable (S : PMSetup p n)
include S

/-- `ε = e`, `η = e - 1` in `ZMod n`. -/
def ε : ZMod n := (S.e : ZMod n)
def η : ZMod n := ((S.e - 1 : ℕ) : ZMod n)

theorem η_add_one : S.η + 1 = S.ε := by
  simp [η, ε, Nat.cast_sub S.he]

/-- `h` on nonsquares: `H i = χ(c ρ^i - 1)`. -/
def H (i : ZMod n) : ZMod p := (S.c * E S.ρ i - 1) ^ n
/-- `h` on squares: `Hs i = χ(ρ^i - 1)`. -/
def Hs (i : ZMod n) : ZMod p := (E S.ρ i - 1) ^ n
/-- `A(a) = χ((1-ρ^a)(1-ρ^(ae)))`. -/
def A (a : ZMod n) : ZMod p := ((1 - E S.ρ a) * (1 - E S.ρ (a * S.ε))) ^ n

theorem n_pos : 0 < n := by have := S.hpn; have := hp.out.two_le; omega

theorem two_ne : (2 : ZMod p) ≠ 0 := two_ne_zero' S.hpn S.n_pos

theorem c_ne_zero : S.c ≠ 0 := by
  intro h
  have := S.hc
  rw [h, zero_pow (NeZero.ne n)] at this
  exact one_ne_zero (by linear_combination this : (1 : ZMod p) = 0)

theorem cE_ne_one (i : ZMod n) : S.c * E S.ρ i ≠ 1 := by
  intro h
  have := S.hc
  have h2 : (S.c * E S.ρ i) ^ n = -1 := by rw [mul_pow, S.hc, E_pow_n S.hρ, mul_one]
  rw [h, one_pow] at h2
  exact S.two_ne (by linear_combination h2)

theorem sq_of_ne {z : ZMod p} (hz : z ≠ 0) : (z ^ n) ^ 2 = 1 := by
  rcases pow_half_eq S.hpn hz with h | h <;> rw [h] <;> ring

theorem H_sq (i : ZMod n) : S.H i ^ 2 = 1 := by
  unfold H
  exact S.sq_of_ne (sub_ne_zero.mpr (S.cE_ne_one i))

theorem H_ne_zero (i : ZMod n) : S.H i ≠ 0 := by
  intro h
  have := S.H_sq i
  rw [h, zero_pow two_ne_zero] at this
  exact zero_ne_one this

theorem Hs_zero : S.Hs 0 = 0 := by
  unfold Hs
  rw [E_zero, sub_self, zero_pow (NeZero.ne n)]

theorem Hs_sq {i : ZMod n} (hi : i ≠ 0) : S.Hs i ^ 2 = 1 := by
  unfold Hs
  refine S.sq_of_ne (sub_ne_zero.mpr ?_)
  rwa [Ne, E_eq_one_iff S.hρ]

theorem one_sub_pow (i : ZMod n) : (1 - E S.ρ i) ^ n = -S.Hs i := by
  unfold Hs
  rw [show 1 - E S.ρ i = -(E S.ρ i - 1) by ring, neg_pow, Odd.neg_one_pow S.hodd]
  ring

theorem Hs_neg (i : ZMod n) : S.Hs (-i) = -S.Hs i := by
  have h1 : E S.ρ (-i) - 1 = (1 - E S.ρ i) * E S.ρ (-i) := by
    have := E_mul_E_neg S.hρ i
    linear_combination this
  unfold Hs
  rw [h1, mul_pow, E_pow_n S.hρ, mul_one, S.one_sub_pow]
  rfl

/-- **Master relation.** For every `i` and every `a ≠ 0`:
`A(a) · H(iη + aε) · H(iη - a) = -1`. It is the compatibility of the pairs at `x = ρ^i` and `y = ρ^(i+a)`. -/
theorem master (i a : ZMod n) (ha : a ≠ 0) :
    S.A a * S.H (i * S.η + a * S.ε) * S.H (i * S.η - a) = -1 := by
  have hρ := S.hρ
  have hxy : E S.ρ i ≠ E S.ρ (i + a) := by
    intro h
    have := E_inj hρ h
    exact ha (by linear_combination -this)
  have hx := S.hsol (E S.ρ i) (E S.ρ (i + a)) (E_pow_n hρ i) (E_pow_n hρ _) hxy
  unfold Compat at hx
  rw [E_pow hρ, E_pow hρ] at hx
  have he1 : (S.e : ZMod n) = S.η + 1 := S.η_add_one.symm
  have e1 : E S.ρ (i + a) = E S.ρ i * E S.ρ a := E_add hρ i a
  have e2 : E S.ρ (i * (S.e : ZMod n)) = E S.ρ (i * S.η) * E S.ρ i := by
    rw [← E_add hρ, he1]; ring_nf
  have e3 : E S.ρ ((i + a) * (S.e : ZMod n)) = E S.ρ (i * S.η) * E S.ρ i * E S.ρ (a * S.ε) := by
    rw [← E_add hρ, ← E_add hρ]; congr 1; rw [ε, he1]; ring
  have e4 : E S.ρ (i * S.η + a * S.ε) = E S.ρ (i * S.η) * E S.ρ (a * S.ε) := E_add hρ _ _
  have e5 : E S.ρ (i * S.η - a) = E S.ρ (i * S.η) * E S.ρ (-a) := by
    rw [sub_eq_add_neg, E_add hρ]
  have hinv : E S.ρ a * E S.ρ (-a) = 1 := E_mul_E_neg hρ a
  rw [e1, e2, e3] at hx
  unfold A H
  rw [e4, e5]
  -- abbreviations
  generalize hX : E S.ρ i = x at hx ⊢
  generalize hU : E S.ρ a = U at hx hinv ⊢
  generalize hV : E S.ρ (a * S.ε) = V at hx ⊢
  generalize hW : E S.ρ (i * S.η) = W at hx ⊢
  generalize hU' : E S.ρ (-a) = U' at hinv ⊢
  have hWn : W ^ n = 1 := by rw [← hW]; exact E_pow_n hρ _
  have hxn : x ^ n = 1 := by rw [← hX]; exact E_pow_n hρ _
  have hUn : U ^ n = 1 := by rw [← hU]; exact E_pow_n hρ _
  have key : (x - x * U) * (S.c * (W * x) - S.c * (W * x * V)) * (x - S.c * (W * x * V))
        * (S.c * (W * x) - x * U)
      = (S.c * W) * x ^ 4 * ((1 - U) * (1 - V)) * (-U) * ((S.c * (W * V) - 1) * (S.c * (W * U') - 1)) := by
    linear_combination (-(S.c * W) ^ 2 * x ^ 4 * (1 - U) * (1 - V) * (1 - S.c * W * V)) * hinv
  rw [key] at hx
  have h1 : (S.c * W) ^ n = -1 := by rw [mul_pow, S.hc, hWn, mul_one]
  have h2 : (x ^ 4) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow]
  have h3 : (-U) ^ n = -1 := by rw [neg_pow, hUn, Odd.neg_one_pow S.hodd, mul_one]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, h1, h2, h3] at hx
  simp only [mul_pow] at hx ⊢
  linear_combination hx

/-- `(1-U)^n` is `±1` for `U = ρ^a ≠ 1`, hence `((1-U)^2)^n = 1`. -/
theorem A_of_fixed {a : ZMod n} (ha : a ≠ 0) (hK : a * S.η = 0) : S.A a = 1 := by
  have haε : a * S.ε = a := by rw [← S.η_add_one, mul_add, hK, mul_one, zero_add]
  unfold A
  rw [haε, ← sq, ← pow_mul, mul_comm, pow_mul]
  refine S.sq_of_ne (sub_ne_zero.mpr ?_)
  intro h
  exact ha ((E_eq_one_iff S.hρ a).mp h.symm)

/-- **Oddness (F1).** At a center `b = iη`, for `a ≠ 0` with `aη = 0`: `H(b+a) H(b-a) = -1`. -/
theorem odd_rel (i a : ZMod n) (ha : a ≠ 0) (hK : a * S.η = 0) :
    S.H (i * S.η + a) * S.H (i * S.η - a) = -1 := by
  have h := S.master i a ha
  have haε : a * S.ε = a := by rw [← S.η_add_one, mul_add, hK, mul_one, zero_add]
  rw [haε, S.A_of_fixed ha hK, one_mul] at h
  exact h

theorem H_neg_of_odd (i a : ZMod n) (ha : a ≠ 0) (hK : a * S.η = 0) :
    S.H (i * S.η - a) = -S.H (i * S.η + a) := by
  have h := S.odd_rel i a ha hK
  have h' : (1 : ZMod p) * S.H (i * S.η - a) * S.H (i * S.η + a) = -1 := by
    linear_combination h
  have := (pm_rel h' (S.H_sq _) (S.H_sq _)).2.1
  linear_combination this

/-- **Periodicity (F2).** If `η ≠ 0` then `H(jη + s) = H(jη)` with `s = η(ε+1) = (e-1)(e+1)`. -/
theorem periodic (hη : S.η ≠ 0) (j : ZMod n) :
    S.H (j * S.η + S.η * (S.ε + 1)) = S.H (j * S.η) := by
  -- relation from the master identity with a = η, i = j + 1
  have rel : ∀ j : ZMod n, S.A S.η * S.H (j * S.η + S.η * (S.ε + 1)) * S.H (j * S.η) = -1 := by
    intro j
    have h := S.master (j + 1) S.η hη
    have e1 : (j + 1) * S.η + S.η * S.ε = j * S.η + S.η * (S.ε + 1) := by ring
    have e2 : (j + 1) * S.η - S.η = j * S.η := by ring
    rw [e1, e2] at h
    exact h
  set κ : ZMod p := -S.A S.η with hκ
  -- H(y+s) = κ H(y)
  have step : ∀ j : ZMod n, S.H (j * S.η + S.η * (S.ε + 1)) = κ * S.H (j * S.η) := by
    intro j
    exact (pm_rel (rel j) (S.H_sq _) (S.H_sq _)).2.1
  have iter : ∀ m : ℕ, ∀ j : ZMod n,
      S.H (j * S.η + (m : ZMod n) * (S.η * (S.ε + 1))) = κ ^ m * S.H (j * S.η) := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      have h1 := step (j + (m : ZMod n) * (S.ε + 1))
      have e1 : (j + (m : ZMod n) * (S.ε + 1)) * S.η + S.η * (S.ε + 1)
          = j * S.η + ((m + 1 : ℕ) : ZMod n) * (S.η * (S.ε + 1)) := by push_cast; ring
      have e2 : (j + (m : ZMod n) * (S.ε + 1)) * S.η = j * S.η + (m : ZMod n) * (S.η * (S.ε + 1)) := by
        ring
      rw [e1, e2, ih j] at h1
      rw [h1, pow_succ]
      ring
  have hn := iter n j
  rw [ZMod.natCast_self, zero_mul, add_zero] at hn
  have hκn : κ ^ n = 1 := by
    have hne := S.H_ne_zero (j * S.η)
    have : (κ ^ n - 1) * S.H (j * S.η) = 0 := by linear_combination -hn
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  have hκ2 : κ ^ 2 = 1 := by
    rw [hκ, neg_sq]
    exact (pm_rel (rel 0) (S.H_sq _) (S.H_sq _)).2.2
  have hκ1 : κ = 1 := by
    obtain ⟨k, hk⟩ := S.hodd
    rw [hk, pow_succ, pow_mul, hκ2, one_pow, one_mul] at hκn
    exact hκn
  rw [step j, hκ1, one_mul]

end PMSetup

end BSW
