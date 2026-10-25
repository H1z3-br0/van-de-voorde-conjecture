module

/-
  **Theorem (power-map solutions are elliptic).**
  Let `p ≡ 3 (mod 4)` be a prime, `p ≠ 7, 11`, `n = (p-1)/2`, `c` a nonsquare, `e ∈ ℕ`.
  If all pairs `{x, c x^e}` (`x` a nonzero square) are pairwise compatible, i.e.
  `χ((x-y)(ψx-ψy)(x-ψy)(ψx-y)) = -1` for distinct squares `x ≠ y`, then `n ∣ e + 1`,
  i.e. `ψ(x) = c x^e = c/x` on squares (the elliptic solution).

  No analytic input (Weil/Hasse) and no algebraic number theory is used: everything is
  computed in `ZMod p` (see `PowerSums`, `PowerMap`, `PowerMapMain`, `PowerMapFinal`).
-/
public import Mathlib
public import BSWCheck.PowerMapFinal

@[expose] public section

namespace BSW

theorem powermap_elliptic {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 3) (hp7 : p ≠ 7) (hp11 : p ≠ 11)
    (c : ZMod p) (hc : c ^ ((p - 1) / 2) = -1) (e : ℕ)
    (hsol : ∀ x y : ZMod p, x ^ ((p - 1) / 2) = 1 → y ^ ((p - 1) / 2) = 1 → x ≠ y →
      Compat ((p - 1) / 2) x (c * x ^ e) y (c * y ^ e)) :
    (p - 1) / 2 ∣ e + 1 := by
  set n := (p - 1) / 2 with hn
  have hpn : p = 2 * n + 1 := by omega
  have hodd : Odd n := ⟨(p - 3) / 4, by omega⟩
  by_cases hn1 : n = 1
  · rw [hn1]; exact one_dvd _
  have hn3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ρ, hρ⟩ := exists_primitive (p := p) hpn
  by_cases he0 : e = 0
  · exfalso
    have hρ1 : ρ ≠ 1 := hρ.ne_one (by omega)
    have h := hsol 1 ρ (one_pow _) hρ.pow_eq_one (Ne.symm hρ1)
    unfold Compat at h
    rw [he0] at h
    simp only [pow_zero, mul_one, sub_self, mul_zero, zero_mul] at h
    rw [zero_pow (by omega)] at h
    exact one_ne_zero (by linear_combination h : (1 : ZMod p) = 0)
  have he : 1 ≤ e := by omega
  let S : PMSetup p n := ⟨hpn, hodd, ρ, hρ, c, hc, e, he, hsol⟩
  by_cases hη : S.η = 0
  · exfalso
    have h462 := S.e1_462 hη hn3
    have hdvd : p ∣ 462 := by
      have : ((462 : ℕ) : ZMod p) = 0 := by exact_mod_cast h462
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    have hp' := hp.out
    rcases hp'.dvd_mul.mp (show p ∣ 2 * 231 from hdvd) with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    rcases hp'.dvd_mul.mp (show p ∣ 3 * 77 from h) with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    rcases hp'.dvd_mul.mp (show p ∣ 7 * 11 from h) with h | h
    · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp' (by norm_num)).mp h)
    · exact hp11 ((Nat.prime_dvd_prime_iff_eq hp' (by norm_num)).mp h)
  have hcop := S.coprime_fd hη
  by_cases hh : S.d ∣ S.e + 1
  · by_cases hf1 : S.f = 1
    · have hd : S.d = n := by
        have := S.n_eq_fd
        rw [hf1, one_mul] at this
        exact this.symm
      rw [hd] at hh
      exact hh
    · exact (S.hybrid_false hη hcop hh hf1).elim
  · exact (S.nonhybrid_false hη hcop hh).elim

/-- Sanity check (the hypotheses are satisfiable): at `p = 19` the elliptic map `ψ(x) = 2/x = 2x^8`
(`2` is a nonsquare mod 19) satisfies the compatibility hypothesis, verified by the kernel. -/
theorem sanity_p19_elliptic :
    ∀ x y : ZMod 19, x ^ 9 = 1 → y ^ 9 = 1 → x ≠ y → Compat 9 x (2 * x ^ 8) y (2 * y ^ 8) := by
  unfold Compat
  decide

/-- …and the non-elliptic `ψ(x) = 2x` (`e = 1`) does not. -/
theorem sanity_p19_e1_fails :
    ¬ ∀ x y : ZMod 19, x ^ 9 = 1 → y ^ 9 = 1 → x ≠ y → Compat 9 x (2 * x ^ 1) y (2 * y ^ 1) := by
  unfold Compat
  decide

end BSW
