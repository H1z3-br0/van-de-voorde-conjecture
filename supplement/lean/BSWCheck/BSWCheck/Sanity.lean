module

public import Mathlib
public import BSWCheck.Basics
public import BSWCheck.Bridge
public import BSWCheck.Parity
public import BSWCheck.Sporadic
public import BSWCheck.FrameParity
public import BSWCheck.CharSums

@[expose] public section

/-!
# Non-vacuity checks

The hypotheses of the main formal statements are satisfiable on concrete instances (so the theorems
are not vacuously true), checked by the kernel.
-/

namespace BSW.Sanity

open BSW.Basic BSW.Bridge

instance fact19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩

theorem chi19_two : quadraticChar (ZMod 19) 2 = -1 :=
  (chi_eq_neg_one_iff (by norm_num) 2).2 (by decide)

/-- The elliptic map `x ↦ 2/x` over `𝔽₁₉` is admissible (via `elliptic_admissible`). -/
theorem elliptic19 : Admissible (fun x : ZMod 19 => 2 / x) :=
  (elliptic_admissible (by decide)).2 chi19_two

/-- `powermap_admissible` applies to it (`c = 2`, `e = 8`, since `x^8 = x⁻¹` on squares). -/
theorem powermap19 : ∀ x : ZMod 19, x ≠ 0 → (fun x : ZMod 19 => 2 / x) x = 2 / x :=
  powermap_admissible (p := 19) (by norm_num) (by norm_num) (by norm_num) elliptic19 2 8
    (by
      intro x hx
      have hx' : x ^ 9 = 1 := by simpa using hx
      rw [div_eq_mul_inv]
      congr 1
      exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx')).symm)

/-- `parity_even` applies to the elliptic map at `x = 1`. -/
theorem parity19 :
    Even ((((Finset.univ.filter (fun y : ZMod 19 => y ^ 9 = 1)).erase 1).filter
      (fun y => quadraticChar (ZMod 19) ((1 - y) * ((fun x : ZMod 19 => 2 / x) 1
        - (fun x : ZMod 19 => 2 / x) y)) = -1)).card) :=
  BSW.Parity.parity_even (p := 19) (n := 9) (by norm_num) ⟨4, rfl⟩ elliptic19 (by decide)

/-- `parity_even` applies to a *non-elliptic* solution (the sporadic one at `q = 31`). -/
theorem parity31 :
    Even ((((Finset.univ.filter (fun y : ZMod 31 => y ^ 15 = 1)).erase 1).filter
      (fun y => quadraticChar (ZMod 31) ((1 - y) * (BSW.Sporadic.psi31 1
        - BSW.Sporadic.psi31 y)) = -1)).card) :=
  BSW.Parity.parity_even (p := 31) (n := 15) (by norm_num) ⟨7, rfl⟩
    BSW.Sporadic.sporadic_31.1 (by decide)

/-- `statementC` applies to the sporadic solution at `q = 31` with the three pairs through `1, 2, 4`. -/
theorem statementC31 :
    ∑ w ∈ Uncovered BSW.Sporadic.psi31 {1, 2, 4},
      ∏ x ∈ ({1, 2, 4} : Finset (ZMod 31)), fP x (BSW.Sporadic.psi31 x) w = 0 :=
  statementC BSW.Sporadic.sporadic_31.1 {1, 2, 4} (by decide) (by decide)

/-- The sporadic map at `q = 31` gives a (non-Möbius) solution on `PG(1,31)` ... -/
theorem solution31 : BSW.Proj.Solution (BSW.Proj.ofPsi BSW.Sporadic.psi31) :=
  BSW.Proj.solution_of_admissible BSW.Sporadic.sporadic_31.1

/-- ... which is not a Möbius map (frame independence + non-ellipticity) ... -/
theorem not_mob31 : ¬ BSW.Proj.IsMob (BSW.Proj.ofPsi BSW.Sporadic.psi31) := by
  rw [BSW.Proj.isMob_iff_elliptic solution31 (BSW.Proj.ofPsi_zero _)]
  rintro ⟨n, hn⟩
  apply BSW.Sporadic.sporadic_31.2
  exact ⟨n, fun x hx => by rw [← BSW.Proj.toPsi_ofPsi BSW.Sporadic.psi31 hx]; exact hn x hx⟩

/-- ... and the parity theorem holds for it in the frame of every pair (here the pair through `∞`). -/
theorem parity_frames31 :
    ∃ M : BSW.Proj.Mob (ZMod 31), (M.map none = some 0 ∨
        M.map (BSW.Proj.ofPsi BSW.Sporadic.psi31 none) = some 0) ∧
      ∀ x : ZMod 31, x ^ 15 = 1 →
        Even (((Finset.univ.filter (fun y : ZMod 31 => y ^ 15 = 1)).erase x).filter
          (fun y => quadraticChar (ZMod 31)
            ((x - y) * (BSW.Proj.toPsi (fun B => M.map (BSW.Proj.ofPsi BSW.Sporadic.psi31 (M.inv.map B))) x
              - BSW.Proj.toPsi (fun B => M.map (BSW.Proj.ofPsi BSW.Sporadic.psi31 (M.inv.map B))) y))
              = -1)).card :=
  BSW.Proj.parity_every_frame (p := 31) (n := 15) (by norm_num) ⟨7, rfl⟩ solution31 none

/-- (W0) on a concrete instance: `∑_{x ∈ 𝔽₁₉} χ(x² + 1) = -1`. -/
theorem w0_19 : ∑ x : ZMod 19, quadraticChar (ZMod 19) (1 * x ^ 2 + 0 * x + 1) = -1 := by
  rw [BSW.CharSums.sum_quadratic (by rw [ZMod.ringChar_zmod_n]; norm_num) one_ne_zero (by decide),
    map_one]

end BSW.Sanity
