module

public import Mathlib
public import BSWCheck.Projective
public import BSWCheck.Parity

@[expose] public section

/-!
# Frame independence (normalisation lemma) and the parity theorem in every frame

* `BSW.Proj.Mob.comp`, `map_comp` — composition of Möbius maps.
* `BSW.Proj.isMob_conj` — conjugates of Möbius maps are Möbius maps.
* `BSW.Proj.isMob_iff_elliptic` — a solution containing `{0,∞}` is a Möbius involution iff its admissible
  map is elliptic, `ψ(x) = n/x`.  Hence **the BSW conjecture "Ψ ∈ PGL(2,q)" does not depend on the frame**
  (`frame_elliptic_iff`).
* `BSW.Proj.parity_every_frame` — **The parity theorem in every frame** (prime `q ≡ 3 mod 4`): for every pair `P` of
  a solution, after normalising `P` to `{0,∞}` every vertex of the bad graph has even degree.
-/

open Finset

namespace BSW.Proj

set_option linter.unusedSectionVars false

open BSW.Basic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

namespace Mob

/-- Composition `M ∘ N`. -/
def comp (M N : Mob F) : Mob F :=
  ⟨M.α * N.α + M.β * N.γ, M.α * N.β + M.β * N.δ, M.γ * N.α + M.δ * N.γ, M.γ * N.β + M.δ * N.δ, by
    have h : (M.α * N.α + M.β * N.γ) * (M.γ * N.β + M.δ * N.δ)
        - (M.α * N.β + M.β * N.δ) * (M.γ * N.α + M.δ * N.γ) = M.det * N.det := by
      unfold det; ring
    rw [h]; exact mul_ne_zero M.det_ne_zero N.det_ne_zero⟩

theorem act_comp (M N : Mob F) (u : F × F) : (M.comp N).act u = M.act (N.act u) := by
  unfold comp act; ext <;> simp <;> ring

theorem map_comp (M N : Mob F) (A : Option F) : (M.comp N).map A = M.map (N.map A) := by
  unfold map
  obtain ⟨c, hc0, hc'⟩ := hc_proj (N.act_ne_zero (hc_ne_zero A))
  rw [hc', act_smul, proj_smul hc0, act_comp]

end Mob

/-- `Ψ` is (the action of) a Möbius map. -/
def IsMob (Ψ : Option F → Option F) : Prop := ∃ N : Mob F, ∀ A, Ψ A = N.map A

theorem isMob_conj {Ψ : Option F → Option F} (hΨ : IsMob Ψ) (M : Mob F) :
    IsMob (fun A => M.map (Ψ (M.inv.map A))) := by
  obtain ⟨N, hN⟩ := hΨ
  refine ⟨M.comp (N.comp M.inv), fun A => ?_⟩
  simp only [hN, Mob.map_comp]

theorem isMob_conj_iff {Ψ : Option F → Option F} (M : Mob F) :
    IsMob (fun A => M.map (Ψ (M.inv.map A))) ↔ IsMob Ψ := by
  constructor
  · intro h
    have h2 := isMob_conj h M.inv
    obtain ⟨N, hN⟩ := h2
    refine ⟨N, fun A => ?_⟩
    rw [← hN A]
    have hii : ∀ B, M.inv.inv.map B = M.map B := by
      intro B; unfold Mob.map; congr 1; unfold Mob.inv Mob.act; ext <;> simp
    show Ψ A = M.inv.map (M.map (Ψ (M.inv.map (M.inv.inv.map A))))
    rw [hii, Mob.map_inv_map, Mob.map_inv_map]
  · intro h; exact isMob_conj h M

/-- For a solution containing `{0,∞}`: `Ψ` is a Möbius map iff `ψ(x) = n/x` on `F^*` (elliptic). -/
theorem isMob_iff_elliptic {Ψ : Option F → Option F} (h : Solution Ψ) (h0 : Ψ (some 0) = none) :
    IsMob Ψ ↔ ∃ n : F, ∀ x : F, x ≠ 0 → toPsi Ψ x = n / x := by
  have hinf : Ψ none = some 0 := by rw [← h0, h.invol]
  constructor
  · rintro ⟨N, hN⟩
    -- `N 0 = ∞` forces `δ = 0`, `N ∞ = 0` forces `α = 0`
    have hδ : N.δ = 0 := by
      have := hN (some 0); rw [h0] at this
      unfold Mob.map Mob.act hc proj at this
      simp only [mul_zero, mul_one, zero_add] at this
      by_contra hd; simp only [hd, ite_false] at this; exact Option.some_ne_none _ this.symm
    have hγ : N.γ ≠ 0 := by
      intro hg; have := N.det_ne; rw [hδ, hg] at this; simp at this
    have hα : N.α = 0 := by
      have := hN none; rw [hinf] at this
      unfold Mob.map Mob.act hc proj at this
      simp only [mul_zero, mul_one, add_zero, hγ, ite_false, Option.some.injEq] at this
      have := this.symm
      rw [div_eq_zero_iff] at this
      exact this.resolve_right hγ
    refine ⟨N.β / N.γ, fun x hx => ?_⟩
    have := hN (some x)
    unfold toPsi
    rw [this]
    unfold Mob.map Mob.act hc proj
    simp only [hα, hδ, zero_mul, zero_add, mul_one, add_zero, mul_eq_zero, hγ, hx, or_self, ite_false]
    field_simp
  · rintro ⟨n, hn⟩
    have hn0 : n ≠ 0 := by
      intro hnz
      have hfin := hn 1 one_ne_zero
      rw [hnz, zero_div] at hfin
      have hA := admissible_of_solution h h0
      exact hA.ne_zero 1 one_ne_zero hfin
    refine ⟨⟨0, n, 1, 0, by simp [hn0]⟩, fun A => ?_⟩
    cases A with
    | none => rw [hinf]; simp [Mob.map, Mob.act, hc, proj]
    | some x =>
      by_cases hx : x = 0
      · subst hx; rw [h0]; simp [Mob.map, Mob.act, hc, proj]
      · have hA := admissible_of_solution h h0
        have hfin : Ψ (some x) = some (toPsi Ψ x) := by
          unfold toPsi
          cases hΨ : Ψ (some x) with
          | none =>
            exfalso
            have := congrArg Ψ hΨ
            rw [h.invol, hinf] at this
            exact hx (Option.some_injective _ this)
          | some y => rfl
        rw [hfin, hn x hx]
        simp [Mob.map, Mob.act, hc, proj, hx]

/-- **The BSW property is frame independent.**  For any pair `{A, ΨA}` normalised to `{0,∞}` by `M`,
`Ψ` is a Möbius map iff the admissible map of the normalised solution is elliptic. -/
theorem frame_elliptic_iff {Ψ : Option F → Option F} (h : Solution Ψ) (M : Mob F)
    (h0 : (fun B => M.map (Ψ (M.inv.map B))) (some 0) = none) :
    IsMob Ψ ↔ ∃ n : F, ∀ x : F, x ≠ 0 → toPsi (fun B => M.map (Ψ (M.inv.map B))) x = n / x := by
  rw [← isMob_conj_iff M]
  exact isMob_iff_elliptic (h.conj M) h0

/-- **The parity theorem in every frame** (prime `q = p = 2n+1`, `n` odd).  For every pair `{A, ΨA}` of a solution
there is a Möbius map `M` normalising it to `{0,∞}` such that, for the admissible map `ψ'` of the
normalised solution and every square `x`, the number of squares `y ≠ x` with `χ((x-y)(ψ'x-ψ'y)) = -1`
is even. -/
theorem parity_every_frame {p n : ℕ} [Fact p.Prime] [NeZero n] (hpn : p = 2 * n + 1) (hodd : Odd n)
    {Ψ : Option (ZMod p) → Option (ZMod p)} (h : Solution Ψ) (A : Option (ZMod p)) :
    ∃ M : Mob (ZMod p), (M.map A = some 0 ∨ M.map (Ψ A) = some 0) ∧
      ∀ x : ZMod p, x ^ n = 1 →
        Even (((univ.filter (fun y : ZMod p => y ^ n = 1)).erase x).filter
          (fun y => quadraticChar (ZMod p)
            ((x - y) * (toPsi (fun B => M.map (Ψ (M.inv.map B))) x
              - toPsi (fun B => M.map (Ψ (M.inv.map B))) y)) = -1)).card := by
  obtain ⟨M, hor, hadm⟩ := frame_admissible h A
  exact ⟨M, hor, fun x hx => BSW.Parity.parity_even hpn hodd hadm hx⟩

/-- The solution on `PG(1,q)` attached to a map of `F^*`: pairs `{0,∞}` and `{x, ψ x}`. -/
def ofPsi (ψ : F → F) : Option F → Option F
  | none => some 0
  | some x => if x = 0 then none else some (ψ x)

theorem compatP_inf_zero (y z : F) :
    CompatP none (some 0) (some y) (some z) ↔ quadraticChar F (y * z) = -1 := by
  unfold CompatP hc dt
  constructor <;> intro h <;> convert h using 2 <;> ring

theorem compatP_fin_inf_zero (a b : F) :
    CompatP (some a) (some b) none (some 0) ↔ quadraticChar F (a * b) = -1 := by
  unfold CompatP hc dt
  constructor <;> intro h <;> convert h using 2 <;> ring

theorem compatP_fin_zero_inf (a b : F) :
    CompatP (some a) (some b) (some 0) none ↔ quadraticChar F (a * b) = -1 := by
  unfold CompatP hc dt
  constructor <;> intro h <;> convert h using 2 <;> ring

/-- **Converse of `admissible_of_solution`**: an admissible map gives a solution on `PG(1,q)`
containing `{0,∞}`.  So admissible maps of `F^*` and solutions through `{0,∞}` are the same objects. -/
theorem solution_of_admissible {ψ : F → F} (h : Admissible ψ) : Solution (ofPsi ψ) := by
  have hprod : ∀ x : F, x ≠ 0 → quadraticChar F (x * ψ x) = -1 := by
    intro x hx
    rw [map_mul]; exact (neg_iff_mul (chi_sq_one hx)).1 (h.swap x hx)
  have hfix : ∀ x : F, x ≠ 0 → ψ x ≠ x := by
    intro x hx he
    have := h.swap x hx
    rw [he] at this
    rcases quadraticChar_dichotomy hx with h1 | h1 <;> rw [h1] at this <;> norm_num at this
  refine ⟨fun A => ?_, fun A => ?_, fun A C hCA hCψ => ?_⟩
  · cases A with
    | none => simp [ofPsi]
    | some x =>
      by_cases hx : x = 0
      · simp [ofPsi, hx]
      · simp [ofPsi, hx, h.ne_zero x hx, h.invol x hx]
  · cases A with
    | none => simp [ofPsi]
    | some x =>
      by_cases hx : x = 0
      · simp [ofPsi, hx]
      · simp only [ofPsi, hx, ite_false, ne_eq, Option.some.injEq]; exact hfix x hx
  · cases A with
    | none =>
      cases C with
      | none => exact (hCA rfl).elim
      | some y =>
        have hy : y ≠ 0 := by intro hy; apply hCψ; simp [ofPsi, hy]
        simp only [ofPsi, hy, ite_false]
        exact (compatP_inf_zero y (ψ y)).2 (hprod y hy)
    | some x =>
      by_cases hx : x = 0
      · subst hx
        cases C with
        | none => exact (hCψ (by simp [ofPsi])).elim
        | some y =>
          have hy : y ≠ 0 := by intro hy; apply hCA; rw [hy]
          simp only [ofPsi, hy, ite_true, ite_false]
          exact (compatP_zero_inf y (ψ y)).2 (hprod y hy)
      · cases C with
        | none =>
          simp only [ofPsi, hx, ite_false]
          exact (compatP_fin_inf_zero x (ψ x)).2 (hprod x hx)
        | some y =>
          by_cases hy : y = 0
          · subst hy
            simp only [ofPsi, hx, ite_false, ite_true]
            exact (compatP_fin_zero_inf x (ψ x)).2 (hprod x hx)
          · simp only [ofPsi, hx, hy, ite_false]
            rw [compatP_some]
            apply h.cross x y hx hy
            · intro he; apply hCA; rw [he]
            · intro he; apply hCψ; simp [ofPsi, hx, he]

theorem ofPsi_zero (ψ : F → F) : ofPsi ψ (some 0) = none := by simp [ofPsi]

theorem toPsi_ofPsi (ψ : F → F) {x : F} (hx : x ≠ 0) : toPsi (ofPsi ψ) x = ψ x := by
  simp [toPsi, ofPsi, hx]

end BSW.Proj
