module

public import Mathlib
public import BSWCheck.Basics

@[expose] public section

/-!
# The projective line, Möbius maps and the normalisation lemma

* Points of `PG(1,q)` are `Option F` (`none = ∞`) with homogeneous coordinates `hc`.
* `CompatP A B C D` — compatibility of the pairs `{A,B}`, `{C,D}` of `PG(1,q)`:
  `χ(det(A,C) det(A,D) det(B,C) det(B,D)) = -1`; for finite points this is (H3), and factors containing
  `∞` reduce to the paper's convention.
* `mob M` — the Möbius map of an invertible `2×2` matrix `M = (α β; γ δ)`.
* `compatP_mob` — compatibility is `PGL(2,q)`-invariant.
* `Solution Ψ` — a fixed-point-free involution of `PG(1,q)` whose pairs are pairwise compatible
  (a complete exterior set of size `(q+1)/2`).
* `admissible_of_solution` — a solution containing the pair `{0,∞}` is an admissible map of `F^*`.
* `normalize_pair` — for every pair `{A, Ψ A}` of a solution there is a Möbius map `g` with
  `g A = 0`, `g (Ψ A) = ∞`, and `g Ψ g⁻¹` is again a solution (normalisation lemma).
* `frame_admissible` — hence every pair of a solution can be taken as `P₀ = {0,∞}`.
-/

open Finset

namespace BSW.Proj

set_option linter.unusedSectionVars false

open BSW.Basic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Homogeneous coordinates: `x ↦ (x,1)`, `∞ ↦ (1,0)`. -/
def hc : Option F → F × F
  | none => (1, 0)
  | some x => (x, 1)

/-- `det(u,v) = u₀ v₁ - u₁ v₀`. -/
def dt (u v : F × F) : F := u.1 * v.2 - u.2 * v.1

/-- Compatibility of the pairs `{A,B}`, `{C,D}` of `PG(1,q)`. -/
def CompatP (A B C D : Option F) : Prop :=
  quadraticChar F (dt (hc A) (hc C) * dt (hc A) (hc D) * dt (hc B) (hc C) * dt (hc B) (hc D)) = -1

theorem compatP_some (a b c d : F) :
    CompatP (some a) (some b) (some c) (some d) ↔ Compat a b c d := by
  unfold CompatP Compat hc dt; simp only [mul_one, one_mul]

/-- Compatibility with the pair `{0,∞}`: `χ(yz) = -1`. -/
theorem compatP_zero_inf (y z : F) :
    CompatP (some 0) none (some y) (some z) ↔ quadraticChar F (y * z) = -1 := by
  unfold CompatP hc dt
  constructor <;> intro h <;> convert h using 2 <;> ring

theorem hc_ne_zero (A : Option F) : hc A ≠ 0 := by
  cases A <;> simp [hc, Prod.ext_iff]

/-- From homogeneous coordinates back to `PG(1,q)`. -/
def proj (u : F × F) : Option F := if u.2 = 0 then none else some (u.1 / u.2)

theorem hc_proj {u : F × F} (hu : u ≠ 0) : ∃ c : F, c ≠ 0 ∧ hc (proj u) = (c * u.1, c * u.2) := by
  unfold proj
  by_cases h2 : u.2 = 0
  · have h1 : u.1 ≠ 0 := by
      intro h1; apply hu; ext <;> simp [h1, h2]
    refine ⟨u.1⁻¹, inv_ne_zero h1, ?_⟩
    simp only [h2, ite_true, hc, mul_zero]
    rw [inv_mul_cancel₀ h1]
  · refine ⟨u.2⁻¹, inv_ne_zero h2, ?_⟩
    simp only [h2, ite_false, hc]
    rw [inv_mul_cancel₀ h2]
    ext <;> simp [div_eq_mul_inv, mul_comm]

theorem proj_hc (A : Option F) : proj (hc A) = A := by
  cases A <;> simp [proj, hc]

theorem proj_smul {u : F × F} {c : F} (hc0 : c ≠ 0) : proj (c * u.1, c * u.2) = proj u := by
  unfold proj
  simp only [mul_eq_zero, hc0, false_or]
  split_ifs <;> try rfl
  congr 1
  field_simp

/-- A Möbius map, given by the entries `α β γ δ` with `αδ - βγ ≠ 0`. -/
structure Mob (F : Type*) [Field F] where
  α : F
  β : F
  γ : F
  δ : F
  det_ne : α * δ - β * γ ≠ 0

namespace Mob

def act (M : Mob F) (u : F × F) : F × F := (M.α * u.1 + M.β * u.2, M.γ * u.1 + M.δ * u.2)

def det (M : Mob F) : F := M.α * M.δ - M.β * M.γ

theorem det_ne_zero (M : Mob F) : M.det ≠ 0 := M.det_ne

theorem dt_act (M : Mob F) (u v : F × F) : dt (M.act u) (M.act v) = M.det * dt u v := by
  unfold dt act det; ring

theorem act_ne_zero (M : Mob F) {u : F × F} (hu : u ≠ 0) : M.act u ≠ 0 := by
  intro h
  apply hu
  have h1 : M.α * u.1 + M.β * u.2 = 0 := congrArg Prod.fst h
  have h2 : M.γ * u.1 + M.δ * u.2 = 0 := congrArg Prod.snd h
  have hd := M.det_ne
  have e1 : (M.α * M.δ - M.β * M.γ) * u.1 = 0 := by linear_combination M.δ * h1 - M.β * h2
  have e2 : (M.α * M.δ - M.β * M.γ) * u.2 = 0 := by linear_combination M.α * h2 - M.γ * h1
  ext
  · exact (mul_eq_zero.mp e1).resolve_left hd
  · exact (mul_eq_zero.mp e2).resolve_left hd

/-- The Möbius map on `PG(1,q)`. -/
def map (M : Mob F) (A : Option F) : Option F := proj (M.act (hc A))

/-- The inverse matrix (adjugate divided by nothing: the adjugate gives the same projective map). -/
def inv (M : Mob F) : Mob F :=
  ⟨M.δ, -M.β, -M.γ, M.α, by have := M.det_ne; intro h; apply this; linear_combination h⟩

theorem act_smul (M : Mob F) (c : F) (u : F × F) :
    M.act (c * u.1, c * u.2) = (c * (M.act u).1, c * (M.act u).2) := by
  unfold act; ext <;> simp <;> ring

theorem inv_act_act (M : Mob F) (u : F × F) :
    M.inv.act (M.act u) = (M.det * u.1, M.det * u.2) := by
  unfold inv act det; ext <;> simp <;> ring

theorem act_inv_act (M : Mob F) (u : F × F) :
    M.act (M.inv.act u) = (M.det * u.1, M.det * u.2) := by
  unfold inv act det; ext <;> simp <;> ring

theorem map_inv_map (M : Mob F) (A : Option F) : M.inv.map (M.map A) = A := by
  unfold map
  obtain ⟨c, hc0, hc'⟩ := hc_proj (M.act_ne_zero (hc_ne_zero A))
  rw [hc', act_smul, inv_act_act, proj_smul hc0, proj_smul M.det_ne_zero, proj_hc]

theorem map_map_inv (M : Mob F) (A : Option F) : M.map (M.inv.map A) = A := by
  unfold map
  obtain ⟨c, hc0, hc'⟩ := hc_proj (M.inv.act_ne_zero (hc_ne_zero A))
  rw [hc', act_smul, act_inv_act, proj_smul hc0, proj_smul M.det_ne_zero, proj_hc]

theorem map_injective (M : Mob F) : Function.Injective M.map := by
  intro A B h
  rw [← M.map_inv_map A, h, M.map_inv_map]

/-- **Compatibility is `PGL(2,q)`-invariant.** -/
theorem compatP_map (M : Mob F) (A B C D : Option F) :
    CompatP (M.map A) (M.map B) (M.map C) (M.map D) ↔ CompatP A B C D := by
  obtain ⟨a, ha, hA⟩ := hc_proj (M.act_ne_zero (hc_ne_zero A))
  obtain ⟨b, hb, hB⟩ := hc_proj (M.act_ne_zero (hc_ne_zero B))
  obtain ⟨c, hc0, hC⟩ := hc_proj (M.act_ne_zero (hc_ne_zero C))
  obtain ⟨d, hd, hD⟩ := hc_proj (M.act_ne_zero (hc_ne_zero D))
  unfold CompatP map
  rw [hA, hB, hC, hD]
  have key : ∀ (s t : F) (u v : F × F),
      dt (s * (M.act u).1, s * (M.act u).2) (t * (M.act v).1, t * (M.act v).2)
        = s * t * M.det * dt u v := by
    intro s t u v
    have := M.dt_act u v
    unfold dt at this ⊢
    linear_combination s * t * this
  rw [key, key, key, key]
  have e : a * c * M.det * dt (hc A) (hc C) * (a * d * M.det * dt (hc A) (hc D)) *
        (b * c * M.det * dt (hc B) (hc C)) * (b * d * M.det * dt (hc B) (hc D))
      = (a * b * c * d * M.det ^ 2) ^ 2 *
        (dt (hc A) (hc C) * dt (hc A) (hc D) * dt (hc B) (hc C) * dt (hc B) (hc D)) := by ring
  rw [e, chi_sq_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc0) hd)
    (pow_ne_zero 2 M.det_ne_zero))]

end Mob

/-- A solution on `PG(1,q)`: a fixed-point-free involution `Ψ` whose pairs are pairwise compatible. -/
structure Solution (Ψ : Option F → Option F) : Prop where
  invol : ∀ A, Ψ (Ψ A) = A
  free : ∀ A, Ψ A ≠ A
  cross : ∀ A C, C ≠ A → C ≠ Ψ A → CompatP A (Ψ A) C (Ψ C)

/-- Conjugating a solution by a Möbius map gives a solution. -/
theorem Solution.conj {Ψ : Option F → Option F} (h : Solution Ψ) (M : Mob F) :
    Solution (fun A => M.map (Ψ (M.inv.map A))) := by
  refine ⟨fun A => ?_, fun A => ?_, fun A C hCA hCψ => ?_⟩
  · show M.map (Ψ (M.inv.map (M.map (Ψ (M.inv.map A))))) = A
    rw [Mob.map_inv_map, h.invol, Mob.map_map_inv]
  · intro he
    apply h.free (M.inv.map A)
    have := congrArg M.inv.map he
    rwa [Mob.map_inv_map] at this
  · have e1 := (Mob.compatP_map M (M.inv.map A) (Ψ (M.inv.map A)) (M.inv.map C)
      (Ψ (M.inv.map C)))
    rw [Mob.map_map_inv, Mob.map_map_inv] at e1
    show CompatP A (M.map (Ψ (M.inv.map A))) C (M.map (Ψ (M.inv.map C)))
    rw [e1]
    apply h.cross
    · intro he; apply hCA
      have := congrArg M.map he; rwa [Mob.map_map_inv, Mob.map_map_inv] at this
    · intro he; apply hCψ
      have := congrArg M.map he; rwa [Mob.map_map_inv] at this

/-- The admissible map of `F^*` attached to a solution containing `{0,∞}`. -/
def toPsi (Ψ : Option F → Option F) (x : F) : F :=
  match Ψ (some x) with
  | some y => y
  | none => 0

/-- A solution containing the pair `{0,∞}` gives an admissible map of `F^*` (and conversely the pairs
of `toPsi Ψ` are the pairs of `Ψ`). -/
theorem admissible_of_solution {Ψ : Option F → Option F} (h : Solution Ψ) (h0 : Ψ (some 0) = none) :
    Admissible (toPsi Ψ) := by
  have hinf : Ψ none = some 0 := by rw [← h0, h.invol]
  -- for `x ≠ 0`, `Ψ (some x) = some (toPsi Ψ x)` with `toPsi Ψ x ≠ 0`
  have hfin : ∀ x : F, x ≠ 0 → Ψ (some x) = some (toPsi Ψ x) ∧ toPsi Ψ x ≠ 0 := by
    intro x hx
    unfold toPsi
    cases hΨ : Ψ (some x) with
    | none =>
      exfalso
      have := congrArg Ψ hΨ
      rw [h.invol, hinf] at this
      exact hx (Option.some_injective _ this)
    | some y =>
      refine ⟨rfl, ?_⟩
      intro hy
      subst hy
      have := congrArg Ψ hΨ
      rw [h.invol, h0] at this
      exact Option.some_ne_none _ this
  refine ⟨fun x hx => (hfin x hx).2, fun x hx => ?_, fun x hx => ?_, fun x y hx hy hyx hyψ => ?_⟩
  · obtain ⟨e1, e2⟩ := hfin x hx
    obtain ⟨e3, -⟩ := hfin (toPsi Ψ x) e2
    have := h.invol (some x)
    rw [e1, e3] at this
    exact Option.some_injective _ this
  · -- compatibility with `{0,∞}`: `χ(x ψ x) = -1`
    obtain ⟨e1, e2⟩ := hfin x hx
    have hcmp := h.cross (some 0) (some x) (by simpa using hx) (by rw [h0]; simp)
    rw [h0, e1, compatP_zero_inf, map_mul] at hcmp
    exact (neg_iff_mul (chi_sq_one hx)).2 hcmp
  · obtain ⟨e1, -⟩ := hfin x hx
    obtain ⟨e3, -⟩ := hfin y hy
    have hcmp := h.cross (some x) (some y) (by simpa using hyx) (by rw [e1]; simpa using hyψ)
    rw [e1, e3, compatP_some] at hcmp
    exact hcmp

/-- Möbius map sending the finite pair `(a, b)` (`a ≠ b`) to `(0, ∞)`: `x ↦ (x - a)/(x - b)`. -/
def normFin (a b : F) (hab : a ≠ b) : Mob F :=
  ⟨1, -a, 1, -b, by intro h; apply hab; linear_combination h⟩

/-- Möbius map sending `(a, ∞)` to `(0, ∞)`: `x ↦ x - a`. -/
def normInf (a : F) : Mob F := ⟨1, -a, 0, 1, by simp⟩

/-- **Normalisation.** Every pair `{A, Ψ A}` of a solution is mapped to `{0,∞}` by some
Möbius map `M`, and the conjugated solution `M Ψ M⁻¹` contains the pair `{0,∞}`. -/
theorem normalize_pair {Ψ : Option F → Option F} (h : Solution Ψ) (A : Option F) :
    ∃ M : Mob F, (M.map A = some 0 ∨ M.map (Ψ A) = some 0) ∧
      (fun B => M.map (Ψ (M.inv.map B))) (some 0) = none := by
  have key : ∀ (P Q : Option F), P ≠ Q →
      ∃ M : Mob F, (M.map P = some 0 ∧ M.map Q = none) ∨ (M.map Q = some 0 ∧ M.map P = none) := by
    intro P Q hne
    cases P with
    | none =>
      cases Q with
      | none => exact (hne rfl).elim
      | some b =>
        refine ⟨normInf b, Or.inr ⟨?_, ?_⟩⟩ <;> simp [Mob.map, normInf, Mob.act, hc, proj]
    | some a =>
      cases Q with
      | none =>
        refine ⟨normInf a, Or.inl ⟨?_, ?_⟩⟩ <;> simp [Mob.map, normInf, Mob.act, hc, proj]
      | some b =>
        have hab : a ≠ b := fun e => hne (by rw [e])
        have hab' : a + -b ≠ 0 := by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr hab
        refine ⟨normFin a b hab, Or.inl ⟨?_, ?_⟩⟩
        · simp [Mob.map, normFin, Mob.act, hc, proj, hab']
        · simp [Mob.map, normFin, Mob.act, hc, proj]
  obtain ⟨M, hM⟩ := key A (Ψ A) (Ne.symm (h.free A))
  rcases hM with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨M, Or.inl h1, ?_⟩
    show M.map (Ψ (M.inv.map (some 0))) = none
    rw [← h1, Mob.map_inv_map, h2]
  · refine ⟨M, Or.inr h1, ?_⟩
    show M.map (Ψ (M.inv.map (some 0))) = none
    rw [← h1, Mob.map_inv_map, h.invol, h2]

/-- **Every pair of a solution can serve as `P₀`.**  For every point `A` there is a Möbius map `M`
sending the pair `{A, Ψ A}` to `{0, ∞}` such that the conjugated solution gives an admissible map. -/
theorem frame_admissible {Ψ : Option F → Option F} (h : Solution Ψ) (A : Option F) :
    ∃ M : Mob F, (M.map A = some 0 ∨ M.map (Ψ A) = some 0) ∧
      Admissible (toPsi (fun B => M.map (Ψ (M.inv.map B)))) := by
  obtain ⟨M, hor, h0⟩ := normalize_pair h A
  exact ⟨M, hor, admissible_of_solution (h.conj M) h0⟩

end BSW.Proj
