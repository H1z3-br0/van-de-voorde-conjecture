module

public import Mathlib
public import BSWCheck.Segre
public import BSWCheck.Projective
public import BSWCheck.FrameParity
public import BSWCheck.TheoremV

@[expose] public section

/-!
# The plane model of the problem and the frame-free form of Theorem 7.5

`PG(2,q)` is the projective plane of binary quadratic forms `a X² + b XZ + c Z²` (`V3 F`).

* `det3_eq_zero_iff` — three points are collinear iff `det3 = 0` (linear dependence).
* `disc`; `onConic_iff` — the conic `C = {disc = 0}` consists of the squares `ℓ_A²` of linear forms,
  i.e. of the forms `pformP A A`, `A ∈ PG(1,q)`.
* `external_iff` — the external points (`disc` a nonzero square) are exactly the forms `pformP A B`,
  `A ≠ B`: external points ↔ pairs of points of `PG(1,q)`.
* `compat_iff_passant` — **the dictionary of the problem**: the pairs `{A,B}`, `{C,D}` are compatible
  (condition (H3)) iff the line through the two external points is a passant (meets no point of `C`).
* `ArcLikeP` — no three points of a solution on `PG(1,q)` are collinear (no frame chosen);
  `arcLikeP_conj` — this is `PGL(2,q)`-invariant (the action on forms is the symmetric square,
  `det3_Lmat`: determinant `det(M)³`).
* `theoremV_proj` — **Theorem 7.5 (prime q) for an arbitrary solution on `PG(1,p)`** (modulo `StickelHyp`).
* `arcP7` — non-vacuity at `q = 7`.
-/

open Finset

namespace BSW.Plane

open BSW.Basic BSW.Segre BSW.Proj

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Collinearity -/

/-- **Collinearity**: `det3 u v w = 0` iff `u, v, w` are linearly dependent. -/
theorem det3_eq_zero_iff (u v w : V3 F) :
    det3 u v w = 0 ↔ ∃ a b c : F, ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧
      a * u.a + b * v.a + c * w.a = 0 ∧ a * u.b + b * v.b + c * w.b = 0 ∧
      a * u.c + b * v.c + c * w.c = 0 := by
  set Mx : Matrix (Fin 3) (Fin 3) F := !![u.a, v.a, w.a; u.b, v.b, w.b; u.c, v.c, w.c] with hMx
  have hdet : Mx.det = det3 u v w := by
    rw [Matrix.det_fin_three]; simp [Mx]; unfold det3; ring
  rw [← hdet, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨x, hx, hMx0⟩
    refine ⟨x 0, x 1, x 2, ?_, ?_, ?_, ?_⟩
    · rintro ⟨h0, h1, h2⟩; apply hx; funext i; fin_cases i <;> simp [h0, h1, h2]
    all_goals
      have := congrFun hMx0
      simp [Mx, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    · have := this 0; simp at this; linear_combination this
    · have := this 1; simp at this; linear_combination this
    · have := this 2; simp at this; linear_combination this
  · rintro ⟨a, b, c, hne, h1, h2, h3⟩
    refine ⟨![a, b, c], ?_, ?_⟩
    · intro h0; apply hne
      exact ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2⟩
    · funext i
      fin_cases i
      · simp [Mx, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linear_combination h1
      · simp [Mx, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linear_combination h2
      · simp [Mx, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linear_combination h3

/-! ## The conic and the external points -/

/-- Discriminant of the form `a X² + b XZ + c Z²`. -/
def disc (u : V3 F) : F := u.b ^ 2 - 4 * u.a * u.c

/-- Scalar multiple of a form. -/
def smul3 (k : F) (u : V3 F) : V3 F := ⟨k * u.a, k * u.b, k * u.c⟩

/-- The form `ℓ_A ℓ_B` with roots `A, B ∈ PG(1,q)`, where `ℓ_A(X,Z) = det(hc A, (X,Z))`. -/
def pformP (A B : Option F) : V3 F :=
  ⟨(hc A).2 * (hc B).2, -((hc A).1 * (hc B).2 + (hc A).2 * (hc B).1), (hc A).1 * (hc B).1⟩

theorem disc_pformP (A B : Option F) : disc (pformP A B) = (dt (hc A) (hc B)) ^ 2 := by
  unfold disc pformP dt; ring

theorem disc_smul3 (k : F) (u : V3 F) : disc (smul3 k u) = k ^ 2 * disc u := by
  unfold disc smul3; ring

theorem dt_hc_eq_zero_iff (A B : Option F) : dt (hc A) (hc B) = 0 ↔ A = B := by
  constructor
  · intro h
    cases A with
    | none => cases B with
      | none => rfl
      | some b => simp [dt, hc] at h
    | some a => cases B with
      | none => simp [dt, hc] at h
      | some b => simp [dt, hc] at h; rw [sub_eq_zero.mp h]
  · rintro rfl; unfold dt; ring

theorem pformP_some (x y : F) : pformP (some x) (some y) = pf x y := by
  unfold pformP pf hc; ext <;> simp

theorem pformP_zero_inf : pformP (some (0 : F)) none = smul3 (-1) p0 := by
  unfold pformP smul3 p0 hc; ext <;> simp

theorem two_ne_zero_F (hF : ringChar F ≠ 2) : (2 : F) ≠ 0 := Ring.two_ne_zero hF

/-- Every nonzero form with discriminant `d²` splits: `u = k · pformP A B` with `dt(A,B) = ±d`. -/
theorem split_of_disc (hF : ringChar F ≠ 2) {u : V3 F} (hu : u ≠ ⟨0, 0, 0⟩) {d : F}
    (hd : disc u = d ^ 2) :
    ∃ A B : Option F, ∃ k : F, k ≠ 0 ∧ u = smul3 k (pformP A B) := by
  have h2 := two_ne_zero_F hF
  by_cases ha : u.a = 0
  · by_cases hb : u.b = 0
    · -- `u = c Z²`: the double root `∞`
      have hc0 : u.c ≠ 0 := by
        intro hc0; apply hu; ext <;> simp [ha, hb, hc0]
      refine ⟨none, none, u.c, hc0, ?_⟩
      ext <;> simp [smul3, pformP, hc, ha, hb]
    · -- `u = Z (b X + c Z)`: roots `∞` and `-c/b`
      refine ⟨none, some (-u.c / u.b), -u.b, neg_ne_zero.mpr hb, ?_⟩
      ext <;> simp [smul3, pformP, hc, ha]; field_simp
  · -- roots `(-b ± d)/(2a)`
    refine ⟨some ((-u.b + d) / (2 * u.a)), some ((-u.b - d) / (2 * u.a)), u.a, ha, ?_⟩
    have hd' : d ^ 2 = u.b ^ 2 - 4 * u.a * u.c := hd.symm
    ext <;> simp [smul3, pformP, hc]
    · field_simp; ring
    · field_simp
      linear_combination hd'

/-- **The conic.**  `C = {u ≠ 0 : disc u = 0}` = the squares of linear forms `k · ℓ_A²`. -/
theorem onConic_iff (hF : ringChar F ≠ 2) (u : V3 F) :
    (u ≠ ⟨0, 0, 0⟩ ∧ disc u = 0) ↔ ∃ A : Option F, ∃ k : F, k ≠ 0 ∧ u = smul3 k (pformP A A) := by
  constructor
  · rintro ⟨hu, hd⟩
    obtain ⟨A, B, k, hk, rfl⟩ := split_of_disc hF hu (d := 0) (by rw [hd]; ring)
    rw [disc_smul3, disc_pformP] at hd
    have : dt (hc A) (hc B) = 0 := by
      have := (mul_eq_zero.mp hd).resolve_left (pow_ne_zero 2 hk)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    rw [(dt_hc_eq_zero_iff A B).mp this]
    exact ⟨B, k, hk, rfl⟩
  · rintro ⟨A, k, hk, rfl⟩
    refine ⟨?_, by rw [disc_smul3, disc_pformP, (dt_hc_eq_zero_iff A A).mpr rfl]; ring⟩
    intro h
    have h1 := congrArg V3.a h; have h2 := congrArg V3.b h; have h3 := congrArg V3.c h
    cases A <;> simp [smul3, pformP, hc, hk] at h1 h2 h3

/-- **External points ↔ pairs.**  A form has a nonzero square discriminant iff it is (up to a
scalar) `pformP A B` for two distinct points `A ≠ B` of `PG(1,q)`. -/
theorem external_iff (hF : ringChar F ≠ 2) (u : V3 F) :
    (∃ d : F, d ≠ 0 ∧ disc u = d ^ 2) ↔
      ∃ A B : Option F, A ≠ B ∧ ∃ k : F, k ≠ 0 ∧ u = smul3 k (pformP A B) := by
  constructor
  · rintro ⟨d, hd0, hd⟩
    have hu : u ≠ ⟨0, 0, 0⟩ := by
      rintro rfl; simp [disc] at hd; exact hd0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hd.symm)
    obtain ⟨A, B, k, hk, rfl⟩ := split_of_disc hF hu hd
    refine ⟨A, B, ?_, k, hk, rfl⟩
    rintro rfl
    rw [disc_smul3, disc_pformP, (dt_hc_eq_zero_iff A A).mpr rfl] at hd
    apply hd0; simpa using hd.symm
  · rintro ⟨A, B, hAB, k, hk, rfl⟩
    refine ⟨k * dt (hc A) (hc B), mul_ne_zero hk (fun h => hAB ((dt_hc_eq_zero_iff A B).mp h)), ?_⟩
    rw [disc_smul3, disc_pformP]; ring

/-! ## Passants -/

/-- `s U + t V`. -/
def lin2 (s t : F) (U V : V3 F) : V3 F := ⟨s * U.a + t * V.a, s * U.b + t * V.b, s * U.c + t * V.c⟩

/-- `U, V` span a line containing no point of the conic: `disc(sU + tV) ≠ 0` for `(s,t) ≠ 0`
(`passant_iff`: equivalently `U, V` are independent and no point `sU + tV` lies on the conic). -/
def Passant (U V : V3 F) : Prop := ∀ s t : F, ¬(s = 0 ∧ t = 0) → disc (lin2 s t U V) ≠ 0

theorem passant_iff (U V : V3 F) :
    Passant U V ↔ (∀ s t : F, ¬(s = 0 ∧ t = 0) → lin2 s t U V ≠ ⟨0, 0, 0⟩) ∧
      ∀ s t : F, ¬(lin2 s t U V ≠ ⟨0, 0, 0⟩ ∧ disc (lin2 s t U V) = 0) := by
  constructor
  · intro h
    refine ⟨fun s t hst h0 => h s t hst (by rw [h0]; simp [disc]), fun s t ⟨hne, hd⟩ => ?_⟩
    have hst : ¬(s = 0 ∧ t = 0) := by rintro ⟨rfl, rfl⟩; apply hne; simp [lin2]
    exact h s t hst hd
  · rintro ⟨h1, h2⟩ s t hst hd
    exact h2 s t ⟨h1 s t hst, hd⟩

/-- `a s² + 2 b s t + c t²` has no nontrivial zero iff `b² - ac` is a nonsquare. -/
theorem quad_no_zero_iff (a b c : F) :
    (∀ s t : F, ¬(s = 0 ∧ t = 0) → a * s ^ 2 + 2 * b * s * t + c * t ^ 2 ≠ 0) ↔
      quadraticChar F (b ^ 2 - a * c) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare]
  constructor
  · rintro h ⟨r, hr⟩
    by_cases ha : a = 0
    · exact h 1 0 (by simp) (by rw [ha]; ring)
    · apply h ((r - b) / a) 1 (by simp)
      field_simp
      linear_combination -hr
  · intro hns s t hst h0
    apply hns
    by_cases ha : a = 0
    · exact ⟨b, by rw [ha]; ring⟩
    by_cases ht : t = 0
    · subst ht
      have : a * s ^ 2 = 0 := by linear_combination h0
      exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp this).resolve_left ha)) (fun hs => hst ⟨hs, rfl⟩)
    · refine ⟨(a * s + b * t) / t, ?_⟩
      field_simp
      linear_combination (-a) * h0

/-- **The dictionary of the problem.**  Two pairs of `PG(1,q)` are compatible iff the line joining
the corresponding external points is a passant. -/
theorem compat_iff_passant (hF : ringChar F ≠ 2) (A B C D : Option F) :
    CompatP A B C D ↔ Passant (pformP A B) (pformP C D) := by
  set U := pformP A B
  set V := pformP C D
  set β := U.b * V.b - 2 * (U.a * V.c + U.c * V.a) with hβ
  have hdisc : ∀ s t, disc (lin2 s t U V) = disc U * s ^ 2 + 2 * β * s * t + disc V * t ^ 2 := by
    intro s t
    unfold disc lin2; rw [hβ]; ring
  have hres : β ^ 2 - disc U * disc V =
      2 ^ 2 * (dt (hc A) (hc C) * dt (hc A) (hc D) * dt (hc B) (hc C) * dt (hc B) (hc D)) := by
    simp only [hβ, U, V, disc, pformP, dt]; ring
  unfold Passant CompatP
  simp_rw [hdisc]
  rw [quad_no_zero_iff, hres, map_mul (quadraticChar F) (2 ^ 2), quadraticChar_sq_one' (two_ne_zero_F hF), one_mul]

/-! ## Möbius maps act linearly on forms -/

/-- The action of `M = (α β; γ δ)` on binary quadratic forms (symmetric square). -/
def Lmat (M : Mob F) (X : V3 F) : V3 F :=
  ⟨M.δ ^ 2 * X.a - M.γ * M.δ * X.b + M.γ ^ 2 * X.c,
   -2 * M.β * M.δ * X.a + (M.α * M.δ + M.β * M.γ) * X.b - 2 * M.α * M.γ * X.c,
   M.β ^ 2 * X.a - M.α * M.β * X.b + M.α ^ 2 * X.c⟩

theorem det3_Lmat (M : Mob F) (u v w : V3 F) :
    det3 (Lmat M u) (Lmat M v) (Lmat M w) = M.det ^ 3 * det3 u v w := by
  unfold det3 Lmat Mob.det; ring

theorem det3_smul3 (a b c : F) (u v w : V3 F) :
    det3 (smul3 a u) (smul3 b v) (smul3 c w) = a * b * c * det3 u v w := by
  unfold det3 smul3; ring

theorem pformP_map (M : Mob F) (X Y : Option F) :
    ∃ k : F, k ≠ 0 ∧ pformP (M.map X) (M.map Y) = smul3 k (Lmat M (pformP X Y)) := by
  obtain ⟨c, hc0, hcX⟩ := hc_proj (M.act_ne_zero (hc_ne_zero X))
  obtain ⟨d, hd0, hcY⟩ := hc_proj (M.act_ne_zero (hc_ne_zero Y))
  refine ⟨c * d, mul_ne_zero hc0 hd0, ?_⟩
  unfold pformP Mob.map
  rw [hcX, hcY]
  unfold smul3 Lmat Mob.act
  ext <;> simp <;> ring

/-! ## Arc-like solutions on `PG(1,q)` -/

/-- No three points `pformP A (Ψ A)` of the solution `Ψ` are collinear. -/
def ArcLikeP (Ψ : Option F → Option F) : Prop :=
  ∀ A B C : Option F, B ≠ A → B ≠ Ψ A → C ≠ A → C ≠ Ψ A → C ≠ B → C ≠ Ψ B →
    det3 (pformP A (Ψ A)) (pformP B (Ψ B)) (pformP C (Ψ C)) ≠ 0

/-- Arc-likeness is `PGL(2,q)`-invariant. -/
theorem arcLikeP_conj {Ψ : Option F → Option F} (h : ArcLikeP Ψ) (M : Mob F) :
    ArcLikeP (fun B => M.map (Ψ (M.inv.map B))) := by
  intro A B C h1 h2 h3 h4 h5 h6
  simp only at h2 h4 h6 ⊢
  have key : ∀ X : Option F, ∃ k : F, k ≠ 0 ∧
      pformP X (M.map (Ψ (M.inv.map X))) = smul3 k (Lmat M (pformP (M.inv.map X) (Ψ (M.inv.map X)))) := by
    intro X
    obtain ⟨k, hk, e⟩ := pformP_map M (M.inv.map X) (Ψ (M.inv.map X))
    rw [Mob.map_map_inv] at e
    exact ⟨k, hk, e⟩
  obtain ⟨ka, hka, ea⟩ := key A
  obtain ⟨kb, hkb, eb⟩ := key B
  obtain ⟨kc, hkc, ec⟩ := key C
  rw [ea, eb, ec, det3_smul3, det3_Lmat]
  have ne : ∀ {X Y : Option F}, X ≠ Y → M.inv.map X ≠ M.inv.map Y := by
    intro X Y hne he
    exact hne (by rw [← Mob.map_map_inv M X, he, Mob.map_map_inv])
  have neψ : ∀ {X Y : Option F}, X ≠ M.map (Ψ (M.inv.map Y)) →
      M.inv.map X ≠ Ψ (M.inv.map Y) := by
    intro X Y hne he
    exact hne (by rw [← he, Mob.map_map_inv])
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hka hkb) hkc)
    (mul_ne_zero (pow_ne_zero 3 M.det_ne_zero)
      (h _ _ _ (ne h1) (neψ h2) (ne h3) (neψ h4) (ne h5) (neψ h6)))

theorem psi_some_of_frame {Ψ : Option F → Option F} (hS : Solution Ψ) (h0 : Ψ (some 0) = none)
    {x : F} (hx : x ≠ 0) : Ψ (some x) = some (toPsi Ψ x) := by
  have hinf : Ψ none = some 0 := by rw [← h0, hS.invol]
  unfold toPsi
  cases e : Ψ (some x) with
  | none =>
    exfalso; apply hx
    have := congrArg Ψ e
    rw [hS.invol, hinf] at this
    exact Option.some_injective _ this
  | some y => rfl

/-- In the frame `P₀ = {0,∞}` the projective notion agrees with `BSW.Segre.ArcLike`. -/
theorem arcLike_of_arcLikeP {Ψ : Option F → Option F} (hS : Solution Ψ) (h0 : Ψ (some 0) = none)
    (harc : ArcLikeP Ψ) : ArcLike (toPsi Ψ) := by
  have hfin := fun x (hx : x ≠ 0) => psi_some_of_frame hS h0 hx
  constructor
  · intro x y hx hy hyx hyψ hd
    have e := harc (some 0) (some x) (some y) (by simpa using hx) (by rw [h0]; simp)
      (by simpa using hy) (by rw [h0]; simp) (by simpa using hyx)
      (by rw [hfin x hx]; simpa using hyψ)
    rw [h0, hfin x hx, hfin y hy, pformP_zero_inf, pformP_some, pformP_some] at e
    apply e
    have : smul3 (-1 : F) (p0 : V3 F) = smul3 (-1) p0 := rfl
    calc det3 (smul3 (-1) p0) (pf x (toPsi Ψ x)) (pf y (toPsi Ψ y))
        = -det3 p0 (pf x (toPsi Ψ x)) (pf y (toPsi Ψ y)) := by unfold det3 smul3; ring
      _ = 0 := by rw [hd, neg_zero]
  · intro x y z hx hy hz h1 h2 h3 h4 h5 h6 hd
    have e := harc (some x) (some y) (some z) (by simpa using h1) (by rw [hfin x hx]; simpa using h2)
      (by simpa using h3) (by rw [hfin x hx]; simpa using h4) (by simpa using h5)
      (by rw [hfin y hy]; simpa using h6)
    rw [hfin x hx, hfin y hy, hfin z hz, pformP_some, pformP_some, pformP_some] at e
    exact e hd

/-- **Theorem 7.5 (prime q) for an arbitrary solution on `PG(1,p)`** (no frame chosen), modulo `StickelHyp`:
for a prime `p ≡ 3 (mod 4)`, `p ∉ {3, 7, 11}`, the `(p+1)/2` external points of a solution always
contain three collinear points. -/
theorem theoremV_proj {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    (hp11 : p ≠ 11) (hst : BSW.Jacobi.StickelHyp p) {Ψ : Option (ZMod p) → Option (ZMod p)}
    (hS : Solution Ψ) : ¬ ArcLikeP Ψ := by
  intro harc
  obtain ⟨M, -, h0⟩ := normalize_pair hS none
  have hS' := hS.conj M
  exact BSW.TheoremV.theoremV hp4 hp3 hp7 hp11 hst (admissible_of_solution hS' h0)
    (arcLike_of_arcLikeP hS' h0 (arcLikeP_conj harc M))

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 10000 in
/-- Non-vacuity: the multiplicative starter at `q = 7`, as a solution on `PG(1,7)`, is arc-like. -/
theorem arcP7 : Solution (ofPsi BSW.Sporadic.psi7) ∧ ArcLikeP (ofPsi BSW.Sporadic.psi7) := by
  refine ⟨solution_of_admissible BSW.Sporadic.sporadic_7.1, ?_⟩
  unfold ArcLikeP
  decide +kernel

end BSW.Plane
