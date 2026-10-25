module

public import Mathlib
public import BSWCheck.Plane

@[expose] public section

/-!
# The case `q ≡ 1 (mod 4)` (Blokhuis–Seress–Wilbrink) for prime `q`, and Van de Voorde's conjecture for all primes

* `gS Ψ A B = χ(-det(A,ΨA) det(B,ΨB) det(A,ΨB) det(ΨA,B))` — the sign `γ(P,Q) = χ(1 - [P;Q])` of the
  paper for the ordered pairs `(A, ΨA)`, `(B, ΨB)` (Plücker: `1 - [P;Q]` differs by a square factor);
  `eS = γγγ` is the two-graph of the solution.
* `eS_orient` — `ε` does not depend on the order of the points inside the pairs; `gS_conj` — `γ`
  (hence `ε`) is `PGL(2,q)`-invariant.
* `Pairs Ψ` — the set of pairs of a solution (`2·|Pairs| = q + 1`).
* `twograph_pm` — two-graphs of odd order, multiplicative form.
* `parity_gen`, `parity_pairs` — Wilson parity (any odd prime `q`) in the frame of **every** pair.
* `bsw1` — **Blokhuis–Seress–Wilbrink theorem for prime `p ≡ 1 (mod 4)`**, assuming `CarlitzHyp p` (Carlitz's theorem: a map
  of `𝔽_p` all of whose difference quotients are nonzero squares is affine): every solution is elliptic.
* `vdv_prime` — **Van de Voorde's conjecture for all primes `p > 11`** (no solution on `PG(1,p)` is
  arc-like), assuming `StickelHyp p` if `p ≡ 3 (mod 4)` and `CarlitzHyp p` if `p ≡ 1 (mod 4)`.
-/

open Finset

namespace BSW.BSW1

open BSW.Basic BSW.Segre BSW.Proj BSW.Plane

set_option linter.unusedSectionVars false

section General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `D A B = det(hc A, hc B)`. -/
def D (A B : Option F) : F := dt (hc A) (hc B)

theorem D_ne {A B : Option F} (hAB : A ≠ B) : D A B ≠ 0 :=
  fun h => hAB ((dt_hc_eq_zero_iff A B).mp h)

theorem D_swap (A B : Option F) : D B A = -D A B := by unfold D dt; ring

/-- `γ` of the ordered pairs `(A, Ψ A)`, `(B, Ψ B)`. -/
def gS (Ψ : Option F → Option F) (A B : Option F) : ℤ :=
  quadraticChar F (-(D A (Ψ A) * D B (Ψ B) * D A (Ψ B) * D (Ψ A) B))

/-- The two-graph `ε = γ γ γ`. -/
def eS (Ψ : Option F → Option F) (A B C : Option F) : ℤ := gS Ψ A B * gS Ψ A C * gS Ψ B C

theorem gS_symm (Ψ : Option F → Option F) (A B : Option F) : gS Ψ A B = gS Ψ B A := by
  unfold gS; congr 1; rw [D_swap B (Ψ A), D_swap (Ψ B) A]; ring

variable {Ψ : Option F → Option F}

theorem gS_arg_ne (hS : Solution Ψ) {A B : Option F} (h2 : B ≠ Ψ A) :
    -(D A (Ψ A) * D B (Ψ B) * D A (Ψ B) * D (Ψ A) B) ≠ 0 := by
  have hA : A ≠ Ψ A := Ne.symm (hS.free A)
  have hB : B ≠ Ψ B := Ne.symm (hS.free B)
  have hAB : A ≠ Ψ B := by intro he; apply h2; rw [he, hS.invol]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (D_ne hA) (D_ne hB)) (D_ne hAB))
    (D_ne (Ne.symm h2)))

theorem gS_pm (hS : Solution Ψ) {A B : Option F} (h2 : B ≠ Ψ A) :
    gS Ψ A B = 1 ∨ gS Ψ A B = -1 :=
  quadraticChar_dichotomy (gS_arg_ne hS h2)

theorem gS_sq (hS : Solution Ψ) {A B : Option F} (h2 : B ≠ Ψ A) :
    gS Ψ A B * gS Ψ A B = 1 := chi_sq_one (gS_arg_ne hS h2)

/-- Reversing the pair `(A, ΨA)` multiplies `γ(·, B)` by `-χ(-1)`. -/
theorem gS_flip (hS : Solution Ψ) {A B : Option F} (h1 : B ≠ A) (h2 : B ≠ Ψ A) :
    gS Ψ (Ψ A) B = -quadraticChar F (-1) * gS Ψ A B := by
  have hcp := hS.cross A B h1 h2
  unfold CompatP at hcp
  have hA : A ≠ Ψ A := Ne.symm (hS.free A)
  have hB : B ≠ Ψ B := Ne.symm (hS.free B)
  have e1 : gS Ψ (Ψ A) B * gS Ψ A B = -quadraticChar F (-1) := by
    unfold gS
    rw [← map_mul, hS.invol A]
    have : -(D (Ψ A) A * D B (Ψ B) * D (Ψ A) (Ψ B) * D A B) *
        -(D A (Ψ A) * D B (Ψ B) * D A (Ψ B) * D (Ψ A) B) =
        (D A (Ψ A) * D B (Ψ B)) ^ 2 * (-1 * (dt (hc A) (hc B) * dt (hc A) (hc (Ψ B)) *
          dt (hc (Ψ A)) (hc B) * dt (hc (Ψ A)) (hc (Ψ B)))) := by
      rw [D_swap (Ψ A) A]; unfold D; ring
    rw [this, chi_sq_mul (mul_ne_zero (D_ne hA) (D_ne hB)), map_mul, hcp]; ring
  have e2 := gS_sq hS h2
  linear_combination gS Ψ A B * e1 - gS Ψ (Ψ A) B * e2

/-- Three points in pairwise different pairs. -/
def Tri (Ψ : Option F → Option F) (A B C : Option F) : Prop :=
  B ≠ A ∧ B ≠ Ψ A ∧ C ≠ A ∧ C ≠ Ψ A ∧ C ≠ B ∧ C ≠ Ψ B

theorem Tri.perm12 (hS : Solution Ψ) {A B C : Option F} (h : Tri Ψ A B C) : Tri Ψ B A C := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Ne.symm h1, ?_, h5, h6, h3, h4⟩
  intro he; apply h2; rw [he, hS.invol]

theorem Tri.perm23 (hS : Solution Ψ) {A B C : Option F} (h : Tri Ψ A B C) : Tri Ψ A C B := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h3, h4, h1, h2, Ne.symm h5, ?_⟩
  intro he; apply h6; rw [he, hS.invol]

theorem Tri.flip1 (hS : Solution Ψ) {A B C : Option F} (h : Tri Ψ A B C) : Tri Ψ (Ψ A) B C := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h2, by rw [hS.invol]; exact h1, h4, by rw [hS.invol]; exact h3, h5, h6⟩

theorem eS_flip1 (hS : Solution Ψ) {A B C : Option F} (h : Tri Ψ A B C) :
    eS Ψ (Ψ A) B C = eS Ψ A B C := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := h
  unfold eS
  rw [gS_flip hS h1 h2, gS_flip hS h3 h4]
  have := chi_sq_one (F := F) (a := -1) (neg_ne_zero.mpr one_ne_zero)
  linear_combination (gS Ψ A B * gS Ψ A C * gS Ψ B C) * this

theorem eS_perm12 (A B C : Option F) : eS Ψ B A C = eS Ψ A B C := by
  unfold eS; rw [gS_symm Ψ B A]; ring

theorem eS_perm23 (A B C : Option F) : eS Ψ A C B = eS Ψ A B C := by
  unfold eS; rw [gS_symm Ψ C B]; ring

theorem eS_rev (A B C : Option F) : eS Ψ A B C = eS Ψ C B A := by
  unfold eS; rw [gS_symm Ψ C B, gS_symm Ψ C A, gS_symm Ψ B A]; ring

/-- **`ε` does not depend on the order inside the pairs.** -/
theorem eS_orient (hS : Solution Ψ) {A B C A' B' C' : Option F} (h : Tri Ψ A B C)
    (hA : A' = A ∨ A' = Ψ A) (hB : B' = B ∨ B' = Ψ B) (hC : C' = C ∨ C' = Ψ C) :
    eS Ψ A' B' C' = eS Ψ A B C := by
  have stepA : ∀ {X Y Z X' : Option F}, Tri Ψ X Y Z → (X' = X ∨ X' = Ψ X) →
      eS Ψ X' Y Z = eS Ψ X Y Z ∧ Tri Ψ X' Y Z := by
    intro X Y Z X' hT hX
    rcases hX with rfl | rfl
    · exact ⟨rfl, hT⟩
    · exact ⟨eS_flip1 hS hT, hT.flip1 hS⟩
  obtain ⟨e1, t1⟩ := stepA h hA
  obtain ⟨e2, t2⟩ := stepA (t1.perm12 hS) hB
  obtain ⟨e3, -⟩ := stepA ((t2.perm23 hS).perm12 hS) hC
  calc eS Ψ A' B' C' = eS Ψ C' B' A' := eS_rev _ _ _
    _ = eS Ψ C B' A' := e3
    _ = eS Ψ A' B' C := (eS_rev _ _ _).symm
    _ = eS Ψ B' A' C := eS_perm12 _ _ _
    _ = eS Ψ B A' C := e2
    _ = eS Ψ A' B C := eS_perm12 _ _ _
    _ = eS Ψ A B C := e1

/-- **`γ` is `PGL(2,q)`-invariant.** -/
theorem gS_conj (M : Mob F) (A B : Option F) :
    gS (fun X => M.map (Ψ (M.inv.map X))) (M.map A) (M.map B) = gS Ψ A B := by
  have hcm : ∀ X : Option F, ∃ c : F, c ≠ 0 ∧
      hc (M.map X) = (c * (M.act (hc X)).1, c * (M.act (hc X)).2) :=
    fun X => hc_proj (M.act_ne_zero (hc_ne_zero X))
  have Dm : ∀ {X Y : Option F} {cX cY : F},
      hc (M.map X) = (cX * (M.act (hc X)).1, cX * (M.act (hc X)).2) →
      hc (M.map Y) = (cY * (M.act (hc Y)).1, cY * (M.act (hc Y)).2) →
      D (M.map X) (M.map Y) = cX * cY * M.det * D X Y := by
    intro X Y cX cY hX hY
    unfold D; rw [hX, hY]; unfold dt Mob.act Mob.det; ring
  obtain ⟨a, ha, hA⟩ := hcm A
  obtain ⟨a', ha', hA'⟩ := hcm (Ψ A)
  obtain ⟨b, hb, hB⟩ := hcm B
  obtain ⟨b', hb', hB'⟩ := hcm (Ψ B)
  unfold gS
  simp only [Mob.map_inv_map]
  rw [Dm hA hA', Dm hB hB', Dm hA hB', Dm hA' hB]
  have : -(a * a' * M.det * D A (Ψ A) * (b * b' * M.det * D B (Ψ B)) *
      (a * b' * M.det * D A (Ψ B)) * (a' * b * M.det * D (Ψ A) B)) =
      (a * a' * b * b' * M.det ^ 2) ^ 2 * -(D A (Ψ A) * D B (Ψ B) * D A (Ψ B) * D (Ψ A) B) := by
    ring
  rw [this, chi_sq_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha ha') hb) hb')
    (pow_ne_zero 2 M.det_ne_zero))]

theorem conj_map (M : Mob F) (A : Option F) :
    (fun X => M.map (Ψ (M.inv.map X))) (M.map A) = M.map (Ψ A) := by
  simp only [Mob.map_inv_map]

theorem eS_conj (M : Mob F) (A B C : Option F) :
    eS (fun X => M.map (Ψ (M.inv.map X))) (M.map A) (M.map B) (M.map C) = eS Ψ A B C := by
  unfold eS; rw [gS_conj, gS_conj, gS_conj]

/-! ## The set of pairs -/

/-- The pair `{A, Ψ A}`. -/
def pairOf (Ψ : Option F → Option F) (A : Option F) : Finset (Option F) := {A, Ψ A}

/-- All pairs of `Ψ`. -/
def Pairs (Ψ : Option F → Option F) : Finset (Finset (Option F)) := univ.image (pairOf Ψ)

theorem mem_pairOf {A X : Option F} : X ∈ pairOf Ψ A ↔ X = A ∨ X = Ψ A := by
  simp [pairOf]

theorem pairOf_eq_iff (hS : Solution Ψ) {A B : Option F} :
    pairOf Ψ B = pairOf Ψ A ↔ B = A ∨ B = Ψ A := by
  constructor
  · intro h
    have : B ∈ pairOf Ψ A := by rw [← h]; exact mem_pairOf.mpr (Or.inl rfl)
    exact mem_pairOf.mp this
  · rintro (rfl | rfl)
    · rfl
    · unfold pairOf; rw [hS.invol, Finset.pair_comm]

theorem card_pairOf (hS : Solution Ψ) (A : Option F) : (pairOf Ψ A).card = 2 :=
  Finset.card_pair (Ne.symm (hS.free A))

theorem two_mul_card_Pairs (hS : Solution Ψ) :
    2 * (Pairs Ψ).card = Fintype.card (Option F) := by
  rw [← card_univ, card_eq_sum_card_image (pairOf Ψ) univ]
  unfold Pairs
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl (fun P hP => ?_)
  obtain ⟨B, -, rfl⟩ := mem_image.mp hP
  rw [← card_pairOf hS B]
  congr 1
  ext X
  simp only [mem_filter, mem_univ, true_and]
  rw [pairOf_eq_iff hS, mem_pairOf]

/-- An orientation of a pair (any of its points). -/
noncomputable def o (P : Finset (Option F)) : Option F :=
  if h : P.Nonempty then h.choose else none

theorem o_mem {P : Finset (Option F)} (h : P.Nonempty) : o P ∈ P := by
  unfold o; rw [dite_eq_left h]; exact h.choose_spec

theorem o_pairOf (A : Option F) : o (pairOf Ψ A) = A ∨ o (pairOf Ψ A) = Ψ A :=
  mem_pairOf.mp (o_mem ⟨A, mem_pairOf.mpr (Or.inl rfl)⟩)

/-- `γ` and `ε` on pairs. -/
noncomputable def gP (Ψ : Option F → Option F) (P Q : Finset (Option F)) : ℤ := gS Ψ (o P) (o Q)

noncomputable def eP (Ψ : Option F → Option F) (P X Y : Finset (Option F)) : ℤ :=
  gP Ψ P X * gP Ψ P Y * gP Ψ X Y

theorem Tri_of_pairs (hS : Solution Ψ) {A B C : Option F} (h1 : pairOf Ψ B ≠ pairOf Ψ A)
    (h2 : pairOf Ψ C ≠ pairOf Ψ A) (h3 : pairOf Ψ C ≠ pairOf Ψ B) : Tri Ψ A B C := by
  simp only [ne_eq, pairOf_eq_iff hS, not_or] at h1 h2 h3
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩

theorem eP_pairOf (hS : Solution Ψ) {A B C : Option F} (h1 : pairOf Ψ B ≠ pairOf Ψ A)
    (h2 : pairOf Ψ C ≠ pairOf Ψ A) (h3 : pairOf Ψ C ≠ pairOf Ψ B) :
    eP Ψ (pairOf Ψ A) (pairOf Ψ B) (pairOf Ψ C) = eS Ψ A B C :=
  eS_orient hS (Tri_of_pairs hS h1 h2 h3) (o_pairOf A) (o_pairOf B) (o_pairOf C)

theorem gP_symm (P Q : Finset (Option F)) : gP Ψ P Q = gP Ψ Q P := gS_symm Ψ _ _

theorem gP_pm (hS : Solution Ψ) {P Q : Finset (Option F)} (hP : P ∈ Pairs Ψ) (hQ : Q ∈ Pairs Ψ)
    (hPQ : P ≠ Q) : gP Ψ P Q = 1 ∨ gP Ψ P Q = -1 := by
  obtain ⟨A, -, rfl⟩ := mem_image.mp hP
  obtain ⟨B, -, rfl⟩ := mem_image.mp hQ
  have hne : pairOf Ψ (o (pairOf Ψ B)) ≠ pairOf Ψ (o (pairOf Ψ A)) := by
    have e : ∀ X, pairOf Ψ (o (pairOf Ψ X)) = pairOf Ψ X := fun X =>
      (pairOf_eq_iff hS).mpr (o_pairOf X)
    rw [e, e]; exact Ne.symm hPQ
  rw [ne_eq, pairOf_eq_iff hS, not_or] at hne
  exact gS_pm hS hne.2

/-! ## Two-graphs of odd order (multiplicative form) -/

theorem prod_pm {α : Type*} (s : Finset α) (f : α → ℤ) (h : ∀ a ∈ s, f a = 1 ∨ f a = -1) :
    (∏ a ∈ s, f a) = 1 ∨ (∏ a ∈ s, f a) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    rcases h a (mem_insert_self a s) with h1 | h1 <;>
      rcases ih (fun b hb => h b (mem_insert_of_mem hb)) with h2 | h2 <;>
      simp [h1, h2]

theorem twograph_pm {α : Type*} [DecidableEq α] (V : Finset α) (g : α → α → ℤ)
    (hsym : ∀ a b, g a b = g b a)
    (hpm : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → g a b = 1 ∨ g a b = -1) (hodd : Odd V.card)
    (heul : ∀ P ∈ V, ∀ X ∈ V, P ≠ X →
      ∏ Y ∈ (V.erase P).erase X, (g P X * g P Y * g X Y) = 1) :
    ∀ P ∈ V, ∀ X ∈ V, ∀ Y ∈ V, P ≠ X → P ≠ Y → X ≠ Y → g P X * g P Y * g X Y = 1 := by
  set σ : α → ℤ := fun a => ∏ Y ∈ V.erase a, g a Y with hσ
  have hσpm : ∀ a ∈ V, σ a * σ a = 1 := by
    intro a ha
    rcases prod_pm (V.erase a) (g a) (fun b hb => hpm a ha b (mem_of_mem_erase hb)
      (Ne.symm (ne_of_mem_erase hb))) with h | h <;> simp [hσ, h]
  have key : ∀ P ∈ V, ∀ X ∈ V, P ≠ X → g P X = σ P * σ X := by
    intro P hP X hX hPX
    have hg : g P X * g P X = 1 := by
      rcases hpm P hP X hX hPX with h | h <;> rw [h] <;> norm_num
    have e := heul P hP X hX hPX
    rw [prod_mul_distrib, prod_mul_distrib, prod_const] at e
    have hXm : X ∈ V.erase P := mem_erase.mpr ⟨Ne.symm hPX, hX⟩
    have hPm : P ∈ V.erase X := mem_erase.mpr ⟨hPX, hP⟩
    have eP : σ P = g P X * ∏ Y ∈ (V.erase P).erase X, g P Y := by
      simp only [hσ]; rw [mul_prod_erase _ _ hXm]
    have eX : σ X = g X P * ∏ Y ∈ (V.erase P).erase X, g X Y := by
      simp only [hσ]; rw [erase_right_comm, mul_prod_erase _ _ hPm]
    rw [hsym X P] at eX
    have hcard : ((V.erase P).erase X).card + 2 = V.card := by
      rw [card_erase_of_mem hXm, card_erase_of_mem hP]
      have : 2 ≤ V.card := by
        have := card_le_card (show {P, X} ⊆ V by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
        rw [card_pair hPX] at this; exact this
      omega
    obtain ⟨k, hk⟩ := hodd
    have hcard' : ((V.erase P).erase X).card = 2 * k - 1 := by omega
    -- `g^(2k-1) = g`
    have hpow : g P X ^ (2 * k - 1) = g P X := by
      have hk1 : 1 ≤ k := by omega
      rw [show 2 * k - 1 = 2 * (k - 1) + 1 by omega, pow_succ, pow_mul, sq, hg, one_pow, one_mul]
    rw [hcard', hpow] at e
    -- `e : g * A_P * A_X = 1`, `σ P = g A_P`, `σ X = g A_X`
    linear_combination (-g P X) * e - σ X * eP -
      (g P X * ∏ Y ∈ (V.erase P).erase X, g P Y) * eX
  intro P hP X hX Y hY hPX hPY hXY
  rw [key P hP X hX hPX, key P hP Y hY hPY, key X hX Y hY hXY]
  have h1 := hσpm P hP; have h2 := hσpm X hX; have h3 := hσpm Y hY
  linear_combination (σ X * σ X * σ Y * σ Y) * h1 + σ Y * σ Y * h2 + h3

end General


/-! ## Prime fields -/

section FieldCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

theorem chi_neg_one_eq (hpn : Fintype.card F = 2 * n + 1) : quadraticChar F (-1) = (-1) ^ n := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow]; exact (chi_one_iff hpn (-1)).2 he.neg_one_pow
  · rw [ho.neg_one_pow]; exact (chi_neg_iff hpn (-1)).2 ho.neg_one_pow

/-- **Wilson parity in the frame `P₀`, any `n`**: `∏_{y square, y ≠ x} χ((x-y)(ψx-ψy)) = (-1)^(n-1)`. -/
theorem parity_gen (hpn : Fintype.card F = 2 * n + 1) (hn : 0 < n) {ψ : F → F} (h : Admissible ψ)
    {x : F} (hx : x ^ n = 1) :
    ∏ y ∈ (SQ (F := F) n).erase x, quadraticChar F ((x - y) * (ψ x - ψ y)) = (-1) ^ (n - 1) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ρ, hρ⟩ := BSW.FB.exists_primitive (n := n) hpn
  have hx0 : x ≠ 0 := pow_ne_zero_of hn one_ne_zero hx
  have hψx0 := h.ne_zero x hx0
  have hχx : quadraticChar F x = 1 := (chi_one_iff hpn x).2 hx
  have hψxn : (ψ x) ^ n = -1 := by
    rw [← chi_neg_iff hpn, h.swap x hx0, hχx]
  have hP1 : ∏ y ∈ (SQ (F := F) n).erase x, (x - y) = x ^ (n - 1) * (n : F) := by
    have e : SQ (F := F) n = univ.filter (fun z : F => z ^ n = x ^ n) := by
      ext z; simp [SQ, hx]
    rw [e]; exact BSW.FB.prod_coset_erase hρ hx0
  have hP2 : ∏ y ∈ (SQ (F := F) n).erase x, (ψ x - ψ y) = (ψ x) ^ (n - 1) * (n : F) := by
    have e : NS (F := F) n = univ.filter (fun z : F => z ^ n = (ψ x) ^ n) := by
      ext z; simp [NS, hψxn]
    rw [← BSW.FB.prod_coset_erase hρ hψx0, ← e]
    have hsq : ∀ y ∈ (SQ (F := F) n).erase x, y ≠ 0 ∧ y ^ n = 1 ∧ y ≠ x := by
      intro y hy
      rw [mem_erase] at hy
      have hyn : y ^ n = 1 := by simpa [SQ] using hy.2
      exact ⟨pow_ne_zero_of hn one_ne_zero hyn, hyn, hy.1⟩
    have hns : ∀ z ∈ (NS (F := F) n).erase (ψ x), z ≠ 0 ∧ z ^ n = -1 ∧ z ≠ ψ x := by
      intro z hz
      rw [mem_erase] at hz
      have hzn : z ^ n = -1 := by simpa [NS] using hz.2
      exact ⟨pow_ne_zero_of hn (neg_ne_zero.mpr one_ne_zero) hzn, hzn, hz.1⟩
    refine prod_nbij' ψ ψ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨hy0, hyn, hyx⟩ := hsq y hy
      rw [mem_erase]
      refine ⟨fun he => hyx (psi_inj h hy0 hx0 he), ?_⟩
      simp only [NS, mem_filter, mem_univ, true_and]
      rw [← chi_neg_iff hpn, h.swap y hy0, (chi_one_iff hpn y).2 hyn]
    · intro z hz
      obtain ⟨hz0, hzn, hzx⟩ := hns z hz
      rw [mem_erase]
      refine ⟨fun he => hzx (by rw [← he, h.invol z hz0]), ?_⟩
      simp only [SQ, mem_filter, mem_univ, true_and]
      rw [← chi_one_iff hpn, h.swap z hz0, (chi_neg_iff hpn z).2 hzn, neg_neg]
    · intro y hy; exact h.invol y (hsq y hy).1
    · intro z hz; exact h.invol z (hns z hz).1
    · intro y _; rfl
  rw [← map_prod, prod_mul_distrib, hP1, hP2,
    show x ^ (n - 1) * (n : F) * ((ψ x) ^ (n - 1) * (n : F)) =
      (x * ψ x) ^ (n - 1) * (n : F) ^ 2 by ring,
    map_mul, map_pow, chi_mul_psi h hx0, quadraticChar_sq_one' (n_ne_zero hpn hn), mul_one]

theorem D_ss (a b : F) : D (some a) (some b) = a - b := by simp [D, dt, hc]
theorem D_sn (a : F) : D (some a) none = -1 := by simp [D, dt, hc]
theorem D_ns (b : F) : D none (some b) = 1 := by simp [D, dt, hc]

variable {Ψ : Option F → Option F}

/-- `ε(P₀, X, Y)` in coordinates. -/
theorem eS_frame (hS : Solution Ψ) (h0 : Ψ (some 0) = none) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) (hyx : y ≠ x) (hyψ : y ≠ toPsi Ψ x) :
    eS Ψ (some 0) (some x) (some y) = -quadraticChar F (-1) *
      quadraticChar F (toPsi Ψ x * toPsi Ψ y) *
      quadraticChar F ((x - y) * (toPsi Ψ x - toPsi Ψ y)) := by
  have hadm := admissible_of_solution hS h0
  set ψ := toPsi Ψ with hψ
  have hfx := psi_some_of_frame hS h0 hx
  have hfy := psi_some_of_frame hS h0 hy
  have hc := hadm.cross x y hx hy hyx hyψ
  unfold eS gS
  rw [h0, hfx, hfy]
  simp only [D_sn, D_ss, D_ns]
  rw [← map_mul, ← map_mul]
  have hxx : x - ψ x ≠ 0 := sub_ne_zero.mpr (Ne.symm (psi_ne_self hadm hx))
  have hyy : y - ψ y ≠ 0 := sub_ne_zero.mpr (Ne.symm (psi_ne_self hadm hy))
  have e : -(-1 * (x - ψ x) * (0 - ψ x) * 1) * -(-1 * (y - ψ y) * (0 - ψ y) * 1) *
      -((x - ψ x) * (y - ψ y) * (x - ψ y) * (ψ x - y)) =
      ((x - ψ x) * (y - ψ y)) ^ 2 * (-1 * (ψ x * ψ y) * ((x - ψ y) * (ψ x - y))) := by ring
  rw [e, chi_sq_mul (mul_ne_zero hxx hyy), map_mul, map_mul]
  have hc' : quadraticChar F ((x - ψ y) * (ψ x - y)) *
      quadraticChar F ((x - y) * (ψ x - ψ y)) = -1 := by
    rw [← map_mul, ← hc]; congr 1; ring
  have hsq : quadraticChar F ((x - y) * (ψ x - ψ y)) *
      quadraticChar F ((x - y) * (ψ x - ψ y)) = 1 := by
    apply chi_sq_one
    refine mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyx)) (sub_ne_zero.mpr ?_)
    intro he; exact hyx (psi_inj hadm hy hx he.symm)
  linear_combination (quadraticChar F (-1) * quadraticChar F (ψ x * ψ y) *
    quadraticChar F ((x - y) * (ψ x - ψ y))) * hc' -
    (quadraticChar F (-1) * quadraticChar F (ψ x * ψ y) *
      quadraticChar F ((x - ψ y) * (ψ x - y))) * hsq

/-- **Wilson parity at `P₀`** (any odd prime): every descendant at `P₀ = {0,∞}` is Eulerian, as a product
over the pairs of the solution. -/
theorem parity_P0 (hpn : Fintype.card F = 2 * n + 1) (hn : 0 < n) (hS : Solution Ψ) (h0 : Ψ (some 0) = none)
    {X : Finset (Option F)} (hX : X ∈ Pairs Ψ) (hX0 : X ≠ pairOf Ψ (some 0)) :
    ∏ Y ∈ ((Pairs Ψ).erase (pairOf Ψ (some 0))).erase X, eP Ψ (pairOf Ψ (some 0)) X Y = 1 := by
  have hadm := admissible_of_solution hS h0
  set ψ := toPsi Ψ with hψ
  have hinf : Ψ none = some 0 := by rw [← h0, hS.invol]
  have hfin := fun x (hx : x ≠ 0) => psi_some_of_frame hS h0 hx
  -- the pair `X` through a square `x`
  obtain ⟨B, -, rfl⟩ := mem_image.mp hX
  obtain ⟨x, hxn, hXx⟩ : ∃ x : F, x ^ n = 1 ∧ pairOf Ψ B = pairOf Ψ (some x) := by
    cases B with
    | none => exact absurd ((pairOf_eq_iff hS).mpr (Or.inr h0.symm)) hX0
    | some b =>
      by_cases hb : b = 0
      · subst hb; exact absurd rfl hX0
      refine ⟨sqrep ψ b, sqrep_sq hpn hadm hb, ((pairOf_eq_iff hS).mpr ?_).symm⟩
      rcases sqrep_mem (ψ := ψ) b with e | e
      · left; rw [e]
      · right; rw [hfin b hb, e]
  rw [hXx] at hX0 ⊢
  have hx0 : x ≠ 0 := pow_ne_zero_of hn one_ne_zero hxn
  have hsqψ : ∀ s t : F, s ≠ 0 → s ^ n = 1 → t ^ n = 1 → t ≠ ψ s := by
    intro s t hs0 hs ht he
    rw [← chi_one_iff hpn] at hs ht
    rw [he, hadm.swap s hs0, hs] at ht; norm_num at ht
  -- reindex by the squares
  set pr : F → Finset (Option F) := fun y => pairOf Ψ (some y) with hpr
  have hinj : Set.InjOn pr ((SQ (F := F) n).erase x) := by
    intro y1 hy1 y2 hy2 he
    have h1 : y1 ^ n = 1 := by simpa [SQ] using (mem_erase.mp hy1).2
    have h2 : y2 ^ n = 1 := by simpa [SQ] using (mem_erase.mp hy2).2
    have hy10 := pow_ne_zero_of hn one_ne_zero h1
    have hy20 := pow_ne_zero_of hn one_ne_zero h2
    rcases (pairOf_eq_iff hS).mp he with e | e
    · exact Option.some_injective _ e
    · rw [hfin y2 hy20] at e
      exact absurd (Option.some_injective _ e) (hsqψ y2 y1 hy20 h2 h1)
  have himg : ((SQ (F := F) n).erase x).image pr =
      ((Pairs Ψ).erase (pairOf Ψ (some 0))).erase (pairOf Ψ (some x)) := by
    ext Y
    simp only [mem_image, mem_erase]
    constructor
    · rintro ⟨y, ⟨hyx, hy⟩, rfl⟩
      have hyn : y ^ n = 1 := by simpa [SQ] using hy
      have hy0 := pow_ne_zero_of hn one_ne_zero hyn
      refine ⟨?_, ?_, mem_image.mpr ⟨some y, mem_univ _, rfl⟩⟩
      · rw [hpr]; simp only; rw [ne_eq, pairOf_eq_iff hS, not_or]
        refine ⟨fun e => hyx (Option.some_injective _ e), ?_⟩
        rw [hfin x hx0]; intro e
        exact hsqψ x y hx0 hxn hyn (Option.some_injective _ e)
      · rw [hpr]; simp only; rw [ne_eq, pairOf_eq_iff hS, not_or, h0]
        exact ⟨fun e => hy0 (Option.some_injective _ e), by simp⟩
    · rintro ⟨hYx, hY0, hY⟩
      obtain ⟨C, -, rfl⟩ := mem_image.mp hY
      cases C with
      | none => exact absurd ((pairOf_eq_iff hS).mpr (Or.inr h0.symm)) hY0
      | some c =>
        by_cases hc : c = 0
        · subst hc; exact absurd rfl hY0
        have hrep : pairOf Ψ (some c) = pr (sqrep ψ c) := by
          rw [hpr]; simp only
          refine ((pairOf_eq_iff hS).mpr ?_).symm
          rcases sqrep_mem (ψ := ψ) c with e | e
          · left; rw [e]
          · right; rw [hfin c hc, e]
        refine ⟨sqrep ψ c, ⟨?_, by simp [SQ, sqrep_sq hpn hadm hc]⟩, hrep.symm⟩
        intro he; apply hYx; rw [hrep, he]
  rw [← himg, prod_image hinj]
  -- values
  have hval : ∀ y ∈ (SQ (F := F) n).erase x, eP Ψ (pairOf Ψ (some 0)) (pairOf Ψ (some x)) (pr y) =
      -quadraticChar F (-1) * quadraticChar F ((x - y) * (ψ x - ψ y)) := by
    intro y hy
    have hyn : y ^ n = 1 := by simpa [SQ] using (mem_erase.mp hy).2
    have hyx : y ≠ x := (mem_erase.mp hy).1
    have hy0 := pow_ne_zero_of hn one_ne_zero hyn
    have hyψ : y ≠ ψ x := hsqψ x y hx0 hxn hyn
    have n1 : pairOf Ψ (some x) ≠ pairOf Ψ (some 0) := hX0
    have n2 : pr y ≠ pairOf Ψ (some 0) := by
      rw [hpr]; simp only; rw [ne_eq, pairOf_eq_iff hS, not_or, h0]
      exact ⟨fun e => hy0 (Option.some_injective _ e), by simp⟩
    have n3 : pr y ≠ pairOf Ψ (some x) := by
      rw [hpr]; simp only; rw [ne_eq, pairOf_eq_iff hS, not_or, hfin x hx0]
      exact ⟨fun e => hyx (Option.some_injective _ e),
        fun e => hyψ (Option.some_injective _ e)⟩
    rw [hpr] at n2 n3 ⊢
    rw [eP_pairOf hS n1 n2 n3, eS_frame hS h0 hx0 hy0 hyx hyψ]
    have hχ : quadraticChar F (ψ x * ψ y) = 1 := by
      rw [map_mul, hadm.swap x hx0, hadm.swap y hy0, (chi_one_iff hpn x).2 hxn,
        (chi_one_iff hpn y).2 hyn]; norm_num
    rw [hχ, mul_one]
  rw [prod_congr rfl hval, prod_mul_distrib, prod_const, parity_gen hpn hn hadm hxn]
  have hcard : ((SQ (F := F) n).erase x).card = n - 1 := by
    rw [card_erase_of_mem (by simp [SQ, hxn]), card_SQ hpn]
  rw [hcard, chi_neg_one_eq hpn, ← mul_pow, show -(-1 : ℤ) ^ n * -1 = (-1) ^ n by ring, ← pow_mul]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n * (n - 1) = 2 * (k * (n - 1)) by rw [hk]; ring, pow_mul]; norm_num
  · rw [show n * (n - 1) = 2 * (n * k) by rw [hk]; simp; ring, pow_mul]; norm_num

/-- **Wilson parity in the frame of every pair** (any odd prime): all descendants of the two-graph of a
solution on `PG(1,p)` are Eulerian. -/
theorem parity_pairs (hpn : Fintype.card F = 2 * n + 1) (hn : 0 < n) (hS : Solution Ψ)
    {P X : Finset (Option F)} (hP : P ∈ Pairs Ψ) (hX : X ∈ Pairs Ψ) (hPX : P ≠ X) :
    ∏ Y ∈ ((Pairs Ψ).erase P).erase X, eP Ψ P X Y = 1 := by
  obtain ⟨A, -, rfl⟩ := mem_image.mp hP
  obtain ⟨M, hor, h0⟩ := normalize_pair hS A
  set Ψ' := fun B => M.map (Ψ (M.inv.map B)) with hΨ'
  have hS' : Solution Ψ' := hS.conj M
  set φ : Finset (Option F) → Finset (Option F) := fun Q => Q.image M.map with hφ
  have hφinj : Function.Injective φ := Finset.image_injective (Mob.map_injective M)
  have hφpair : ∀ B, φ (pairOf Ψ B) = pairOf Ψ' (M.map B) := by
    intro B
    simp only [hφ, pairOf, image_insert, image_singleton, hΨ', Mob.map_inv_map]
  have hPairs : Pairs Ψ' = (Pairs Ψ).image φ := by
    ext Q
    simp only [Pairs, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨C, rfl⟩
      exact ⟨pairOf Ψ (M.inv.map C), ⟨_, rfl⟩, by rw [hφpair, Mob.map_map_inv]⟩
    · rintro ⟨Q', ⟨C, rfl⟩, rfl⟩
      exact ⟨M.map C, (hφpair C).symm⟩
  have hφP : φ (pairOf Ψ A) = pairOf Ψ' (some 0) := by
    rw [hφpair]
    rcases hor with e | e
    · rw [e]
    · apply (pairOf_eq_iff hS').mpr
      right
      rw [← e]
      show M.map A = M.map (Ψ (M.inv.map (M.map (Ψ A))))
      rw [Mob.map_inv_map, hS.invol]
  -- values are preserved
  have hval : ∀ Y ∈ ((Pairs Ψ).erase (pairOf Ψ A)).erase X,
      eP Ψ (pairOf Ψ A) X Y = eP Ψ' (φ (pairOf Ψ A)) (φ X) (φ Y) := by
    intro Y hY
    obtain ⟨hYX, hYP, hY'⟩ := by simpa only [mem_erase] using hY
    obtain ⟨B, -, rfl⟩ := mem_image.mp hX
    obtain ⟨C, -, rfl⟩ := mem_image.mp hY'
    rw [hφpair, hφpair, hφpair, eP_pairOf hS (Ne.symm hPX) hYP hYX]
    have n1 : pairOf Ψ' (M.map B) ≠ pairOf Ψ' (M.map A) := by
      rw [← hφpair, ← hφpair]; exact fun e => hPX (hφinj e).symm
    have n2 : pairOf Ψ' (M.map C) ≠ pairOf Ψ' (M.map A) := by
      rw [← hφpair, ← hφpair]; exact fun e => hYP (hφinj e)
    have n3 : pairOf Ψ' (M.map C) ≠ pairOf Ψ' (M.map B) := by
      rw [← hφpair, ← hφpair]; exact fun e => hYX (hφinj e)
    rw [eP_pairOf hS' n1 n2 n3, hΨ', eS_conj]
  rw [prod_congr rfl hval, ← prod_image (f := fun Y => eP Ψ' (φ (pairOf Ψ A)) (φ X) Y)
    (fun a _ b _ e => hφinj e), image_erase hφinj, image_erase hφinj, ← hPairs, hφP]
  apply parity_P0 hpn hn hS' h0
  · rw [hPairs]; exact mem_image_of_mem φ hX
  · rw [← hφP]; exact fun e => hPX (hφinj e).symm

theorem pair_ne_P0 (hS : Solution Ψ) (h0 : Ψ (some 0) = none) {x : F} (hx : x ≠ 0) :
    pairOf Ψ (some x) ≠ pairOf Ψ (some 0) := by
  rw [ne_eq, pairOf_eq_iff hS, not_or, h0]
  exact ⟨fun e => hx (Option.some_injective _ e), by simp⟩

theorem pair_ne_sq (hpn : Fintype.card F = 2 * n + 1) (hn : 0 < n) (hS : Solution Ψ) (h0 : Ψ (some 0) = none)
    {x y : F} (hxn : x ^ n = 1) (hyn : y ^ n = 1) (hxy : x ≠ y) :
    pairOf Ψ (some y) ≠ pairOf Ψ (some x) := by
  have hadm := admissible_of_solution hS h0
  have hx0 := pow_ne_zero_of hn one_ne_zero hxn
  rw [ne_eq, pairOf_eq_iff hS, not_or, psi_some_of_frame hS h0 hx0]
  refine ⟨fun e => hxy (Option.some_injective _ e).symm, fun e => ?_⟩
  have e' := Option.some_injective _ e
  rw [← chi_one_iff hpn] at hxn hyn
  rw [e', hadm.swap x hx0, hxn] at hyn; norm_num at hyn

/-- `f(s) = ψ(1/s)`, `f(0) = 0`. -/
def fq (Ψ : Option F → Option F) (s : F) : F := if s = 0 then 0 else toPsi Ψ s⁻¹

/-- **Core of the Blokhuis–Seress–Wilbrink theorem (`q ≡ 1 mod 4`, any finite field)**: in the frame `P₀` the two-graph of a solution
is trivial, hence all difference quotients of `f(s) = ψ(1/s)` (`f(0) = 0`) are nonsquares. -/
theorem quot_nonsq (hpn : Fintype.card F = 2 * n + 1) (heven : Even n) (hn : 0 < n)
    (hS : Solution Ψ) (h0 : Ψ (some 0) = none) :
    ∀ s t : F, s ≠ t → quadraticChar F ((fq Ψ s - fq Ψ t) / (s - t)) = -1 := by
  have hadm := admissible_of_solution hS h0
  set ψ := toPsi Ψ with hψ
  have hχm1 : quadraticChar F (-1) = 1 := by rw [chi_neg_one_eq hpn, heven.neg_one_pow]
  -- the two-graph is trivial
  have hodd : Odd (Pairs Ψ).card := by
    have e := two_mul_card_Pairs hS
    rw [Fintype.card_option, hpn] at e
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by omega⟩
  have htg := twograph_pm (Pairs Ψ) (gP Ψ) gP_symm (fun a ha b hb hab => gP_pm hS ha hb hab) hodd
    (fun P hP X hX hPX => parity_pairs hpn hn hS hP hX hPX)
  have hmem : ∀ A, pairOf Ψ A ∈ Pairs Ψ := fun A => mem_image_of_mem _ (mem_univ A)
  -- step 1: `T(x,y) = -1` for squares
  have hT : ∀ x y : F, x ^ n = 1 → y ^ n = 1 → x ≠ y →
      quadraticChar F ((x - y) * (ψ x - ψ y)) = -1 := by
    intro x y hxn hyn hxy
    have hx0 := pow_ne_zero_of hn one_ne_zero hxn
    have hy0 := pow_ne_zero_of hn one_ne_zero hyn
    have n1 := pair_ne_P0 hS h0 hx0
    have n2 := pair_ne_P0 hS h0 hy0
    have n3 := pair_ne_sq hpn hn hS h0 hxn hyn hxy
    have e := htg _ (hmem _) _ (hmem _) _ (hmem _) (Ne.symm n1) (Ne.symm n2) (Ne.symm n3)
    have e' : eP Ψ (pairOf Ψ (some 0)) (pairOf Ψ (some x)) (pairOf Ψ (some y)) = 1 := e
    have hyψ : y ≠ ψ x := by
      intro he; apply n3; apply (pairOf_eq_iff hS).mpr; right
      rw [psi_some_of_frame hS h0 hx0, he]
    rw [eP_pairOf hS n1 n2 n3, eS_frame hS h0 hx0 hy0 (Ne.symm hxy) hyψ, hχm1] at e'
    have hχ : quadraticChar F (ψ x * ψ y) = 1 := by
      rw [map_mul, hadm.swap x hx0, hadm.swap y hy0, (chi_one_iff hpn x).2 hxn,
        (chi_one_iff hpn y).2 hyn]; norm_num
    rw [hχ] at e'
    linarith
  -- step 2: `L(x,y) = χ((x-y)(ψx-ψy)xy) = -1` for all `x ≠ y` in `𝔽ₚ*`
  set L : F → F → ℤ := fun a b => quadraticChar F ((a - b) * (ψ a - ψ b) * (a * b))
    with hL
  have Lsymm : ∀ a b, L a b = L b a := by intro a b; simp only [hL]; congr 1; ring
  have Lsq : ∀ a b, a ≠ 0 → b ≠ 0 → b ≠ a → L a b * L a b = 1 := by
    intro a b ha hb hba
    apply chi_sq_one
    refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hba)) (sub_ne_zero.mpr ?_))
      (mul_ne_zero ha hb)
    intro he; exact hba (psi_inj hadm hb ha he.symm)
  have Lflip : ∀ a b, a ≠ 0 → b ≠ 0 → b ≠ a → b ≠ ψ a → L (ψ a) b = L a b := by
    intro a b ha hb hba hbψ
    have hψa := hadm.ne_zero a ha
    have hc := hadm.cross a b ha hb hba hbψ
    have e1 : L (ψ a) b * L a b = 1 := by
      simp only [hL]
      rw [← map_mul, hadm.invol a ha]
      have : (ψ a - b) * (a - ψ b) * (ψ a * b) * ((a - b) * (ψ a - ψ b) * (a * b)) =
          b ^ 2 * ((a * ψ a) * ((a - b) * (a - ψ b) * (ψ a - b) * (ψ a - ψ b))) := by ring
      rw [this, chi_sq_mul hb, map_mul, hc, map_mul, hadm.swap a ha]
      have := chi_sq_one ha
      linear_combination this
    have e2 := Lsq a b ha hb hba
    linear_combination L a b * e1 - L (ψ a) b * e2
  have Lrep : ∀ a b A, (A = a ∨ A = ψ a) → a ≠ 0 → b ≠ 0 → b ≠ a → b ≠ ψ a → L a b = L A b := by
    intro a b A eA ha hb hba hbψ
    rcases eA with e | e
    · rw [e]
    · rw [e, Lflip a b ha hb hba hbψ]
  have hLall : ∀ a b, a ≠ 0 → b ≠ 0 → b ≠ a → L a b = -1 := by
    intro a b ha hb hba
    by_cases hbψ : b = ψ a
    · subst hbψ
      simp only [hL]
      rw [hadm.invol a ha, show (a - ψ a) * (ψ a - a) * (a * ψ a) =
        (a - ψ a) ^ 2 * (-1 * (a * ψ a)) by ring,
        chi_sq_mul (sub_ne_zero.mpr (Ne.symm (psi_ne_self hadm ha))), map_mul, hχm1,
        chi_mul_psi hadm ha]; norm_num
    obtain ⟨A, hAsq, eA⟩ : ∃ A, A ^ n = 1 ∧ (A = a ∨ A = ψ a) :=
      ⟨sqrep ψ a, sqrep_sq hpn hadm ha, sqrep_mem a⟩
    obtain ⟨B, hBsq, eB⟩ : ∃ B, B ^ n = 1 ∧ (B = b ∨ B = ψ b) :=
      ⟨sqrep ψ b, sqrep_sq hpn hadm hb, sqrep_mem b⟩
    have hA0 : A ≠ 0 := pow_ne_zero_of hn one_ne_zero hAsq
    have hAb : b ≠ A := by
      rcases eA with e | e <;> rw [e]
      · exact hba
      · exact hbψ
    have hAψb : A ≠ ψ b := by
      intro he
      rcases eA with e | e
      · apply hbψ; rw [← e, he, hadm.invol b hb]
      · exact hba (psi_inj hadm ha hb (e.symm.trans he)).symm
    have hBA : B ≠ A := by
      intro he
      rcases eB with e | e
      · exact hAb (e.symm.trans he)
      · exact hAψb (he.symm.trans e)
    rw [Lrep a b A eA ha hb hba hbψ, Lsymm, Lrep b A B eB hb hA0 (Ne.symm hAb) hAψb]
    simp only [hL]
    rw [map_mul, hT B A hBsq hAsq hBA, map_mul, (chi_one_iff hpn _).2 hBsq,
      (chi_one_iff hpn _).2 hAsq]
    norm_num
  -- step 3: Carlitz
  set f : F → F := fun s => if s = 0 then 0 else ψ s⁻¹ with hf
  have hf0 : f 0 = 0 := by simp [hf]
  have hfs' : ∀ s, s ≠ 0 → f s = ψ s⁻¹ := by intro s hs; simp [hf, hs]
  have hq : ∀ s t, s ≠ t → quadraticChar F ((f s - f t) / (s - t)) = -1 := by
    have one_side : ∀ s : F, s ≠ 0 → quadraticChar F (ψ s⁻¹ / s) = -1 := by
      intro s hs
      have : ψ s⁻¹ / s = s⁻¹ * ψ s⁻¹ := by rw [div_eq_mul_inv, mul_comm]
      rw [this]; exact chi_mul_psi hadm (inv_ne_zero hs)
    intro s t hst
    by_cases hs : s = 0
    · subst hs
      have ht : t ≠ 0 := Ne.symm hst
      rw [hf0, hfs' t ht, show (0 - ψ t⁻¹) / (0 - t) = ψ t⁻¹ / t by ring]
      exact one_side t ht
    by_cases ht : t = 0
    · subst ht
      rw [hf0, hfs' s hs, show (ψ s⁻¹ - 0) / (s - 0) = ψ s⁻¹ / s by ring]
      exact one_side s hs
    rw [hfs' s hs, hfs' t ht]
    set x := s⁻¹ with hx
    set y := t⁻¹ with hy
    have hx0 : x ≠ 0 := inv_ne_zero hs
    have hy0 : y ≠ 0 := inv_ne_zero ht
    have hyx : y ≠ x := fun e => hst (by rw [← inv_inv s, ← inv_inv t, ← hx, ← hy, e])
    have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
    have e : (ψ x - ψ y) / (s - t) = (x - y)⁻¹ ^ 2 * (-1 * ((x - y) * (ψ x - ψ y) * (x * y))) := by
      have hs' : s = x⁻¹ := by rw [hx, inv_inv]
      have ht' : t = y⁻¹ := by rw [hy, inv_inv]
      rw [hs', ht']
      field_simp
      ring
    rw [e, chi_sq_mul (inv_ne_zero hxy), map_mul, hχm1, one_mul]
    exact hLall x y hx0 hy0 hyx
  exact hq

/-- An elliptic solution (`q ≥ 5`) is not arc-like: all its points lie on one line. -/
theorem elliptic_not_arc (hpn : Fintype.card F = 2 * n + 1) (hn : 2 ≤ n) {ψ : F → F}
    (h : Admissible ψ) (hell : ∀ x : F, x ≠ 0 → ψ x = ψ 1 / x) : ¬ ArcLike ψ := by
  intro harc
  obtain ⟨y, hy⟩ : ((SQ (F := F) n).erase 1).Nonempty := by
    rw [← card_pos, card_erase_of_mem (by simp [SQ]), card_SQ hpn]; omega
  rw [mem_erase] at hy
  have hyn : y ^ n = 1 := by simpa [SQ] using hy.2
  have hy0 : y ≠ 0 := pow_ne_zero_of (by omega) one_ne_zero hyn
  have hyψ : y ≠ ψ 1 := by
    intro e
    have := h.swap 1 one_ne_zero
    rw [← e, map_one, (chi_one_iff hpn y).2 hyn] at this
    norm_num at this
  apply harc.1 1 y one_ne_zero hy0 hy.1 hyψ
  rw [hell y hy0]
  unfold det3 pf p0
  field_simp
  ring

end FieldCase

section Prime

variable {p n : ℕ} [hp : Fact p.Prime]

/-- **Carlitz's theorem** (prime case), **taken as a hypothesis**: a map of `𝔽_p` all of whose
difference quotients are nonzero squares is affine. (Checked by exhaustive search for `p ≤ 23`.) -/
def CarlitzHyp (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ f : ZMod p → ZMod p, (∀ s t, s ≠ t → quadraticChar (ZMod p) ((f s - f t) / (s - t)) = 1) →
    ∃ a b : ZMod p, ∀ s, f s = a * s + b

/-- **Blokhuis–Seress–Wilbrink theorem for prime `p ≡ 1 (mod 4)`, in the frame `P₀`**, assuming
Carlitz's theorem: every solution through `{0,∞}` is elliptic, `ψ(x) = ψ(1)/x`. -/
theorem bsw1_frame (hpn : p = 2 * n + 1) (heven : Even n) (hn : 0 < n) (hcar : CarlitzHyp p)
    {Ψ : Option (ZMod p) → Option (ZMod p)} (hS : Solution Ψ) (h0 : Ψ (some 0) = none) :
    ∀ x : ZMod p, x ≠ 0 → toPsi Ψ x = toPsi Ψ 1 / x := by
  have hcard : Fintype.card (ZMod p) = 2 * n + 1 := by rw [ZMod.card]; exact hpn
  have hadm := admissible_of_solution hS h0
  set ψ := toPsi Ψ with hψ
  have hq := quot_nonsq hcard heven hn hS h0
  set c0 := ψ 1 with hc0
  have hc0χ : quadraticChar (ZMod p) c0 = -1 := by rw [hc0, hadm.swap 1 one_ne_zero, map_one]
  have hc00 : c0 ≠ 0 := hadm.ne_zero 1 one_ne_zero
  set f : ZMod p → ZMod p := fq Ψ with hf
  have hf0 : f 0 = 0 := by simp [hf, fq]
  have hfs' : ∀ s, s ≠ 0 → f s = ψ s⁻¹ := by intro s hs; simp [hf, fq, hs, hψ]
  set g : ZMod p → ZMod p := fun s => f s / c0 with hg
  have hgq : ∀ s t, s ≠ t → quadraticChar (ZMod p) ((g s - g t) / (s - t)) = 1 := by
    intro s t hst
    have : (g s - g t) / (s - t) = (f s - f t) / (s - t) * c0⁻¹ := by
      simp only [hg]; field_simp
    rw [this, map_mul, hq s t hst, chi_inv hc00, hc0χ]; norm_num
  obtain ⟨a, b, hab⟩ := hcar g hgq
  have hb : b = 0 := by
    have := hab 0
    simp only [hg, hf0, zero_div, mul_zero, zero_add] at this
    exact this.symm
  have hfs : ∀ s, f s = c0 * (a * s) := by
    intro s
    have := hab s
    rw [hb, add_zero] at this
    simp only [hg] at this
    field_simp at this
    linear_combination this
  intro x hx
  have h1 := hfs 1
  rw [hfs' 1 one_ne_zero, inv_one] at h1
  have hxx := hfs x⁻¹
  rw [hfs' _ (inv_ne_zero hx), inv_inv] at hxx
  have ha1 : a = 1 := by
    have : c0 * (a - 1) = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc00)
  rw [hxx, ha1]
  field_simp

/-- **Blokhuis–Seress–Wilbrink theorem for prime `p ≡ 1 (mod 4)`** (assuming `CarlitzHyp p`): every admissible map is
elliptic. -/
theorem bsw1 (hpn : p = 2 * n + 1) (heven : Even n) (hn : 0 < n) (hcar : CarlitzHyp p)
    {ψ : ZMod p → ZMod p} (h : Admissible ψ) : ∀ x : ZMod p, x ≠ 0 → ψ x = ψ 1 / x := by
  intro x hx
  have e := bsw1_frame hpn heven hn hcar (solution_of_admissible h) (ofPsi_zero ψ) x hx
  rwa [toPsi_ofPsi ψ hx, toPsi_ofPsi ψ one_ne_zero] at e

/-- Frame-free form: for prime `p ≡ 1 (mod 4)` every solution on `PG(1,p)` is a Möbius involution. -/
theorem bsw1_proj (hpn : p = 2 * n + 1) (heven : Even n) (hn : 0 < n) (hcar : CarlitzHyp p)
    {Ψ : Option (ZMod p) → Option (ZMod p)} (hS : Solution Ψ) : IsMob Ψ := by
  obtain ⟨M, -, h0⟩ := normalize_pair hS none
  rw [← isMob_conj_iff M, isMob_iff_elliptic (hS.conj M) h0]
  exact ⟨_, bsw1_frame hpn heven hn hcar (hS.conj M) h0⟩

/-- **Van de Voorde's conjecture for all primes** `p > 11`: no solution on `PG(1,p)` is arc-like
(every complete exterior set of `(p+1)/2` points contains three collinear points).  Assumed:
`StickelHyp p` when `p ≡ 3 (mod 4)` and `CarlitzHyp p` when `p ≡ 1 (mod 4)`. -/
theorem vdv_prime (hp5 : 5 ≤ p) (hp7 : p ≠ 7) (hp11 : p ≠ 11)
    (hst : p % 4 = 3 → BSW.Jacobi.StickelHyp p) (hcar : p % 4 = 1 → CarlitzHyp p)
    {Ψ : Option (ZMod p) → Option (ZMod p)} (hS : Solution Ψ) : ¬ ArcLikeP Ψ := by
  have hodd : p % 2 = 1 := (hp.out.eq_one_or_self_of_dvd 2 |> fun h => by
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso; have := h ⟨k, by omega⟩; omega
    · omega)
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h4 with h1 | h3
  · intro harc
    obtain ⟨M, -, h0⟩ := normalize_pair hS none
    have hS' := hS.conj M
    have hadm := admissible_of_solution hS' h0
    set n := p / 2
    have hpn : p = 2 * n + 1 := by omega
    have heven : Even n := ⟨p / 4, by omega⟩
    have hell := bsw1 hpn heven (by omega) (hcar h1) hadm
    exact elliptic_not_arc (by rw [ZMod.card]; exact hpn) (by omega) hadm hell
      (arcLike_of_arcLikeP hS' h0 (arcLikeP_conj harc M))
  · exact theoremV_proj h3 (by omega) hp7 hp11 (hst h3) hS

end Prime


/-! ## Non-vacuity of `CarlitzHyp` -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem carlitz5_pow : ∀ f : ZMod 5 → ZMod 5, (∀ s t, s ≠ t → ((f s - f t) / (s - t)) ^ 2 = 1) →
    ∃ a b : ZMod 5, ∀ s, f s = a * s + b := by decide +kernel

/-- `CarlitzHyp 5` holds (kernel check over all `5^5` maps). -/
theorem carlitzHyp_five : CarlitzHyp 5 := by
  intro f hf
  apply carlitz5_pow f
  intro s t hst
  exact (chi_one_iff (F := ZMod 5) (n := 2) (by rw [ZMod.card]) _).1 (hf s t hst)

end BSW.BSW1
