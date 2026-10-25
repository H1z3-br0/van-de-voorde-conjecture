module

public import Mathlib
public import BSWCheck.Basics
public import BSWCheck.Exponents
public import BSWCheck.Parity
public import BSWCheck.Bridge
public import BSWCheck.FieldBasics

@[expose] public section

/-!
# Segre–Paley identity for arc-like solutions (Lemma 4.2 and Corollary 4.3, prime `q`)

Points of the plane `PG(2,q)` are binary quadratic forms `a X² + b XZ + c Z²` up to a scalar
(`V3`); the conic consists of the squares of linear forms, and an external point is the pair of
roots `{x, y}` of its form (`pf x y`, and `p0` for the pair `{0, ∞}`).  Three points are collinear
iff the determinant `det3` of their forms vanishes.

A solution in the frame `P₀ = {0,∞}` is given by an admissible `ψ`; its points are `P₀` and the
pairs `{x, ψ x}`.  It is **arc-like** (`ArcLike`) if no three of these points are collinear.

Main result (`arc_A`): for an arc-like solution over a finite field `F`, `|F| = 2n+1` (`n` odd, `n ≥ 3`), and
`y, z ≠ 0` in different pairs,
`χ((ψ y - z)(ψ z - y)) = -χ(ψ y · ψ z)`,
which is condition (A) of the paper (`arc_A'` gives (A) literally).

The proof is the paper's: Ceva's relation for the triangle `P₀, Q, R` multiplied over the other
`n - 2` points of the solution, and at each vertex a Wilson-type product over the nonsquares
(`vertex_prod`, `wilson_ratio`).  The pencil of lines through a vertex is coordinatised by
`n_V(X) = ℓ₁(X)/ℓ₂(X)` (values of the form at the two points of `V`), see `pencil_pf`, `pencil_p0`.
-/

open Finset

namespace BSW.Segre

open BSW.Basic

/-- A binary quadratic form `a X² + b XZ + c Z²` (a point of `PG(2,q)`). -/
@[ext] structure V3 (K : Type*) where
  a : K
  b : K
  c : K

section General

variable {K : Type*} [Field K]

/-- The determinant of three forms (zero iff the three points are collinear). -/
def det3 (u v w : V3 K) : K :=
  u.a * (v.b * w.c - v.c * w.b) - u.b * (v.a * w.c - v.c * w.a) + u.c * (v.a * w.b - v.b * w.a)

/-- The pair `{x, y}` of points of the conic: the form `(X - xZ)(X - yZ)`. -/
def pf (x y : K) : V3 K := ⟨1, -(x + y), x * y⟩

/-- The pair `{0, ∞}`: the form `XZ`. -/
def p0 : V3 K := ⟨0, 1, 0⟩

/-- The value of a form at the point `t` of the conic. -/
def ev (t : K) (u : V3 K) : K := u.a * t ^ 2 + u.b * t + u.c

theorem det_swap12 (u v w : V3 K) : det3 u v w = -det3 v u w := by unfold det3; ring
theorem det_swap23 (u v w : V3 K) : det3 u v w = -det3 u w v := by unfold det3; ring
theorem det_cyc (u v w : V3 K) : det3 u v w = det3 v w u := by unfold det3; ring

theorem ev_pf (t x y : K) : ev t (pf x y) = (t - x) * (t - y) := by unfold ev pf; ring
theorem ev_p0 (t : K) : ev t (p0 : V3 K) = t := by unfold ev p0; ring

theorem pf_comm (x y : K) : pf x y = pf y x := by unfold pf; ext <;> simp <;> ring

/-- Pencil coordinate at a finite pair `{y, w}`. -/
theorem pencil_pf (y w : K) (U W : V3 K) :
    (y - w) * det3 (pf y w) U W = ev y U * ev w W - ev w U * ev y W := by
  unfold det3 pf ev; ring

/-- Pencil coordinate at `{0, ∞}`: `ℓ₁ = c` (value at `0`), `ℓ₂ = a` (value at `∞`). -/
theorem pencil_p0 (U W : V3 K) : 1 * det3 p0 U W = U.c * W.a - U.a * W.c := by
  unfold det3 p0; ring

theorem ratio_aux {a1 a2 b1 b2 x1 x2 : K} (ha2 : a2 ≠ 0) (hb2 : b2 ≠ 0) (hx2 : x2 ≠ 0)
    (hd : b1 * x2 - b2 * x1 ≠ 0) :
    (a1 * x2 - a2 * x1) / (b1 * x2 - b2 * x1) = (a2 / b2) * ((x1 / x2 - a1 / a2) / (x1 / x2 - b1 / b2)) := by
  have e1 : x1 / x2 - b1 / b2 = -(b1 * x2 - b2 * x1) / (x2 * b2) := by field_simp; ring
  have e2 : x1 / x2 - a1 / a2 = -(a1 * x2 - a2 * x1) / (x2 * a2) := by field_simp; ring
  have hd' : -(b1 * x2 - b2 * x1) ≠ 0 := neg_ne_zero.mpr hd
  rw [e1, e2, div_div_div_eq, div_mul_div_comm, div_eq_div_iff hd (mul_ne_zero hb2
    (mul_ne_zero (mul_ne_zero hx2 ha2) hd'))]
  ring

/-- No three points of the solution `{P₀} ∪ {{x, ψ x}}` are collinear. -/
def ArcLike (ψ : K → K) : Prop :=
  (∀ x y : K, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ ψ x → det3 p0 (pf x (ψ x)) (pf y (ψ y)) ≠ 0) ∧
  (∀ x y z : K, x ≠ 0 → y ≠ 0 → z ≠ 0 → y ≠ x → y ≠ ψ x → z ≠ x → z ≠ ψ x → z ≠ y → z ≠ ψ y →
    det3 (pf x (ψ x)) (pf y (ψ y)) (pf z (ψ z)) ≠ 0)

end General

/-! ## Prime fields: squares, nonsquares and the Wilson product -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Nonzero squares of `F` (`p = 2n+1`). -/
def SQ (n : ℕ) : Finset (F) := univ.filter (fun z => z ^ n = 1)
/-- Nonsquares of `F`. -/
def NS (n : ℕ) : Finset (F) := univ.filter (fun z => z ^ n = -1)

theorem card_SQ (hpn : Fintype.card F = 2 * n + 1) : (SQ (F := F) n).card = n := by
  have hn0 : 0 < n := by
    have : 1 < Fintype.card F := Fintype.one_lt_card; omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ρ, hρ⟩ := BSW.FB.exists_primitive (n := n) hpn
  have : SQ (F := F) n = Polynomial.nthRootsFinset n (1 : F) := by
    ext u
    rw [SQ, mem_filter, Polynomial.mem_nthRootsFinset hn0]
    simp
  rw [this, hρ.card_nthRootsFinset]

omit [Fintype F] [DecidableEq F] in
theorem pow_ne_zero_of {n : ℕ} (hn : 0 < n) {z : F} {v : F} (hv : v ≠ 0) (h : z ^ n = v) :
    z ≠ 0 := by
  rintro rfl; rw [zero_pow (by omega)] at h; exact hv h.symm

theorem card_NS (hpn : Fintype.card F = 2 * n + 1) {α : F} (hα : α ^ n = -1) : (NS (F := F) n).card = n := by
  have hn0 : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0; simp at hα
    have h2 : (2 : F) = 0 := by linear_combination hα
    exact absurd h2 (BSW.FB.two_ne_zero' hpn)
  have hα0 : α ≠ 0 := pow_ne_zero_of hn0 (neg_ne_zero.mpr one_ne_zero) hα
  have : NS (F := F) n = (SQ (F := F) n).image (fun s => α * s) := by
    ext m
    simp only [NS, SQ, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hm
      refine ⟨m / α, ?_, by field_simp⟩
      rw [div_pow, hm, hα]; norm_num
    · rintro ⟨s, hs, rfl⟩
      rw [mul_pow, hs, hα, mul_one]
  rw [this, card_image_of_injective _ (mul_right_injective₀ hα0), card_SQ hpn]

/-- `(n : F) ≠ 0` for `p = 2n+1`. -/
theorem n_ne_zero (hpn : Fintype.card F = 2 * n + 1) (_hn : 0 < n) : (n : F) ≠ 0 :=
  BSW.FB.n_ne_zero hpn

/-- **Wilson ratio.** For distinct nonsquares `α, β`:
`∏_{m ∈ N \ {α, β}} (m - α)/(m - β) = -β/α`. -/
theorem wilson_ratio (hpn : Fintype.card F = 2 * n + 1) (hn : 0 < n) {α β : F} (hα : α ^ n = -1)
    (hβ : β ^ n = -1) (hab : α ≠ β) :
    ∏ m ∈ ((NS (F := F) n).erase α).erase β, ((m - α) / (m - β)) = -(β / α) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ρ, hρ⟩ := BSW.FB.exists_primitive (n := n) hpn
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hα0 : α ≠ 0 := pow_ne_zero_of hn hm1 hα
  have hβ0 : β ≠ 0 := pow_ne_zero_of hn hm1 hβ
  have hNSα : NS (F := F) n = univ.filter (fun z : F => z ^ n = α ^ n) := by
    ext z; simp [NS, hα]
  have hNSβ : NS (F := F) n = univ.filter (fun z : F => z ^ n = β ^ n) := by
    ext z; simp [NS, hβ]
  set T := ((NS (F := F) n).erase α).erase β with hT
  have hβmem : β ∈ (NS (F := F) n).erase α := by
    rw [mem_erase]; exact ⟨Ne.symm hab, by simp [NS, hβ]⟩
  have hαmem : α ∈ (NS (F := F) n).erase β := by
    rw [mem_erase]; exact ⟨hab, by simp [NS, hα]⟩
  have hA : (α - β) * ∏ m ∈ T, (α - m) = α ^ (n - 1) * (n : F) := by
    rw [hT, mul_prod_erase _ (fun m => α - m) hβmem, hNSα]
    exact BSW.FB.prod_coset_erase hρ hα0
  have hB : (β - α) * ∏ m ∈ T, (β - m) = β ^ (n - 1) * (n : F) := by
    rw [hT, erase_right_comm, mul_prod_erase _ (fun m => β - m) hαmem, hNSβ]
    exact BSW.FB.prod_coset_erase hρ hβ0
  have hα1 : α ^ (n - 1) * α = -1 := by rw [← pow_succ, Nat.sub_add_cancel hn, hα]
  have hβ1 : β ^ (n - 1) * β = -1 := by rw [← pow_succ, Nat.sub_add_cancel hn, hβ]
  have hn0 := n_ne_zero hpn hn
  have hPB : ∏ m ∈ T, (β - m) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hB
    exact mul_ne_zero (pow_ne_zero _ hβ0) hn0 hB.symm
  have hstep : ∏ m ∈ T, ((m - α) / (m - β)) = (∏ m ∈ T, (α - m)) / ∏ m ∈ T, (β - m) := by
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro m _
    rw [show m - α = -(α - m) by ring, show m - β = -(β - m) by ring, neg_div_neg_eq]
  rw [hstep, div_eq_iff hPB]
  have hab' : α - β ≠ 0 := sub_ne_zero.mpr hab
  have key : (α - β) * ((∏ m ∈ T, (α - m)) * α + β * ∏ m ∈ T, (β - m)) = 0 := by
    linear_combination α * hA - β * hB + (n : F) * hα1 - (n : F) * hβ1
  have key2 := (mul_eq_zero.mp key).resolve_left hab'
  field_simp
  linear_combination key2

/-- **Product at a vertex.**  Let `V` be a vertex whose pencil is coordinatised by
`n(X) = ℓ₁(X)/ℓ₂(X)` (`κ · det(V, U, W) = ℓ₁U ℓ₂W - ℓ₂U ℓ₁W`), let `A, B` and the points
`X i` (`i ∈ I`, `|I| = n - 2`) lie on external lines through `V` (nonsquare coordinates), with no
three of `V, A, B, X i` collinear.  Then
`∏_{i ∈ I} det(V,A,X i)/det(V,B,X i) = (ℓ₂A/ℓ₂B)^(n-2) · (-(n(B)/n(A)))`. -/
theorem vertex_prod (hpn : Fintype.card F = 2 * n + 1) (hn : 2 ≤ n) {ι : Type*} [DecidableEq ι]
    {ℓ1 ℓ2 : V3 (F) → F} {V : V3 (F)} {κ : F} (hκ : κ ≠ 0)
    (hid : ∀ U W, κ * det3 V U W = ℓ1 U * ℓ2 W - ℓ2 U * ℓ1 W)
    {A B : V3 (F)} (hA2 : ℓ2 A ≠ 0) (hB2 : ℓ2 B ≠ 0)
    (hAn : (ℓ1 A / ℓ2 A) ^ n = -1) (hBn : (ℓ1 B / ℓ2 B) ^ n = -1) (hAB : det3 V A B ≠ 0)
    (I : Finset ι) (X : ι → V3 (F)) (hcard : I.card = n - 2)
    (hX2 : ∀ i ∈ I, ℓ2 (X i) ≠ 0) (hXn : ∀ i ∈ I, (ℓ1 (X i) / ℓ2 (X i)) ^ n = -1)
    (hXA : ∀ i ∈ I, det3 V A (X i) ≠ 0) (hXB : ∀ i ∈ I, det3 V B (X i) ≠ 0)
    (hXX : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → det3 V (X i) (X j) ≠ 0) :
    ∏ i ∈ I, det3 V A (X i) / det3 V B (X i)
      = (ℓ2 A / ℓ2 B) ^ (n - 2) * (-((ℓ1 B / ℓ2 B) / (ℓ1 A / ℓ2 A))) := by
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hn0 : 0 < n := by omega
  -- coordinates differ iff the determinant is nonzero
  have hne : ∀ U W, ℓ2 U ≠ 0 → ℓ2 W ≠ 0 → det3 V U W ≠ 0 → ℓ1 U / ℓ2 U ≠ ℓ1 W / ℓ2 W := by
    intro U W hU hW hd heq
    apply hd
    have h1 := hid U W
    rw [div_eq_div_iff hU hW] at heq
    have : κ * det3 V U W = 0 := by rw [h1]; linear_combination heq
    exact (mul_eq_zero.mp this).resolve_left hκ
  set nA := ℓ1 A / ℓ2 A with hnA
  set nB := ℓ1 B / ℓ2 B with hnB
  set nX : ι → F := fun i => ℓ1 (X i) / ℓ2 (X i) with hnX
  -- each factor
  have hfac : ∀ i ∈ I, det3 V A (X i) / det3 V B (X i)
      = (ℓ2 A / ℓ2 B) * ((nX i - nA) / (nX i - nB)) := by
    intro i hi
    have hx2 := hX2 i hi
    have e1 : det3 V A (X i) = (ℓ1 A * ℓ2 (X i) - ℓ2 A * ℓ1 (X i)) / κ := by
      rw [eq_div_iff hκ, mul_comm, hid]
    have e2 : det3 V B (X i) = (ℓ1 B * ℓ2 (X i) - ℓ2 B * ℓ1 (X i)) / κ := by
      rw [eq_div_iff hκ, mul_comm, hid]
    have hdB' : ℓ1 B * ℓ2 (X i) - ℓ2 B * ℓ1 (X i) ≠ 0 := by
      intro h0; apply hXB i hi; rw [e2, h0, zero_div]
    rw [e1, e2, div_div_div_cancel_right₀ hκ]
    exact ratio_aux hA2 hB2 hx2 hdB'
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_const, hcard]
  congr 1
  -- reindex by the coordinate
  have hinj : Set.InjOn nX I := by
    intro i hi j hj hij
    by_contra hne'
    exact hne (X i) (X j) (hX2 i hi) (hX2 j hj) (hXX i hi j hj hne') hij
  have himg : I.image nX = ((NS (F := F) n).erase nA).erase nB := by
    apply eq_of_subset_of_card_le
    · intro m hm
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
      rw [mem_erase, mem_erase]
      refine ⟨hne (X i) B (hX2 i hi) hB2 ?_, hne (X i) A (hX2 i hi) hA2 ?_, ?_⟩
      · rw [det_swap23]; exact neg_ne_zero.mpr (hXB i hi)
      · rw [det_swap23]; exact neg_ne_zero.mpr (hXA i hi)
      · simpa [NS] using hXn i hi
    · rw [card_image_of_injOn hinj, hcard]
      have hAB' : nB ≠ nA := Ne.symm (hne A B hA2 hB2 hAB)
      have hBmem : nB ∈ (NS (F := F) n).erase nA := by
        rw [mem_erase]; exact ⟨hAB', by simp [NS, hBn]⟩
      have hAmem : nA ∈ NS (F := F) n := by simp [NS, hAn]
      rw [card_erase_of_mem hBmem, card_erase_of_mem hAmem, card_NS hpn hAn]
      omega
  rw [← prod_image (f := fun m => (m - nA) / (m - nB)) hinj, himg]
  exact wilson_ratio hpn hn0 hAn hBn (hne A B hA2 hB2 hAB)


/-! ## The arc-like case -/

theorem chi_neg_iff (hpn : Fintype.card F = 2 * n + 1) (a : F) :
    quadraticChar (F) a = -1 ↔ a ^ n = -1 := by
  exact BSW.FB.chi_neg_iff hpn a

theorem chi_one_iff (hpn : Fintype.card F = 2 * n + 1) (a : F) :
    quadraticChar (F) a = 1 ↔ a ^ n = 1 := by
  exact BSW.FB.chi_one_iff hpn a

/-- The square element of the pair `{y, ψ y}`. -/
def sqrep (ψ : F → F) (y : F) : F :=
  if quadraticChar (F) y = 1 then y else ψ y

theorem sqrep_sq (hpn : Fintype.card F = 2 * n + 1) {ψ : F → F} (h : Admissible ψ) {y : F}
    (hy : y ≠ 0) : (sqrep ψ y) ^ n = 1 := by
  rw [← chi_one_iff hpn]
  unfold sqrep
  split_ifs with h1
  · exact h1
  · rw [h.swap y hy]
    rcases quadraticChar_dichotomy hy with h2 | h2
    · exact absurd h2 h1
    · rw [h2]; rfl

theorem sqrep_mem {ψ : F → F} (y : F) : sqrep ψ y = y ∨ sqrep ψ y = ψ y := by
  unfold sqrep; split_ifs <;> simp

theorem eq_sqrep (hpn : Fintype.card F = 2 * n + 1) {ψ : F → F} (h : Admissible ψ) {y s : F}
    (hy : y ≠ 0) (hs : s ^ n = 1) (hsy : s = y ∨ s = ψ y) : s = sqrep ψ y := by
  rw [← chi_one_iff hpn] at hs
  unfold sqrep
  rcases hsy with rfl | rfl
  · rw [ite_eq_left hs]
  · have : quadraticChar (F) y ≠ 1 := by
      intro h1; rw [h.swap y hy, h1] at hs; norm_num at hs
    rw [ite_eq_right this]

theorem chi_mul_psi {ψ : F → F} (h : Admissible ψ) {y : F} (hy : y ≠ 0) :
    quadraticChar (F) (y * ψ y) = -1 := by
  rw [map_mul, h.swap y hy, mul_neg, chi_sq_one hy]

theorem psi_ne_self {ψ : F → F} (h : Admissible ψ) {y : F} (hy : y ≠ 0) :
    ψ y ≠ y := by
  intro he
  have := chi_mul_psi h hy
  rw [he, map_mul, chi_sq_one hy] at this
  norm_num at this

theorem psi_inj {ψ : F → F} (h : Admissible ψ) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (he : ψ a = ψ b) : a = b := by
  rw [← h.invol a ha, he, h.invol b hb]

omit [Fintype F] [DecidableEq F] in
/-- Ceva's relation for the triangle `P, Q, R` and a point `X` in general position. -/
theorem ceva {P Q R X : V3 (F)} (h1 : det3 P Q X ≠ 0) (h2 : det3 P R X ≠ 0)
    (h3 : det3 Q R X ≠ 0) :
    (det3 P Q X / det3 P R X) * (det3 Q R X / det3 Q P X) * (det3 R P X / det3 R Q X) = -1 := by
  rw [det_swap12 Q P X, det_swap12 R P X, det_swap12 R Q X]
  field_simp

theorem nonsq_of_chi (hpn : Fintype.card F = 2 * n + 1) {a b : F} (hb : b ≠ 0)
    (h : quadraticChar (F) (a * b) = -1) : (a / b) ^ n = -1 := by
  rw [← chi_neg_iff hpn, chi_div hb, ← map_mul]; exact h

/-- **Segre–Paley for arc-like solutions** (Lemma 4.2 and Corollary 4.3, in the frame `P₀ = {0,∞}`):
for `y, z ≠ 0` in different pairs, `χ((ψ y - z)(ψ z - y)) = -χ(ψ y · ψ z)`. -/
theorem arc_A (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (hn3 : 3 ≤ n) {ψ : F → F}
    (h : Admissible ψ) (harc : ArcLike ψ) {y z : F} (hy : y ≠ 0) (hz : z ≠ 0) (hzy : z ≠ y)
    (hzψ : z ≠ ψ y) :
    quadraticChar (F) ((ψ y - z) * (ψ z - y)) = -quadraticChar (F) (ψ y * ψ z) := by
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  set y' := ψ y with hy'
  set z' := ψ z with hz'
  have hy'0 : y' ≠ 0 := h.ne_zero y hy
  have hz'0 : z' ≠ 0 := h.ne_zero z hz
  have hψy' : ψ y' = y := h.invol y hy
  have hψz' : ψ z' = z := h.invol z hz
  have hyy' : y ≠ y' := Ne.symm (psi_ne_self h hy)
  have hzz' : z ≠ z' := Ne.symm (psi_ne_self h hz)
  have hz'y : z' ≠ y := by
    intro he; apply hzψ; rw [← hψz', he]
  have hz'y' : z' ≠ y' := by
    intro he; apply hzy; exact psi_inj h hz hy he
  -- the points
  set P : V3 (F) := p0
  set Q : V3 (F) := pf y y' with hQ
  set R : V3 (F) := pf z z' with hR
  set X : F → V3 (F) := fun s => pf s (ψ s) with hX
  set Y := sqrep ψ y
  set Z := sqrep ψ z
  have hYsq : Y ^ n = 1 := sqrep_sq hpn h hy
  have hZsq : Z ^ n = 1 := sqrep_sq hpn h hz
  have hYZ : Y ≠ Z := by
    intro he
    have e1 : Y = y ∨ Y = y' := sqrep_mem y
    have e2 : Z = z ∨ Z = z' := sqrep_mem z
    rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2
    · exact hzy (h2.symm.trans (he.symm.trans h1))
    · exact hz'y (h2.symm.trans (he.symm.trans h1))
    · exact hzψ (h2.symm.trans (he.symm.trans h1))
    · exact hz'y' (h2.symm.trans (he.symm.trans h1))
  set I := ((SQ (F := F) n).erase Y).erase Z with hI
  have hcard : I.card = n - 2 := by
    have hZmem : Z ∈ (SQ (F := F) n).erase Y := by
      rw [mem_erase]; exact ⟨Ne.symm hYZ, by simp [SQ, hZsq]⟩
    have hYmem : Y ∈ SQ (F := F) n := by simp [SQ, hYsq]
    rw [hI, card_erase_of_mem hZmem, card_erase_of_mem hYmem, card_SQ hpn]
    omega
  have hmemI : ∀ s ∈ I, s ^ n = 1 ∧ s ≠ 0 ∧ s ≠ y ∧ s ≠ y' ∧ s ≠ z ∧ s ≠ z' := by
    intro s hs
    rw [hI, mem_erase, mem_erase] at hs
    obtain ⟨hsZ, hsY, hs⟩ := hs
    have hsn : s ^ n = 1 := by simpa [SQ] using hs
    refine ⟨hsn, pow_ne_zero_of (by omega) one_ne_zero hsn, ?_, ?_, ?_, ?_⟩
    · intro he; exact hsY (eq_sqrep hpn h hy hsn (Or.inl he))
    · intro he; exact hsY (eq_sqrep hpn h hy hsn (Or.inr he))
    · intro he; exact hsZ (eq_sqrep hpn h hz hsn (Or.inl he))
    · intro he; exact hsZ (eq_sqrep hpn h hz hsn (Or.inr he))
  -- a square is never `ψ` of a square
  have hsqψ : ∀ s t : F, s ≠ 0 → s ^ n = 1 → t ^ n = 1 → t ≠ ψ s := by
    intro s t hs0 hs ht he
    rw [← chi_one_iff hpn] at hs ht
    rw [he, h.swap s hs0, hs] at ht
    norm_num at ht
  -- general position
  have dPQR : det3 P Q R ≠ 0 := harc.1 y z hy hz hzy hzψ
  have dPQX : ∀ s ∈ I, det3 P Q (X s) ≠ 0 := by
    intro s hs; obtain ⟨-, hs0, hsy, hsy', -, -⟩ := hmemI s hs
    exact harc.1 y s hy hs0 hsy hsy'
  have dPRX : ∀ s ∈ I, det3 P R (X s) ≠ 0 := by
    intro s hs; obtain ⟨-, hs0, -, -, hsz, hsz'⟩ := hmemI s hs
    exact harc.1 z s hz hs0 hsz hsz'
  have dQRX : ∀ s ∈ I, det3 Q R (X s) ≠ 0 := by
    intro s hs; obtain ⟨-, hs0, hsy, hsy', hsz, hsz'⟩ := hmemI s hs
    exact harc.2 y z s hy hz hs0 hzy hzψ hsy hsy' hsz hsz'
  -- Ceva, multiplied over `I`
  have hceva : (∏ s ∈ I, det3 P Q (X s) / det3 P R (X s)) *
      (∏ s ∈ I, det3 Q R (X s) / det3 Q P (X s)) *
      (∏ s ∈ I, det3 R P (X s) / det3 R Q (X s)) = -1 := by
    rw [← prod_mul_distrib, ← prod_mul_distrib,
      prod_congr rfl (fun s hs => ceva (dPQX s hs) (dPRX s hs) (dQRX s hs)), prod_const, hcard]
    obtain ⟨k, hk⟩ := hodd
    rw [show n - 2 = 2 * (k - 1) + 1 by omega, pow_succ, pow_mul]; norm_num
  -- facts about the pairs through `y` and `s ∈ I`
  have hXev : ∀ (a : F), a ≠ 0 → ∀ s ∈ I, a ≠ s → a ≠ ψ s → ev a (X s) ≠ 0 := by
    intro a _ s _ h1 h2
    simp only [hX, ev_pf]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)
  have hψs : ∀ s ∈ I, ∀ a : F, a ≠ 0 → s ≠ a → ψ a ≠ ψ s := by
    intro s hs a ha hsa he
    exact hsa (psi_inj h (hmemI s hs).2.1 ha he.symm)
  have hcompat : ∀ a b : F, a ≠ 0 → b ≠ 0 → b ≠ a → b ≠ ψ a →
      ((ev a (pf b (ψ b))) / ev (ψ a) (pf b (ψ b))) ^ n = -1 := by
    intro a b ha hb hba hbψ
    have hc := h.cross a b ha hb hba hbψ
    have hne : ev (ψ a) (pf b (ψ b)) ≠ 0 := by
      rw [ev_pf]
      refine mul_ne_zero (sub_ne_zero.mpr ?_) (sub_ne_zero.mpr ?_)
      · intro he; apply hbψ; rw [he]
      · intro he; apply hba; exact psi_inj h hb ha he.symm
    apply nonsq_of_chi hpn hne
    rw [ev_pf, ev_pf, show (a - b) * (a - ψ b) * ((ψ a - b) * (ψ a - ψ b))
      = (a - b) * (a - ψ b) * (ψ a - b) * (ψ a - ψ b) by ring]
    exact hc
  -- vertex `P`
  have vP := vertex_prod hpn (by omega) (ℓ1 := fun U => U.c) (ℓ2 := fun U => U.a) (V := P)
    one_ne_zero (fun U W => pencil_p0 U W) (A := Q) (B := R)
    (by simp [hQ, pf]) (by simp [hR, pf])
    (by simpa [hQ, pf] using (chi_neg_iff hpn _).1 (chi_mul_psi h hy))
    (by simpa [hR, pf] using (chi_neg_iff hpn _).1 (chi_mul_psi h hz)) dPQR I X hcard
    (fun s _ => by simp [hX, pf])
    (fun s hs => by simpa [hX, pf] using (chi_neg_iff hpn _).1 (chi_mul_psi h (hmemI s hs).2.1))
    dPQX dPRX
    (fun s hs t ht hst => harc.1 s t (hmemI s hs).2.1 (hmemI t ht).2.1 (Ne.symm hst)
      (hsqψ s t (hmemI s hs).2.1 (hmemI s hs).1 (hmemI t ht).1))
  -- vertex `Q`
  have vQ := vertex_prod hpn (by omega) (ℓ1 := ev y) (ℓ2 := ev y') (V := Q)
    (sub_ne_zero.mpr hyy') (fun U W => pencil_pf y y' U W) (A := R) (B := P)
    (by rw [hR, ev_pf]; exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm (hzψ))) (sub_ne_zero.mpr (Ne.symm hz'y')))
    (by rw [ev_p0]; exact hy'0)
    (hcompat y z hy hz hzy hzψ)
    (by rw [ev_p0, ev_p0]; exact nonsq_of_chi hpn hy'0 (chi_mul_psi h hy))
    (by rw [← det_cyc]; exact dPQR) I X hcard
    (fun s hs => hXev y' hy'0 s hs (Ne.symm (hmemI s hs).2.2.2.1)
      (fun he => (hmemI s hs).2.2.1 (psi_inj h (hmemI s hs).2.1 hy he.symm)))
    (fun s hs => hcompat y s hy (hmemI s hs).2.1 (hmemI s hs).2.2.1 (hmemI s hs).2.2.2.1)
    dQRX
    (fun s hs => by rw [det_swap12]; exact neg_ne_zero.mpr (dPQX s hs))
    (fun s hs t ht hst => harc.2 y s t hy (hmemI s hs).2.1 (hmemI t ht).2.1
      (hmemI s hs).2.2.1 (hmemI s hs).2.2.2.1 (hmemI t ht).2.2.1 (hmemI t ht).2.2.2.1 (Ne.symm hst)
      (hsqψ s t (hmemI s hs).2.1 (hmemI s hs).1 (hmemI t ht).1))
  -- vertex `R`
  have vR := vertex_prod hpn (by omega) (ℓ1 := ev z) (ℓ2 := ev z') (V := R)
    (sub_ne_zero.mpr hzz') (fun U W => pencil_pf z z' U W) (A := P) (B := Q)
    (by rw [ev_p0]; exact hz'0)
    (by rw [hQ, ev_pf]; exact mul_ne_zero (sub_ne_zero.mpr hz'y) (sub_ne_zero.mpr hz'y'))
    (by rw [ev_p0, ev_p0]; exact nonsq_of_chi hpn hz'0 (chi_mul_psi h hz))
    (hcompat z y hz hy (Ne.symm hzy) (Ne.symm hz'y))
    (by rw [← det_cyc, ← det_cyc]; exact dPQR) I X hcard
    (fun s hs => hXev z' hz'0 s hs (Ne.symm (hmemI s hs).2.2.2.2.2)
      (fun he => (hmemI s hs).2.2.2.2.1 (psi_inj h (hmemI s hs).2.1 hz he.symm)))
    (fun s hs => hcompat z s hz (hmemI s hs).2.1 (hmemI s hs).2.2.2.2.1 (hmemI s hs).2.2.2.2.2)
    (fun s hs => by rw [det_swap12]; exact neg_ne_zero.mpr (dPRX s hs))
    (fun s hs => by rw [det_swap12]; exact neg_ne_zero.mpr (dQRX s hs))
    (fun s hs t ht hst => harc.2 z s t hz (hmemI s hs).2.1 (hmemI t ht).2.1
      (hmemI s hs).2.2.2.2.1 (hmemI s hs).2.2.2.2.2 (hmemI t ht).2.2.2.2.1
      (hmemI t ht).2.2.2.2.2 (Ne.symm hst)
      (hsqψ s t (hmemI s hs).2.1 (hmemI s hs).1 (hmemI t ht).1))
  rw [vP, vQ, vR] at hceva
  simp only [hQ, hR, P, ev_pf, ev_p0] at hceva
  simp only [pf, div_one, one_pow, one_mul] at hceva
  -- algebra
  have h1 : y - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzy)
  have h2 : y - z' ≠ 0 := sub_ne_zero.mpr (Ne.symm hz'y)
  have h3 : y' - z ≠ 0 := sub_ne_zero.mpr (fun he => hzψ he.symm)
  have h4 : y' - z' ≠ 0 := sub_ne_zero.mpr (Ne.symm hz'y')
  have h5 : z' - y ≠ 0 := sub_ne_zero.mpr hz'y
  have h6 : z' - y' ≠ 0 := sub_ne_zero.mpr hz'y'
  have h7 : z - y ≠ 0 := sub_ne_zero.mpr hzy
  have h8 : z - y' ≠ 0 := sub_ne_zero.mpr hzψ
  set u : F := (y' - z) * (y' - z') / y' * (z' / ((z' - y) * (z' - y'))) with hu
  have hG : z * z' / (y * y') * (y / y' / ((y - z) * (y - z') / ((y' - z) * (y' - z')))) *
      ((z - y) * (z - y') / ((z' - y) * (z' - y')) / (z / z')) = u ^ 2 := by
    rw [hu]; field_simp; ring
  have hun : u ^ n = 1 := by
    have hk : u ^ n = u ^ (n - 2) * u ^ 2 := by rw [← pow_add]; congr 1; omega
    rw [hk, ← hG, hu, mul_pow]
    linear_combination -hceva
  -- `-w (y'-z')² = u D²`
  set w := (y' - z) * (z' - y) * (y' * z') with hw
  set D := y' * (z' - y) * (z' - y') with hD
  have hwu : -w * (y' - z') ^ 2 = u * D ^ 2 := by
    rw [hw, hu, hD]; field_simp; ring
  have hD0 : D ≠ 0 := mul_ne_zero (mul_ne_zero hy'0 h5) h6
  have hpow1 : ∀ x : F, x ≠ 0 → (x ^ 2) ^ n = 1 := by
    intro x hx
    rw [← pow_mul]
    exact BSW.FB.pow_card_sub_one hpn hx
  have hwn : w ^ n = -1 := by
    have e := congrArg (· ^ n) hwu
    simp only [mul_pow, hpow1 _ h4, hpow1 _ hD0, hun, mul_one] at e
    rw [neg_pow, hodd.neg_one_pow] at e
    linear_combination -e
  have hχw := (chi_neg_iff hpn w).2 hwn
  rw [hw, map_mul] at hχw
  have hB := chi_sq_one (mul_ne_zero hy'0 hz'0)
  linear_combination (quadraticChar (F) (y' * z')) * hχw -
    (quadraticChar (F) ((y' - z) * (z' - y))) * hB

end BSW.Segre
