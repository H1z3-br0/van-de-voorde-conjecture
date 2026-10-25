module

public import Mathlib

@[expose] public section

/-!
# Basic lemmas of the BSW project over an arbitrary finite field

Formal versions (no `sorry`, no extra axioms) of the elementary lemmas on which the computer proof
(the computer search) and several structural statements rest.

* `BSW.Basic.elliptic_admissible`  — `x ↦ n/x` is admissible iff `n` is a nonsquare.
* `BSW.Basic.res_identity`         — the four-difference product is the resultant.
* `BSW.Basic.not_compat_of_common` — pairs sharing a point are never compatible (perfect matching).
* `BSW.Basic.reform`               — (H3) ⟺ (⋆) `f_P(ψ y) = - f_P(y)`.
* `BSW.Basic.balance_image`, `balance_card` — the balance lemma in abstract form.
* `BSW.Basic.balance_admissible`   — the balance lemma for an admissible `ψ` (the pruning rule of the search).
* `BSW.Basic.statementC`           — zero trace for an odd number of pairs, character-sum form.
* `BSW.Basic.doubling`             — even number of pairs: the sum is twice the sum over squares.
* `BSW.Basic.gamma_inv`            — `χ(1 - λ⁻¹) = χ(1 - λ)` when `χ(λ) = χ(-1) = -1`.
* `BSW.Basic.slope_char`           — step 1 of a Gács-type argument: the character of a slope of the graph of `ψ(1/s)`.
* `BSW.Basic.twograph_odd`         — two-graphs: on an odd vertex set, Eulerian descendants force a
                                     trivial two-graph (key step of BSW for `q ≡ 1 mod 4`).
* `BSW.Basic.twograph_sum_even`    — on an even vertex set the same hypothesis only says that all
                                     degrees have the same parity (the barrier for `q ≡ 3 mod 4`).
* `BSW.Basic.clique_bound`         — spectral clique bound.
* `BSW.Basic.fix_card_even`, `not_unique_fixed` — the symmetry lemma, combinatorial core.
-/

open Finset

namespace BSW.Basic

/-! ## Finite-field part -/

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Compatibility of the pairs `{a,b}` and `{c,d}` (condition (H3)):
`χ((a-c)(a-d)(b-c)(b-d)) = -1`. -/
def Compat (a b c d : F) : Prop :=
  quadraticChar F ((a - c) * (a - d) * (b - c) * (b - d)) = -1

/-- Admissible maps (Definition `def:admissible`): an involution of `F^*` exchanging squares and
nonsquares such that any two of its pairs are compatible.  The value at `0` is irrelevant. -/
structure Admissible (ψ : F → F) : Prop where
  ne_zero : ∀ x, x ≠ 0 → ψ x ≠ 0
  invol : ∀ x, x ≠ 0 → ψ (ψ x) = x
  swap : ∀ x, x ≠ 0 → quadraticChar F (ψ x) = -quadraticChar F x
  cross : ∀ x y, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ ψ x → Compat x (ψ x) y (ψ y)

/-- `f_P(w) = χ((w-a)(w-b))` for the pair `P = {a,b}`. -/
def fP (a b w : F) : ℤ := quadraticChar F ((w - a) * (w - b))

theorem chi_sq_one {a : F} (ha : a ≠ 0) : quadraticChar F a * quadraticChar F a = 1 := by
  rw [← sq]; exact quadraticChar_sq_one ha

theorem chi_inv {a : F} (ha : a ≠ 0) : quadraticChar F a⁻¹ = quadraticChar F a := by
  have h1 : quadraticChar F a⁻¹ * quadraticChar F a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have h2 := chi_sq_one ha
  calc quadraticChar F a⁻¹ = quadraticChar F a⁻¹ * (quadraticChar F a * quadraticChar F a) := by
        rw [h2, mul_one]
    _ = (quadraticChar F a⁻¹ * quadraticChar F a) * quadraticChar F a := by ring
    _ = quadraticChar F a := by rw [h1, one_mul]

theorem chi_div {a b : F} (hb : b ≠ 0) :
    quadraticChar F (a / b) = quadraticChar F a * quadraticChar F b := by
  rw [div_eq_mul_inv, map_mul, chi_inv hb]

theorem chi_sq_mul {s a : F} (hs : s ≠ 0) : quadraticChar F (s ^ 2 * a) = quadraticChar F a := by
  rw [map_mul, quadraticChar_sq_one' hs, one_mul]

/-- **Elliptic maps.** For `n ≠ 0` the map `x ↦ n/x` is admissible iff `n` is a nonsquare. -/
theorem elliptic_admissible {n : F} (hn : n ≠ 0) :
    Admissible (fun x => n / x) ↔ quadraticChar F n = -1 := by
  constructor
  · intro h
    have := h.swap 1 one_ne_zero
    simpa using this
  · intro hχ
    refine ⟨fun x hx => div_ne_zero hn hx, fun x hx => by field_simp, fun x hx => ?_, ?_⟩
    · rw [chi_div hx, hχ]; ring
    · intro x y hx hy hyx hyψ
      have hxy : x * y - n ≠ 0 := by
        intro h0
        apply hyψ
        field_simp
        linear_combination h0
      have hs : (x - y) * (x * y - n) / (x * y) ≠ 0 :=
        div_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyx)) hxy) (mul_ne_zero hx hy)
      have key : (x - y) * (x - n / y) * (n / x - y) * (n / x - n / y)
          = ((x - y) * (x * y - n) / (x * y)) ^ 2 * n := by
        field_simp
        ring
      unfold Compat
      rw [key, chi_sq_mul hs, hχ]

/-- **Compatibility as a resultant.** With `s = a+b`, `π = ab`, `s' = c+d`, `π' = cd`:
`(a-c)(a-d)(b-c)(b-d) = (π-π')² + (s-s')(sπ' - s'π)` (the resultant of the two quadratics). -/
theorem res_identity {R : Type*} [CommRing R] (a b c d : R) :
    (a - c) * (a - d) * (b - c) * (b - d)
      = (a * b - c * d) ^ 2 + ((a + b) - (c + d)) * ((a + b) * (c * d) - (c + d) * (a * b)) := by
  ring

/-- Pairs with a common point are never compatible; hence the pairs of a solution are disjoint and a
solution with `(q+1)/2` pairs is a perfect matching of `PG(1,q)`. -/
theorem not_compat_of_common {a b c d : F} (h : a = c ∨ a = d ∨ b = c ∨ b = d) :
    ¬ Compat a b c d := by
  unfold Compat
  have h0 : (a - c) * (a - d) * (b - c) * (b - d) = 0 := by
    rcases h with h | h | h | h <;> subst h <;> ring
  rw [h0, MulChar.map_zero]
  norm_num

theorem neg_iff_mul {u v : ℤ} (hu : u * u = 1) : v = -u ↔ u * v = -1 := by
  constructor
  · rintro rfl; linarith
  · intro h
    have : u * (u * v) = u * (-1) := by rw [h]
    rw [← mul_assoc, hu, one_mul] at this
    linarith

/-- **Reformulation of (H3).** Condition (H3) is equivalent to the antisymmetry (⋆) `f_P(ψ y) = - f_P(y)` for
every pair `P = {x, ψ x}` and every `y ∉ P` (pointwise, for any map `ψ`). -/
theorem reform (ψ : F → F) :
    (∀ x y, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ ψ x → Compat x (ψ x) y (ψ y)) ↔
    (∀ x y, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ ψ x → fP x (ψ x) (ψ y) = -fP x (ψ x) y) := by
  have key : ∀ x y, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ ψ x →
      (Compat x (ψ x) y (ψ y) ↔ fP x (ψ x) (ψ y) = -fP x (ψ x) y) := by
    intro x y hx hy hyx hyψ
    have hne1 : (y - x) * (y - ψ x) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hyx) (sub_ne_zero.mpr hyψ)
    unfold Compat fP
    rw [neg_iff_mul (chi_sq_one hne1), ← map_mul]
    constructor <;> intro h <;> convert h using 2 <;> ring
  constructor
  · intro h x y hx hy hyx hyψ; exact (key x y hx hy hyx hyψ).1 (h x y hx hy hyx hyψ)
  · intro h x y hx hy hyx hyψ; exact (key x y hx hy hyx hyψ).2 (h x y hx hy hyx hyψ)

/-- **The sign γ.** If `χ(-1) = -1` and `χ(λ) = -1`, then `χ(1 - λ⁻¹) = χ(1 - λ)`: the sign `γ` does not
depend on the numbering of the points inside the pairs. -/
theorem gamma_inv (hneg : quadraticChar F (-1) = -1) {l : F} (hl : quadraticChar F l = -1) :
    quadraticChar F (1 - l⁻¹) = quadraticChar F (1 - l) := by
  have hl0 : l ≠ 0 := by
    intro h; rw [h, MulChar.map_zero] at hl; norm_num at hl
  have e : 1 - l⁻¹ = (-1) * (1 - l) * l⁻¹ := by field_simp; ring
  rw [e, map_mul, map_mul, chi_inv hl0, hneg, hl]; ring

/-- **Step 1 of a Gács-type argument.** For `s = 1/x`, `t = 1/y` the slope `(u - v)/(s - t)` of the graph of
`s ↦ ψ(1/s)` (`u = ψ x`, `v = ψ y`) has character `-χ(xy(x-y)(u-v))` when `χ(-1) = -1`. -/
theorem slope_char (hneg : quadraticChar F (-1) = -1) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) (u v : F) :
    quadraticChar F ((u - v) / (x⁻¹ - y⁻¹)) = -quadraticChar F (x * y * (x - y) * (u - v)) := by
  have hd : x⁻¹ - y⁻¹ ≠ 0 := by
    intro h; apply hxy; have := sub_eq_zero.mp h; exact inv_injective this
  have e : (u - v) / (x⁻¹ - y⁻¹) = (-1) * (x * y * (x - y) * (u - v)) / (x - y) ^ 2 := by
    field_simp
    ring
  have hsq : (x - y) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxy)
  rw [e, chi_div hsq, quadraticChar_sq_one' (sub_ne_zero.mpr hxy), map_mul, hneg]; ring

end Field

/-! ## Combinatorial part -/

section Comb

/-- **Balance lemma, abstract form.** Let `ψ` be an involution preserving a finite set `U`, and let
`s : α → ι → ℤ` be a signature with `s(ψ w) = - s(w)` on `U`.  Then `ψ` maps the class
`K_ε = {w ∈ U : s w = ε}` onto `K_{-ε}`. -/
theorem balance_image {α ι : Type*} [DecidableEq α] [Fintype ι] (ψ : α → α)
    (hψ : ∀ w, ψ (ψ w) = w) (U : Finset α) (hU : ∀ w ∈ U, ψ w ∈ U) (s : α → ι → ℤ)
    (hs : ∀ w ∈ U, s (ψ w) = -s w) (ε : ι → ℤ) :
    (U.filter (fun w => s w = ε)).image ψ = U.filter (fun w => s w = -ε) := by
  ext w
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨v, ⟨hvU, hvε⟩, rfl⟩
    exact ⟨hU v hvU, by rw [hs v hvU, hvε]⟩
  · rintro ⟨hwU, hwε⟩
    refine ⟨ψ w, ⟨hU w hwU, ?_⟩, hψ w⟩
    rw [hs w hwU, hwε, neg_neg]

theorem balance_card {α ι : Type*} [DecidableEq α] [Fintype ι] (ψ : α → α)
    (hψ : ∀ w, ψ (ψ w) = w) (U : Finset α) (hU : ∀ w ∈ U, ψ w ∈ U) (s : α → ι → ℤ)
    (hs : ∀ w ∈ U, s (ψ w) = -s w) (ε : ι → ℤ) :
    (U.filter (fun w => s w = ε)).card = (U.filter (fun w => s w = -ε)).card := by
  rw [← balance_image ψ hψ U hU s hs ε, card_image_of_injective]
  intro a b h
  rw [← hψ a, ← hψ b, h]

/-- **Two-graphs of odd order.** Let `s` be a graph on `V` (`ZMod 2`-valued, symmetric) and
`ε(P,X,Y) = s P X + s P Y + s X Y` its two-graph.  If `|V|` is odd and every descendant is
Eulerian (`∑_{Y ≠ P,X} ε(P,X,Y) = 0`), then the two-graph is trivial. -/
theorem twograph_odd {V : Type*} [Fintype V] [DecidableEq V] (s : V → V → ZMod 2)
    (hsym : ∀ a b, s a b = s b a) (hodd : Odd (Fintype.card V))
    (heul : ∀ P X, P ≠ X → ∑ Y ∈ (univ.erase P).erase X, (s P X + s P Y + s X Y) = 0) :
    ∀ P X Y, P ≠ X → P ≠ Y → X ≠ Y → s P X + s P Y + s X Y = 0 := by
  set deg : V → ZMod 2 := fun a => ∑ Y ∈ univ.erase a, s a Y with hdeg
  have hsum : ∀ P X, P ≠ X →
      ∑ Y ∈ (univ.erase P).erase X, (s P X + s P Y + s X Y)
        = (((Fintype.card V - 2 : ℕ)) : ZMod 2) * s P X + (deg P - s P X) + (deg X - s X P) := by
    intro P X hPX
    have hXmem : X ∈ univ.erase P := mem_erase.mpr ⟨Ne.symm hPX, mem_univ X⟩
    have hcard : ((univ.erase P).erase X).card = Fintype.card V - 2 := by
      rw [card_erase_of_mem hXmem, card_erase_of_mem (mem_univ P), card_univ]; omega
    rw [sum_add_distrib, sum_add_distrib, sum_const, hcard, nsmul_eq_mul]
    congr 1
    · congr 1
      rw [sum_erase_eq_sub hXmem]
    · have hPmem : P ∈ univ.erase X := mem_erase.mpr ⟨hPX, mem_univ P⟩
      have : (univ.erase P).erase X = (univ.erase X).erase P := by
        ext y; simp [mem_erase]; tauto
      rw [this, sum_erase_eq_sub hPmem]
  have hcast : ∀ P X : V, P ≠ X → (((Fintype.card V - 2 : ℕ)) : ZMod 2) = 1 := by
    intro P X hPX
    have h2 : 2 ≤ Fintype.card V := by
      have := Finset.card_le_univ ({P, X} : Finset V)
      rw [card_pair hPX] at this; exact this
    rw [ZMod.natCast_eq_one_iff_odd]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k - 1, by omega⟩
  have hdegrel : ∀ P X, P ≠ X → s P X = deg P + deg X := by
    intro P X hPX
    have h := heul P X hPX
    rw [hsum P X hPX, hcast P X hPX, hsym X P] at h
    linear_combination (-1 : ZMod 2) * h
  intro P X Y hPX hPY hXY
  rw [hdegrel P X hPX, hdegrel P Y hPY, hdegrel X Y hXY]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (deg P + deg X + deg Y) * h2

/-- **Even order (the barrier for `q ≡ 3 mod 4`).**  If `|V|` is even, the Euler sum of the
descendant at `P` on the vertex `X` equals `deg P + deg X`: Eulerian descendants only say that all
degrees have the same parity, and do not force a trivial two-graph. -/
theorem twograph_sum_even {V : Type*} [Fintype V] [DecidableEq V] (s : V → V → ZMod 2)
    (hsym : ∀ a b, s a b = s b a) (heven : Even (Fintype.card V)) (P X : V) (hPX : P ≠ X) :
    ∑ Y ∈ (univ.erase P).erase X, (s P X + s P Y + s X Y)
      = (∑ Y ∈ univ.erase P, s P Y) + ∑ Y ∈ univ.erase X, s X Y := by
  have hXmem : X ∈ univ.erase P := mem_erase.mpr ⟨Ne.symm hPX, mem_univ X⟩
  have hPmem : P ∈ univ.erase X := mem_erase.mpr ⟨hPX, mem_univ P⟩
  have hcard : ((univ.erase P).erase X).card = Fintype.card V - 2 := by
    rw [card_erase_of_mem hXmem, card_erase_of_mem (mem_univ P), card_univ]; omega
  have h2le : 2 ≤ Fintype.card V := by
    have := Finset.card_le_univ ({P, X} : Finset V)
    rw [card_pair hPX] at this; exact this
  have hcast : (((Fintype.card V - 2 : ℕ)) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff_even]
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  have hswap : (univ.erase P).erase X = (univ.erase X).erase P := by
    ext y; simp [mem_erase]; tauto
  rw [sum_add_distrib, sum_add_distrib, sum_const, hcard, nsmul_eq_mul, hcast, zero_mul, zero_add,
    sum_erase_eq_sub hXmem, hswap, sum_erase_eq_sub hPmem, hsym X P]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (-(s P X)) * h2

/-- **Spectral clique bound.** If the quadratic form of `A + c I` is nonnegative (i.e. `λ_min(A) ≥ -c` for
symmetric `A`) and `K` is a nonempty clique on which `A = -1` off the diagonal and `0` on it, then
`|K| ≤ 1 + c`. -/
theorem clique_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℝ) (c : ℝ)
    (hpsd : ∀ x : ι → ℝ, 0 ≤ (∑ i, ∑ j, x i * A i j * x j) + c * ∑ i, x i ^ 2)
    (K : Finset ι) (hKne : K.Nonempty) (hK : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → A i j = -1)
    (hdiag : ∀ i ∈ K, A i i = 0) :
    (K.card : ℝ) ≤ 1 + c := by
  set x : ι → ℝ := fun i => if i ∈ K then 1 else 0 with hx
  have hrow : ∀ i ∈ K, ∑ j, x i * A i j * x j = -((K.card : ℝ) - 1) := by
    intro i hi
    have : ∀ j, x i * A i j * x j = if j ∈ K then A i j else 0 := by
      intro j; simp only [hx, hi, ite_true, one_mul]; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, ← Finset.add_sum_erase K _ hi, hdiag i hi]
    rw [Finset.sum_congr rfl (fun j hj => hK i hi j (Finset.mem_of_mem_erase hj)
      (Ne.symm (Finset.ne_of_mem_erase hj)))]
    rw [Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul]
    have : (1 : ℕ) ≤ K.card := Finset.card_pos.mpr hKne
    push_cast [Nat.cast_sub this]
    ring
  have hquad : (∑ i, ∑ j, x i * A i j * x j) = -((K.card : ℝ) * ((K.card : ℝ) - 1)) := by
    have : ∀ i, (∑ j, x i * A i j * x j) = if i ∈ K then -((K.card : ℝ) - 1) else 0 := by
      intro i
      by_cases hi : i ∈ K
      · simp only [hi, ite_true]; exact hrow i hi
      · simp [hx, hi]
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hnorm : (∑ i, x i ^ 2) = (K.card : ℝ) := by
    have : ∀ i, x i ^ 2 = if i ∈ K then 1 else 0 := by
      intro i; simp only [hx]; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h := hpsd x
  rw [hquad, hnorm] at h
  have hk : (0 : ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hKne
  nlinarith

/-- **The symmetry lemma, combinatorial core.** If `g` commutes with a fixed-point-free involution `ψ`
(i.e. `g` preserves the perfect matching of `ψ`), then the number of fixed points of `g` is even. -/
theorem fix_card_even {α : Type*} [Fintype α] [DecidableEq α] (ψ g : α → α)
    (hψ : ∀ w, ψ (ψ w) = w) (hfree : ∀ w, ψ w ≠ w) (hcomm : ∀ w, g (ψ w) = ψ (g w)) :
    Even ((univ.filter (fun w => g w = w)).card) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  have : (((univ.filter (fun w => g w = w)).card : ℕ) : ZMod 2)
      = ∑ w ∈ univ.filter (fun w => g w = w), (1 : ZMod 2) := by
    rw [sum_const, nsmul_eq_mul, mul_one]
  rw [this]
  refine Finset.sum_involution (fun w _ => ψ w) ?_ ?_ ?_ ?_
  · intro w _; rfl
  · intro w _ _; exact hfree w
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [hcomm, hw]
  · intro w _; exact hψ w

/-- In particular an element with exactly one fixed point (e.g. an element of order `p` of
`PGL(2,q)` acting on `PG(1,q)`) cannot preserve a solution. -/
theorem not_unique_fixed {α : Type*} [Fintype α] [DecidableEq α] (ψ g : α → α)
    (hψ : ∀ w, ψ (ψ w) = w) (hfree : ∀ w, ψ w ≠ w) (hcomm : ∀ w, g (ψ w) = ψ (g w)) :
    (univ.filter (fun w => g w = w)).card ≠ 1 := by
  intro h
  have := fix_card_even ψ g hψ hfree hcomm
  rw [h] at this
  exact Nat.not_even_one this

end Comb

/-! ## The balance lemma and the zero-trace statement for admissible maps -/

section Admissible

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The points of `F^*` not covered by the pairs `{x, ψ x}`, `x ∈ xs` (and not `0`). -/
def Uncovered (ψ : F → F) (xs : Finset F) : Finset F :=
  univ.filter (fun w => w ≠ 0 ∧ ∀ x ∈ xs, w ≠ x ∧ w ≠ ψ x)

theorem uncovered_stable {ψ : F → F} (h : Admissible ψ) {xs : Finset F} (hxs : ∀ x ∈ xs, x ≠ 0)
    {w : F} (hw : w ∈ Uncovered ψ xs) : ψ w ∈ Uncovered ψ xs := by
  simp only [Uncovered, mem_filter, mem_univ, true_and] at hw ⊢
  obtain ⟨hw0, hwx⟩ := hw
  refine ⟨h.ne_zero w hw0, fun x hx => ⟨?_, ?_⟩⟩
  · intro he
    apply (hwx x hx).2
    rw [← h.invol w hw0, he]
  · intro he
    apply (hwx x hx).1
    rw [← h.invol w hw0, he, h.invol x (hxs x hx)]

/-- Signature of `w` with respect to `P₀ = {0,∞}` (`χ(w)`) and the pairs `{x, ψ x}`, `x ∈ xs`. -/
def signature (ψ : F → F) (xs : Finset F) (w : F) : Option xs → ℤ
  | none => quadraticChar F w
  | some x => fP (x : F) (ψ x) w

theorem signature_anti {ψ : F → F} (h : Admissible ψ) {xs : Finset F} (hxs : ∀ x ∈ xs, x ≠ 0)
    {w : F} (hw : w ∈ Uncovered ψ xs) : signature ψ xs (ψ w) = -signature ψ xs w := by
  simp only [Uncovered, mem_filter, mem_univ, true_and] at hw
  obtain ⟨hw0, hwx⟩ := hw
  have hstar := (reform ψ).1 h.cross
  funext i
  cases i with
  | none => simp only [signature, Pi.neg_apply]; exact h.swap w hw0
  | some x =>
    simp only [signature, Pi.neg_apply]
    exact hstar x w (hxs x x.2) hw0 (hwx x x.2).1 (hwx x x.2).2

/-- **Balance lemma** (the pruning rule of the search program).  For an admissible `ψ`, pairs
`P₀ = {0,∞}` and `{x, ψ x}` (`x ∈ xs`), the uncovered points with signature `ε` and with signature
`-ε` are equinumerous (indeed `ψ` maps one class onto the other). -/
theorem balance_admissible {ψ : F → F} (h : Admissible ψ) (xs : Finset F) (hxs : ∀ x ∈ xs, x ≠ 0)
    (ε : Option xs → ℤ) :
    ((Uncovered ψ xs).filter (fun w => signature ψ xs w = ε)).card
      = ((Uncovered ψ xs).filter (fun w => signature ψ xs w = -ε)).card := by
  have hψ : ∀ w ∈ Uncovered ψ xs, ψ (ψ w) = w := by
    intro w hw
    simp only [Uncovered, mem_filter] at hw
    exact h.invol w hw.2.1
  -- apply the abstract lemma to the involution `ψ` restricted to `Uncovered`
  classical
  let ψ' : F → F := fun w => if w ∈ Uncovered ψ xs then ψ w else w
  have hψ' : ∀ w, ψ' (ψ' w) = w := by
    intro w
    by_cases hw : w ∈ Uncovered ψ xs
    · have h2 := uncovered_stable h hxs hw
      simp only [ψ', hw, ite_true, h2, hψ w hw]
    · simp only [ψ', hw, ite_false]
  have hU : ∀ w ∈ Uncovered ψ xs, ψ' w ∈ Uncovered ψ xs := by
    intro w hw; simp only [ψ', hw, ite_true]; exact uncovered_stable h hxs hw
  have hs : ∀ w ∈ Uncovered ψ xs, signature ψ xs (ψ' w) = -signature ψ xs w := by
    intro w hw; simp only [ψ', hw, ite_true]; exact signature_anti h hxs hw
  exact balance_card ψ' hψ' _ hU _ hs ε

/-- **The zero-trace statement (character-sum form).**  For an admissible `ψ` and an odd number of its pairs
`{x, ψ x}`, `x ∈ B`, the sum of `∏_{x ∈ B} f_{x,ψx}(w)` over the uncovered points vanishes.  (Together
with the terms `w = 0` (`(-1)^{|B|}`) and `w = ∞` (`1`) this is `a_q = 0` for the hyperelliptic curve
`y² = ∏_{x ∈ B} (t - x)(t - ψ x)`.) -/
theorem statementC {ψ : F → F} (h : Admissible ψ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hodd : Odd B.card) :
    ∑ w ∈ Uncovered ψ B, ∏ x ∈ B, fP x (ψ x) w = 0 := by
  have hstar := (reform ψ).1 h.cross
  refine Finset.sum_involution (fun w _ => ψ w) ?_ ?_ ?_ ?_
  · intro w hw
    have hw' := hw
    simp only [Uncovered, mem_filter, mem_univ, true_and] at hw'
    obtain ⟨hw0, hwx⟩ := hw'
    have : ∏ x ∈ B, fP x (ψ x) (ψ w) = ∏ x ∈ B, (-1 : ℤ) * fP x (ψ x) w := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [hstar x w (hB x hx) hw0 (hwx x hx).1 (hwx x hx).2]; ring
    rw [this, Finset.prod_mul_distrib, Finset.prod_const, hodd.neg_one_pow]
    ring
  · intro w hw hne he
    apply hne
    have hw' := hw
    simp only [Uncovered, mem_filter, mem_univ, true_and] at hw'
    obtain ⟨hw0, _⟩ := hw'
    -- `ψ w = w` would make the signature at `P₀` vanish: χ(w) = -χ(w)
    exfalso
    have hs := h.swap w hw0
    rw [he] at hs
    have h1 := quadraticChar_dichotomy hw0
    rcases h1 with h1 | h1 <;> rw [h1] at hs <;> norm_num at hs
  · intro w hw; exact uncovered_stable h hB hw
  · intro w hw
    simp only [Uncovered, mem_filter] at hw
    exact h.invol w hw.2.1

/-- **Doubling.**  For an admissible `ψ` and an even number of its pairs `{x, ψ x}`, `x ∈ B`,
the sum of `∏_{x ∈ B} f_{x,ψx}(w)` over the uncovered points equals twice the sum over the uncovered
*squares* (one representative of each pair of `ψ`).  Hence `a_q(C_B) = -2 · Σ_{representatives}`. -/
theorem doubling {ψ : F → F} (h : Admissible ψ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (heven : Even B.card) :
    ∑ w ∈ Uncovered ψ B, ∏ x ∈ B, fP x (ψ x) w
      = 2 * ∑ w ∈ (Uncovered ψ B).filter (fun w => quadraticChar F w = 1), ∏ x ∈ B, fP x (ψ x) w := by
  have hstar := (reform ψ).1 h.cross
  have hg : ∀ w ∈ Uncovered ψ B, ∏ x ∈ B, fP x (ψ x) (ψ w) = ∏ x ∈ B, fP x (ψ x) w := by
    intro w hw
    have hw' := hw
    simp only [Uncovered, mem_filter, mem_univ, true_and] at hw'
    obtain ⟨hw0, hwx⟩ := hw'
    have : ∏ x ∈ B, fP x (ψ x) (ψ w) = ∏ x ∈ B, (-1 : ℤ) * fP x (ψ x) w := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [hstar x w (hB x hx) hw0 (hwx x hx).1 (hwx x hx).2]; ring
    rw [this, Finset.prod_mul_distrib, Finset.prod_const, heven.neg_one_pow, one_mul]
  rw [← Finset.sum_filter_add_sum_filter_not (Uncovered ψ B) (fun w => quadraticChar F w = 1), two_mul]
  congr 1
  symm
  refine Finset.sum_nbij' (fun w => ψ w) (fun w => ψ w) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [mem_filter] at hw ⊢
    obtain ⟨hwU, hw1⟩ := hw
    have hw0 : w ≠ 0 := by
      simp only [Uncovered, mem_filter] at hwU; exact hwU.2.1
    refine ⟨uncovered_stable h hB hwU, ?_⟩
    rw [h.swap w hw0, hw1]; norm_num
  · intro w hw
    rw [mem_filter] at hw ⊢
    obtain ⟨hwU, hw1⟩ := hw
    have hw0 : w ≠ 0 := by
      simp only [Uncovered, mem_filter] at hwU; exact hwU.2.1
    refine ⟨uncovered_stable h hB hwU, ?_⟩
    rw [h.swap w hw0]
    rcases quadraticChar_dichotomy hw0 with h1 | h1
    · exact (hw1 h1).elim
    · rw [h1, neg_neg]
  · intro w hw
    rw [mem_filter] at hw
    simp only [Uncovered, mem_filter] at hw
    exact h.invol w hw.1.2.1
  · intro w hw
    rw [mem_filter] at hw
    simp only [Uncovered, mem_filter] at hw
    exact h.invol w hw.1.2.1
  · intro w hw
    rw [mem_filter] at hw
    exact (hg w hw.1).symm

end Admissible

end BSW.Basic
