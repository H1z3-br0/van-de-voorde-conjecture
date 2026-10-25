module

public import Mathlib
public import BSWCheck.VdVPK

@[expose] public section

/-!
# Van de Voorde's conjecture for every finite field of odd order (one statement)

`vdv_all`: let `F` be a finite field with `|F| = q = p^k`, `p` odd, `q ∉ {3, 7, 11}`.  Then no solution
on `PG(1,q)` is arc-like (every complete exterior set of `(q+1)/2` points contains three collinear
points), assuming the classical theorems used in the paper:
* `q ≡ 1 (mod 4)`: McConnel's theorem (`McConnelHyp`, includes Carlitz's theorem for `k = 1`);
* `q ≡ 3 (mod 4)`, `k = 1`: Proposition 6.2 for the prime field (`StickelHyp p`);
* `q ≡ 3 (mod 4)`, `k ≥ 3`: Proposition 6.2 and Weil's bound (`StickelPKHyp`, `WeilHyp`).

The prime case `k = 1` over an abstract field `F` is transported to `ZMod p` along a ring isomorphism
(`chi_map`, `solution_transport`, `arcLikeP_transport`).
-/

open Finset

namespace BSW.Unified

open BSW.Basic BSW.Segre BSW.Proj BSW.Plane BSW.BSW1 BSW.VdVPK

set_option linter.unusedSectionVars false

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Fintype K] [DecidableEq K]

/-- The quadratic character is preserved by ring isomorphisms (odd order). -/
theorem chi_map {n : ℕ} (e : F ≃+* K) (hF : Fintype.card F = 2 * n + 1)
    (hK : Fintype.card K = 2 * n + 1) (a : F) : quadraticChar K (e a) = quadraticChar F a := by
  have h1 := BSW.FB.chi_eq_pow hF a
  have h2 := BSW.FB.chi_eq_pow hK (e a)
  rw [← map_pow, ← h1, map_intCast] at h2
  have hne := BSW.FB.neg_one_ne_one hK
  have h2' : (2 : K) ≠ 0 := BSW.FB.two_ne_zero' hK
  by_cases ha : a = 0
  · subst ha; simp
  have hea : e a ≠ 0 := by simpa using ha
  rcases quadraticChar_dichotomy ha with h | h <;>
    rcases quadraticChar_dichotomy hea with h' | h' <;> rw [h, h'] at h2 ⊢ <;> push_cast at h2
  · exact absurd h2 hne
  · exact absurd h2.symm hne

/-- Transport along a ring isomorphism. -/
def tr (e : F ≃+* K) (Ψ : Option F → Option F) : Option K → Option K :=
  fun B => Option.map e (Ψ (Option.map e.symm B))

theorem hc_map (e : F ≃+* K) (A : Option F) :
    hc (Option.map e A) = (e (hc A).1, e (hc A).2) := by
  cases A <;> simp [hc]

theorem dt_map (e : F ≃+* K) (A B : Option F) :
    dt (hc (Option.map e A)) (hc (Option.map e B)) = e (dt (hc A) (hc B)) := by
  rw [hc_map, hc_map]; unfold dt; simp

theorem map_symm_map (e : F ≃+* K) (A : Option F) : Option.map e.symm (Option.map e A) = A := by
  cases A <;> simp

theorem map_map_symm (e : F ≃+* K) (B : Option K) : Option.map e (Option.map e.symm B) = B := by
  cases B <;> simp

theorem tr_map (e : F ≃+* K) (Ψ : Option F → Option F) (A : Option F) :
    tr e Ψ (Option.map e A) = Option.map e (Ψ A) := by
  unfold tr; rw [map_symm_map]

theorem compatP_map {n : ℕ} (e : F ≃+* K) (hF : Fintype.card F = 2 * n + 1)
    (hK : Fintype.card K = 2 * n + 1) (A B C D : Option F) :
    CompatP (Option.map e A) (Option.map e B) (Option.map e C) (Option.map e D) ↔
      CompatP A B C D := by
  unfold CompatP
  rw [dt_map, dt_map, dt_map, dt_map, ← map_mul, ← map_mul, ← map_mul, chi_map e hF hK]

theorem solution_transport {n : ℕ} (e : F ≃+* K) (hF : Fintype.card F = 2 * n + 1)
    (hK : Fintype.card K = 2 * n + 1) {Ψ : Option F → Option F} (hS : Solution Ψ) :
    Solution (tr e Ψ) := by
  refine ⟨fun B => ?_, fun B => ?_, fun A C hCA hCψ => ?_⟩
  · obtain ⟨A, rfl⟩ : ∃ A, B = Option.map e A := ⟨_, (map_map_symm e B).symm⟩
    rw [tr_map, tr_map, hS.invol]
  · obtain ⟨A, rfl⟩ : ∃ A, B = Option.map e A := ⟨_, (map_map_symm e B).symm⟩
    rw [tr_map]
    intro h
    exact hS.free A (Option.map_injective e.injective h)
  · obtain ⟨A', rfl⟩ : ∃ A', A = Option.map e A' := ⟨_, (map_map_symm e A).symm⟩
    obtain ⟨C', rfl⟩ : ∃ C', C = Option.map e C' := ⟨_, (map_map_symm e C).symm⟩
    rw [tr_map, tr_map] at *
    rw [compatP_map e hF hK]
    exact hS.cross A' C' (fun h => hCA (by rw [h])) (fun h => hCψ (by rw [h]))

theorem pformP_map (e : F ≃+* K) (A B : Option F) :
    pformP (Option.map e A) (Option.map e B) =
      ⟨e (pformP A B).a, e (pformP A B).b, e (pformP A B).c⟩ := by
  unfold pformP; rw [hc_map, hc_map]; ext <;> simp

theorem det3_map (e : F ≃+* K) (u v w : V3 F) :
    det3 (⟨e u.a, e u.b, e u.c⟩ : V3 K) ⟨e v.a, e v.b, e v.c⟩ ⟨e w.a, e w.b, e w.c⟩ =
      e (det3 u v w) := by
  unfold det3; simp

theorem arcLikeP_transport (e : F ≃+* K) {Ψ : Option F → Option F} (h : ArcLikeP Ψ) :
    ArcLikeP (tr e Ψ) := by
  intro A B C h1 h2 h3 h4 h5 h6
  obtain ⟨A', rfl⟩ : ∃ A', A = Option.map e A' := ⟨_, (map_map_symm e A).symm⟩
  obtain ⟨B', rfl⟩ : ∃ B', B = Option.map e B' := ⟨_, (map_map_symm e B).symm⟩
  obtain ⟨C', rfl⟩ : ∃ C', C = Option.map e C' := ⟨_, (map_map_symm e C).symm⟩
  rw [tr_map] at h2 h4 h6 ⊢
  rw [tr_map, tr_map, pformP_map, pformP_map, pformP_map, det3_map]
  have ne : ∀ {X Y : Option F}, Option.map e X ≠ Option.map e Y → X ≠ Y :=
    fun hne he => hne (by rw [he])
  have hd := h A' B' C' (ne h1) (ne h2) (ne h3) (ne h4) (ne h5) (ne h6)
  simpa using hd

/-- **Van de Voorde's conjecture for every finite field of odd order `q ∉ {3, 7, 11}`**, modulo the
classical theorems listed in the module docstring. -/
theorem vdv_all {p k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hq : Fintype.card F = p ^ k)
    (hk : 1 ≤ k) (h3 : Fintype.card F ≠ 3) (h7 : Fintype.card F ≠ 7) (h11 : Fintype.card F ≠ 11)
    (hmc : Fintype.card F % 4 = 1 → McConnelHyp F p k)
    (hst1 : Fintype.card F % 4 = 3 → k = 1 → BSW.Jacobi.StickelHyp p)
    (hst : Fintype.card F % 4 = 3 → 3 ≤ k → StickelPKHyp F p k ∧ WeilHyp F)
    {Ψ : Option F → Option F} (hS : Solution Ψ) : ¬ ArcLikeP Ψ := by
  have hpodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have hcodd : Fintype.card F % 2 = 1 := by
    rw [hq, Nat.pow_mod, hpodd, one_pow]; rfl
  have hc2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨n, hpn⟩ : ∃ n, Fintype.card F = 2 * n + 1 := ⟨Fintype.card F / 2, by omega⟩
  have h4 : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  rcases h4 with h1 | h3'
  · exact vdv_q1 hq hpn ⟨n / 2, by omega⟩ (by omega) (hmc h1) hS
  · have hodd : Odd n := ⟨n / 2, by omega⟩
    have hkodd := k_odd hq hpn hodd
    rcases (show k = 1 ∨ 3 ≤ k by obtain ⟨t, ht⟩ := hkodd; omega) with hk1 | hk3
    · subst hk1
      rw [pow_one] at hq
      intro harc
      have hcardZ : Fintype.card F = Fintype.card (ZMod p) := by rw [ZMod.card, hq]
      let e : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq hcardZ
      have hK : Fintype.card (ZMod p) = 2 * n + 1 := by rw [← hcardZ, hpn]
      exact theoremV_proj (by omega) (by omega) (by omega) (by omega) (hst1 h3' rfl)
        (solution_transport e hpn hK hS) (arcLikeP_transport e harc)
    · exact vdv_q3_pk hq hpn hodd hk3 (hst h3' hk3).1 (hst h3' hk3).2 hS

end BSW.Unified
