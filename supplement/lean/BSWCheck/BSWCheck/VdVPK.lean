module

public import Mathlib
public import BSWCheck.BSW1
public import BSWCheck.LemmaL

@[expose] public section

/-!
# Van de Voorde's conjecture for prime powers `q = p^k`

Hypotheses (classical theorems absent from Mathlib):
* `McConnelHyp F p k` — McConnel's theorem: a map of `𝔽_q` all of whose difference quotients are
  nonzero squares is `s ↦ a s^{p^j} + b`.
* `StickelPKHyp F p k` — Proposition 6.2 of the paper (Stickelberger's theorem + Lemma 6.1):
  for a generator `η₁` of the characters of `𝔽_q^*`, `J(χ,η₁) + conj J(χ,η') = 0` only if
  `η' = χ η₁^{p^j}`.
* `WeilHyp F` — Weil's bound `|∑ₓ χ(f(x))| ≤ (deg f - 1)√q` for squarefree `f` of positive degree.

Results:
* `bsw1_pk_frame`, `vdv_q1` — **`q ≡ 1 (mod 4)`**: every solution is elliptic (Blokhuis–Seress–Wilbrink), hence not
  arc-like (modulo `McConnelHyp`).
* `vdv_q3_pk` — **`q ≡ 3 (mod 4)`, `q = p^k`, `k ≥ 3`** (Theorem 7.5 for prime powers, modulo `StickelPKHyp` and `WeilHyp`).
  The case `ψ = c x^{p^j}`, `j ≠ 0`, is closed by Weil's bound applied to `1 - c y^e` (from (B)),
  which works for every `q` — no computer check of small `q` is needed.
* `vdv_pk` — the combined statement.
-/

open Finset

namespace BSW.VdVPK

open BSW.Basic BSW.Segre BSW.Proj BSW.Plane BSW.BSW1

set_option linter.unusedSectionVars false

/-! ## Number theory -/

/-- `p^a + p^d = p^b + p^c` (`p ≥ 3`) forces `{a,d} = {b,c}`. -/
theorem pow_sum_eq {p a b c d : ℕ} (hp3 : 3 ≤ p) (e : p ^ a + p ^ d = p ^ b + p ^ c) :
    (a = b ∧ d = c) ∨ (a = c ∧ d = b) := by
  -- core case `a ≤ d`, `b ≤ c`
  have core : ∀ {a b c d : ℕ}, a ≤ d → b ≤ c → p ^ a + p ^ d = p ^ b + p ^ c → a = b ∧ d = c := by
    intro a b c d had hbc e
    have hU : ∀ m : ℕ, ¬ p ∣ 1 + p ^ m := by
      intro m hd
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at hd
        have := Nat.le_of_dvd (by norm_num) hd; omega
      · have : (1 + p ^ m) % p = 1 := by
          rw [show 1 + p ^ m = 1 + p * p ^ (m - 1) by rw [← pow_succ']; congr 2; omega,
            Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
        have := Nat.mod_eq_zero_of_dvd hd; omega
    have e' : p ^ a * (1 + p ^ (d - a)) = p ^ b * (1 + p ^ (c - b)) := by
      rw [mul_add, mul_add, mul_one, mul_one, ← pow_add, ← pow_add, Nat.add_sub_cancel' had,
        Nat.add_sub_cancel' hbc, e]
    obtain ⟨hab, hUV⟩ := BSW.LemmaL.pow_mul_inj (by omega) (hU _) (hU _) e'
    have : d - a = c - b := Nat.pow_right_injective (by omega) (by omega : p ^ (d - a) = p ^ (c - b))
    exact ⟨hab, by omega⟩
  rcases le_total a d with h1 | h1 <;> rcases le_total b c with h2 | h2
  · exact Or.inl (core h1 h2 e)
  · have := core h1 h2 (by rw [e, add_comm]); exact Or.inr ⟨this.1, this.2⟩
  · have := core h1 h2 (by rw [add_comm, e]); exact Or.inr ⟨this.2, this.1⟩
  · have := core h1 h2 (by rw [add_comm, e, add_comm]); exact Or.inl ⟨this.2, this.1⟩

/-- The `p = 3` obstruction: `2(3^x + 3^y) + 1 ≠ 3^k + 2(3^z + 3^w)` for `x, y, z, w < k`, `k ≥ 3`. -/
theorem three_aux {k x y z w : ℕ} (hk : 3 ≤ k) (hx : x < k) (hy : y < k) (hz : z < k) (hw : w < k) :
    2 * (3 ^ x + 3 ^ y) + 1 ≠ 3 ^ k + 2 * (3 ^ z + 3 ^ w) := by
  intro E
  set Q := 3 ^ (k - 1) with hQ
  have h3k : 3 ^ k = 3 * Q := by rw [hQ, ← pow_succ']; congr 1; omega
  have hle : ∀ i, i < k → 3 ^ i ≤ Q := fun i hi => Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle2 : ∀ i, i < k → i ≠ k - 1 → 3 * 3 ^ i ≤ Q := by
    intro i hi hi'
    rw [hQ, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hz1 := Nat.one_le_pow z 3 (by norm_num)
  have hw1 := Nat.one_le_pow w 3 (by norm_num)
  -- one of `x, y` is `k - 1`, and then both are
  have hxy : x = k - 1 ∧ y = k - 1 := by
    by_contra hne
    by_cases hxk : x = k - 1
    · have hyk : y ≠ k - 1 := fun h => hne ⟨hxk, h⟩
      have := hle2 y hy hyk
      rw [hxk, ← hQ] at E; omega
    · by_cases hyk : y = k - 1
      · have := hle2 x hx hxk
        rw [hyk, ← hQ] at E; omega
      · have := hle2 x hx hxk; have := hle2 y hy hyk; omega
  obtain ⟨rfl, rfl⟩ := hxy
  rw [← hQ] at E
  -- `Q + 1 = 2(3^z + 3^w)`; reduce mod 3
  have hQ3 : Q % 3 = 0 := by
    rw [hQ, show k - 1 = (k - 2) + 1 by omega, pow_succ]; simp
  have hmod : ∀ i, 3 ^ i % 3 = if i = 0 then 1 else 0 := by
    intro i; rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [ite_eq_right (by omega), show i = (i - 1) + 1 by omega, pow_succ]; simp
  have hz0 : z = 0 := by
    by_contra hz0
    have := hmod z; rw [ite_eq_right hz0] at this
    have := hmod w
    split_ifs at this <;> omega
  have hw0 : w = 0 := by
    by_contra hw0
    have := hmod w; rw [ite_eq_right hw0] at this
    have := hmod z
    split_ifs at this; omega
  subst hz0; subst hw0
  have : 9 ≤ Q := by rw [hQ]; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
    (show 2 ≤ k - 1 by omega))
  simp at E; omega

/-- **Differences of powers of `p` modulo `h`**: if `h ∣ p^a + p^d - p^b - p^c` with `c ≠ d`, then
`a = c` and `b = d` (`p ≥ 3`, `p^k = 2h + 1`, `k ≥ 3`, all exponents `< k`). -/
theorem nt_diff {p k h a b c d : ℕ} (hp3 : 3 ≤ p) (hk : 3 ≤ k) (hpk : p ^ k = 2 * h + 1)
    (ha : a < k) (hb : b < k) (hc : c < k) (hd : d < k) (hcd : c ≠ d)
    (hdiv : (h : ℤ) ∣ ((p ^ a + p ^ d : ℕ) : ℤ) - ((p ^ b + p ^ c : ℕ) : ℤ)) : a = c ∧ b = d := by
  have hh1 : 1 < h := by
    have : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    have : 27 ≤ p ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
    omega
  have hlt : ∀ i, i < k → p ^ i < h := fun i hi =>
    BSW.LemmaL.pow_lt_h (h := h) hp3 (by omega) hpk hh1 hi
  have h1 : ∀ i, 1 ≤ p ^ i := fun i => Nat.one_le_pow _ _ (by omega)
  have hA := hlt a ha; have hB := hlt b hb; have hC := hlt c hc; have hD := hlt d hd
  have hA1 := h1 a; have hB1 := h1 b; have hC1 := h1 c; have hD1 := h1 d
  obtain ⟨t, ht⟩ := hdiv
  have hpos : (0 : ℤ) < h := by exact_mod_cast (show 0 < h by omega)
  have u1 : (h : ℤ) * t < 2 * h := by rw [← ht]; omega
  have u2 : -(2 * (h : ℤ)) < h * t := by rw [← ht]; omega
  have ht1 : t = 0 ∨ t = 1 ∨ t = -1 := by
    have : t < 2 := by
      by_contra hc'
      have := mul_le_mul_of_nonneg_left (not_lt.mp hc') hpos.le; linarith
    have : -2 < t := by
      by_contra hc'
      have := mul_le_mul_of_nonneg_left (not_lt.mp hc') hpos.le; linarith
    omega
  have hodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
    · exfalso
      have : 2 ∣ p ^ k := dvd_pow ⟨r, by omega⟩ (by omega)
      omega
    · omega
  -- the case `|N| = h` is impossible
  have hno : ∀ {x y z w : ℕ}, x < k → y < k → z < k → w < k →
      p ^ x + p ^ y = p ^ z + p ^ w + h → False := by
    intro x y z w hx hy hz hw e
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have hp : p = 3 := by omega
      subst hp
      exact three_aux hk hx hy hz hw (by omega)
    · have hpk1 : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      have hle : ∀ i, i < k → p ^ i ≤ p ^ (k - 1) :=
        fun i hi => Nat.pow_le_pow_right (by omega) (by omega)
      have := hle x hx; have := hle y hy
      have := h1 z; have := h1 w
      have h5 : 5 * p ^ (k - 1) ≤ p * p ^ (k - 1) := Nat.mul_le_mul_right _ hp5
      omega
  rcases ht1 with rfl | rfl | rfl
  · have e : p ^ a + p ^ d = p ^ b + p ^ c := by omega
    rcases pow_sum_eq hp3 e with ⟨-, h2⟩ | ⟨h1', h2⟩
    · exact absurd h2.symm hcd
    · exact ⟨h1', h2.symm⟩
  · exact (hno ha hd hb hc (by omega)).elim
  · exact (hno hb hc ha hd (by omega)).elim

/-! ## `q ≡ 1 (mod 4)`: the Blokhuis–Seress–Wilbrink theorem for prime powers (modulo McConnel) -/

section Q1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- **McConnel's theorem, taken as a hypothesis**: a map of `𝔽_q` (`q = p^k`) all of whose difference
quotients are nonzero squares is `s ↦ a s^{p^j} + b`, `j < k`.  (Checked by exhaustive search for
`q = 9, 25`.) -/
def McConnelHyp (F : Type*) [Field F] [Fintype F] [DecidableEq F] (p k : ℕ) : Prop :=
  ∀ f : F → F, (∀ s t, s ≠ t → quadraticChar F ((f s - f t) / (s - t)) = 1) →
    ∃ a b : F, ∃ j, j < k ∧ ∀ s, f s = a * s ^ (p ^ j) + b

/-- If `x^{p^{2j}} = x` on `𝔽_q^*` with `0 < j < k`, `q = p^k`, then `k = 2j`. -/
theorem frob_sq_eq {p k j : ℕ} [hp : Fact p.Prime] (hq : Fintype.card F = p ^ k) (hj0 : 0 < j)
    (hjk : j < k) (hfix : ∀ x : F, x ≠ 0 → x ^ (p ^ j * p ^ j) = x) : k = 2 * j := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = p ^ k - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hq]
  have hp2 := hp.out.two_le
  have hpj : 1 ≤ p ^ j * p ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hg1 : g ^ (p ^ j * p ^ j - 1) = 1 := by
    have e := hfix (g : F) g.ne_zero
    have e' : g ^ (p ^ j * p ^ j) = g := Units.ext (by push_cast; exact e)
    have : g ^ (p ^ j * p ^ j - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel hpj, e', one_mul]
    exact mul_right_cancel this
  have hdvd := orderOf_dvd_of_pow_eq_one hg1
  rw [hg, hcard, ← pow_add, show j + j = 2 * j by ring] at hdvd
  have hgcd := Nat.pow_sub_one_gcd_pow_sub_one p k (2 * j)
  rw [Nat.gcd_eq_left hdvd] at hgcd
  have hk : k = Nat.gcd k (2 * j) := by
    have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ p ^ Nat.gcd k (2 * j) := Nat.one_le_pow _ _ (by omega)
    exact Nat.pow_right_injective hp2 (show p ^ k = p ^ Nat.gcd k (2 * j) by omega)
  have : k ∣ 2 * j := by rw [hk]; exact Nat.gcd_dvd_right _ _
  obtain ⟨r, hr⟩ := this
  rcases r with _ | _ | r
  · omega
  · omega
  · nlinarith

/-- **Blokhuis–Seress–Wilbrink theorem for `q = p^k ≡ 1 (mod 4)`** in the frame `P₀`, modulo `McConnelHyp`: every solution is
elliptic, `ψ(x) = ψ(1)/x`. -/
theorem bsw1_pk_frame {p k : ℕ} [hp : Fact p.Prime] (hq : Fintype.card F = p ^ k)
    (hpn : Fintype.card F = 2 * n + 1) (heven : Even n) (hn : 0 < n) (hmc : McConnelHyp F p k)
    {Ψ : Option F → Option F} (hS : Solution Ψ) (h0 : Ψ (some 0) = none) :
    ∀ x : F, x ≠ 0 → toPsi Ψ x = toPsi Ψ 1 / x := by
  have hadm := admissible_of_solution hS h0
  set ψ := toPsi Ψ with hψ
  have hqn := quot_nonsq hpn heven hn hS h0
  set c0 := ψ 1 with hc0
  have hc0χ : quadraticChar F c0 = -1 := by rw [hc0, hadm.swap 1 one_ne_zero, map_one]
  have hc00 : c0 ≠ 0 := hadm.ne_zero 1 one_ne_zero
  set f : F → F := fq Ψ with hf
  have hf0 : f 0 = 0 := by simp [hf, fq]
  have hfs' : ∀ s, s ≠ 0 → f s = ψ s⁻¹ := by intro s hs; simp [hf, fq, hs, hψ]
  set g : F → F := fun s => f s / c0 with hg
  have hgq : ∀ s t, s ≠ t → quadraticChar F ((g s - g t) / (s - t)) = 1 := by
    intro s t hst
    have : (g s - g t) / (s - t) = (f s - f t) / (s - t) * c0⁻¹ := by
      simp only [hg]; field_simp
    rw [this, map_mul, hqn s t hst, chi_inv hc00, hc0χ]; norm_num
  obtain ⟨a, b, j, hj, hab⟩ := hmc g hgq
  have hp2 := hp.out.two_le
  set σ := p ^ j with hσ
  have hσ0 : σ ≠ 0 := by positivity
  have hb : b = 0 := by
    have := hab 0
    simp only [hg, hf0, zero_div, zero_pow hσ0, mul_zero, zero_add] at this
    exact this.symm
  have hfs : ∀ s, f s = c0 * a * s ^ σ := by
    intro s
    have := hab s
    rw [hb, add_zero] at this
    simp only [hg] at this
    field_simp at this
    linear_combination this
  have ha1 : a = 1 := by
    have h1 := hfs 1
    rw [hfs' 1 one_ne_zero, inv_one, one_pow, mul_one] at h1
    have : c0 * (a - 1) = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc00)
  have hψx : ∀ x : F, x ≠ 0 → ψ x = c0 * (x⁻¹) ^ σ := by
    intro x hx
    have := hfs x⁻¹
    rwa [hfs' _ (inv_ne_zero hx), inv_inv, ha1, mul_one] at this
  -- `j = 0`
  have hj0 : j = 0 := by
    by_contra hj0
    have hj0' : 0 < j := Nat.pos_of_ne_zero hj0
    have hinv : ∀ x : F, x ≠ 0 → c0 * (c0⁻¹) ^ σ * x ^ (σ * σ) = x := by
      intro x hx
      have e := hadm.invol x hx
      have hψ0 : ψ x ≠ 0 := hadm.ne_zero x hx
      rw [hψx (ψ x) hψ0, hψx x hx] at e
      calc c0 * (c0⁻¹) ^ σ * x ^ (σ * σ) = c0 * ((c0 * (x⁻¹) ^ σ)⁻¹) ^ σ := by
            rw [mul_inv, inv_pow x σ, inv_inv, mul_pow, ← pow_mul]; ring
        _ = x := e
    have hc1 : c0 * (c0⁻¹) ^ σ = 1 := by
      have := hinv 1 one_ne_zero; rwa [one_pow, mul_one] at this
    have hfix : ∀ x : F, x ≠ 0 → x ^ (σ * σ) = x := by
      intro x hx; have := hinv x hx; rwa [hc1, one_mul] at this
    have hk := frob_sq_eq hq hj0' hj hfix
    -- `c0^{σ-1} = 1` and `n = (σ-1)(σ+1)/2`
    have hcσ : c0 ^ (σ - 1) = 1 := by
      have e : c0 ^ (σ - 1) * c0 = 1 * c0 := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hσ0), one_mul]
        have : (c0⁻¹) ^ σ = c0⁻¹ := by
          field_simp at hc1 ⊢; linear_combination hc1
        rw [inv_pow] at this
        exact inv_injective this
      exact mul_right_cancel₀ hc00 e
    have hσodd : σ % 2 = 1 := by
      have : Fintype.card F % 2 = 1 := by omega
      rw [hq] at this
      rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
      · exfalso; have : 2 ∣ p ^ k := dvd_pow ⟨r, by omega⟩ (by omega); omega
      · rw [hσ]; exact Nat.odd_iff.mp (Odd.pow ⟨r, hr⟩)
    have hqσ : Fintype.card F = σ * σ := by rw [hq, hk, show 2 * j = j + j by ring, pow_add]
    have hnσ : n = (σ - 1) * ((σ + 1) / 2) := by
      have h1 : 1 ≤ σ := Nat.one_le_iff_ne_zero.mpr hσ0
      obtain ⟨t, ht⟩ : ∃ t, σ = 2 * t + 1 := ⟨σ / 2, by omega⟩
      rw [ht, show (2 * t + 1 + 1) / 2 = t + 1 by omega, show 2 * t + 1 - 1 = 2 * t by omega]
      have : 2 * n + 1 = (2 * t + 1) * (2 * t + 1) := by rw [← hpn, hqσ, ht]
      nlinarith
    have he := BSW.FB.chi_eq_pow hpn c0
    rw [hc0χ, hnσ, pow_mul, hcσ, one_pow] at he
    push_cast at he
    exact BSW.FB.neg_one_ne_one hpn he
  intro x hx
  have hσ1 : σ = 1 := by rw [hσ, hj0, pow_zero]
  rw [hψx x hx, hσ1, pow_one, div_eq_mul_inv]

/-- **Van de Voorde's conjecture for `q = p^k ≡ 1 (mod 4)`**, `q ≥ 5`, modulo `McConnelHyp`: no
solution on `PG(1,q)` is arc-like. -/
theorem vdv_q1 {p k : ℕ} [hp : Fact p.Prime] (hq : Fintype.card F = p ^ k)
    (hpn : Fintype.card F = 2 * n + 1) (heven : Even n) (hn2 : 2 ≤ n) (hmc : McConnelHyp F p k)
    {Ψ : Option F → Option F} (hS : Solution Ψ) : ¬ ArcLikeP Ψ := by
  intro harc
  obtain ⟨M, -, h0⟩ := normalize_pair hS none
  have hS' := hS.conj M
  have hadm := admissible_of_solution hS' h0
  have hell := bsw1_pk_frame hq hpn heven (by omega) hmc hS' h0
  exact elliptic_not_arc hpn hn2 hadm hell (arcLike_of_arcLikeP hS' h0 (arcLikeP_conj harc M))

end Q1

/-! ## `q ≡ 3 (mod 4)`, prime powers: the analytic part of Theorem 7.5 for prime powers -/

section Q3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

open BSW.Jacobi

/-- **Proposition 6.2 (Stickelberger's theorem + Lemma 6.1), taken as a hypothesis**: for a generator
`η₁` of the characters of `𝔽_q^*` and `η' ∉ {1, χ}`, `J(χ,η₁) + conj J(χ,η') = 0` only if
`η' = χ η₁^{p^j}` (`j < k`).  (Checked numerically for `q = 27, 243, 343`.) -/
def StickelPKHyp (F : Type*) [Field F] [Fintype F] [DecidableEq F] (p k : ℕ) : Prop :=
  ∀ η₁ η' : MulChar F ℂ, orderOf η₁ = Fintype.card F - 1 → η' ≠ 1 → η' ≠ chiC →
    J η₁ + star (J η') = 0 → ∃ j, j < k ∧ η' = chiC * η₁ ^ (p ^ j)

/-- **Weil's bound, taken as a hypothesis**: `(∑ₓ χ(f x))² ≤ (deg f - 1)² q` for every squarefree `f`
of positive degree. -/
def WeilHyp (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ f : Polynomial F, 0 < f.natDegree → Squarefree f →
    (∑ x : F, (quadraticChar F (f.eval x) : ℤ)) ^ 2 ≤ ((f.natDegree : ℤ) - 1) ^ 2 * Fintype.card F

theorem chiC_sq : (chiC : MulChar F ℂ) * chiC = 1 := by
  calc (chiC : MulChar F ℂ) * chiC = chiC * chiC⁻¹ := by rw [chiC_inv]
    _ = 1 := mul_inv_cancel _

theorem natCard_chars : Nat.card (MulChar F ℂ) = Fintype.card F - 1 := by
  rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
    Fintype.card_units]

theorem exists_gen : ∃ η₁ : MulChar F ℂ, orderOf η₁ = Fintype.card F - 1 := by
  obtain ⟨e⟩ := MulChar.mulEquiv_units F ℂ
  have : IsCyclic (MulChar F ℂ) := (MulEquiv.isCyclic e).mpr inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulChar F ℂ)
  exact ⟨g, by rw [hg, natCard_chars]⟩

theorem gen_pow {η₁ : MulChar F ℂ} (hη : orderOf η₁ = Fintype.card F - 1) (η : MulChar F ℂ) :
    ∃ m : ℕ, η₁ ^ m = η := by
  have htop : Subgroup.zpowers η₁ = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hη, natCard_chars])
  have hmem : η ∈ Subgroup.zpowers η₁ := by rw [htop]; exact Subgroup.mem_top η
  obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
  exact ⟨m, hm⟩

/-- A generator separates the points of `F^*`. -/
theorem gen_inj {η₁ : MulChar F ℂ} (hη : orderOf η₁ = Fintype.card F - 1) {u : F}
    (hu : η₁ u = 1) : u = 1 := by
  by_contra hne
  obtain ⟨η, hη'⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity F ℂ hne
  obtain ⟨m, rfl⟩ := gen_pow hη η
  apply hη'
  by_cases hm : m = 0
  · subst hm; simp only [pow_zero]
    have hu0 : u ≠ 0 := by intro h0; rw [h0, MulChar.map_zero] at hu; exact zero_ne_one hu
    exact MulChar.one_apply (Ne.isUnit hu0)
  · rw [MulChar.pow_apply' η₁ hm, hu, one_pow]

/-- `χ = η₁^n` (the unique element of order 2). -/
theorem chiC_eq_pow (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) {η₁ : MulChar F ℂ}
    (hη : orderOf η₁ = Fintype.card F - 1) : (chiC : MulChar F ℂ) = η₁ ^ n := by
  have h2n : orderOf η₁ = 2 * n := by rw [hη, hpn]; omega
  obtain ⟨m, hm⟩ := gen_pow hη chiC
  have hm' : η₁ ^ (m % (2 * n)) = chiC := by rw [← h2n, pow_mod_orderOf, hm]
  have hsq : η₁ ^ (2 * (m % (2 * n))) = η₁ ^ 0 := by
    rw [pow_zero, mul_comm, pow_mul, hm', sq, chiC_sq]
  rw [pow_eq_pow_iff_modEq, h2n] at hsq
  have hlt : m % (2 * n) < 2 * n := Nat.mod_lt _ (by have := hodd.pos; omega)
  have hdvd : 2 * n ∣ 2 * (m % (2 * n)) := (Nat.modEq_zero_iff_dvd).mp hsq
  have : m % (2 * n) = 0 ∨ m % (2 * n) = n := by
    obtain ⟨r, hr⟩ := hdvd
    rcases r with _ | _ | r
    · omega
    · omega
    · nlinarith
  rcases this with h0 | hn
  · exfalso; rw [h0, pow_zero] at hm'
    exact chiC_ne_one (n := n) hpn hodd hm'.symm
  · rw [← hm', hn]

/-- The candidate support of `M(·, η₁)`. -/
noncomputable def Sset (η₁ : MulChar F ℂ) (p k : ℕ) : Finset (MulChar F ℂ) :=
  (range k).image (fun j => η₁ ^ (p ^ j)) ∪ (range k).image (fun j => chiC * η₁ ^ (p ^ j))

theorem M_zero_out {p k : ℕ} (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n)
    (hst : StickelPKHyp F p k) {η₁ : MulChar F ℂ} (hη : orderOf η₁ = Fintype.card F - 1)
    (hη1 : η₁ ≠ 1) (hηχ : η₁ ≠ chiC) {ψ : F → F} (h : Admissible ψ) (hA : CondA ψ) (hk1 : 1 ≤ k)
    {η' : MulChar F ℂ} (hout : η' ∉ Sset η₁ p k) : M ψ η' η₁ = 0 := by
  by_cases e1 : η' = 1
  · subst e1; exact M_one h hη1
  by_cases e2 : η' = chiC
  · subst e2; exact M_chi h hηχ
  have hne : η' ≠ η₁ := by
    rintro rfl; apply hout; unfold Sset; apply mem_union_left
    exact mem_image.mpr ⟨0, mem_range.mpr hk1, by simp⟩
  have hJ : J η₁ + J η'⁻¹ ≠ 0 := by
    intro hz
    obtain ⟨j, hj, he⟩ := hst η₁ η' hη e1 e2 (by rw [star_J]; exact hz)
    apply hout; unfold Sset; apply mem_union_right
    exact mem_image.mpr ⟨j, mem_range.mpr hj, he.symm⟩
  have hid := jacobi_id hpn hodd h hA η' η₁
  have hs : ∑ x, η'⁻¹ x * η₁ x = 0 := by
    have hne' : η'⁻¹ * η₁ ≠ 1 := by intro he; apply hne; exact inv_mul_eq_one.mp he
    rw [← MulChar.sum_eq_zero_of_ne_one hne']
    exact sum_congr rfl (fun x _ => (MulChar.mul_apply _ _ _).symm)
  rw [hs, mul_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left hJ

/-- Sums of a character over the squares. -/
theorem sum_SQ_char (hpn : Fintype.card F = 2 * n + 1) (hn : 0 < n) {lam : MulChar F ℂ}
    (h1 : lam ≠ 1) (h2 : lam ≠ chiC) : ∑ x ∈ SQ (F := F) n, lam x = 0 := by
  have hpt : ∀ x : F, (if x ^ n = 1 then lam x else 0) = (lam x + ((chiC : MulChar F ℂ) * lam) x) / 2 := by
    intro x
    rw [MulChar.mul_apply, chiC_apply]
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero, zero_pow hn.ne']
    by_cases hsq : x ^ n = 1
    · rw [ite_eq_left hsq, (chi_one_iff hpn x).2 hsq]; push_cast; ring
    · rw [ite_eq_right hsq]
      rcases quadraticChar_dichotomy hx with hc | hc
      · exact absurd ((chi_one_iff hpn x).1 hc) hsq
      · rw [hc]; push_cast; ring
  have hχlam : (chiC : MulChar F ℂ) * lam ≠ 1 := by
    intro he; apply h2
    rw [eq_inv_of_mul_eq_one_right he, chiC_inv]
  rw [SQ, sum_filter, sum_congr rfl (fun x _ => hpt x), ← sum_div, sum_add_distrib,
    MulChar.sum_eq_zero_of_ne_one h1, MulChar.sum_eq_zero_of_ne_one hχlam]; simp

theorem sum_SQ_one (hpn : Fintype.card F = 2 * n + 1) :
    ∑ x ∈ SQ (F := F) n, (1 : MulChar F ℂ) x = n := by
  have hn : 0 < n := by have : 1 < Fintype.card F := Fintype.one_lt_card; omega
  rw [sum_congr rfl (fun x hx => by
    have hxn : x ^ n = 1 := by simpa [SQ] using hx
    exact MulChar.one_apply (Ne.isUnit (pow_ne_zero_of hn one_ne_zero hxn)))]
  rw [sum_const, card_SQ hpn]; simp

/-- Coefficients of `η₁(ψ x)` on the squares. -/
noncomputable def CC (ψ : F → F) (η₁ : MulChar F ℂ) (p j : ℕ) : ℂ :=
  M ψ (η₁ ^ (p ^ j)) η₁ + M ψ (chiC * η₁ ^ (p ^ j)) η₁

/-- **The analytic part of Theorem 7.5 for prime powers**: under `StickelPKHyp`, an admissible `ψ` with (A) is a
twisted Frobenius on the squares: `ψ(x) = ψ(1) x^{p^j}`. -/
theorem psi_power {p k : ℕ} [hp : Fact p.Prime] (hq : Fintype.card F = p ^ k)
    (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (hk : 3 ≤ k) (hst : StickelPKHyp F p k)
    {ψ : F → F} (h : Admissible ψ) (hA : CondA ψ) :
    ∃ j, j < k ∧ ∀ x : F, x ^ n = 1 → ψ x = ψ 1 * x ^ (p ^ j) := by
  have hn : 0 < n := hodd.pos
  have hp2 := hp.out.two_le
  have hp3 : 3 ≤ p := by
    by_contra hlt
    have : p = 2 := by omega
    subst this
    have : 2 ∣ Fintype.card F := by rw [hq]; exact dvd_pow_self 2 (by omega)
    omega
  have hpk : p ^ k = 2 * n + 1 := by rw [← hq, hpn]
  have hn1 : 1 < n := by
    have : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    have : 27 ≤ p ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
    omega
  have hpj : ∀ j, j < k → p ^ j < n := fun j hj =>
    BSW.LemmaL.pow_lt_h (h := n) hp3 (by omega) hpk hn1 hj
  obtain ⟨η₁, hη⟩ := exists_gen (F := F)
  have h2n : orderOf η₁ = 2 * n := by rw [hη, hpn]; omega
  have hχ := chiC_eq_pow hpn hodd hη
  have hη1 : η₁ ≠ 1 := by intro he; rw [he, orderOf_one] at h2n; omega
  have hηχ : η₁ ≠ chiC := by
    intro he
    have : η₁ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [he]; rw [he, chiC_sq]
    have := orderOf_le_of_pow_eq_one (by norm_num) this
    omega
  set ρ : ℕ → MulChar F ℂ := fun j => η₁ ^ (p ^ j) with hρ
  -- exponent facts
  have hmod : ∀ a b : ℕ, a < 2 * n → b < 2 * n → η₁ ^ a = η₁ ^ b → a = b := by
    intro a b ha hb he
    rw [pow_eq_pow_iff_modEq, h2n] at he
    unfold Nat.ModEq at he
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at he
  have hρinj : ∀ i j, i < k → j < k → ρ i = ρ j → i = j := by
    intro i j hi hj he
    have := hmod _ _ (by have := hpj i hi; omega) (by have := hpj j hj; omega) he
    exact Nat.pow_right_injective hp2 this
  have hdisj : ∀ i j, i < k → j < k → ρ i ≠ chiC * ρ j := by
    intro i j hi hj he
    rw [hχ, hρ] at he; simp only at he
    rw [← pow_add] at he
    have := hmod _ _ (by have := hpj i hi; omega) (by have := hpj j hj; omega) he
    have := hpj i hi; omega
  -- `M` vanishes outside `Sset`
  have hout := fun {η'} (hη' : η' ∉ Sset η₁ p k) =>
    M_zero_out hpn hodd hst hη hη1 hηχ h hA (by omega) hη'
  -- Fourier on the squares
  have hsq_chi : ∀ x : F, x ^ n = 1 → chiC x = 1 := by
    intro x hx; rw [chiC_apply, (chi_one_iff hpn x).2 hx]; simp
  have hfour : ∀ x : F, x ^ n = 1 →
      ((Fintype.card F - 1 : ℕ) : ℂ) * η₁ (ψ x) = ∑ j ∈ range k, CC ψ η₁ p j * ρ j x := by
    intro x hx
    have hx0 : x ≠ 0 := pow_ne_zero_of hn one_ne_zero hx
    rw [← fourier η₁ hx0,
      ← sum_subset (subset_univ (Sset η₁ p k)) (fun η' _ hη' => by rw [hout hη', mul_zero])]
    unfold Sset
    rw [sum_union, sum_image (fun i hi j hj he => hρinj i j (mem_range.mp hi) (mem_range.mp hj) he),
      sum_image (fun i hi j hj he => hρinj i j (mem_range.mp hi) (mem_range.mp hj)
        (mul_left_cancel he)), ← sum_add_distrib]
    · refine sum_congr rfl (fun j _ => ?_)
      rw [MulChar.mul_apply, hsq_chi x hx, one_mul]; unfold CC; ring
    · rw [disjoint_left]
      intro η' h1 h2
      obtain ⟨i, hi, rfl⟩ := mem_image.mp h1
      obtain ⟨j, hj, he⟩ := mem_image.mp h2
      exact hdisj i j (mem_range.mp hi) (mem_range.mp hj) he.symm
  -- `|η₁(ψ x)| = 1`
  have hunit : ∀ u : F, u ≠ 0 → η₁ u * star (η₁ u) = 1 := by
    intro u hu
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (Ne.isUnit hu)]
  -- orthogonality of the coefficients
  have horth : ∀ a b, a < k → b < k → a ≠ b → CC ψ η₁ p a * star (CC ψ η₁ p b) = 0 := by
    intro a b ha hb hab
    set lam := (ρ a)⁻¹ * ρ b with hlam
    have hlam1 : lam ≠ 1 := by
      intro he; apply hab; apply hρinj a b ha hb
      exact (inv_mul_eq_one.mp he)
    have hlamχ : lam ≠ chiC := by
      intro he
      apply hdisj b a hb ha
      rw [← he, hlam, mul_comm ((ρ a)⁻¹ * ρ b) (ρ a), ← mul_assoc, mul_inv_cancel, one_mul]
    -- way 1
    have w1 : ∑ x ∈ SQ (F := F) n, (∑ j ∈ range k, CC ψ η₁ p j * ρ j x) *
        star (∑ j ∈ range k, CC ψ η₁ p j * ρ j x) * lam x = 0 := by
      rw [sum_congr rfl (fun x hx => by
        have hxn : x ^ n = 1 := by simpa [SQ] using hx
        rw [← hfour x hxn, star_mul', star_natCast,
          show ((Fintype.card F - 1 : ℕ) : ℂ) * η₁ (ψ x) * (((Fintype.card F - 1 : ℕ) : ℂ) *
            star (η₁ (ψ x))) = ((Fintype.card F - 1 : ℕ) : ℂ) ^ 2 * (η₁ (ψ x) * star (η₁ (ψ x)))
            by ring,
          hunit _ (h.ne_zero x (pow_ne_zero_of hn one_ne_zero hxn)), mul_one])]
      rw [← mul_sum, sum_SQ_char hpn hn hlam1 hlamχ, mul_zero]
    -- way 2
    have w2 : ∑ x ∈ SQ (F := F) n, (∑ j ∈ range k, CC ψ η₁ p j * ρ j x) *
        star (∑ j ∈ range k, CC ψ η₁ p j * ρ j x) * lam x =
        ∑ s ∈ range k, ∑ t ∈ range k, CC ψ η₁ p s * star (CC ψ η₁ p t) *
          ∑ x ∈ SQ (F := F) n, (ρ s * (ρ t)⁻¹ * lam) x := by
      have hpt : ∀ x : F, (∑ j ∈ range k, CC ψ η₁ p j * ρ j x) *
          star (∑ j ∈ range k, CC ψ η₁ p j * ρ j x) * lam x =
          ∑ s ∈ range k, ∑ t ∈ range k, CC ψ η₁ p s * star (CC ψ η₁ p t) *
            (ρ s * (ρ t)⁻¹ * lam) x := by
        intro x
        rw [star_sum]
        simp only [star_mul', MulChar.star_apply']
        rw [sum_mul_sum, sum_mul]
        refine sum_congr rfl (fun s _ => ?_)
        rw [sum_mul]
        refine sum_congr rfl (fun t _ => ?_)
        rw [hlam]; simp only [MulChar.mul_apply]; ring
      rw [sum_congr rfl (fun x _ => hpt x), sum_comm]
      refine sum_congr rfl (fun s _ => ?_)
      rw [sum_comm]
      refine sum_congr rfl (fun t _ => ?_)
      rw [mul_sum]
    have hinner : ∀ s t, s < k → t < k → ¬ (s = a ∧ t = b) →
        ∑ x ∈ SQ (F := F) n, (ρ s * (ρ t)⁻¹ * lam) x = 0 := by
      intro s t hs ht hst
      apply sum_SQ_char hpn hn
      · intro he
        apply hst
        have e : ρ s * ρ b = ρ t * ρ a := by
          have : ρ s * (ρ t)⁻¹ * ((ρ a)⁻¹ * ρ b) = (ρ s * ρ b) * (ρ t * ρ a)⁻¹ := by
            rw [mul_inv]; ac_rfl
          rw [hlam, this] at he
          exact mul_inv_eq_one.mp he
        simp only [hρ, ← pow_add] at e
        rw [pow_eq_pow_iff_modEq, h2n] at e
        have hd := (Nat.modEq_iff_dvd).mp e
        have hd' : (n : ℤ) ∣ ((p ^ s + p ^ b : ℕ) : ℤ) - ((p ^ t + p ^ a : ℕ) : ℤ) := by
          obtain ⟨r, hr⟩ := hd
          exact ⟨-(2 * r), by push_cast at hr ⊢; linear_combination -hr⟩
        exact nt_diff hp3 hk hpk hs ht ha hb hab hd'
      · intro he
        apply hst
        have e : ρ s * ρ b = chiC * (ρ t * ρ a) := by
          have : ρ s * (ρ t)⁻¹ * ((ρ a)⁻¹ * ρ b) = (ρ s * ρ b) * (ρ t * ρ a)⁻¹ := by
            rw [mul_inv]; ac_rfl
          rw [hlam, this] at he
          rw [← he, inv_mul_cancel_right]
        rw [hχ] at e
        simp only [hρ, ← pow_add] at e
        rw [pow_eq_pow_iff_modEq, h2n] at e
        have hd := (Nat.modEq_iff_dvd).mp e
        have hd' : (n : ℤ) ∣ ((p ^ s + p ^ b : ℕ) : ℤ) - ((p ^ t + p ^ a : ℕ) : ℤ) := by
          obtain ⟨r, hr⟩ := hd
          exact ⟨-(2 * r) + 1, by push_cast at hr ⊢; linear_combination -hr⟩
        exact nt_diff hp3 hk hpk hs ht ha hb hab hd'
    rw [w2, sum_eq_single a, sum_eq_single b] at w1
    · have hone : ρ a * (ρ b)⁻¹ * lam = 1 := by
        rw [hlam]; rw [show ρ a * (ρ b)⁻¹ * ((ρ a)⁻¹ * ρ b) = (ρ a * (ρ a)⁻¹) * ((ρ b)⁻¹ * ρ b) by ac_rfl,
          mul_inv_cancel, inv_mul_cancel, one_mul]
      rw [hone, sum_SQ_one hpn] at w1
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      exact (mul_eq_zero.mp w1).resolve_right hn0
    · intro t ht htb
      rw [hinner a t ha (mem_range.mp ht) (fun e => htb e.2), mul_zero]
    · intro hb'; exact absurd (mem_range.mpr hb) hb'
    · intro s hs hsa
      apply sum_eq_zero
      intro t ht
      rw [hinner s t (mem_range.mp hs) (mem_range.mp ht) (fun e => hsa e.1), mul_zero]
    · intro ha'; exact absurd (mem_range.mpr ha) ha'
  -- exactly one coefficient survives
  have hq1 : ((Fintype.card F - 1 : ℕ) : ℂ) ≠ 0 := by
    have : 1 < Fintype.card F := Fintype.one_lt_card
    exact_mod_cast (show Fintype.card F - 1 ≠ 0 by omega)
  have hψ1 := h.ne_zero 1 one_ne_zero
  have hG1 := hfour 1 (one_pow n)
  obtain ⟨j0, hj0, hC0⟩ : ∃ j0, j0 < k ∧ CC ψ η₁ p j0 ≠ 0 := by
    by_contra hall
    have hall' : ∀ j, j < k → CC ψ η₁ p j = 0 := fun j hj => by
      by_contra hne; exact hall ⟨j, hj, hne⟩
    rw [sum_eq_zero (fun j hj => by rw [hall' j (mem_range.mp hj), zero_mul])] at hG1
    exact mul_ne_zero hq1 (map_ne_zero_of_ne (η := η₁) hψ1) hG1
  have hzero : ∀ j, j < k → j ≠ j0 → CC ψ η₁ p j = 0 := by
    intro j hj hne
    have := horth j0 j hj0 hj (Ne.symm hne)
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hC0
    · exact star_eq_zero.mp h0
  have hsingle : ∀ x : F, x ^ n = 1 →
      ((Fintype.card F - 1 : ℕ) : ℂ) * η₁ (ψ x) = CC ψ η₁ p j0 * ρ j0 x := by
    intro x hx
    rw [hfour x hx, sum_eq_single j0]
    · intro j hj hne; rw [hzero j (mem_range.mp hj) hne, zero_mul]
    · intro h'; exact absurd (mem_range.mpr hj0) h'
  refine ⟨j0, hj0, fun x hx => ?_⟩
  have e1 := hsingle x hx
  have e0 := hsingle 1 (one_pow n)
  rw [map_one, mul_one] at e0
  have hx0 : x ≠ 0 := pow_ne_zero_of hn one_ne_zero hx
  have hu : ψ 1 * x ^ (p ^ j0) ≠ 0 := mul_ne_zero hψ1 (pow_ne_zero _ hx0)
  have hρx : ρ j0 x = η₁ (x ^ (p ^ j0)) := by
    rw [hρ]; simp only
    rw [MulChar.pow_apply' η₁ (by positivity), map_pow]
  have key : η₁ (ψ x) = η₁ (ψ 1 * x ^ (p ^ j0)) := by
    rw [map_mul, ← hρx]
    apply mul_left_cancel₀ hq1
    rw [e1, ← e0]; ring
  have hdiv : η₁ (ψ x / (ψ 1 * x ^ (p ^ j0))) = 1 := by
    rw [div_eq_mul_inv, map_mul, key, ← map_mul, mul_inv_cancel₀ hu, map_one]
  have := gen_inj hη hdiv
  rw [div_eq_one_iff_eq hu] at this
  exact this

/-! ## The two endgames (Weil) -/

theorem sep_quartic (hpn : Fintype.card F = 2 * n + 1) {c : F} (hc0 : c ≠ 0) (hc2 : c ≠ c⁻¹) :
    Squarefree ((Polynomial.X ^ 2 - Polynomial.C c) * (Polynomial.X ^ 2 - Polynomial.C c⁻¹) : Polynomial F) := by
  have h2 : ((2 : ℕ) : F) ≠ 0 := by exact_mod_cast BSW.FB.two_ne_zero' hpn
  apply Polynomial.Separable.squarefree
  refine Polynomial.Separable.mul (Polynomial.separable_X_pow_sub_C c h2 hc0)
    (Polynomial.separable_X_pow_sub_C c⁻¹ h2 (inv_ne_zero hc0)) ?_
  set u := c - c⁻¹ with hu
  have hu0 : u ≠ 0 := sub_ne_zero.mpr hc2
  refine ⟨-Polynomial.C u⁻¹, Polynomial.C u⁻¹, ?_⟩
  have : -Polynomial.C u⁻¹ * (Polynomial.X ^ 2 - Polynomial.C c) +
      Polynomial.C u⁻¹ * (Polynomial.X ^ 2 - Polynomial.C c⁻¹) = Polynomial.C (u⁻¹ * (c - c⁻¹)) := by
    simp only [map_mul, map_sub]; ring
  rw [this, ← hu, inv_mul_cancel₀ hu0, map_one]

theorem natDegree_quartic (c : F) :
    ((Polynomial.X ^ 2 - Polynomial.C c) * (Polynomial.X ^ 2 - Polynomial.C c⁻¹) : Polynomial F).natDegree = 4 := by
  rw [Polynomial.natDegree_mul (Polynomial.monic_X_pow_sub_C c (by norm_num)).ne_zero
    (Polynomial.monic_X_pow_sub_C c⁻¹ (by norm_num)).ne_zero, Polynomial.natDegree_X_pow_sub_C,
    Polynomial.natDegree_X_pow_sub_C]

/-- **Endgame `j = 0`**: `ψ(x) = c x` on the squares is impossible for `q ≥ 27` (Weil, degree 4). -/
theorem endgame_lin (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (hq27 : 27 ≤ Fintype.card F)
    (hW : WeilHyp F) {ψ : F → F} (h : Admissible ψ)
    (hlin : ∀ x : F, x ^ n = 1 → ψ x = ψ 1 * x) : False := by
  have hn : 0 < n := hodd.pos
  have hF := BSW.FB.ringChar_ne_two hpn
  set c := ψ 1 with hc
  have hcχ : quadraticChar F c = -1 := by rw [hc, h.swap 1 one_ne_zero, map_one]
  have hc0 : c ≠ 0 := h.ne_zero 1 one_ne_zero
  have hm1 : quadraticChar F (-1) = -1 := BSW.Jacobi.chi_neg_one hpn hodd
  -- `χ((t - c)(ct - 1)) = 1` for squares `t ≠ 1`
  have hT : ∀ t : F, t ^ n = 1 → t ≠ 1 → quadraticChar F ((t - c) * (c * t - 1)) = 1 := by
    intro t ht ht1
    have ht0 : t ≠ 0 := pow_ne_zero_of hn one_ne_zero ht
    have h1ψ : (1 : F) ≠ ψ t := by
      intro e
      have := h.swap t ht0
      rw [← e, map_one, (chi_one_iff hpn t).2 ht] at this; norm_num at this
    have hcr := h.cross t 1 ht0 one_ne_zero (Ne.symm ht1) h1ψ
    simp only [BSW.Basic.Compat] at hcr
    rw [hlin t ht, ← hc] at hcr
    have e : (t - 1) * (t - c) * (c * t - 1) * (c * t - c) =
        (t - 1) ^ 2 * (c * ((t - c) * (c * t - 1))) := by ring
    rw [e, chi_sq_mul (sub_ne_zero.mpr ht1), map_mul, hcχ] at hcr
    linarith
  -- a square `t ≠ 1`
  obtain ⟨t0, ht0⟩ : ((SQ (F := F) n).erase 1).Nonempty := by
    rw [← card_pos, card_erase_of_mem (by simp [SQ]), card_SQ hpn]
    have : 13 ≤ n := by omega
    omega
  rw [mem_erase] at ht0
  have ht0n : t0 ^ n = 1 := by simpa [SQ] using ht0.2
  -- `c ≠ ±1`
  have hc1 : c ≠ 1 := by intro e; rw [e, map_one] at hcχ; norm_num at hcχ
  have hcm1 : c ≠ -1 := by
    intro e
    have := hT t0 ht0n ht0.1
    have hneg : t0 + 1 ≠ 0 := by
      intro e'
      have : t0 = -1 := by linear_combination e'
      rw [this] at ht0n
      exact BSW.FB.neg_one_ne_one hpn (by rw [← hodd.neg_one_pow]; exact ht0n)
    rw [e, show (t0 - -1) * (-1 * t0 - 1) = (t0 + 1) ^ 2 * (-1) by ring,
      chi_sq_mul hneg, hm1] at this
    norm_num at this
  have hc2 : c ≠ c⁻¹ := by
    intro e
    have h1 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    rw [← e] at h1
    have : (c - 1) * (c + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact hc1 (by linear_combination h)
    · exact hcm1 (by linear_combination h)
  -- the character sum `∑_r χ((r² - c)(c r² - 1)) = 2n - 5`
  set g : F → ℤ := fun t => quadraticChar F ((t - c) * (c * t - 1)) with hg
  have hsum : ∑ r : F, g (r ^ 2) = 2 * n - 5 := by
    rw [BSW.CharSums.sum_comp_sq hF g,
      ← sum_filter_add_sum_filter_not univ (fun t : F => t ^ n = 1)]
    have hSQ : univ.filter (fun t : F => t ^ n = 1) = SQ (F := F) n := rfl
    rw [hSQ]
    have h1mem : (1 : F) ∈ SQ (F := F) n := by simp [SQ]
    have part1 : ∑ t ∈ SQ (F := F) n, (quadraticChar F t + 1) * g t = 2 * n - 4 := by
      rw [← add_sum_erase _ _ h1mem]
      have e1 : (quadraticChar F 1 + 1) * g 1 = -2 := by
        show (quadraticChar F 1 + 1) * quadraticChar F ((1 - c) * (c * 1 - 1)) = -2
        rw [map_one, show (1 - c) * (c * 1 - 1) = (1 - c) ^ 2 * (-1) by ring,
          chi_sq_mul (sub_ne_zero.mpr (Ne.symm hc1)), hm1]; norm_num
      have e2 : ∑ t ∈ (SQ (F := F) n).erase 1, (quadraticChar F t + 1) * g t =
          ∑ t ∈ (SQ (F := F) n).erase 1, (2 : ℤ) := by
        refine sum_congr rfl (fun t ht => ?_)
        rw [mem_erase] at ht
        have htn : t ^ n = 1 := by simpa [SQ] using ht.2
        simp only [hg]
        rw [(chi_one_iff hpn t).2 htn, hT t htn ht.1]; norm_num
      rw [e1, e2, sum_const, card_erase_of_mem h1mem, card_SQ hpn, nsmul_eq_mul,
        Nat.cast_sub (show 1 ≤ n by omega)]
      push_cast
      ring
    have part2 : ∑ t ∈ univ.filter (fun t : F => ¬ t ^ n = 1), (quadraticChar F t + 1) * g t = -1 := by
      rw [sum_eq_single 0]
      · simp only [hg, MulChar.map_zero, zero_add, one_mul]
        rw [show (0 - c) * (c * 0 - 1) = c by ring, hcχ]
      · intro t ht ht0
        have htn : ¬ t ^ n = 1 := (mem_filter.mp ht).2
        rcases quadraticChar_dichotomy ht0 with hc' | hc'
        · exact absurd ((chi_one_iff hpn t).1 hc') htn
        · rw [hc']; ring
      · intro h0; exfalso; apply h0
        simp [zero_pow hn.ne']
    rw [part1, part2]; ring
  -- Weil for `(X² - c)(X² - c⁻¹) = c⁻¹ (X² - c)(cX² - 1)`
  have hWe := hW _ (by rw [natDegree_quartic]; norm_num) (sep_quartic hpn hc0 hc2)
  rw [natDegree_quartic] at hWe
  have hev : ∀ r : F, quadraticChar F (Polynomial.eval r ((Polynomial.X ^ 2 - Polynomial.C c) *
      (Polynomial.X ^ 2 - Polynomial.C c⁻¹))) = -g (r ^ 2) := by
    intro r
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, hg]
    rw [show (r ^ 2 - c) * (r ^ 2 - c⁻¹) = c⁻¹ * ((r ^ 2 - c) * (c * r ^ 2 - 1)) by
      field_simp, map_mul, chi_inv hc0, hcχ]; ring
  rw [sum_congr rfl (fun r _ => hev r), sum_neg_distrib, hsum, hpn] at hWe
  have : (13 : ℤ) ≤ n := by omega
  push_cast at hWe
  nlinarith

/-- `q = p^k ≡ 3 (mod 4)` forces `k` odd. -/
theorem k_odd {p k : ℕ} (hq : Fintype.card F = p ^ k) (hpn : Fintype.card F = 2 * n + 1)
    (hodd : Odd n) : Odd k := by
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ho
  · exfalso
    have hpr : p ^ k = (p ^ r) ^ 2 := by rw [hr, ← two_mul, pow_mul']
    have hodd' : (p ^ r) % 2 = 1 := by
      rcases Nat.even_or_odd (p ^ r) with ⟨t, ht⟩ | ⟨t, ht⟩
      · exfalso
        have : 2 ∣ p ^ k := by rw [hpr, ht]; exact ⟨2 * t * t, by ring⟩
        omega
      · omega
    obtain ⟨t, ht⟩ : ∃ t, p ^ r = 2 * t + 1 := ⟨p ^ r / 2, by omega⟩
    rw [ht] at hpr
    obtain ⟨u, hu⟩ := hodd
    have : 2 * n + 1 = (2 * t + 1) ^ 2 := by rw [← hpn, hq, hpr]
    have : n = 2 * (t * t + t) := by nlinarith
    omega
  · exact ho

/-- `3g ≤ k` for `g = gcd(j, k)`, `0 < j < k`, `k` odd. -/
theorem three_gcd_le {j k : ℕ} (hj0 : 0 < j) (hjk : j < k) (hk : Odd k) : 3 * Nat.gcd j k ≤ k := by
  obtain ⟨u, hu⟩ := hk
  have key : ∀ g r : ℕ, 0 < g → g ≤ j → k = g * r → 3 * g ≤ k := by
    intro g r hg0 hgj hr
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with h | h | h | h
    · subst h; simp at hr; omega
    · subst h; simp at hr; omega
    · subst h; omega
    · nlinarith
  obtain ⟨r, hr⟩ := Nat.gcd_dvd_right j k
  exact key _ r (Nat.gcd_pos_of_pos_left _ hj0) (Nat.le_of_dvd hj0 (Nat.gcd_dvd_left _ _)) hr

/-- The final inequality: `(Q-2)² ≤ (e-1)² Q` is impossible if `1 ≤ e ≤ 2P - 2`, `P ≥ 3`, `P³ ≤ Q`. -/
theorem final_ineq {Q e P : ℤ} (hE1 : 1 ≤ e) (hE2 : e ≤ 2 * P - 2) (hP : 3 ≤ P) (hQ : P ^ 3 ≤ Q)
    (hW : (Q - 2) ^ 2 ≤ (e - 1) ^ 2 * Q) : False := by
  have hQpos : 0 ≤ Q := by nlinarith
  have hcube : (2 * P - 3) ^ 2 ≤ P ^ 3 - 4 := by
    have h1 : 0 ≤ P ^ 2 - P + 9 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) h1]
  have hE : (e - 1) ^ 2 ≤ (2 * P - 3) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have s1 := mul_le_mul_of_nonneg_right hE hQpos
  have s2 := mul_le_mul_of_nonneg_right hcube hQpos
  have s3 : (P ^ 3 - 4) * Q ≤ (Q - 4) * Q := mul_le_mul_of_nonneg_right (by linarith) hQpos
  have : (Q - 2) ^ 2 = (Q - 4) * Q + 4 := by ring
  linarith

/-- **Endgame `j ≠ 0`**: `ψ(x) = c x^{p^j}` on the squares (`0 < j < k`) is impossible.  By (B),
`χ(1 - c y^e) = -1` for all `y ≠ 0`, `e = gcd(2(p^j - 1), q - 1)`, so `∑_y χ(1 - c y^e) = 2 - q`;
Weil gives `(q-2)² ≤ (e-1)² q` with `e ≤ 2(p^g - 1)`, `p^{3g} ≤ q` — a contradiction for every `q`. -/
theorem endgame_frob {p k : ℕ} [hp : Fact p.Prime] (hq : Fintype.card F = p ^ k)
    (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (hk : 3 ≤ k) (hW : WeilHyp F)
    {ψ : F → F} (h : Admissible ψ) (hA : CondA ψ) {j : ℕ} (hj0 : 0 < j) (hjk : j < k)
    (hpow : ∀ x : F, x ^ n = 1 → ψ x = ψ 1 * x ^ (p ^ j)) : False := by
  have hn : 0 < n := hodd.pos
  have hp2 := hp.out.two_le
  have hp3 : 3 ≤ p := by
    by_contra hlt
    have : p = 2 := by omega
    subst this
    have : 2 ∣ Fintype.card F := by rw [hq]; exact dvd_pow_self 2 (by omega)
    omega
  have hpk : p ^ k = 2 * n + 1 := by rw [← hq, hpn]
  have hn1 : 1 < n := by
    have : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    have : 27 ≤ p ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
    omega
  obtain ⟨c, hc⟩ : ∃ c, c = ψ 1 := ⟨_, rfl⟩
  have hcχ : quadraticChar F c = -1 := by rw [hc, h.swap 1 one_ne_zero, map_one]
  have hc0 : c ≠ 0 := by rw [hc]; exact h.ne_zero 1 one_ne_zero
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = p ^ j := ⟨_, rfl⟩
  have hσn : σ < n := by rw [hσ]; exact BSW.LemmaL.pow_lt_h (h := n) hp3 (by omega) hpk hn1 hjk
  have hσ3 : 3 ≤ σ := le_trans hp3 (by rw [hσ]; exact Nat.le_self_pow (by omega) p)
  -- (B) on the squares
  have hB : ∀ x : F, x ^ n = 1 → quadraticChar F (1 - c * x ^ (σ - 1)) = -1 := by
    intro x hx
    have hx0 : x ≠ 0 := pow_ne_zero_of hn one_ne_zero hx
    have e := BSW.Jacobi.autocorr_B hpn hodd h hA hx0
    rw [hpow x hx, ← hc, ← hσ] at e
    have : x * (x - c * x ^ σ) = x ^ 2 * (1 - c * x ^ (σ - 1)) := by
      obtain ⟨t, ht⟩ : ∃ t, σ = t + 1 := ⟨σ - 1, by omega⟩
      rw [ht, Nat.add_sub_cancel, pow_succ]; ring
    rw [this, chi_sq_mul hx0] at e
    exact e
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * (σ - 1) := ⟨_, rfl⟩
  have hy : ∀ y : F, y ≠ 0 → quadraticChar F (1 - c * y ^ m) = -1 := by
    intro y hy0
    have hx : (y ^ 2) ^ n = 1 := by rw [← pow_mul]; exact BSW.FB.pow_card_sub_one hpn hy0
    have := hB (y ^ 2) hx
    rwa [← pow_mul, ← hm] at this
  obtain ⟨e, he⟩ : ∃ e, e = Nat.gcd m (2 * n) := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have he0 : 0 < e := by rw [he]; exact Nat.gcd_pos_of_pos_left _ hm0
  have hem : e ≤ m := by rw [he]; exact Nat.le_of_dvd hm0 (Nat.gcd_dvd_left _ _)
  have he2n : e < 2 * n := by omega
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_gcd (k := 2 * n) (n := m) (by rw [← he]; exact he2n)
  have hye : ∀ y : F, y ≠ 0 → quadraticChar F (1 - c * y ^ e) = -1 := by
    intro y hy0
    have h2n := BSW.FB.pow_card_sub_one hpn hy0
    have : y ^ e = (y ^ u) ^ m := by
      rw [← pow_mul, mul_comm u m, ← Nat.div_add_mod (m * u) (2 * n), hu, ← he, pow_add, pow_mul,
        h2n, one_pow, one_mul]
    rw [this]; exact hy _ (pow_ne_zero _ hy0)
  have hsum : ∑ y : F, quadraticChar F (1 - c * y ^ e) = 1 - 2 * n := by
    rw [← add_sum_erase _ _ (mem_univ (0 : F)), zero_pow he0.ne', mul_zero, sub_zero, map_one,
      sum_congr rfl (fun y hy => hye y (mem_erase.mp hy).1), sum_const, card_erase_of_mem (mem_univ _),
      card_univ, hpn]
    simp; ring
  -- Weil for `X^e - c⁻¹`
  have heF : ((e : ℕ) : F) ≠ 0 := by
    intro h0
    have hq0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    obtain ⟨r, hr⟩ : e ∣ 2 * n := by rw [he]; exact Nat.gcd_dvd_right m (2 * n)
    rw [hpn] at hq0
    have h2 : ((2 * n : ℕ) : F) = 0 := by rw [hr]; push_cast; rw [h0]; ring
    have h1 : ((2 * n + 1 : ℕ) : F) = 1 := by push_cast at h2 ⊢; rw [h2]; ring
    rw [h1] at hq0; exact one_ne_zero hq0
  have hsep : Squarefree (Polynomial.X ^ e - Polynomial.C c⁻¹ : Polynomial F) :=
    (Polynomial.separable_X_pow_sub_C c⁻¹ heF (inv_ne_zero hc0)).squarefree
  have hdeg : (Polynomial.X ^ e - Polynomial.C c⁻¹ : Polynomial F).natDegree = e :=
    Polynomial.natDegree_X_pow_sub_C
  have hWe := hW _ (by rw [hdeg]; exact he0) hsep
  rw [hdeg] at hWe
  have hev : ∀ y : F, quadraticChar F (Polynomial.eval y (Polynomial.X ^ e - Polynomial.C c⁻¹)) =
      quadraticChar F (-c⁻¹) * quadraticChar F (1 - c * y ^ e) := by
    intro y
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [← map_mul]; congr 1; field_simp; ring
  have hsq : quadraticChar F (-c⁻¹) ^ 2 = 1 := by
    rw [sq]; exact chi_sq_one (neg_ne_zero.mpr (inv_ne_zero hc0))
  rw [sum_congr rfl (fun y _ => hev y), ← mul_sum, hsum, hpn, mul_pow, hsq, one_mul] at hWe
  -- `e ≤ 2(p^g - 1)`, `p^{3g} ≤ q`
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd j k := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left _ hj0
  have hP : Nat.gcd (σ - 1) (2 * n) = p ^ g - 1 := by
    rw [show 2 * n = p ^ k - 1 by omega, hσ, Nat.pow_sub_one_gcd_pow_sub_one, hg]
  have hedvd : e ∣ 2 * (p ^ g - 1) := by
    rw [← hP, ← Nat.gcd_mul_left, he, hm]
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 2)
  have hPge : 3 ≤ p ^ g := le_trans hp3 (Nat.le_self_pow (by omega) p)
  have he_le : e ≤ 2 * (p ^ g - 1) := Nat.le_of_dvd (by omega) hedvd
  have h3g : 3 * g ≤ k := by rw [hg]; exact three_gcd_le hj0 hjk (k_odd hq hpn hodd)
  have hP3 : (p ^ g) ^ 3 ≤ 2 * n + 1 := by
    rw [← pow_mul, ← hpk]; exact Nat.pow_le_pow_right (by omega) (by omega)
  apply final_ineq (Q := 2 * n + 1) (e := e) (P := ((p ^ g : ℕ) : ℤ))
  · exact_mod_cast he0
  · have : (e : ℤ) ≤ ((2 * (p ^ g - 1) : ℕ) : ℤ) := by exact_mod_cast he_le
    push_cast [Nat.cast_sub (show 1 ≤ p ^ g by omega)] at this ⊢; linarith
  · exact_mod_cast hPge
  · exact_mod_cast hP3
  · push_cast at hWe ⊢
    have : ((1 : ℤ) - 2 * n) ^ 2 = (2 * n + 1 - 2) ^ 2 := by ring
    linarith

/-- **Theorem 7.5 for prime powers (`q = p^k ≡ 3 mod 4`, `k ≥ 3`)** in the frame `P₀`, modulo `StickelPKHyp` and
`WeilHyp`: no admissible `ψ` is arc-like. -/
theorem vdv_q3_pk_frame {p k : ℕ} [hp : Fact p.Prime] (hq : Fintype.card F = p ^ k)
    (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (hk : 3 ≤ k) (hst : StickelPKHyp F p k)
    (hW : WeilHyp F) {ψ : F → F} (h : Admissible ψ) : ¬ ArcLike ψ := by
  intro harc
  have hp2 := hp.out.two_le
  have hq27 : 27 ≤ Fintype.card F := by
    have hp3 : 3 ≤ p := by
      by_contra hlt
      have : p = 2 := by omega
      subst this
      have : 2 ∣ Fintype.card F := by rw [hq]; exact dvd_pow_self 2 (by omega)
      omega
    rw [hq]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  have hn3 : 3 ≤ n := by omega
  have hA : CondA ψ := fun y z hy hz hzy hzψ => arc_A hpn hodd hn3 h harc hy hz hzy hzψ
  obtain ⟨j, hj, hpow⟩ := psi_power hq hpn hodd hk hst h hA
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact endgame_lin hpn hodd hq27 hW h (fun x hx => by rw [hpow x hx, pow_zero, pow_one])
  · exact endgame_frob hq hpn hodd hk hW h hA hj0 hj hpow

/-- **Theorem 7.5 (prime powers) for an arbitrary solution on `PG(1,q)`**, `q = p^k ≡ 3 (mod 4)`, `k ≥ 3`. -/
theorem vdv_q3_pk {p k : ℕ} [hp : Fact p.Prime] (hq : Fintype.card F = p ^ k)
    (hpn : Fintype.card F = 2 * n + 1) (hodd : Odd n) (hk : 3 ≤ k) (hst : StickelPKHyp F p k)
    (hW : WeilHyp F) {Ψ : Option F → Option F} (hS : Solution Ψ) : ¬ ArcLikeP Ψ := by
  intro harc
  obtain ⟨M, -, h0⟩ := normalize_pair hS none
  have hS' := hS.conj M
  exact vdv_q3_pk_frame hq hpn hodd hk hst hW (admissible_of_solution hS' h0)
    (arcLike_of_arcLikeP hS' h0 (arcLikeP_conj harc M))

end Q3

/-! ## Van de Voorde's conjecture for all prime powers `q = p^k`, `k ≥ 2` -/

/-- **Van de Voorde's conjecture for `q = p^k`, `p` odd, `k ≥ 2`**: no solution on `PG(1,q)` is
arc-like, i.e. every complete exterior set of `(q+1)/2` points contains three collinear points.
Assumed: McConnel's theorem if `q ≡ 1 (mod 4)`; Proposition 6.2 and Weil's bound if `q ≡ 3 (mod 4)`.
(Primes: `BSW.BSW1.vdv_prime`.) -/
theorem vdv_pk {F : Type*} [Field F] [Fintype F] [DecidableEq F] {p k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hq : Fintype.card F = p ^ k) (hk2 : 2 ≤ k)
    (hmc : Fintype.card F % 4 = 1 → McConnelHyp F p k)
    (hst : Fintype.card F % 4 = 3 → StickelPKHyp F p k ∧ WeilHyp F)
    {Ψ : Option F → Option F} (hS : Solution Ψ) : ¬ ArcLikeP Ψ := by
  have hpodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have hcodd : Fintype.card F % 2 = 1 := by
    rw [hq, Nat.pow_mod, hpodd, one_pow]; rfl
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hq9 : 9 ≤ Fintype.card F := by
    rw [hq]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk2
  obtain ⟨n, hpn⟩ : ∃ n, Fintype.card F = 2 * n + 1 := ⟨Fintype.card F / 2, by omega⟩
  have h4 : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  rcases h4 with h1 | h3
  · exact vdv_q1 hq hpn ⟨n / 2, by omega⟩ (by omega) (hmc h1) hS
  · have hodd : Odd n := ⟨n / 2, by omega⟩
    have hkodd := k_odd hq hpn hodd
    have hk3 : 3 ≤ k := by obtain ⟨t, ht⟩ := hkodd; omega
    exact vdv_q3_pk hq hpn hodd hk3 (hst h3).1 (hst h3).2 hS





end BSW.VdVPK
