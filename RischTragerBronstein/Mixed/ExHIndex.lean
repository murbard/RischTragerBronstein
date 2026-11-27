import RischTragerBronstein.Mixed.ExHStar0
import RischTragerBronstein.Mixed.ExHMult

/-!
# The points of non-singular reduction have finite index (minimal models)

**`local_index`**: for `y² = x³ + a x + b` over a field with a valuation `V` of residue
characteristic `0`, with `a`, `b` integral, `Δ = 4a³ + 27b² ≠ 0` and the model minimal
(not both `a ∈ 𝔭⁴` and `b ∈ 𝔭⁶`), every point `P` has a multiple `m • P` of non-singular
reduction with `0 < m ≤ 2 v(Δ) + 14`.

The proof is the case distinction by reduction type (good, multiplicative, additive
II, III, IV, I₀*/Iₙ*, IV*, III*, II*) of the files `ExHAdd`, `ExHStar`, `ExHStar0`, `ExHMult`;
no Néron models, no Tate curve, no completions.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {V : LVal K} {a b : K}

/-- One class: any two singular points related gives a multiple `m ≤ 4`. -/
lemma index_one (ha : Dv V 0 a) (hb : Dv V 0 b)
    (hpair : ∀ P Q, Sing V a b P → Sing V a b Q →
      (Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb)) (P : (shortF a b).toAffine.Point) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 4 ∧ m • P ∈ E0 V a b ha hb := by
  obtain ⟨m, h1, h2, h3⟩ := index_of_pair ha hb 1 (fun _ ↦ 0) (fun _ ↦ by norm_num)
    (fun P Q hP hQ _ ↦ hpair P Q hP hQ) P
  exact ⟨m, h1, by omega, h3⟩

/-- No singular points: `m = 1`. -/
lemma index_none (ha : Dv V 0 a) (hb : Dv V 0 b) (h : ∀ P, ¬Sing V a b P)
    (P : (shortF a b).toAffine.Point) : ∃ m : ℕ, 0 < m ∧ m ≤ 1 ∧ m • P ∈ E0 V a b ha hb :=
  ⟨1, by norm_num, le_rfl, by rw [one_nsmul]; exact h P⟩

/-- **Finite index of the points of non-singular reduction.** -/
theorem local_index (ha : Dv V 0 a) (hb : Dv V 0 b) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hmin : ¬(Dv V 4 a ∧ Dv V 6 b)) (P : (shortF a b).toAffine.Point) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2 * (V.v (4 * a ^ 3 + 27 * b ^ 2)).toNat + 14 ∧
      m • P ∈ E0 V a b ha hb := by
  have hD0 : Dv V 0 (4 * a ^ 3 + 27 * b ^ 2) := by dvt [ha, hb]
  have wk : ∀ M : ℕ, M ≤ 14 → (∃ m : ℕ, 0 < m ∧ m ≤ M ∧ m • P ∈ E0 V a b ha hb) →
      ∃ m : ℕ, 0 < m ∧ m ≤ 2 * (V.v (4 * a ^ 3 + 27 * b ^ 2)).toNat + 14 ∧
        m • P ∈ E0 V a b ha hb := fun M hM ⟨m, h1, h2, h3⟩ ↦ ⟨m, h1, by omega, h3⟩
  by_cases hD : Dv V 1 (4 * a ^ 3 + 27 * b ^ 2)
  swap
  · -- good reduction
    exact wk 1 (by norm_num) (index_none ha hb
      (no_sing_good ha hb (ex_of_dv_not hD0 hD (by norm_num))) P)
  by_cases ha1 : Dv V 1 a
  swap
  · -- multiplicative reduction
    have hae : Ex V 0 a := ex_of_dv_not ha ha1 (by norm_num)
    have hbe : Ex V 0 b := by
      refine ex_of_dv_not (k' := 1) hb (fun hb1 ↦ ?_) (by norm_num)
      have h4 : Ex V 0 (4 * a ^ 3) := by exq [hae]
      refine h4.not_dv (l := 1) (by norm_num) ?_
      rw [show 4 * a ^ 3 = (4 * a ^ 3 + 27 * b ^ 2) - 27 * b ^ 2 by ring]
      dvt [hD, hb1]
    have hN : Ex V (V.v (4 * a ^ 3 + 27 * b ^ 2)) (4 * a ^ 3 + 27 * b ^ 2) := ⟨hΔ, rfl⟩
    obtain ⟨m, h1, h2, h3⟩ := index_mult ha hb hae hbe hN (dv_of_ne hD hΔ) P
    exact ⟨m, h1, by omega, h3⟩
  -- additive reduction
  have hb1 : Dv V 1 b := by
    have h27 : Dv V (1 + 0) (b ^ 2 * 27) := by
      rw [show b ^ 2 * 27 = (4 * a ^ 3 + 27 * b ^ 2) - 4 * a ^ 3 by ring]
      dvt [hD, ha1]
    have h2 : Dv V 1 (b ^ 2) := dv_of_mul_ex h27 (ex_ofNat V 27)
    exact dv_of_sq (k := 1) ((dv_sq_succ h2 (by norm_num)).mono (by norm_num))
  by_cases hb2 : Dv V 2 b
  swap
  · -- type II
    exact wk 1 (by norm_num) (index_none ha hb
      (no_sing_II ha1 (ex_of_dv_not hb1 hb2 (by norm_num))) P)
  by_cases ha2 : Dv V 2 a
  swap
  · -- type III
    exact wk 4 (by norm_num) (index_one ha hb
      (pair_III ha hb (ex_of_dv_not ha1 ha2 (by norm_num)) hb2) P)
  by_cases hb3 : Dv V 3 b
  swap
  · -- type IV
    exact wk 4 (by norm_num) (index_one ha hb
      (pair_IV ha hb ha2 (ex_of_dv_not hb2 hb3 (by norm_num))) P)
  by_cases h34 : Dv V 3 a ∧ Dv V 4 b
  swap
  · -- types I₀*, Iₙ*
    exact wk 14 (by norm_num) (index_star0 ha hb ha2 hb3 h34 hΔ P)
  obtain ⟨ha3, hb4⟩ := h34
  by_cases hb5 : Dv V 5 b
  swap
  · -- type IV*
    exact wk 4 (by norm_num) (index_one ha hb
      (pair_IVs ha hb ha3 (ex_of_dv_not hb4 hb5 (by norm_num))) P)
  by_cases ha4 : Dv V 4 a
  swap
  · -- type III*
    exact wk 4 (by norm_num) (index_one ha hb
      (pair_IIIs ha hb (ex_of_dv_not ha3 ha4 (by norm_num)) hb5) P)
  -- type II*
  have hb6 : ¬Dv V 6 b := fun h ↦ hmin ⟨ha4, h⟩
  exact wk 1 (by norm_num) (index_none ha hb
    (no_sing_IIs ha4 (ex_of_dv_not hb5 hb6 (by norm_num))) P)

end ExH
