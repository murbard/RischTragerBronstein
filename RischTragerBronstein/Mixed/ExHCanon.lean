import RischTragerBronstein.Mixed.ExHDouble
import RischTragerBronstein.Mixed.EllIsoGram

/-!
# The canonical height on minimal models over `K(X)` is integral and positive

On points of everywhere non-singular reduction (`E0g A B`) the weighted height
`sP n P = max (deg num x) (deg den x + 2n)` quadruples exactly under doubling (`sH_double`), and it
differs from the naive height by at most `2n`. Hence on `E0g A B`, off the `2`-power torsion,
`canonH = sP` (**`canonH_eq_sP`**): a natural number, at least `2n`.

**`hint_htor_min`**: for a model minimal at all finite places with `n = nInf A B ≥ 1` (not both
`A`, `B` constant), some `k > 0` makes `k · canonH` natural-valued, and `canonH P = 0` only for
torsion points — without any hypothesis on the constant field, and without Manin's kernel
theorem or the Lang–Néron theorem.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine Filter Topology

namespace ExH

open FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

variable (A B : K[X])

/-- The weighted height of a point. -/
noncomputable def sP (n : ℕ) : (shortF (ι A) (ι B)).toAffine.Point → ℕ
  | .zero => 0
  | .some x _ _ => sH n x

lemma hN_le_sP (n : ℕ) (P : (shortF (ι A) (ι B)).toAffine.Point) :
    hN A B P ≤ sP A B n P ∧ (P ≠ 0 → sP A B n P ≤ hN A B P + 2 * n ∧ 2 * n ≤ sP A B n P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨le_refl _, fun h ↦ absurd rfl h⟩
  · show max x.num.natDegree x.denom.natDegree ≤ max x.num.natDegree (x.denom.natDegree + 2 * n) ∧
      (_ → max x.num.natDegree (x.denom.natDegree + 2 * n) ≤
        max x.num.natDegree x.denom.natDegree + 2 * n ∧
        2 * n ≤ max x.num.natDegree (x.denom.natDegree + 2 * n))
    exact ⟨by omega, fun _ ↦ ⟨by omega, by omega⟩⟩

lemma mem_E0g_iff (P : (shortF (ι A) (ι B)).toAffine.Point) :
    P ∈ E0g A B ↔ (∀ (p : K[X]) (hp : Irreducible p), ¬Sing (Vp p hp) (ι A) (ι B) P) ∧
      ¬Sing Vinf (uInf (nInf A B) ^ 4 * ι A) (uInf (nInf A B) ^ 6 * ι B)
        (scaleHom (ι A) (ι B) (uInf (nInf A B)) (uInf_ne _) P) := by
  unfold E0g
  rw [AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp ↦ h1 ⟨p, hp⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p ↦ h1 p.1 p.2, h2⟩

/-- Doubling on `E0g`. -/
lemma dbl_E0g {P : (shortF (ι A) (ι B)).toAffine.Point} (hP : P ∈ E0g A B) (hP0 : P ≠ 0) :
    MWPair.dbl P = 0 ∨ (MWPair.dbl P ≠ 0 ∧
      sP A B (nInf A B) (MWPair.dbl P) = 4 * sP A B (nInf A B) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP0
  obtain ⟨hfin, hinf⟩ := (mem_E0g_iff A B _).mp hP
  by_cases hy : y = 0
  · left
    unfold MWPair.dbl
    exact Point.add_self_of_Y_eq (by rw [negY_shortF, hy, neg_zero])
  · right
    obtain ⟨x2, y2, h2, hadd, hs⟩ := sH_double A B h hy hfin hinf
    unfold MWPair.dbl
    rw [hadd]
    exact ⟨Point.some_ne_zero h2, hs⟩

/-- Iterated doubling on `E0g`. -/
lemma iter_E0g {P : (shortF (ι A) (ι B)).toAffine.Point} (hP : P ∈ E0g A B) (k : ℕ) :
    (∃ j, MWPair.dbl^[j] P = 0) ∨ (MWPair.dbl^[k] P ≠ 0 ∧
      sP A B (nInf A B) (MWPair.dbl^[k] P) = 4 ^ k * sP A B (nInf A B) P) := by
  induction k with
  | zero =>
    by_cases h0 : P = 0
    · exact Or.inl ⟨0, h0⟩
    · exact Or.inr ⟨h0, by simp⟩
  | succ k ih =>
    rcases ih with h | ⟨h1, h2⟩
    · exact Or.inl h
    · have hmem : MWPair.dbl^[k] P ∈ E0g A B := by
        rw [MWPair.dbl_iter]; exact (E0g A B).nsmul_mem hP _
      rcases dbl_E0g A B hmem h1 with h | ⟨h3, h4⟩
      · left
        exact ⟨k + 1, by rw [Function.iterate_succ_apply']; exact h⟩
      · right
        rw [Function.iterate_succ_apply']
        exact ⟨h3, by rw [h4, h2, pow_succ]; ring⟩

variable {A B}

/-- **The canonical height on points of everywhere non-singular reduction.** -/
theorem canonH_eq_sP (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    {P : (shortF (ι A) (ι B)).toAffine.Point} (hP : P ∈ E0g A B)
    (hnt : ∀ j, MWPair.dbl^[j] P ≠ 0) : canonH A B P = sP A B (nInf A B) P := by
  have hC := hR_double A B hΔ
  have t1 := MWTate.tendsto_canon hC P
  have hk : ∀ k, (sP A B (nInf A B) P : ℝ) - 2 * (nInf A B : ℝ) / 4 ^ k ≤
      MWTate.seq MWPair.dbl (hR A B) P k ∧
      MWTate.seq MWPair.dbl (hR A B) P k ≤ sP A B (nInf A B) P := by
    intro k
    rcases iter_E0g A B hP k with ⟨j, hj⟩ | ⟨h1, h2⟩
    · exact absurd hj (hnt j)
    obtain ⟨l1, l2⟩ := hN_le_sP A B (nInf A B) (MWPair.dbl^[k] P)
    obtain ⟨l3, -⟩ := l2 h1
    rw [h2] at l1 l3
    have h4 : (0 : ℝ) < 4 ^ k := by positivity
    have e1 : ((hN A B (MWPair.dbl^[k] P) : ℕ) : ℝ) ≤ 4 ^ k * sP A B (nInf A B) P := by
      exact_mod_cast l1
    have e2 : (4 : ℝ) ^ k * sP A B (nInf A B) P ≤ hN A B (MWPair.dbl^[k] P) + 2 * nInf A B := by
      exact_mod_cast l3
    have e3 : MWTate.seq MWPair.dbl (hR A B) P k = (hN A B (MWPair.dbl^[k] P) : ℝ) / 4 ^ k := rfl
    rw [e3]
    constructor
    · rw [le_div_iff₀ h4]
      have : ((sP A B (nInf A B) P : ℝ) - 2 * (nInf A B : ℝ) / 4 ^ k) * 4 ^ k =
          4 ^ k * sP A B (nInf A B) P - 2 * nInf A B := by
        field_simp
      linarith
    · rw [div_le_iff₀ h4]
      linarith
  have t2 : Tendsto (fun k : ℕ ↦ (sP A B (nInf A B) P : ℝ) - 2 * (nInf A B : ℝ) / 4 ^ k) atTop
      (𝓝 (sP A B (nInf A B) P)) := by
    have h0 : Tendsto (fun k : ℕ ↦ 2 * (nInf A B : ℝ) / 4 ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    simpa using (tendsto_const_nhds (x := (sP A B (nInf A B) P : ℝ))).sub h0
  have t3 := tendsto_of_tendsto_of_tendsto_of_le_of_le t2 tendsto_const_nhds
    (fun k ↦ (hk k).1) (fun k ↦ (hk k).2)
  exact tendsto_nhds_unique t1 t3

/-- **Integrality and positivity of the canonical height on minimal non-constant models.** -/
theorem hint_htor_min (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hmin : ∀ p : K[X], Irreducible p → ¬(p ^ 4 ∣ A ∧ p ^ 6 ∣ B)) (hn : 1 ≤ nInf A B) :
    ∃ k : ℕ, 0 < k ∧
      (∀ P : (shortW A B).toAffine.Point, ∃ z : ℕ, (k : ℝ) * canonH A B P = z) ∧
      (∀ P : (shortW A B).toAffine.Point, canonH A B P = 0 → ∃ m : ℕ, 0 < m ∧ m • P = 0) := by
  obtain ⟨N, hN, hmem⟩ := exists_exponent hΔ hmin
  have h0 : canonH A B 0 = 0 := by
    have := canonH_quad hΔ 0 0 0 0
    simpa using this
  have hsm : ∀ (m : ℕ) (P : (shortW A B).toAffine.Point),
      canonH A B (m • P) = (m : ℝ) ^ 2 * canonH A B P := by
    intro m P
    have := canonH_quad hΔ P 0 m 0
    simpa [h0] using this
  have key : ∀ P : (shortW A B).toAffine.Point, (∃ j : ℕ, 0 < j ∧ j • P = 0) ∨
      (∃ z : ℕ, 0 < z ∧ canonH A B (N • P) = z) := by
    intro P
    by_cases hj : ∃ j, MWPair.dbl^[j] (N • P) = 0
    · obtain ⟨j, hj⟩ := hj
      left
      refine ⟨N * 2 ^ j, by positivity, ?_⟩
      rw [mul_nsmul, ← MWPair.dbl_iter]
      exact hj
    · right
      push Not at hj
      have hQ : N • P ∈ E0g A B := hmem P
      refine ⟨sP A B (nInf A B) (N • P), ?_, canonH_eq_sP hΔ hQ hj⟩
      have := ((hN_le_sP A B (nInf A B) (N • P)).2 (hj 0)).2
      omega
  refine ⟨N ^ 2, by positivity, fun P ↦ ?_, fun P hP0 ↦ ?_⟩
  · rcases key P with ⟨j, hj, hj0⟩ | ⟨z, -, hz⟩
    · refine ⟨0, ?_⟩
      have h1 := hsm j P
      rw [hj0, h0] at h1
      have hj' : (j : ℝ) ^ 2 ≠ 0 := by positivity
      have hc : canonH A B P = 0 := (mul_eq_zero.mp h1.symm).resolve_left hj'
      simp [hc]
    · exact ⟨z, by rw [← hz, hsm]; push_cast; ring⟩
  · rcases key P with h | ⟨z, hz0, hz⟩
    · exact h
    · exfalso
      rw [hsm, hP0, mul_zero] at hz
      have hz' : (z : ℝ) = 0 := hz.symm
      have : z = 0 := by exact_mod_cast hz'
      omega

end ExH
