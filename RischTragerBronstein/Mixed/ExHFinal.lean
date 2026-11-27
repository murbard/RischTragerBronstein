import RischTragerBronstein.Mixed.ExHCanon
import RischTragerBronstein.Mixed.EllTwist
import RischTragerBronstein.Mixed.EllIsoClassify
import RischTragerBronstein.Mixed.EllIsoCert
import RischTragerBronstein.Mixed.EllIsoCert1

/-!
# Height certificates exist on every curve over `K(X)` that is not constant up to scaling

* `min_model`: every `y² = x³ + A x + B` (`A, B ∈ K[X]`, `Δ ≠ 0`) is `A = w⁴A′`, `B = w⁶B′` with
  `(A′, B′)` minimal at all finite places.
* `canonH_scale`: the scaling `(x, y) ↦ (x/w², y/w³)` is an injective homomorphism preserving the
  canonical height (naive heights differ by at most `2 deg w`; `MWTate.canon_unique`).
* **`hint_htor`**: if the curve is not constant up to scaling (`¬ConstScale A B`), some `k > 0`
  makes `k · canonH` natural-valued, and `canonH P = 0` only for torsion `P`.
* **`certQ_exists_nc`**, **`certQ1_exists_nc`**: hence the executable height certificates for
  independence of two points, and for infinite order of one point, pass at some level — for
  *every* such curve, in particular for all curves with non-constant `j`. No hypothesis on the
  constant field: this replaces Manin's kernel theorem in the completeness of the Mordell–Weil
  exception of the mixed deciders.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine Filter Topology

namespace ExH

open FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- **Minimal models at the finite places.** -/
theorem min_model : ∀ (d : ℕ) (A B : K[X]), A.natDegree + B.natDegree ≤ d →
    4 * A ^ 3 + 27 * B ^ 2 ≠ 0 →
    ∃ w A' B' : K[X], w ≠ 0 ∧ A = w ^ 4 * A' ∧ B = w ^ 6 * B' ∧
      4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0 ∧ ∀ p : K[X], Irreducible p → ¬(p ^ 4 ∣ A' ∧ p ^ 6 ∣ B') := by
  intro d
  induction d with
  | zero =>
    intro A B hd hΔ
    refine ⟨1, A, B, one_ne_zero, by simp, by simp, hΔ, fun p hp ⟨h4, h6⟩ ↦ ?_⟩
    have hpos := hp.natDegree_pos
    have hA : A = 0 := by
      by_contra hA
      have := natDegree_le_of_dvd h4 hA
      rw [natDegree_pow] at this
      omega
    have hB : B = 0 := by
      by_contra hB
      have := natDegree_le_of_dvd h6 hB
      rw [natDegree_pow] at this
      omega
    exact hΔ (by simp [hA, hB])
  | succ d ih =>
    intro A B hd hΔ
    by_cases hmin : ∀ p : K[X], Irreducible p → ¬(p ^ 4 ∣ A ∧ p ^ 6 ∣ B)
    · exact ⟨1, A, B, one_ne_zero, by simp, by simp, hΔ, hmin⟩
    · push Not at hmin
      obtain ⟨p, hp, ⟨A1, hA1⟩, ⟨B1, hB1⟩⟩ := hmin
      have hpos := hp.natDegree_pos
      have hp0 : p ≠ 0 := hp.ne_zero
      have hΔ1 : 4 * A1 ^ 3 + 27 * B1 ^ 2 ≠ 0 := by
        intro h0
        apply hΔ
        rw [hA1, hB1]
        linear_combination p ^ 12 * h0
      have dA : A1 ≠ 0 → A.natDegree = 4 * p.natDegree + A1.natDegree := fun h ↦ by
        rw [hA1, natDegree_mul (pow_ne_zero 4 hp0) h, natDegree_pow]
      have dB : B1 ≠ 0 → B.natDegree = 6 * p.natDegree + B1.natDegree := fun h ↦ by
        rw [hB1, natDegree_mul (pow_ne_zero 6 hp0) h, natDegree_pow]
      have hdeg : A1.natDegree + B1.natDegree ≤ d := by
        by_cases a0 : A1 = 0
        · by_cases b0 : B1 = 0
          · exact absurd (by simp [a0, b0]) hΔ1
          · have := dB b0
            rw [a0, natDegree_zero]
            omega
        · by_cases b0 : B1 = 0
          · have := dA a0
            rw [b0, natDegree_zero]
            omega
          · have := dA a0
            have := dB b0
            omega
      obtain ⟨w, A', B', hw, eA, eB, hΔ', hm⟩ := ih A1 B1 hdeg hΔ1
      exact ⟨p * w, A', B', mul_ne_zero hp0 hw, by rw [hA1, eA]; ring, by rw [hB1, eB]; ring,
        hΔ', hm⟩

/-- **Scaling to another model preserves the canonical height.** -/
theorem canonH_scale {A B A' B' w : K[X]} (hw : w ≠ 0) (hA : A = w ^ 4 * A')
    (hB : B = w ^ 6 * B') (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0) :
    ∃ φ : (shortW A B).toAffine.Point →+ (shortW A' B').toAffine.Point,
      Function.Injective φ ∧ ∀ P, canonH A' B' (φ P) = canonH A B P := by
  have hιw : ι w ≠ 0 := ι_ne hw
  have ha : ι A' = (ι w)⁻¹ ^ 4 * ι A := by rw [hA, map_mul, map_pow]; field_simp
  have hb : ι B' = (ι w)⁻¹ ^ 6 * ι B := by rw [hB, map_mul, map_pow]; field_simp
  obtain ⟨φ, hφdef⟩ : ∃ φ : (shortW A B).toAffine.Point →+ (shortW A' B').toAffine.Point,
      φ = scaleHomEq (ι A) (ι B) (ι A') (ι B') (ι w)⁻¹ (inv_ne_zero hιw) ha hb := ⟨_, rfl⟩
  refine ⟨φ, by rw [hφdef]; exact scaleHomEq_injective _ _ _ _ _ _ ha hb, fun P ↦ ?_⟩
  have hu2 : ht (((ι w)⁻¹) ^ 2) = 2 * w.natDegree := by
    rw [inv_pow, ht_inv, ← map_pow, ht_ι, natDegree_pow]
  have hu2' : ht ((((ι w)⁻¹) ^ 2)⁻¹) = 2 * w.natDegree := by rw [ht_inv, hu2]
  have hbd : ∀ P : (shortW A B).toAffine.Point,
      |hR A' B' (φ P) - hR A B P| ≤ 2 * (w.natDegree : ℝ) := by
    intro P
    rcases P with _ | ⟨x, y, h⟩
    · have e0 : φ Point.zero = Point.zero := map_zero φ
      rw [e0]
      have e1 : hR A' B' Point.zero = 0 := by simp [hR, hN]
      have e2 : hR A B Point.zero = 0 := by simp [hR, hN]
      rw [e1, e2]
      simp
    · obtain ⟨h', e⟩ := scaleHomEq_some (ι A) (ι B) (ι A') (ι B') (ι w)⁻¹ (inv_ne_zero hιw) ha hb h
      have e' : φ (Point.some x y h) = Point.some _ _ h' := by subst hφdef; exact e
      have e1 : hR A' B' (φ (Point.some x y h)) = ht ((ι w)⁻¹ ^ 2 * x) := by
        rw [e']; rfl
      have e2 : hR A B (Point.some x y h) = ht x := rfl
      rw [e1, e2]
      have l1 := ht_mul_le ((ι w)⁻¹ ^ 2) x
      have l2 := ht_mul_le (((ι w)⁻¹ ^ 2)⁻¹) ((ι w)⁻¹ ^ 2 * x)
      rw [inv_mul_cancel_left₀ (pow_ne_zero 2 (inv_ne_zero hιw))] at l2
      rw [hu2] at l1
      rw [hu2'] at l2
      have l1' : (ht ((ι w)⁻¹ ^ 2 * x) : ℝ) ≤ 2 * w.natDegree + ht x := by exact_mod_cast l1
      have l2' : (ht x : ℝ) ≤ 2 * w.natDegree + ht ((ι w)⁻¹ ^ 2 * x) := by exact_mod_cast l2
      rw [abs_le]
      constructor <;> linarith
  have hC := hR_double A B hΔ
  have hC' := hR_double A' B' hΔ'
  refine MWTate.canon_unique hC (fun P ↦ canonH A' B' (φ P))
    (11 * (max A'.natDegree B'.natDegree : ℕ) / 3 + 2 * (w.natDegree : ℝ)) (fun P ↦ ?_)
    (fun P ↦ ?_) P
  · show canonH A' B' (φ (MWPair.dbl P)) = 4 * canonH A' B' (φ P)
    have e : φ (MWPair.dbl P) = MWPair.dbl (φ P) := map_add φ P P
    rw [e]
    exact MWTate.canon_double hC' (φ P)
  · have c1 := canonH_close A' B' hΔ' (φ P)
    have c2 := hbd P
    have e : canonH A' B' (φ P) - hR A B P =
        (canonH A' B' (φ P) - hR A' B' (φ P)) + (hR A' B' (φ P) - hR A B P) := by ring
    show |canonH A' B' (φ P) - hR A B P| ≤ _
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add c1 c2)

/-- **Integrality and positivity of the canonical height**, for every curve over `K(X)` that is
not constant up to scaling. -/
theorem hint_htor {A B : K[X]} (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hcs : ¬ConstScale A B) :
    ∃ k : ℕ, 0 < k ∧
      (∀ P : (shortW A B).toAffine.Point, ∃ z : ℕ, (k : ℝ) * canonH A B P = z) ∧
      (∀ P : (shortW A B).toAffine.Point, canonH A B P = 0 → ∃ m : ℕ, 0 < m ∧ m • P = 0) := by
  obtain ⟨w, A', B', hw, hA, hB, hΔ', hmin⟩ := min_model _ A B le_rfl hΔ
  have hn : 1 ≤ nInf A' B' := by
    by_contra h0
    have h0' : nInf A' B' = 0 := by omega
    apply hcs
    have dA := degA_le A' B'
    have dB := degB_le A' B'
    rw [h0'] at dA dB
    refine ⟨ι w, A'.coeff 0, B'.coeff 0, ι_ne hw, ?_, ?_⟩
    · rw [hA, map_mul, map_pow]
      congr 1
      conv_lhs => rw [eq_C_of_natDegree_eq_zero (by omega : A'.natDegree = 0)]
      simp [RatFunc.algebraMap_eq_C]
    · rw [hB, map_mul, map_pow]
      congr 1
      conv_lhs => rw [eq_C_of_natDegree_eq_zero (by omega : B'.natDegree = 0)]
      simp [RatFunc.algebraMap_eq_C]
  obtain ⟨k, hk, hint, htor⟩ := hint_htor_min hΔ' hmin hn
  obtain ⟨φ, hφ, hcan⟩ := canonH_scale hw hA hB hΔ hΔ'
  refine ⟨k, hk, fun P ↦ ?_, fun P hP ↦ ?_⟩
  · rw [← hcan]; exact hint (φ P)
  · obtain ⟨m, hm, hm0⟩ := htor (φ P) (by rw [hcan]; exact hP)
    exact ⟨m, hm, hφ (by rw [map_nsmul, hm0, map_zero])⟩

/-- **Positivity of the canonical height at points of infinite order.** -/
theorem canonH_pos_nc (A B : K[X]) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hcs : ¬ConstScale A B)
    (P : (shortW A B).toAffine.Point) (hP : ∀ n : ℤ, n • P = 0 → n = 0) : 0 < canonH A B P := by
  obtain ⟨k, hk, hint, htor⟩ := hint_htor hΔ' hcs
  obtain ⟨z, hz⟩ := hint P
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h0 : 0 ≤ canonH A B P := by
    have h1 : (0 : ℝ) ≤ k * canonH A B P := by rw [hz]; positivity
    exact nonneg_of_mul_nonneg_right h1 hk'
  rcases h0.lt_or_eq with h | h
  · exact h
  · obtain ⟨n, hn, hnP⟩ := htor P h.symm
    have := hP n (by rw [natCast_zsmul]; exact hnP)
    omega

variable [DecidableEq K]

/-- **The two-point height certificate exists** on every curve not constant up to scaling. -/
theorem certQ_exists_nc (Ac : CPoly K) (A B : K[X]) (hAc : CPoly.toPoly Ac = A)
    (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hcs : ¬ConstScale A B)
    (oP oQ : PtC K) (P Q : (shortW A B).toAffine.Point) (hP : Rel A B oP P) (hQ : Rel A B oQ Q)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k, certQ Ac (max A.natDegree B.natDegree) k oP oQ = true := by
  obtain ⟨k, hk, hint, htor⟩ := hint_htor hΔ' hcs
  obtain ⟨k', hk'⟩ := hgap_exists_gen hΔ' k hk hint htor P Q hind
  exact ⟨k', certQ_of_hgap Ac A B hAc k' oP oQ P Q hP hQ hk'⟩

/-- **The one-point height certificate exists** on every curve not constant up to scaling. -/
theorem certQ1_exists_nc (Ac : CPoly K) (A B : K[X]) (hAc : CPoly.toPoly Ac = A)
    (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hcs : ¬ConstScale A B) (oP : PtC K)
    (P : (shortW A B).toAffine.Point) (hRel : Rel A B oP P) (hP : ∀ n : ℤ, n • P = 0 → n = 0) :
    ∃ k, certQ1 Ac (max A.natDegree B.natDegree) k oP = true := by
  have hpos := canonH_pos_nc A B hΔ' hcs P hP
  set C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
  have tP := MWTate.tendsto_canon (hR_double A B hΔ') P
  have te : Tendsto (fun k : ℕ ↦ C / 3 / 4 ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨k, hk⟩ := (te.eventually_lt tP hpos).exists
  refine ⟨k, ?_⟩
  have e1 := htC_spec A B _ _ (dblC_spec Ac A B hAc k oP P hRel)
  simp only [certQ1, decide_eq_true_eq]
  apply (Rat.cast_lt (K := ℝ)).mp
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
  have : (htC (dblC Ac k oP) : ℝ) = hR A B (MWPair.dbl^[k] P) := by simp only [hR, e1]
  rw [this]
  exact hk

end ExH
