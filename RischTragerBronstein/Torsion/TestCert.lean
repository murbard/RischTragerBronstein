import RischTragerBronstein.Torsion.CertBranches

/-!
# Certificates for the principality test

The columns of `princTest` at an unramified point `a` with `D(a) ≠ 0`, along a certified branch
`Y ≡ yt (mod T^prec)`, are computable: `basisSer_trunc` identifies `B(a + T, Y)/D(a + T)` modulo
`T^prec` with `serTrunc`.
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries GTors CPoly Sup

section Trunc

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

lemma branchSub_one_map (ψ : F →+* K) (a : F) (P : CPoly F) :
    branchSub (C := K) (K := K) 1 (ψ a) ((toPoly P).map ψ) =
      HahnSeries.ofPowerSeries ℤ K (thetaT ψ (toPoly (compC P (shiftC a 1)))) := by
  rw [branchSub_apply, toPoly_compC, toPoly_shiftC, thetaT_apply, Polynomial.map_comp,
    Algebra.algebraMap_self, Polynomial.map_id]
  simp

lemma branchSub_one_mapB (ψ : F →+* K) (a : F) (B : BPoly F) (Y : PowerSeries K) :
    (((toB B).map (mapRingHom ψ)).map (branchSub (C := K) (K := K) 1 (ψ a))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) =
      HahnSeries.ofPowerSeries ℤ K (((toB B).map (thetaN ψ a 1)).eval Y) := by
  have e : ((toB B).map (mapRingHom ψ)).map (branchSub (C := K) (K := K) 1 (ψ a)) =
      ((toB B).map (thetaN ψ a 1)).map (HahnSeries.ofPowerSeries ℤ K) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun P ↦ ?_
    have := ofPS_thetaN (K := K) ψ a 1 P
    rw [Algebra.algebraMap_self, RingHom.id_comp] at this
    rw [RingHom.comp_apply, RingHom.comp_apply, this]
    rfl
  rw [e, eval_map, eval₂_at_apply]

/-- **The basis series modulo `T^prec`.** -/
theorem basisSer_trunc (ψ : F →+* K) (B : BPoly F) (Dc : CPoly F) (a : F)
    (hμ0 : muD Dc a 1 = 0) (hμ : muD Dc a 1 < (compC Dc (shiftC a 1)).length)
    (Y : PowerSeries K) (yt : CPoly F) (prec : ℕ)
    (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ Y - thetaT ψ (toPoly yt)) :
    ∃ V : PowerSeries K,
      (((toB B).map (mapRingHom ψ)).map (branchSub (C := K) (K := K) 1 (ψ a))).eval
          (HahnSeries.ofPowerSeries ℤ K Y) *
        (branchSub (C := K) (K := K) 1 (ψ a) ((toPoly Dc).map ψ))⁻¹ =
        HahnSeries.ofPowerSeries ℤ K V ∧
      (PowerSeries.X : PowerSeries K) ^ prec ∣
        V - thetaT ψ (toPoly (serTrunc B Dc a 1 prec yt)) := by
  set Qa := compC Dc (shiftC a 1) with hQa
  have hU0 : Qa.getD 0 0 ≠ 0 := by
    have := getD_ordC Qa hμ
    unfold muD at hμ0
    rwa [hμ0] at this
  set U' := thetaT ψ (toPoly Qa) with hU'
  have hUc : PowerSeries.constantCoeff U' ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hU', coeff_thetaT]
    exact (map_ne_zero_iff ψ ψ.injective).mpr hU0
  set G := (toB B).map (thetaN ψ a 1) with hG
  have hU'inv : HahnSeries.ofPowerSeries ℤ K U' * HahnSeries.ofPowerSeries ℤ K U'⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel U' hUc, map_one]
  refine ⟨G.eval Y * U'⁻¹, ?_, ?_⟩
  · rw [branchSub_one_mapB, branchSub_one_map, ← hQa, ← hU', ← hG, map_mul]
    congr 1
    exact (eq_inv_of_mul_eq_one_right hU'inv).symm
  · refine X_pow_dvd_of_mul_unit hUc ?_
    have h1 : G.eval Y * U'⁻¹ * U' = G.eval Y := by
      rw [mul_assoc, PowerSeries.inv_mul_cancel U' hUc, mul_one]
    set Wk := bivEval B (shiftC a 1) yt with hWk
    have h2 : (PowerSeries.X : PowerSeries K) ^ prec ∣ G.eval Y - thetaT ψ (toPoly Wk) := by
      rw [hWk, thetaT_bivEval, ← hG]
      exact hy.trans (sub_dvd_eval_sub _ _ _)
    have hst : serTrunc B Dc a 1 prec yt = divTrunc Wk Qa prec := by
      rw [serTrunc, hμ0, List.drop_zero]
    have h3 : (PowerSeries.X : PowerSeries K) ^ prec ∣ thetaT ψ (toPoly Wk) -
        thetaT ψ (toPoly (divTrunc Wk Qa prec)) * U' := by
      rw [hU', ← map_mul]
      rw [PowerSeries.X_pow_dvd_iff]
      intro j hj
      rw [map_sub, coeff_thetaT, thetaT_apply, Polynomial.coeff_coe, coeff_map,
        mul_comm (toPoly (divTrunc Wk Qa prec)), coeff_mul_divTrunc Wk Qa hU0 prec j hj, sub_self]
    have := dvd_add h2 h3
    rw [sub_mul, h1, hst]
    convert this using 1
    ring

/-- The computable column entry: coefficient `t` of `(a + T)^d · Bᵢ(a + T, y)/D(a + T)`. -/
def colC (Bc : List (BPoly F)) (Dc : CPoly F) (a : F) (yt : CPoly F) (prec i d t : ℕ) : F :=
  (mul (compC (xPowC d) (shiftC a 1)) (serTrunc (Bc.getD i []) Dc a 1 prec yt)).getD t 0

/-- **Columns of the test from certificates.** -/
theorem coeff_basisSer_cert (ψ : F →+* K) {n : ℕ} (Bc : List (BPoly F)) (Dc : CPoly F) (a : F)
    (hμ0 : muD Dc a 1 = 0) (hμ : muD Dc a 1 < (compC Dc (shiftC a 1)).length)
    (Y : PowerSeries K) (yt : CPoly F) (prec : ℕ)
    (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ Y - thetaT ψ (toPoly yt))
    (i : Fin n) (d t : ℕ) (ht : t < prec) :
    (branchSub (C := K) (K := K) 1 (ψ a) (X ^ d) *
      basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ)) ((toPoly Dc).map ψ) 1 (ψ a)
        (HahnSeries.ofPowerSeries ℤ K Y) i).coeff (t : ℤ) = ψ (colC Bc Dc a yt prec i d t) := by
  obtain ⟨V, hV, hVt⟩ := basisSer_trunc ψ (Bc.getD i []) Dc a hμ0 hμ Y yt prec hy
  have hX : (X ^ d : K[X]) = (toPoly (xPowC d : CPoly F)).map ψ := by
    rw [toPoly_xPowC, Polynomial.map_pow, map_X]
  rw [basisSer, hV, hX, branchSub_one_map, ← map_mul, coeff_ofPS, if_pos (by omega),
    Int.toNat_natCast]
  set A := thetaT ψ (toPoly (compC (xPowC d) (shiftC a 1))) with hA
  have h1 : (PowerSeries.X : PowerSeries K) ^ prec ∣ A * V -
      thetaT ψ (toPoly (mul (compC (xPowC d) (shiftC a 1))
        (serTrunc (Bc.getD i []) Dc a 1 prec yt))) := by
    rw [toPoly_mul, map_mul, ← hA, ← mul_sub]
    exact Dvd.dvd.mul_left hVt _
  have h2 := (PowerSeries.X_pow_dvd_iff.mp h1) t ht
  rw [map_sub, coeff_thetaT, sub_eq_zero] at h2
  rw [h2]
  rfl

lemma coeff_sum_basisSer (ψ : F →+* K) {n : ℕ} (Bc : List (BPoly F)) (Dc : CPoly F) (a : F)
    (hμ0 : muD Dc a 1 = 0) (hμ : muD Dc a 1 < (compC Dc (shiftC a 1)).length)
    (Y : PowerSeries K) (yt : CPoly F) (prec : ℕ)
    (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ Y - thetaT ψ (toPoly yt))
    (cc : Fin n → K[X]) (M : ℕ) (hdeg : ∀ i, (cc i).natDegree ≤ M) (t : ℕ) (ht : t < prec) :
    (∑ i, branchSub (C := K) (K := K) 1 (ψ a) (cc i) *
      basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ)) ((toPoly Dc).map ψ) 1 (ψ a)
        (HahnSeries.ofPowerSeries ℤ K Y) i).coeff (t : ℤ) =
      ∑ i, ∑ d ∈ Finset.range (M + 1), (cc i).coeff d * ψ (colC Bc Dc a yt prec i d t) := by
  rw [HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_lhs => rw [(cc i).as_sum_range' (M + 1) (by have := hdeg i; omega)]
  rw [map_sum, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← C_mul_X_pow_eq_monomial, map_mul, bs_C, mul_assoc, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, coeff_basisSer_cert ψ Bc Dc a hμ0 hμ Y yt prec hy i d t ht,
    Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]

end Trunc

section Check

variable {F : Type*} [Field F] [DecidableEq F]

/-- The certificate data at the points: `m` points `a_j` with certified unramified branches. -/
def testEntry (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F) (cL : List (BranchCert F))
    (j k t i d : ℕ) : F :=
  colC Bc Dc (αL.getD j 0) (((cL.getD j ⟨1, [], 0⟩).ys).getD k []) (cL.getD j ⟨1, [], 0⟩).prec i d t

/-- The side conditions: `D(a_j) ≠ 0` and `b_{jk} ≤ prec_j`. -/
def testSide (n : ℕ) (Dc : CPoly F) (αL : List F) (cL : List (BranchCert F)) (bL : List (List ℕ)) :
    Bool :=
  (List.range αL.length).all fun j ↦
    decide (muD Dc (αL.getD j 0) 1 = 0) &&
    decide (muD Dc (αL.getD j 0) 1 < (compC Dc (shiftC (αL.getD j 0) 1)).length) &&
    (List.range n).all fun k ↦ decide ((bL.getD j []).getD k 0 ≤ (cL.getD j ⟨1, [], 0⟩).prec)

/-- **The failed-test certificate**: `Lm` is a left inverse of the test matrix on the admissible
columns `(i, d)`, `d + δᵢ ≤ M` (rows `(j, k, t)`, `t < b_{jk}`, at position `(j n + k) P + t`). -/
def nonPrincCheck (n M P : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F)
    (cL : List (BranchCert F)) (bL : List (List ℕ)) (Lm : List (List F)) : Bool :=
  testSide n Dc αL cL bL &&
  (List.range αL.length).all (fun j ↦ (List.range n).all fun k ↦
    decide ((bL.getD j []).getD k 0 ≤ P)) &&
  (List.range n).all fun i ↦ (List.range (M + 1)).all fun d ↦
    (List.range n).all fun i' ↦ (List.range (M + 1)).all fun d' ↦
      !(decide (d + δL.getD i 0 ≤ M) && decide (d' + δL.getD i' 0 ≤ M)) ||
      decide ((∑ j ∈ Finset.range αL.length, ∑ k ∈ Finset.range n,
        ∑ t ∈ Finset.range ((bL.getD j []).getD k 0),
          (Lm.getD (i * (M + 1) + d) []).getD ((j * n + k) * P + t) 0 *
            testEntry Bc Dc αL cL j k t i' d') = if i = i' ∧ d = d' then 1 else 0)

/-- **The principal-witness certificate**: coefficients `G` on the admissible columns, not all
zero, killing every row. -/
def princWitCheck (n M : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F)
    (cL : List (BranchCert F)) (bL : List (List ℕ)) (G : List (List F)) : Bool :=
  testSide n Dc αL cL bL &&
  ((List.range n).any fun i ↦ (List.range (M + 1)).any fun d ↦
    decide (d + δL.getD i 0 ≤ M) && decide ((G.getD i []).getD d 0 ≠ 0)) &&
  (List.range αL.length).all fun j ↦ (List.range n).all fun k ↦
    (List.range ((bL.getD j []).getD k 0)).all fun t ↦
      decide ((∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (M + 1),
        (if d + δL.getD i 0 ≤ M then (G.getD i []).getD d 0 else 0) *
          testEntry Bc Dc αL cL j k t i d) = 0)

end Check

end Curves

namespace Curves

open Differential LaurentSeries GTors CPoly Sup

section Spec

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

lemma testSide_spec {n : ℕ} {Dc : CPoly F} {αL : List F} {cL : List (BranchCert F)}
    {bL : List (List ℕ)} (h : testSide n Dc αL cL bL = true) (j : ℕ) (hj : j < αL.length) :
    muD Dc (αL.getD j 0) 1 = 0 ∧ muD Dc (αL.getD j 0) 1 < (compC Dc (shiftC (αL.getD j 0) 1)).length ∧
      ∀ k < n, (bL.getD j []).getD k 0 ≤ (cL.getD j ⟨1, [], 0⟩).prec := by
  simp only [testSide, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(h j hj).1.1, (h j hj).1.2, (h j hj).2⟩

lemma sum_swap2 {α β γ R : Type*} [AddCommMonoid R] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → R) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z = ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, f x y z := by
  calc _ = ∑ x ∈ s, ∑ z ∈ u, ∑ y ∈ t, f x y z :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_comm

variable (ψ : F →+* K) (n M : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F)
  (cL : List (BranchCert F)) (bL : List (List ℕ)) (Y : Fin αL.length → Fin n → PowerSeries K)

/-- The rows of the test vanish for a coefficient vector passing the test. -/
lemma test_rows (hside : testSide n Dc αL cL bL = true)
    (hY : ∀ (j : Fin αL.length) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k [])))
    (cc : Fin n → K[X]) (hdeg : ∀ i, (cc i).natDegree ≤ M) (j : Fin αL.length) (k : Fin n) (t : ℕ)
    (ht : t < (bL.getD j []).getD k 0) :
    (∑ i, branchSub (C := K) (K := K) 1 (ψ (αL.getD j 0)) (cc i) *
      basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ)) ((toPoly Dc).map ψ) 1
        (ψ (αL.getD j 0)) (HahnSeries.ofPowerSeries ℤ K (Y j k)) i).coeff (t : ℤ) =
      ∑ i, ∑ d ∈ Finset.range (M + 1), (cc i).coeff d * ψ (testEntry Bc Dc αL cL j k t i d) := by
  obtain ⟨hμ0, hμ, hb⟩ := testSide_spec hside j j.2
  exact coeff_sum_basisSer ψ Bc Dc _ hμ0 hμ (Y j k) _ _ (hY j k) cc M hdeg t
    (lt_of_lt_of_le ht (hb k k.2))

/-- **A failed test**: the certificate proves that the test fails. -/
theorem not_princTest_of_cert (P : ℕ) (Lm : List (List F))
    (hchk : nonPrincCheck n M P δL Bc Dc αL cL bL Lm = true)
    (hY : ∀ (j : Fin αL.length) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M (fun _ : Fin αL.length × Fin n ↦ 1)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) 1 (ψ (αL.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) := by
  classical
  simp only [nonPrincCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at hchk
  obtain ⟨⟨hside, -⟩, hinv⟩ := hchk
  rintro ⟨cc, hc0, hdeg, hlb⟩
  apply hc0
  have hdeg' : ∀ i, (cc i).natDegree ≤ M := fun i ↦ by
    by_cases h : cc i = 0
    · rw [h, natDegree_zero]; exact Nat.zero_le _
    · have := hdeg i h; simp only at this; omega
  have hvan : ∀ (i : Fin n) (d : ℕ), M < d + δL.getD i 0 → (cc i).coeff d = 0 := fun i d hd ↦ by
    by_cases h : cc i = 0
    · rw [h, Polynomial.coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by have := hdeg i h; simp only at this; omega)
  set cN : ℕ → ℕ → K := fun i d ↦ if h : i < n then (cc ⟨i, h⟩).coeff d else 0 with hcN
  have hcNv : ∀ i d, M < d + δL.getD i 0 → cN i d = 0 := fun i d hd ↦ by
    simp only [hcN]; split_ifs with h
    · exact hvan _ d hd
    · rfl
  -- the rows
  have hrow : ∀ j < αL.length, ∀ k < n, ∀ t < (bL.getD j []).getD k 0,
      ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (M + 1),
        ψ (testEntry Bc Dc αL cL j k t i d) * cN i d = 0 := by
    intro j hj k hk t ht
    have h1 := hlb (⟨j, hj⟩, ⟨k, hk⟩) t (by simp only; exact_mod_cast ht)
    rw [test_rows ψ n M Bc Dc αL cL bL Y hside hY cc hdeg' ⟨j, hj⟩ ⟨k, hk⟩ t ht] at h1
    rw [← h1, ← Fin.sum_univ_eq_sum_range (fun i ↦ ∑ d ∈ Finset.range (M + 1),
      ψ (testEntry Bc Dc αL cL j k t i d) * cN i d)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [hcN, dif_pos i.2, Fin.eta]
    ring
  -- every admissible coefficient vanishes
  have hall : ∀ i < n, ∀ d ≤ M, d + δL.getD i 0 ≤ M → cN i d = 0 := by
    intro i0 hi0 d0 hd0 hv0
    have e1 : cN i0 d0 = ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (M + 1),
        (if i0 = i ∧ d0 = d then (1 : K) else 0) * cN i d := by
      rw [Finset.sum_eq_single i0, Finset.sum_eq_single d0]
      · simp
      · intro d _ hd; rw [if_neg (fun h ↦ hd h.2.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro i _ hi
        exact Finset.sum_eq_zero fun d _ ↦ by rw [if_neg (fun h ↦ hi h.1.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_range.mpr hi0) h
    have e2 : ∀ i ∈ Finset.range n, ∀ d ∈ Finset.range (M + 1),
        (if i0 = i ∧ d0 = d then (1 : K) else 0) * cN i d =
          ψ (∑ j ∈ Finset.range αL.length, ∑ k ∈ Finset.range n,
            ∑ t ∈ Finset.range ((bL.getD j []).getD k 0),
              (Lm.getD (i0 * (M + 1) + d0) []).getD ((j * n + k) * P + t) 0 *
                testEntry Bc Dc αL cL j k t i d) * cN i d := by
      intro i hi d hd
      by_cases hv : d + δL.getD i 0 ≤ M
      · rcases hinv i0 hi0 d0 (by omega) i (Finset.mem_range.mp hi) d (Finset.mem_range.mp hd)
          with h | h
        · rcases h with h | h
          · exact absurd hv0 h
          · exact absurd hv h
        · rw [h]; split_ifs <;> simp
      · rw [hcNv i d (by omega), mul_zero, mul_zero]
    rw [e1, Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun d hd ↦ e2 i hi d hd]
    simp only [map_sum, map_mul, Finset.sum_mul]
    rw [sum_swap2]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [sum_swap2]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [sum_swap2]
    refine Finset.sum_eq_zero fun t ht ↦ ?_
    have := hrow j (Finset.mem_range.mp hj) k (Finset.mem_range.mp hk) t (Finset.mem_range.mp ht)
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [this, mul_zero]
  funext i
  ext d
  rw [Pi.zero_apply, Polynomial.coeff_zero]
  by_cases hv : d + δL.getD i 0 ≤ M
  · have := hall i i.2 d (by omega) hv
    simpa [hcN] using this
  · exact hvan i d (by omega)

/-- **A passing test**: the certificate is a non-zero solution of the test. -/
theorem princTest_of_cert (G : List (List F))
    (hchk : princWitCheck n M δL Bc Dc αL cL bL G = true) {m : ℕ} (hm : αL.length = m)
    (Y' : Fin m → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin m) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y' j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    princTest (fun i : Fin n ↦ δL.getD i 0) M (fun _ : Fin m × Fin n ↦ 1)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) 1 (ψ (αL.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ K (Y' q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) := by
  classical
  subst hm
  set Y := Y' with hYdef
  simp only [princWitCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, List.any_eq_true] at hchk
  obtain ⟨⟨hside, ⟨i0, hi0, d0, hd0, hv0, hG0⟩⟩, hrows⟩ := hchk
  set gN : ℕ → ℕ → F := fun i d ↦ if d + δL.getD i 0 ≤ M then (G.getD i []).getD d 0 else 0 with hgN
  set cc : Fin n → K[X] := fun i ↦ ∑ d ∈ Finset.range (M + 1),
    Polynomial.C (ψ (gN i d)) * X ^ d with hcc
  have hcoeff : ∀ i d, (cc i).coeff d = if d < M + 1 then ψ (gN i d) else 0 := by
    intro i d
    simp only [hcc, finset_sum_coeff, coeff_C_mul_X_pow]
    by_cases hd : d < M + 1
    · rw [Finset.sum_eq_single d (fun b _ hb ↦ if_neg (Ne.symm hb))
        (fun h ↦ absurd (Finset.mem_range.mpr hd) h), if_pos rfl, if_pos hd]
    · rw [Finset.sum_eq_zero fun b hb ↦ if_neg (by
        have := Finset.mem_range.mp hb; omega), if_neg hd]
  have hcoeff0 : ∀ i d, (cc i).coeff d ≠ 0 → d + δL.getD i 0 ≤ M := by
    intro i d h
    rw [hcoeff] at h
    split_ifs at h with hd
    · by_contra hv
      apply h
      simp only [hgN, if_neg hv, map_zero]
    · exact absurd rfl h
  have hdeg' : ∀ i, (cc i).natDegree ≤ M := fun i ↦ by
    by_cases h : cc i = 0
    · rw [h, natDegree_zero]; exact Nat.zero_le _
    · have := hcoeff0 i _ (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr h); omega
  refine ⟨cc, ?_, fun i h ↦ hcoeff0 i _ (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr h),
    fun q t ht ↦ ?_⟩
  · intro h
    have := congrArg (fun c ↦ (c ⟨i0, hi0⟩).coeff d0) h
    simp only [Pi.zero_apply, Polynomial.coeff_zero, hcoeff, if_pos (show d0 < M + 1 by omega),
      hgN, if_pos hv0] at this
    exact hG0 ((map_eq_zero_iff ψ ψ.injective).mp this)
  · obtain ⟨j, k⟩ := q
    simp only at ht ⊢
    obtain ⟨hμ0, hμ, hb⟩ := testSide_spec hside j j.2
    by_cases ht0 : t < 0
    · -- negative coefficients vanish
      rw [HahnSeries.coeff_sum]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      obtain ⟨V, hV, -⟩ := basisSer_trunc ψ (Bc.getD i []) Dc (αL.getD j 0) hμ0 hμ (Y j k)
        _ _ (hY j k)
      rw [basisSer, hV, branchSub_apply, ← map_mul, coeff_ofPS, if_neg (by omega)]
    · lift t to ℕ using (by omega)
      have ht' : t < (bL.getD j []).getD k 0 := by exact_mod_cast ht
      rw [test_rows ψ n M Bc Dc αL cL bL Y hside hY cc hdeg' j k t ht']
      have := hrows j j.2 k k.2 t ht'
      rw [← map_zero ψ, ← this, map_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ ψ (∑ d ∈ Finset.range (M + 1),
        (if d + δL.getD i 0 ≤ M then (G.getD i []).getD d 0 else 0) * testEntry Bc Dc αL cL j k t i d))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [hcoeff, if_pos (Finset.mem_range.mp hd), map_mul]

end Spec

end Curves
