import RischTragerBronstein.Torsion.Eisenstein
import RischTragerBronstein.Torsion.ZpLift
import RischTragerBronstein.Curves.ProcRFSound2
import RischTragerBronstein.Torsion.CertBasis4

/-!
# A single check for integral-basis certificates

`IntBasisCert F`: numerators `Bⱼ`, denominator `D`, pole orders `δⱼ`, basis certificates at the
special points and above infinity. `ibCheck Fc n k I G` checks everything (any characteristic),
given a cover polynomial `G`; `ibCheck_spec` yields `IsIntBasis` over every algebraically closed
field once `G` is a multiple of `disc · D · ∏ⱼ Bⱼ,ⱼ` (proved separately: `discRC` in
characteristic `0`, reduction modulo `p`).
-/

open Polynomial

namespace Curves

open CPoly Sup

/-- An integral-basis certificate. -/
structure IntBasisCert (F : Type*) where
  Bc : List (BPoly F)
  Dc : CPoly F
  δL : List ℕ
  pts : List (F × BranchCert F × List (List F))
  infc : BranchCert F
  Linf : List (List F)

section Check

variable {F : Type*} [Field F] [DecidableEq F]

/-- The product of the leading coefficients `∏ⱼ Bⱼ,ⱼ`. -/
def leadProd : ℕ → List (BPoly F) → CPoly F
  | 0, _ => [1]
  | m + 1, Bc => mul (leadProd m Bc) ((Bc.getD m []).getD m [])

/-- A bound for the degrees of the coefficients of the `Bⱼ`. -/
def degBoundB (Bc : List (BPoly F)) : ℕ := (Bc.flatMap id).foldr (fun c m ↦ max m (c.length - 1)) 0

/-- `det [Bⱼ,ᵢ(t)]`. -/
def detValC (n : ℕ) (Bc : List (BPoly F)) (t : F) : F :=
  (Matrix.of fun (i j : Fin n) ↦ Kron.evalC ((Bc.getD j []).getD i []) t).det

/-- **The determinant `det [Bⱼ,ᵢ]`** by interpolation at `0, …, n · degBoundB`. -/
def detC (n : ℕ) (Bc : List (BPoly F)) : CPoly F :=
  interpC (natPts (n * degBoundB Bc)) ((natPts (n * degBoundB Bc)).map (detValC n Bc))

/-- The shape of the curve: monic of degree `n`, with the model above infinity. -/
def shapeCheck (Fc : BPoly F) (n k : ℕ) : Bool :=
  decide (0 < n) && decide (Fc.length = n + 1) && decide (Fc.getD n [] = [1]) &&
  decide ((invB Fc k (k * n)).length = n + 1) && decide ((invB Fc k (k * n)).getD n [] = [1]) &&
  (List.range Fc.length).all (fun j ↦ decide ((Fc.getD j []).length + k * (0 + j) ≤ k * n + 1))

/-- **The integral-basis check** (with the cover polynomial `G`). -/
def ibCheck (Fc : BPoly F) (n k : ℕ) (I : IntBasisCert F) (G : CPoly F) : Bool :=
  shapeCheck Fc n k && !isZero I.Dc &&
  (List.range n).all (fun j ↦ decide ((I.Bc.getD j []).length ≤ n)) &&
  I.pts.all (fun p ↦ certCheck Fc n p.1 p.2.1 && basisCheckAt n I.Bc I.Dc p.1 p.2.1 p.2.2) &&
  coverCheck G (I.pts.map Prod.fst) &&
  certCheck (invB Fc k (k * n)) n 0 I.infc && basisCheckInfS n k I.Bc I.Dc I.δL I.infc I.Linf

/-- The normalisation `B₀ = D`, `δ₀ = 0`, `δⱼ ≥ 1` needed by the descent. -/
def normCheck (n : ℕ) (I : IntBasisCert F) : Bool :=
  decide (I.Bc.getD 0 [] = [I.Dc]) && decide (I.δL.getD 0 0 = 0) &&
  (List.range n).all fun j ↦ decide (j = 0 ∨ 1 ≤ I.δL.getD j 0)

end Check

section Spec

variable {F : Type*} [Field F] [DecidableEq F]

lemma natDegree_toB_le_len' (W : BPoly F) : (toB W).natDegree ≤ W.length - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    have : W.length - 1 < i := by exact_mod_cast hi
    rw [coeff_toB, List.getD_eq_default _ _ (by omega), toPoly_nil]

lemma toPoly_leadProd (n : ℕ) (Bc : List (BPoly F)) :
    toPoly (leadProd n Bc) = ∏ j : Fin n, (toB (Bc.getD j [])).coeff j := by
  rw [Fin.prod_univ_eq_prod_range (fun j ↦ (toB (Bc.getD j [])).coeff j) n]
  induction n with
  | zero => simp [leadProd, toPoly]
  | succ m ih =>
    rw [leadProd, toPoly_mul, ih, Finset.prod_range_succ, coeff_toB]

omit [DecidableEq F] in
lemma natDegree_det_le_of {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R[X])
    (k : ℕ) (hM : ∀ i j, (M i j).natDegree ≤ k) : M.det.natDegree ≤ n * k := by
  rw [Matrix.det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc natDegree (Equiv.Perm.sign g • ∏ i, M (g i) i) ≤ natDegree (∏ i, M (g i) i) := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
        · rw [sg, one_smul]
        · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i, natDegree (M (g i) i) := natDegree_prod_le _ _
    _ ≤ Finset.univ.card • k := Finset.sum_le_card_nsmul _ _ k fun i _ ↦ hM _ _
    _ = n * k := by simp

lemma natDegree_coeff_le_degBoundB (Bc : List (BPoly F)) (i j : ℕ) :
    ((toB (Bc.getD j [])).coeff i).natDegree ≤ degBoundB Bc := by
  rw [coeff_toB]
  refine (natDegree_toPoly_le_length _).trans ?_
  have key0 : ∀ (l : List (CPoly F)), ∀ c ∈ l,
      c.length - 1 ≤ l.foldr (fun c m ↦ max m (c.length - 1)) 0 := by
    intro l
    induction l with
    | nil => intro c hc; simp at hc
    | cons x l ih =>
      intro c hc
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_max_right _ _
      · exact (ih c hc).trans (le_max_left _ _)
  have key : ∀ c ∈ Bc.flatMap id, c.length - 1 ≤ degBoundB Bc := fun c hc ↦ key0 _ c hc
  by_cases hj : j < Bc.length
  · by_cases hi : i < (Bc.getD j []).length
    · refine key _ (List.mem_flatMap.mpr ⟨Bc.getD j [], ?_, ?_⟩)
      · rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
      · rw [id, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    · rw [List.getD_eq_default (Bc.getD j []) [] (by omega)]; simp
  · rw [List.getD_eq_default Bc [] (by omega : Bc.length ≤ j)]; simp

lemma toPoly_detC [CharZero F] (n : ℕ) (Bc : List (BPoly F)) :
    toPoly (detC n Bc) = (Matrix.of fun (i j : Fin n) ↦ (toB (Bc.getD j [])).coeff i).det := by
  set d := n * degBoundB Bc with hd
  refine eq_of_natDegree_lt_card_of_eval_eq _ _ (ι := Fin (d + 1)) (f := fun i ↦ ((i : ℕ) : F))
    (fun a b h ↦ Fin.ext (by simpa using h)) (fun i ↦ ?_) ?_
  · have hi : (i : ℕ) < d + 1 := i.2
    have hl : (i : ℕ) < (natPts d : List F).length := by rw [natPts_length]; exact hi
    rw [detC, ← hd, ← natPts_getD d i hi, eval_interpC _ _ (natPts_nodup d) i hl,
      List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hl, natPts_getD d i hi, detValC,
      show ∀ P : F[X], P.eval ((i : ℕ) : F) = evalRingHom ((i : ℕ) : F) P from fun _ ↦ rfl,
      RingHom.map_det]
    congr 1
    ext a b
    simp [coeff_toB, Kron.evalC_eq]
  · rw [Fintype.card_fin]
    refine max_lt ?_ ?_
    · have := natDegree_interpC_lt (natPts d : List F)
        ((natPts d).map (detValC n Bc)) (by rw [natPts_length]; omega)
      rwa [natPts_length] at this
    · have := natDegree_det_le_of (Matrix.of fun (i j : Fin n) ↦ (toB (Bc.getD j [])).coeff i)
        (degBoundB Bc) (fun i j ↦ natDegree_coeff_le_degBoundB Bc i j)
      omega

/-- The facts behind `shapeCheck`. -/
lemma shapeCheck_spec {Fc : BPoly F} {n k : ℕ} (h : shapeCheck Fc n k = true) :
    0 < n ∧ (toB Fc).Monic ∧ (toB Fc).natDegree = n ∧ InvOK k (k * n) 0 Fc ∧
      (toB (invB Fc k (k * n))).Monic ∧ (toB (invB Fc k (k * n))).natDegree = n := by
  simp only [shapeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hn, hl⟩, hlast⟩, hl'⟩, hlast'⟩, hok⟩ := h
  obtain ⟨hmon, hdeg⟩ := monic_toB_of Fc n hl hlast
  obtain ⟨hmon', hdeg'⟩ := monic_toB_of _ n hl' hlast'
  exact ⟨hn, hmon, hdeg, fun j hj ↦ hok j hj, hmon', hdeg'⟩

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

/-- **The integral basis from `ibCheck`.** -/
theorem ibCheck_spec (S : CurveData C L) (Fc : BPoly F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB Fc).map (mapRingHom ψ₀)) (n k : ℕ) (hn : n = S.F.natDegree)
    (I : IntBasisCert F) (G : CPoly F) (h : ibCheck Fc n k I G = true)
    (hG : resultant (toB Fc) (derivative (toB Fc)) n (n - 1) * toPoly I.Dc *
      (Matrix.of fun (i j : Fin n) ↦ (toB (I.Bc.getD j [])).coeff i).det ∣ toPoly G) :
    S.IsIntBasis K (fun j ↦ (toB (I.Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly I.Dc).map ψ₀)
      (fun j ↦ I.δL.getD j 0) := by
  subst hn
  simp only [ibCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true', Bool.eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨hsh, hD⟩, htl⟩, hpts⟩, hcov⟩, hinfc⟩, hinfb⟩ := h
  obtain ⟨hn0, hmon, hdeg, hok, hmon', hn'⟩ := shapeCheck_spec hsh
  have hG0 : toPoly G ≠ 0 := by
    have hc := hcov
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.eq_false_iff] at hc
    obtain ⟨Q, hQ, -, hQ0⟩ := foldl_strip_spec.{_, 0} (I.pts.map Prod.fst) G
    rw [hQ]
    exact mul_ne_zero hQ0 fun h1 ↦ hc.2 ((isZero_iff _).mpr h1)
  refine S.isIntBasis_of_cert_det Fc ψ₀ hSF hmon hdeg k hok hmon' hn' I.Bc I.Dc I.δL
    (fun h0 ↦ hD ((isZero_iff _).mpr h0)) (fun j ↦ ?_) ?_ I.pts
    (fun p hp ↦ by simpa using hpts p hp) G hG hcov I.infc I.Linf hinfc hinfb
  · exact lt_of_le_of_lt (natDegree_toB_le_len' _) (by have := htl j j.2; omega)
  · intro h0
    rw [h0, mul_zero] at hG
    exact hG0 (zero_dvd_iff.mp hG)

end Spec

end Curves
