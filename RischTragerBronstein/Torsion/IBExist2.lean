import RischTragerBronstein.Torsion.IBExist1

/-!
# Integral bases exist (2): the improvement step at a finite point

For a branch system `σ` above `a` (coefficients in `C`) and a basis `wⱼ = Bⱼ/D`, a non-trivial
`c` with `∑ cⱼ wⱼ ≡ 0 mod (x − a)` along `σ` gives the improved basis `stepB`/`stepD`: `w_{j₀}` is
replaced by `(∑ cⱼ wⱼ)/(x − a)` (`c_{j₀} ≠ 0`), the other `wⱼ` are unchanged.

* `det_stepB`: the determinant is multiplied by `(X − a)^{n−1} · c_{j₀}`;
* `regAt_step_self`, `regAt_step_other`: regularity along `σ` and along systems above other points
  is preserved.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Step

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- A branch system above a point of `C`, with coefficients in `C` and roots without poles. -/
structure LocSys where
  a : C
  N : ℕ
  hN : 0 < N
  r : Fin S.F.natDegree → LaurentSeries C
  hs : S.F.map (branchSub N (algebraMap C C a)) = ∏ k, (X - Polynomial.C (r k))
  hr : ∀ k, LowerBd (r k) 0

variable {S}

/-- The expansion of `f` along the `k`-th branch of `σ`. -/
noncomputable def LocSys.ev (σ : S.LocSys) (k : Fin S.F.natDegree) (f : C⟮S.x⟯⟮S.y⟯) :
    LaurentSeries C :=
  S.embG (branchSub σ.N (algebraMap C C σ.a)) (branchSub_injective _ σ.hN _) (σ.r k)
    (S.root_of_split _ σ.r σ.hs k) f

/-- Regularity of the basis `Bⱼ/D` along `σ`. -/
def RegAt (σ : S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) : Prop :=
  ∀ j k, LowerBd (σ.ev k (S.fnWQ (B j) D)) 0

/-- Independence of the reductions modulo `x − a` along `σ`. -/
def IndepAt (σ : S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) : Prop :=
  ∀ c : Fin S.F.natDegree → C,
    (∀ k, LowerBd (∑ j, HahnSeries.C (c j) * σ.ev k (S.fnWQ (B j) D)) σ.N) → c = 0

/-- The improved numerators. -/
noncomputable def stepB (B : Fin S.F.natDegree → C[X][X]) (a : C) (c : Fin S.F.natDegree → C)
    (j₀ : Fin S.F.natDegree) : Fin S.F.natDegree → C[X][X] := fun j ↦
  if j = j₀ then ∑ l, Polynomial.C (Polynomial.C (c l)) * B l
  else Polynomial.C (X - Polynomial.C a) * B j

/-- The improved denominator. -/
noncomputable def stepD (D : C[X]) (a : C) : C[X] := (X - Polynomial.C a) * D

lemma stepD_ne_zero {D : C[X]} (hD : D ≠ 0) (a : C) : stepD D a ≠ 0 :=
  mul_ne_zero (X_sub_C_ne_zero a) hD

lemma stepB_deg {B : Fin S.F.natDegree → C[X][X]} (hB : ∀ j, (B j).natDegree < S.F.natDegree)
    (a : C) (c : Fin S.F.natDegree → C) (j₀ j : Fin S.F.natDegree) :
    (stepB B a c j₀ j).natDegree < S.F.natDegree := by
  have hn : 0 < S.F.natDegree := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  unfold stepB
  split_ifs
  · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := S.F.natDegree - 1)
      fun l _ ↦ ?_) (by omega)
    exact natDegree_C_mul_le _ _ |>.trans (by have := hB l; omega)
  · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (hB j)

/-- The coefficient matrix `[Bⱼ,ᵢ]`. -/
noncomputable def coeffMat (B : Fin S.F.natDegree → C[X][X]) :
    Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C[X] :=
  Matrix.of fun i j ↦ (B j).coeff i

/-- **The determinant of the improved basis.** -/
lemma det_stepB (B : Fin S.F.natDegree → C[X][X]) (a : C) (c : Fin S.F.natDegree → C)
    (j₀ : Fin S.F.natDegree) :
    (coeffMat (stepB B a c j₀)).det =
      (X - Polynomial.C a) ^ (S.F.natDegree - 1) * (Polynomial.C (c j₀) * (coeffMat B).det) := by
  classical
  set v : Fin S.F.natDegree → C[X] := fun j ↦ if j = j₀ then 1 else X - Polynomial.C a with hv
  set M'' := (coeffMat B).updateCol j₀ (fun i ↦ ∑ l, Polynomial.C (c l) • coeffMat B i l) with hM''
  have hM : coeffMat (stepB B a c j₀) = Matrix.of fun i j ↦ v j * M'' i j := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [coeffMat, stepB, hv, hM'', Matrix.of_apply, Matrix.updateCol_apply]
    by_cases hj : j = j₀
    · subst hj
      simp only [if_true, one_mul, finset_sum_coeff, coeff_C_mul, smul_eq_mul]
    · simp only [hj, if_false, coeff_C_mul]
  have hprod : ∏ j, v j = (X - Polynomial.C a) ^ (S.F.natDegree - 1) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀)]
    simp only [hv, if_true, mul_one]
    rw [Finset.prod_congr rfl (fun j hj ↦ if_neg (Finset.ne_of_mem_erase hj)), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [hM, Matrix.det_mul_row, hprod, hM'', Matrix.det_updateCol_sum, smul_eq_mul]

lemma polyF_X_sub (σ : S.LocSys) (k : Fin S.F.natDegree) (a : C) :
    σ.ev k (S.polyF (X - Polynomial.C a)) = HahnSeries.C (σ.a - a) + single (σ.N : ℤ) (1 : C) := by
  rw [LocSys.ev, S.embG_polyF, map_sub, bs_X, bs_C]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, map_sub]
  ring

lemma fnWQ_stepB_ne (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (a : C)
    (c : Fin S.F.natDegree → C) (j₀ j : Fin S.F.natDegree) (hj : j ≠ j₀) :
    S.fnWQ (stepB B a c j₀ j) (stepD D a) = S.fnWQ (B j) D := by
  have hX : S.polyF (X - Polynomial.C a) ≠ 0 := S.polyF_ne_zero (X_sub_C_ne_zero a)
  simp only [stepB, hj, if_false, stepD, fnWQ]
  have e1 : S.evT (Polynomial.C (X - Polynomial.C a) * B j) = S.polyF (X - Polynomial.C a) * S.evT (B j) := by
    apply Subtype.ext
    rw [S.coe_evT, IntermediateField.coe_mul, coe_polyF, S.coe_evT, S.evXY_mul]
    simp [evXY]
  have e2 : S.polyF ((X - Polynomial.C a) * D) = S.polyF (X - Polynomial.C a) * S.polyF D := by
    simp [polyF]
  rw [e1, e2, mul_inv, show S.polyF (X - Polynomial.C a) * S.evT (B j) *
      ((S.polyF (X - Polynomial.C a))⁻¹ * (S.polyF D)⁻¹) =
      S.evT (B j) * (S.polyF D)⁻¹ * (S.polyF (X - Polynomial.C a) *
        (S.polyF (X - Polynomial.C a))⁻¹) by ring, mul_inv_cancel₀ hX, mul_one]

lemma fnWQ_stepB_eq (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (a : C)
    (c : Fin S.F.natDegree → C) (j₀ : Fin S.F.natDegree) :
    S.fnWQ (stepB B a c j₀ j₀) (stepD D a) =
      (∑ l, S.polyF (Polynomial.C (c l)) * S.fnWQ (B l) D) * (S.polyF (X - Polynomial.C a))⁻¹ := by
  simp only [stepB, if_true, stepD, fnWQ]
  have e1 : S.evT (∑ l, Polynomial.C (Polynomial.C (c l)) * B l) =
      ∑ l, S.polyF (Polynomial.C (c l)) * S.evT (B l) := by
    apply Subtype.ext
    rw [S.coe_evT, IntermediateField.coe_sum]
    simp only [IntermediateField.coe_mul, coe_polyF, S.coe_evT, evXY, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, eval_finset_sum, eval_mul, eval_C]
    rfl
  have e2 : S.polyF ((X - Polynomial.C a) * D) = S.polyF (X - Polynomial.C a) * S.polyF D := by
    simp [polyF]
  rw [e1, e2, mul_inv, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

end CurveData

end Step

end Curves
