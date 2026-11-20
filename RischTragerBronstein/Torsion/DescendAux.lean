import RischTragerBronstein.Torsion.Exist
import RischTragerBronstein.Algebraic.SupDescend

/-!
# Auxiliary lemmas for the descent (general curves)

* `PsiC_cast`: re-indexing coordinates along `Fin.cast`;
* `elt_smul`, `order_elt_smul_fin`, `order_elt_smul_inf`: scaling coordinates by a non-zero
  constant does not change orders;
* `descend_coords`: a non-zero coordinate vector over the fraction field is a constant multiple of
  a primitive one over the discrete valuation ring;
* `normW_map`: norms commute with the coefficient maps.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

lemma PsiC_cast {R : Type*} [CommRing R] {a b : ℕ} (h : a = b) (B : Fin b → R[X][X])
    (c : Fin b → R[X]) :
    PsiC (fun j : Fin a ↦ B (Fin.cast h j)) (fun j ↦ c (Fin.cast h j)) = PsiC B c := by
  unfold PsiC
  exact Fintype.sum_equiv (finCongr h) _ _ fun j ↦ rfl

section Scale

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable {S : CurveData C L}

lemma elt_smul (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (c : Fin S.F.natDegree → C[X])
    (μ : C) : S.elt B D (fun j ↦ Polynomial.C μ * c j) = S.polyF (Polynomial.C μ) * S.elt B D c := by
  simp only [elt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← mul_assoc]
  congr 1
  simp only [polyF, map_mul]

lemma order_elt_smul_fin (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (c : Fin S.F.natDegree → C[X]) (μ : C) (hμ : μ ≠ 0) (N : ℕ) (hN : 0 < N) (a : K)
    (r : LaurentSeries K) (hr : (S.F.map (branchSub N a)).eval r = 0) :
    (S.embG (branchSub N a) (branchSub_injective N hN a) r hr
      (S.elt B D (fun j ↦ Polynomial.C μ * c j))).order =
      (S.embG (branchSub N a) (branchSub_injective N hN a) r hr (S.elt B D c)).order := by
  by_cases h0 : S.embG (branchSub N a) (branchSub_injective N hN a) r hr (S.elt B D c) = 0
  · rw [elt_smul, map_mul, h0, mul_zero]
  have hc : (HahnSeries.C (algebraMap C K μ) : LaurentSeries K) ≠ 0 :=
    HahnSeries.C_ne_zero ((map_ne_zero_iff _ (algebraMap C K).injective).mpr hμ)
  rw [elt_smul, map_mul, S.embG_polyF, bs_C, HahnSeries.order_mul hc h0, HahnSeries.order_C (Γ := ℤ),
    zero_add]

lemma order_elt_smul_inf (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (c : Fin S.F.natDegree → C[X]) (μ : C) (hμ : μ ≠ 0) (N : ℕ) (hN : 0 < N)
    (r : LaurentSeries K) (hr : (S.F.map (infSub N)).eval r = 0) :
    (S.embG (infSub N) (infSub_injective N hN) r hr
      (S.elt B D (fun j ↦ Polynomial.C μ * c j))).order =
      (S.embG (infSub N) (infSub_injective N hN) r hr (S.elt B D c)).order := by
  by_cases h0 : S.embG (infSub N) (infSub_injective N hN) r hr (S.elt B D c) = 0
  · rw [elt_smul, map_mul, h0, mul_zero]
  have hc : (HahnSeries.C (algebraMap C K μ) : LaurentSeries K) ≠ 0 :=
    HahnSeries.C_ne_zero ((map_ne_zero_iff _ (algebraMap C K).injective).mpr hμ)
  rw [elt_smul, map_mul, S.embG_polyF, is_C, HahnSeries.order_mul hc h0, HahnSeries.order_C (Γ := ℤ),
    zero_add]

end CurveData

end Scale

section Descend

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

local notation "ι" => algebraMap O K

/-- **Primitive coordinates.** -/
theorem descend_coords {ϖ : O} (hϖ : Irreducible ϖ) {n : ℕ} (v : Fin n → K[X]) (hv : v ≠ 0) :
    ∃ (w : Fin n → O[X]) (μ : K), μ ≠ 0 ∧ (∀ j, (w j).map ι = Polynomial.C μ * v j) ∧
      ¬ ∀ j, Polynomial.C ϖ ∣ w j := by
  classical
  have hι : Function.Injective ι := IsFractionRing.injective O K
  set V : K[X][X] := ∑ j : Fin n, monomial (j : ℕ) (v j) with hV
  have hVc : ∀ (j : Fin n), V.coeff j = v j := by
    intro j
    rw [hV, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_monomial, if_pos rfl]
    · intro b _ hb; rw [coeff_monomial, if_neg (fun h ↦ hb (Fin.ext h))]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hVc' : ∀ k, n ≤ k → V.coeff k = 0 := by
    intro k hk
    rw [hV, finset_sum_coeff]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [coeff_monomial, if_neg (by have := j.isLt; omega)]
  have hV0 : V ≠ 0 := by
    intro h0
    apply hv
    funext j
    rw [← hVc, h0, Polynomial.coeff_zero, Pi.zero_apply]
  obtain ⟨ψ, μ, hμ, hψ, hprim⟩ := Sup.descend_bivar hϖ V hV0
  have hcoef : ∀ k, (ψ.coeff k).map ι = Polynomial.C μ * V.coeff k := by
    intro k
    have := congrArg (fun P : K[X][X] ↦ P.coeff k) hψ
    simpa [coeff_map] using this
  refine ⟨fun j ↦ ψ.coeff j, μ, hμ, fun j ↦ by rw [hcoef, hVc], fun h ↦ hprim fun k ↦ ?_⟩
  by_cases hk : k < n
  · exact h ⟨k, hk⟩
  · have : ψ.coeff k = 0 := by
      apply Polynomial.map_injective _ hι
      rw [hcoef, hVc' k (by omega), mul_zero, Polynomial.map_zero]
    rw [this]; exact dvd_zero _

end Descend

section Norm

variable {O K L : Type*} [CommRing O] [Field K] [Field L] [Algebra K L]

namespace CurveData

lemma normW_map (S : CurveData K L) (φ : O →+* K) (F W : O[X][X]) (hF : F.Monic)
    (hSF : S.F = F.map (mapRingHom φ)) (m : ℕ) :
    S.normW (W.map (mapRingHom φ)) m = (resultant F W F.natDegree m).map φ := by
  have hn : S.F.natDegree = F.natDegree := by rw [hSF, hF.natDegree_map]
  rw [normW, hn, hSF, resultant_map_map]
  rfl

end CurveData

end Norm

end Curves
