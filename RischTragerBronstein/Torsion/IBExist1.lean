import RischTragerBronstein.Torsion.LSpace
import RischTragerBronstein.Curves.Coords
import RischTragerBronstein.Algebraic.SuperExp
import RischTragerBronstein.Torsion.PrincipalG

/-!
# Integral bases exist (1): the local index

For `wⱼ = Bⱼ(x, y)/D(x)` (`deg_y Bⱼ < n`) regular along a branch system above `a` whose roots
have no pole, `disc · Bⱼ,ᵢ` is divisible by `(X − a)^{mult_a D}` (`dvd_of_regular`, from the
Cramer bound `coord_lowerBd`). Hence `n · mult_a D ≤ mult_a (discⁿ · det B)`
(`index_bound`): the *local index* `mult_a (discⁿ · det B) − n · mult_a D` is a natural number,
which each improvement step of an integral basis at `a` lowers by one.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Coords

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- The coordinates of `∑ⱼ qⱼ yʲ`. -/
lemma coords_sum (q : Fin S.F.natDegree → C⟮S.x⟯) (i : Fin S.F.natDegree) :
    S.coords (∑ j, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (q j) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ)) i = q i := by
  classical
  have hdim : (IntermediateField.adjoin.powerBasis S.isIntegral).dim = S.F.natDegree := by
    rw [IntermediateField.adjoin.powerBasis_dim, S.natDegree_minpoly]
  have hgen : (IntermediateField.adjoin.powerBasis S.isIntegral).gen =
      AdjoinSimple.gen C⟮S.x⟯ S.y := IntermediateField.adjoin.powerBasis_gen _
  have hc : ∀ z, S.coords z i =
      (IntermediateField.adjoin.powerBasis S.isIntegral).basis.repr z (finCongr hdim.symm i) :=
    fun z ↦ rfl
  have e : ∀ j : Fin S.F.natDegree, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (q j) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ) =
      q j • (IntermediateField.adjoin.powerBasis S.isIntegral).basis (finCongr hdim.symm j) := by
    intro j
    rw [PowerBasis.coe_basis, hgen, Algebra.smul_def]
    rfl
  rw [hc]
  simp_rw [e]
  rw [map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finsupp.single_apply, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg, mul_zero]
    intro h
    exact hj ((finCongr hdim.symm).injective h)
  · simp

/-- The coordinates of `W(x, y)/Q(x)` (`deg_y W < n`). -/
lemma coords_fnWQ (W : C[X][X]) (hW : W.natDegree < S.F.natDegree) (Q : C[X])
    (i : Fin S.F.natDegree) :
    letI := algebraAdjoinSimple (F := C) S.x
    S.coords (S.fnWQ W Q) i = algebraMap C[X] C⟮S.x⟯ (W.coeff i) / algebraMap C[X] C⟮S.x⟯ Q := by
  letI := algebraAdjoinSimple (F := C) S.x
  set φ := (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).comp (algebraMap C[X] C⟮S.x⟯)
  have hsum : S.fnWQ W Q = ∑ j : Fin S.F.natDegree, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯
      (algebraMap C[X] C⟮S.x⟯ (W.coeff j) / algebraMap C[X] C⟮S.x⟯ Q) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ) := by
    rw [fnWQ, evT, eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le hW), Finset.sum_mul,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coeff_map, polyF, div_eq_mul_inv, map_mul, map_inv₀]
    simp only [φ, RingHom.comp_apply]
    ring
  rw [hsum, coords_sum]

end CurveData

end Coords

section Index

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Regularity above `a` bounds the denominator**: `(X − a)^{mult_a D} ∣ disc · Bⱼ,ᵢ`. -/
theorem dvd_of_regular (B : Fin S.F.natDegree → C[X][X]) (hB : ∀ j, (B j).natDegree < S.F.natDegree)
    (D : C[X]) (hD : D ≠ 0) (a₀ : C) (N : ℕ) (hN : 0 < N)
    (r : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (branchSub N (algebraMap C K a₀)) = ∏ k, (X - Polynomial.C (r k)))
    (hr : ∀ k, LowerBd (r k) 0)
    (hreg : ∀ j k, LowerBd (S.embG (branchSub N (algebraMap C K a₀))
      (branchSub_injective N hN _) (r k) (S.root_of_split _ r hs k) (S.fnWQ (B j) D)) 0)
    (i j : Fin S.F.natDegree) :
    (X - Polynomial.C a₀) ^ D.rootMultiplicity a₀ ∣ S.discR * (B j).coeff i := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  set a := algebraMap C K a₀
  set g : C[X] →+* LaurentSeries K := branchSub N a with hg
  have hgi : Function.Injective g := branchSub_injective N hN a
  have h := S.coord_lowerBd S.discR_ne_zero g hgi r hs 0 le_rfl hr (S.fnWQ (B j) D) 0 (hreg j) i
  rw [mul_zero, add_zero, S.coords_fnWQ (B j) (hB j) D i, map_div₀, S.embXG_algebraMap,
    S.embXG_algebraMap, ← mul_div_assoc, ← map_mul] at h
  set P := S.discR * (B j).coeff i with hP
  by_cases hP0 : P = 0
  · rw [hP0]; exact dvd_zero _
  have hgD : g D ≠ 0 := (map_ne_zero_iff _ hgi).mpr hD
  have hgP : g P ≠ 0 := (map_ne_zero_iff _ hgi).mpr hP0
  have hq : g P / g D ≠ 0 := div_ne_zero hgP hgD
  have hord := le_order_of_lowerBd _ hq 0 h
  have e1 : (g P).order = (g P / g D).order + (g D).order := by
    rw [← HahnSeries.order_mul hq hgD, div_mul_cancel₀ _ hgD]
  rw [order_branchSub N hN a P hP0, order_branchSub N hN a D hD] at e1
  have hle : (D.map (algebraMap C K)).rootMultiplicity a ≤ (P.map (algebraMap C K)).rootMultiplicity a := by
    have : ((N * (D.map (algebraMap C K)).rootMultiplicity a : ℕ) : ℤ) ≤
        ((N * (P.map (algebraMap C K)).rootMultiplicity a : ℕ) : ℤ) := by linarith
    exact Nat.le_of_mul_le_mul_left (by exact_mod_cast this) hN
  rw [← eq_rootMultiplicity_map (algebraMap C K).injective,
    ← eq_rootMultiplicity_map (algebraMap C K).injective] at hle
  exact (pow_dvd_pow _ hle).trans (pow_rootMultiplicity_dvd P a₀)

/-- **The local index is a natural number**: `n · mult_a D ≤ mult_a (discⁿ · det B)`. -/
theorem index_bound (B : Fin S.F.natDegree → C[X][X]) (hB : ∀ j, (B j).natDegree < S.F.natDegree)
    (hdet : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0)
    (D : C[X]) (hD : D ≠ 0) (a₀ : C) (N : ℕ) (hN : 0 < N)
    (r : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (branchSub N (algebraMap C K a₀)) = ∏ k, (X - Polynomial.C (r k)))
    (hr : ∀ k, LowerBd (r k) 0)
    (hreg : ∀ j k, LowerBd (S.embG (branchSub N (algebraMap C K a₀))
      (branchSub_injective N hN _) (r k) (S.root_of_split _ r hs k) (S.fnWQ (B j) D)) 0) :
    S.F.natDegree * D.rootMultiplicity a₀ ≤ (S.discR ^ S.F.natDegree *
      (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det).rootMultiplicity a₀ := by
  classical
  have hdv := fun i j ↦ S.dvd_of_regular B hB D hD a₀ N hN r hs hr hreg i j
  choose M hM using hdv
  set q := (X - Polynomial.C a₀) ^ D.rootMultiplicity a₀
  have hmat : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ S.discR * (B j).coeff i) =
      q • Matrix.of fun i j ↦ M i j := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact hM i j
  have hdet' : S.discR ^ S.F.natDegree * (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det =
      q ^ S.F.natDegree * (Matrix.of fun i j ↦ M i j).det := by
    have h1 := congrArg Matrix.det hmat
    rw [Matrix.det_smul, Fintype.card_fin] at h1
    rw [← h1, show (Matrix.of fun (i j : Fin S.F.natDegree) ↦ S.discR * (B j).coeff i) =
      S.discR • Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i by ext; simp, Matrix.det_smul,
      Fintype.card_fin]
  have hne : S.discR ^ S.F.natDegree * (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ S.discR_ne_zero) hdet
  rw [le_rootMultiplicity_iff hne, hdet', mul_comm S.F.natDegree, pow_mul]
  exact dvd_mul_right _ _

end CurveData

end Index

end Curves
