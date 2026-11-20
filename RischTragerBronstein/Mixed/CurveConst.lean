import RischTragerBronstein.Mixed.RdeBounds

/-!
# Functions without poles on a curve are constant

**`const_of_noPoles`**: over an algebraically closed field of constants `C`, if `z ∈ C⟮x⟯⟮y⟯` has
no pole along any branch (finite or above infinity), then `z ∈ C`.

Every power `zᴺ` has no pole either, so by the ansatz `zᴺ · discR = Wₙ(x, y)` with `Wₙ` in a fixed
finite-dimensional space; `n (B + 1) + 1` of them are linearly dependent, so `z` is algebraic over
`C`, hence in `C`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Const

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]

/-- **An element algebraic over an algebraically closed field is in it.** -/
lemma mem_range_of_aeval_eq_zero [IsAlgClosed C] (z : L) (p : C[X]) (hp : p ≠ 0)
    (hz : aeval z p = 0) : z ∈ Set.range (algebraMap C L) := by
  have hint : IsIntegral C z := (isAlgebraic_iff_isIntegral).mp ⟨p, hp, hz⟩
  have h : (minpoly C z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible C (minpoly.irreducible hint)
  have hmon := minpoly.monic hint
  have e := minpoly.aeval C z
  rw [eq_X_add_C_of_degree_eq_one h, hmon.leadingCoeff, C_1, one_mul, map_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at e
  exact ⟨-(minpoly C z).coeff 0, by rw [map_neg]; exact e.symm⟩

variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- **A function without poles is algebraic over the constants.** -/
theorem algebraic_of_noPoles (z : C⟮S.x⟯⟮S.y⟯)
    (hfin : S.PoleBoundFin (AlgebraicClosure C) z 1)
    (hinf : S.PoleBoundInf (AlgebraicClosure C) z 0) :
    ∃ p : C[X], p ≠ 0 ∧ aeval (z : L) p = 0 := by
  classical
  set K := AlgebraicClosure C
  set n := S.F.natDegree with hn
  set B0 := 1 * 0 + 0 + ((n - 1) * (n - 1) + (n - 1)) * S.degB with hB0
  -- no poles for the powers
  have hfinN : ∀ N : ℕ, S.PoleBoundFin K (z ^ N) 1 := fun N a M hM r hsplit k ↦ by
    have := (hfin a M hM r hsplit k).pow N
    have h1 : rootMultiplicity a (1 : K[X]) = 0 := rootMultiplicity_eq_zero (by simp)
    rw [map_pow]
    simp only [Polynomial.map_one, h1, mul_zero, Nat.cast_zero, neg_zero] at this ⊢
    simpa using this
  have hinfN : ∀ N : ℕ, S.PoleBoundInf K (z ^ N) 0 := fun N M hM r hsplit k ↦ by
    have := (hinf M hM r hsplit k).pow N
    rw [map_pow]
    simp only [mul_zero, Nat.cast_zero, neg_zero] at this ⊢
    simpa using this
  have hans : ∀ N : ℕ, ∃ W : C[X][X], W.natDegree < n ∧ (∀ j, (W.coeff j).natDegree ≤ B0) ∧
      ((z ^ N : C⟮S.x⟯⟮S.y⟯) : L) * aeval S.x (S.discR * 1) = S.evXY W := fun N ↦ by
    obtain ⟨W, h1, h2, h3⟩ := S.ansatz (K := K) (z ^ N) 1 one_ne_zero 0 (hfinN N) (hinfN N)
    refine ⟨W, h1, fun j ↦ (h2 j).trans (le_of_eq ?_), h3⟩
    rw [hB0, natDegree_one]
  choose W hWn hWc hWz using hans
  -- linear dependence of the coefficient vectors
  set M := n * (B0 + 1) with hM
  let v : Fin (M + 1) → (Fin n × Fin (B0 + 1) → C) := fun k ie ↦ ((W k).coeff ie.1).coeff ie.2
  have hnot : ¬LinearIndependent C v := fun hli ↦ by
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, k0, hk0⟩ := Fintype.not_linearIndependent_iff.mp hnot
  -- the relation among the numerators
  set Wt : C[X][X] := ∑ k, Polynomial.C (Polynomial.C (g k)) * W k with hWt
  have hWt0 : Wt = 0 := by
    ext i e
    rw [hWt, finsetSum_coeff, finsetSum_coeff, Polynomial.coeff_zero, Polynomial.coeff_zero]
    simp only [coeff_C_mul]
    by_cases hi : i < n
    · by_cases he : e ≤ B0
      · have := congrFun hg (⟨i, hi⟩, ⟨e, Nat.lt_succ_of_le he⟩)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
        exact this
      · refine Finset.sum_eq_zero fun k _ ↦ ?_
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hWc k i) (by omega)), mul_zero]
    · refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hWn k) (not_lt.mp hi))]
      simp
  -- `z` is algebraic over `C`
  set p : C[X] := ∑ k, Polynomial.C (g k) * X ^ (k : ℕ) with hp
  have hp0 : p ≠ 0 := by
    intro h0
    have := congrArg (fun P ↦ P.coeff (k0 : ℕ)) h0
    simp only [hp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single k0 (fun b _ hb ↦ by
      rw [if_neg (fun h ↦ hb (Fin.ext h.symm)), mul_zero]) (by simp), if_pos rfl, mul_one] at this
    exact hk0 this
  have hD0 : aeval S.x (S.discR * 1) ≠ 0 := by
    rw [mul_one]; exact fun h ↦ S.discR_ne_zero (by
      by_contra hne; exact S.htr ⟨_, hne, h⟩)
  have hpz : aeval (z : L) p = 0 := by
    have hsum : S.evXY Wt = aeval (z : L) p * aeval S.x (S.discR * 1) := by
      have e1 : S.evXY Wt = ∑ k, algebraMap C L (g k) * S.evXY (W k) := by
        simp [hWt, CurveData.evXY, Polynomial.map_sum, eval_finset_sum]
      rw [e1, hp, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← hWz k]
      simp only [map_mul, aeval_C, map_pow, aeval_X, SubmonoidClass.coe_pow]
      ring
    rw [hWt0] at hsum
    have : S.evXY (0 : C[X][X]) = 0 := by simp [CurveData.evXY]
    rw [this] at hsum
    exact (mul_eq_zero.mp hsum.symm).resolve_right hD0
  exact ⟨p, hp0, hpz⟩

/-- **A function without poles is constant** (algebraically closed constants). -/
theorem const_of_noPoles [IsAlgClosed C] (z : C⟮S.x⟯⟮S.y⟯)
    (hfin : S.PoleBoundFin (AlgebraicClosure C) z 1)
    (hinf : S.PoleBoundInf (AlgebraicClosure C) z 0) :
    (z : L) ∈ Set.range (algebraMap C L) := by
  obtain ⟨p, hp0, hpz⟩ := S.algebraic_of_noPoles z hfin hinf
  exact mem_range_of_aeval_eq_zero (z : L) p hp0 hpz

/-- **A function without poles is constant**, when all constants of `L` lie in `C`. -/
theorem const_of_noPoles' (hC : ∀ c : C, c′ = 0)
    (hconst : ∀ w : L, w′ = 0 → w ∈ Set.range (algebraMap C L)) (z : C⟮S.x⟯⟮S.y⟯)
    (hfin : S.PoleBoundFin (AlgebraicClosure C) z 1)
    (hinf : S.PoleBoundInf (AlgebraicClosure C) z 0) :
    (z : L) ∈ Set.range (algebraMap C L) := by
  obtain ⟨p, hp0, hpz⟩ := S.algebraic_of_noPoles z hfin hinf
  refine hconst _ ?_
  by_contra hne
  exact transcendental_of_deriv_ne_zero hC hne ⟨p, hp0, hpz⟩

end CurveData

end Const

end Curves

namespace Curves

open Differential LaurentSeries

section LogSum

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- **The structure of logarithmic sums on a curve**: if `Z′ = ∑ cᵢ uᵢ′/uᵢ` with constant `cᵢ`
and `Z, uᵢ` in the function field, then `Z` is constant. -/
theorem logsum_const_gen (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ w : L, w′ = 0 → w ∈ Set.range (algebraMap C L))
    (Z : L) (hZ : Z ∈ C⟮S.x⟯⟮S.y⟯) {ι : Type*} (s : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (hd : Z′ = ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    Z ∈ Set.range (algebraMap C L) := by
  set K := AlgebraicClosure C
  have hv : -Z ∈ C⟮S.x⟯⟮S.y⟯ := neg_mem hZ
  have heq : (0 : L) = (-Z)′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i) := by
    rw [map_neg, hd, neg_add_cancel]
  have hbr : ∀ (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
      (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
      (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0),
      LowerBd (S.embG g hg Y hY ⟨Z, hZ⟩) 0 := by
    intro Xh hX g hg hgX Y hY
    have h := (S.liouville_local Xh hX g hg hgX hC hx Y hY s c u hu hu0 (-Z) 0 hv (zero_mem _)
      heq).2 0 (by
        have : S.embG g hg Y hY ⟨0, zero_mem _⟩ = 0 := by
          rw [show (⟨0, zero_mem _⟩ : C⟮S.x⟯⟮S.y⟯) = 0 from rfl, map_zero]
        rw [this, zero_mul]; exact lowerBd_zero _)
    have e : S.embG g hg Y hY ⟨-Z, hv⟩ = -S.embG g hg Y hY ⟨Z, hZ⟩ := by
      rw [← map_neg]; rfl
    rw [e] at h
    simpa using h.neg
  have hfin : S.PoleBoundFin K ⟨Z, hZ⟩ 1 := fun a N hN r hsplit k ↦ by
    have h1 : rootMultiplicity a (1 : K[X]) = 0 := rootMultiplicity_eq_zero (by simp)
    simp only [Polynomial.map_one, h1, mul_zero, Nat.cast_zero, neg_zero]
    exact hbr _ (hX_fin N (Nat.pos_of_ne_zero hN) a) (branchSub N a)
      (branchSub_injective N (Nat.pos_of_ne_zero hN) a)
      (fun P ↦ by rw [SuperData.branchSub_eq_subst]) (r k) (S.root_of_split _ r hsplit k)
  have hinf : S.PoleBoundInf K ⟨Z, hZ⟩ 0 := fun N hN r hsplit k ↦ by
    simp only [mul_zero, Nat.cast_zero, neg_zero]
    exact hbr _ (hX_inf N (Nat.pos_of_ne_zero hN)) (infSub N)
      (infSub_injective N (Nat.pos_of_ne_zero hN))
      (fun P ↦ by rw [SuperData.infSub_eq_subst]) (r k) (S.root_of_split _ r hsplit k)
  exact S.const_of_noPoles' hC hconst ⟨Z, hZ⟩ hfin hinf

end CurveData

end LogSum

end Curves
