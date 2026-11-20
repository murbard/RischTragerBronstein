import RischTragerBronstein.Mixed.KPExact
import RischTragerBronstein.Mixed.MTFinal

/-!
# Kummer radicals over a logarithmic level of a mixed tower: helpers

* `not_deriv_of_integral`: if `η ∈ C` has no antiderivative in `C`, it has none among the
  elements algebraic over `C` (the minimal polynomial `p` of an antiderivative `α` would divide
  `p^δ + η p′`, of smaller degree, so `p^δ = −η p′`, and the coefficient of `X^{d−1}` gives
  `η = (−p_{d−1}/d)′`);
* `rdeOKFr_iff`: the Risch equation `y′ + f y = w` with `f` the value of an `FRep` is solvable iff
  the parametric solver returns a solution with non-zero parameter.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

/-- **No antiderivative among the algebraic elements.** -/
theorem not_deriv_of_integral {C A : Type*} [Field C] [Field A] [Differential C] [Differential A]
    [Algebra C A] [DifferentialAlgebra C A] [CharZero C] (η : C) (hη : ∀ z : C, z′ ≠ η)
    (α : A) (hα : IsIntegral C α) : α′ ≠ algebraMap C A η := by
  intro hd
  set p := minpoly C α with hp
  have hmon : p.Monic := minpoly.monic hα
  have hd0 : 0 < p.natDegree := minpoly.natDegree_pos hα
  set q : C[X] := mapCoeffs p + Polynomial.C η * derivative p with hq
  have hqα : aeval α q = 0 := by
    have h := deriv_aeval_eq α p
    rw [minpoly.aeval, map_zero, hd] at h
    rw [hq, map_add, map_mul, aeval_C]
    linear_combination -h
  have hdvd : p ∣ q := minpoly.dvd C α hqα
  have hqdeg : q.natDegree < p.natDegree ∨ q = 0 := by
    by_cases hq0 : q = 0
    · exact Or.inr hq0
    left
    refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_) (Nat.sub_lt hd0 one_pos)
    rw [hq, coeff_add, coeff_mapCoeffs, coeff_C_mul, coeff_derivative]
    rcases Nat.lt_or_ge k p.natDegree with hk1 | hk1
    · omega
    · rcases hk1.lt_or_eq with hk2 | hk2
      · rw [coeff_eq_zero_of_natDegree_lt hk2, coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
      · subst hk2
        rw [hmon.coeff_natDegree, Derivation.map_one_eq_zero,
          coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
  have hq0 : q = 0 := by
    rcases hqdeg with h | h
    · exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd h
    · exact h
  have hc := congrArg (fun r ↦ r.coeff (p.natDegree - 1)) hq0
  simp only [hq, coeff_add, coeff_mapCoeffs, coeff_C_mul, coeff_derivative, coeff_zero] at hc
  rw [Nat.sub_add_cancel hd0, hmon.coeff_natDegree, one_mul] at hc
  have hn : ((p.natDegree - 1 : ℕ) : C) + 1 = (p.natDegree : C) := by
    rw [Nat.cast_sub hd0]; push_cast; ring
  rw [hn] at hc
  have hdC : (p.natDegree : C) ≠ 0 := by exact_mod_cast hd0.ne'
  apply hη (-(p.coeff (p.natDegree - 1)) * ((p.natDegree : C))⁻¹)
  have hinv : (((p.natDegree : C))⁻¹)′ = 0 := by
    rw [Derivation.leibniz_inv, Derivation.map_natCast, smul_zero]
  rw [Derivation.leibniz, hinv, smul_zero, zero_add, smul_eq_mul, map_neg]
  field_simp
  linear_combination -hc

end Differential

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The Risch equation `y′ + f y = w` (`f` the value of `fr`) has a solution, through the
parametric solver. -/
def rdeOKFr (m : ℕ) (fr : FRep (LC m)) (w : LC m) : Bool :=
  (prdeC Fc ks lv m fr [w]).any fun r ↦ decide (r.1.getD 0 0 ≠ 0)

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The Risch-equation check** for an `FRep`, given the specification of `prdeC m`. -/
theorem rdeOKFr_iff (m : ℕ) (h : T.Tr m) (fr : FRep (LC m))
    (hs : RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
      (prdeC Fc ks lv m fr)) (w : LC m) :
    (∃ y : T.F m, y′ + (T.MP m h).sem (fCode (MO Fc ks m) fr) * y = (T.MP m h).sem w) ↔
      rdeOKFr Fc ks lv m fr w = true := by
  classical
  set M := T.MP m h
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨β, hβ, -⟩ := hs.complete [w] [1] (fun i hi ↦ by
      rcases i with _ | i
      · simp at hi
      · rfl) y (by
        rw [hy, sC]
        simp)
    have h1 := hβ 0
    rw [List.getD_cons_zero] at h1
    unfold rdeOKFr
    rw [List.any_eq_true]
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      have : ((prdeC Fc ks lv m fr [w]).getD k ([], (MO Fc ks m).zero)).1.getD 0 0 = 0 := by
        have hmem : (prdeC Fc ks lv m fr [w]).getD k ([], (MO Fc ks m).zero) ∈
            prdeC Fc ks lv m fr [w] := by
          rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
        simpa using hall _ hmem
      rw [this, map_zero, mul_zero]] at h1
    exact one_ne_zero h1
  · intro hok
    unfold rdeOKFr at hok
    obtain ⟨r, hr, hr0⟩ := List.any_eq_true.mp hok
    simp only [decide_eq_true_eq] at hr0
    have hsd := hs.sound [w] r hr
    rw [sQ] at hsd
    simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one,
      Finset.sum_singleton, List.getD_cons_zero] at hsd
    have hq : ((r.1.getD 0 0 : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hr0
    refine ⟨M.sem r.2 / ((r.1.getD 0 0 : ℚ) : T.F m), ?_⟩
    rw [Derivation.leibniz_div, T.deriv_ratCast]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp
    linear_combination hsd

end MTower

end Curves.MT
