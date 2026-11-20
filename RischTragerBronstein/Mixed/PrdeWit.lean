import RischTragerBronstein.Mixed.KRPrde

/-!
# Parametric Risch equations: the antiderivative

For `θⁿ = A` and a solution `r` of the parametric Risch equation
`y′ + (j/n)(A′/A) y = q₀ rhs + ∑ₖ qₖ colₖ` with `q₀ ≠ 0` (`prdeC`),

  `rhs θʲ = ((y/q₀) θʲ)′ + ∑ₖ (−qₖ/q₀) colₖ θʲ`   (`prde_param_eqN`).

`prdeSolN` returns such a solution (`prdeSolN_isSome`: exactly when the deciders' `any` holds).
-/

open Polynomial CPoly Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- A solution of the parametric equation with a non-zero first coefficient. -/
def prdeSolN (m : ℕ) (fr : FRep (LC (m + 1))) (rhs : LC (m + 1)) (cols : List (LC (m + 1))) :
    Option (List ℚ × LC (m + 1)) :=
  (prdeC Fc ks lv (m + 1) fr (rhs :: cols)).find? fun r ↦ decide (r.1.getD 0 0 ≠ 0)

lemma prdeSolN_isSome (m : ℕ) (fr : FRep (LC (m + 1))) (rhs : LC (m + 1))
    (cols : List (LC (m + 1))) :
    (prdeSolN Fc ks lv m fr rhs cols).isSome =
      (prdeC Fc ks lv (m + 1) fr (rhs :: cols)).any fun r ↦ decide (r.1.getD 0 0 ≠ 0) := by
  rw [prdeSolN, Bool.eq_iff_iff, List.find?_isSome, List.any_eq_true]

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The antiderivative of a parametric solution**: the integrand is the derivative of
`(y/q₀) θʲ` plus the columns times `θʲ`. -/
theorem prde_param_eqN (m n j : ℕ) (hn : 0 < n) (hTr : T.Tr (m + 1)) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ n = T.evP m A) (hA0 : T.evP m A ≠ 0)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (rhs : LC (m + 1)) (cols : List (LC (m + 1))) (r : List ℚ × LC (m + 1))
    (hr : r ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A) (rhs :: cols))
    (hq0 : r.1.getD 0 0 ≠ 0) :
    T.ev (m + 1) rhs * θ ^ j = ((T.ev (m + 1) r.2 / (r.1.getD 0 0 : L)) * θ ^ j)′ +
      ∑ k : Fin cols.length, ((-(r.1.getD (k + 1) 0) / r.1.getD 0 0 : ℚ) : L) *
        (T.ev (m + 1) cols[k] * θ ^ j) := by
  have hs := hspec.sound (rhs :: cols) r hr
  have hlen : (rhs :: cols).length = cols.length + 1 := by simp
  have hsQ : sQ (T.MP (m + 1) hTr) r.1 (rhs :: cols) =
      ((r.1.getD 0 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem rhs +
        ∑ k : Fin cols.length, ((r.1.getD (k + 1) 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) hTr).sem cols[k] := by
    unfold sQ
    rw [hlen, Finset.sum_range_succ']
    refine (add_comm _ _).trans ?_
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [List.getD_eq_getElem _ _ k.2]
    rfl
  rw [hsQ] at hs
  have hsL := congrArg Subtype.val hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv,
    IntermediateField.coe_sum] at hsL
  rw [T.sem_kpFr m hTr] at hsL
  simp only [T.sem_MP (m + 1) hTr] at hsL
  set a : L := T.ev (m + 1) r.2
  set q0 : ℚ := r.1.getD 0 0
  have hq0L : (q0 : L) ≠ 0 := by exact_mod_cast hq0
  have h1 := deriv_mul_radical θ (T.evP m A) n hn hθ hA0 (a / q0) j
  have hf : T.ev (m + 1) rhs * θ ^ j = ((a / q0) * θ ^ j)′ + ∑ k : Fin cols.length,
      ((-(r.1.getD (k + 1) 0) / q0 : ℚ) : L) * (T.ev (m + 1) cols[k] * θ ^ j) := by
    rw [h1]
    have hq0d : ((q0 : L))′ = 0 := Tower.NestP.deriv_ratCastK (K := L) q0
    have hd : (a / (q0 : L))′ = a′ / q0 := by
      rw [div_eq_mul_inv a, Derivation.leibniz, Derivation.leibniz_inv, hq0d, div_eq_mul_inv]
      simp only [smul_zero, smul_eq_mul, mul_zero, zero_add, neg_zero]
      ring
    rw [hd]
    have hsum : ∑ k : Fin cols.length, ((-(r.1.getD (k + 1) 0) / q0 : ℚ) : L) *
        (T.ev (m + 1) cols[k] * θ ^ j) =
        -(∑ k : Fin cols.length, ((r.1.getD (k + 1) 0 : ℚ) : L) * T.ev (m + 1) cols[k]) * θ ^ j / q0 := by
      rw [div_eq_mul_inv, neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast; field_simp
    rw [hsum]
    generalize T.ev (m + 1) rhs = R at hsL ⊢
    push_cast at hsL ⊢
    field_simp
    linear_combination (-θ ^ j : L) * hsL
  exact hf

end MTower

end Curves.MT
