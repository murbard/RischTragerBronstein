import RischTragerBronstein.Mixed.CurveRdeLemmas

/-!
# The parametric Risch equation on a curve: values of the codes

For a curve `S` with `S.F = (toB Fc).map ℚ→Kc`, in the model `curveModel`:

* `sem_cvRed`, `length_cvRed`: reduction modulo `F` keeps the value and leaves at most `n`
  coefficients;
* `eval_codeW_red`: the numerator of the reduced code is `Q(x) · value`;
* `sem_bcode`: the value of the basis element `xᵉ yⁱ / den`.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Sem

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

/-- The model of the function field of the curve. -/
noncomputable abbrev cM : CField (GPoly (GFrac ℚ)) E (curveOps Fc) :=
  curveModel (algebraMap ℚ Kc) hC S hx Fc hSF

/-- The model of `ℚ(x)`. -/
noncomputable abbrev xM : CField (GFrac ℚ) E xOps := xModel (algebraMap ℚ Kc) hC S hx

lemma sem_cM (a : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem a = (GPoly.toPoly (xM hC S hx) a).eval S.y := rfl

lemma sem_cvRed (a : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (cvRed Fc a) = (cM hC S hx Fc hSF).sem a := by
  rw [sem_cM, sem_cM, cvRed, GPoly.toPoly_trim]
  exact CField.phi_algRed (xM hC S hx) (curveCodes Fc) (evalRingHom S.y)
    (curveCodes_root (algebraMap ℚ Kc) hC S hx Fc hSF) a

include hC hx hSF in
lemma length_cvRed (a : GPoly (GFrac ℚ)) : (cvRed Fc a).length ≤ S.F.natDegree := by
  have hne : GPoly.trim xOps (curveCodes Fc) ≠ [] := fun h ↦ by
    have := (curveCodes_monic (algebraMap ℚ Kc) hC S hx Fc hSF).ne_zero
    exact this ((GPoly.trim_eq_nil_iff (xM hC S hx) _).mp h)
  have h1 := GPoly.divMod_remainder_lt (xM hC S hx) a (curveCodes Fc) hne
  rw [GPoly.length_trim (xM hC S hx) hne,
    curveCodes_natDegree (algebraMap ℚ Kc) hC S hx Fc hSF] at h1
  rw [cvRed, GPoly.algRed]
  omega

/-- The numerator of a reduced code over its denominator. -/
lemma eval_codeW (a : GPoly (GFrac ℚ)) :
    (((toB (codeW a)).map (mapRingHom (algebraMap ℚ Kc))).map (aeval S.x).toRingHom).eval S.y =
      aeval S.x ((toPoly (codeQ a)).map (algebraMap ℚ Kc)) * (cM hC S hx Fc hSF).sem a :=
  sem_codeFrac (algebraMap ℚ Kc) hC S hx a

lemma aeval_codeQ_ne_zero (a : GPoly (GFrac ℚ)) :
    aeval S.x ((toPoly (codeQ a)).map (algebraMap ℚ Kc)) ≠ 0 :=
  aeval_x_ne_zero' S _ ((Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr
    (codeQ_ne_zero a))

/-- The value of `xᵉ yⁱ / den`. -/
lemma sem_bcode (den : CPoly ℚ) (i e : ℕ) :
    (cM hC S hx Fc hSF).sem (bcode den i e) =
      S.x ^ e / aeval S.x ((toPoly den).map (algebraMap ℚ Kc)) * S.y ^ i := by
  rw [sem_cM, bcode, GPoly.toPoly_append, eval_add, eval_mul, eval_pow, eval_X]
  have hrep : ∀ m : ℕ, GPoly.toPoly (xM hC S hx) (List.replicate m (([], [1]) : GFrac ℚ)) = 0 :=
    fun m ↦ by
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [List.replicate_succ, GPoly.toPoly_cons, ih, sem_xModel]
        simp [CPoly.toPoly]
  rw [hrep, eval_zero, zero_add, List.length_replicate, GPoly.toPoly_cons, GPoly.toPoly_nil,
    mul_zero, add_zero, eval_C, sem_xModel]
  have hz : toPoly (List.replicate e (0 : ℚ)) = 0 := by rw [← isZero_iff]; simp [isZero]
  simp [xPowC, CPoly.toPoly_append, CPoly.toPoly, hz]
  ring

end Sem

end Curves
