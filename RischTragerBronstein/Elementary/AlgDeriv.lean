import RischTragerBronstein.Elementary.AlgDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The derivation of an algebraic extension

For an algebraic extension `A / E` of a differential field `E` of characteristic zero, the
derivation of `E` extends (uniquely) to `A`: every `z ∈ A` with minimal polynomial `p` over `E`
must have `z′ = −p^D(z) / p′(z)` (`deriv_eq_algDerivFun`, `p^D` the polynomial with differentiated
coefficients). That formula is additive and satisfies the Leibniz rule because on every finite
subextension `E⟮z, w⟯` it agrees with the derivation Mathlib constructs there
(`differentialFiniteDimensional`).

* `algDifferential E A`, `algDifferentialAlgebra`: the derivation on `A` and its compatibility;
* in particular the algebraic closure of a differential field is a differential field over it.
-/

open IntermediateField Polynomial

namespace Differential

universe u v

variable {E : Type u} [Field E] [Differential E] [CharZero E]

section Formula

variable {A : Type v} [Field A] [Algebra E A]

variable (E) in
/-- The derivative forced on an element algebraic over `E`. -/
noncomputable def algDerivFun (z : A) : A :=
  -(aeval z (mapCoeffs (minpoly E z))) / aeval z (derivative (minpoly E z))

/-- **The derivative of an algebraic element** is forced by its minimal polynomial. -/
lemma deriv_eq_algDerivFun {B : Type*} [Field B] [Differential B] [Algebra E B]
    [DifferentialAlgebra E B] (z : B) (hz : IsIntegral E z) : z′ = algDerivFun E z := by
  have hsep : (minpoly E z).Separable := (minpoly.irreducible hz).separable
  have hp : aeval z (minpoly E z) = 0 := minpoly.aeval E z
  have hne : aeval z (derivative (minpoly E z)) ≠ 0 := hsep.aeval_derivative_ne_zero hp
  have h := deriv_aeval_eq z (minpoly E z)
  rw [hp, map_zero] at h
  unfold algDerivFun
  field_simp
  linear_combination -h

/-- On a finite subextension, the formula is the derivation of that subextension. -/
lemma algDerivFun_coe (M : IntermediateField E A) [FiniteDimensional E M] (u : M) :
    algDerivFun E (u : A) = ((u′ : M) : A) := by
  have hu : IsIntegral E u := Algebra.IsIntegral.isIntegral u
  rw [deriv_eq_algDerivFun u hu]
  unfold algDerivFun
  rw [IntermediateField.minpoly_eq u, IntermediateField.coe_div, IntermediateField.coe_neg]
  have h1 := Polynomial.aeval_algHom_apply M.val u (mapCoeffs (minpoly E (u : A)))
  have h2 := Polynomial.aeval_algHom_apply M.val u (derivative (minpoly E (u : A)))
  simp only [IntermediateField.coe_val] at h1 h2
  rw [h1, h2]

end Formula

section Extension

variable (A : Type v) [Field A] [Algebra E A] [Algebra.IsAlgebraic E A]

/-- The pair `E⟮z, w⟯` is finite-dimensional. -/
lemma finiteDimensional_pair (z w : A) : FiniteDimensional E (E⟮z, w⟯ : IntermediateField E A) :=
  IntermediateField.finiteDimensional_adjoin_pair (Algebra.IsIntegral.isIntegral z)
    (Algebra.IsIntegral.isIntegral w)

lemma algDerivFun_add (z w : A) :
    algDerivFun E (z + w) = algDerivFun E z + algDerivFun E w := by
  haveI := finiteDimensional_pair (E := E) A z w
  set M : IntermediateField E A := E⟮z, w⟯
  have hz : z ∈ M := subset_adjoin E _ (by simp)
  have hw : w ∈ M := subset_adjoin E _ (by simp)
  have e : z + w = (((⟨z, hz⟩ : M) + ⟨w, hw⟩ : M) : A) := rfl
  have hz' : algDerivFun E z = (((⟨z, hz⟩ : M)′ : M) : A) := algDerivFun_coe M ⟨z, hz⟩
  have hw' : algDerivFun E w = (((⟨w, hw⟩ : M)′ : M) : A) := algDerivFun_coe M ⟨w, hw⟩
  rw [e, algDerivFun_coe M, map_add, IntermediateField.coe_add, hz', hw']

lemma algDerivFun_mul (z w : A) :
    algDerivFun E (z * w) = z * algDerivFun E w + w * algDerivFun E z := by
  haveI := finiteDimensional_pair (E := E) A z w
  set M : IntermediateField E A := E⟮z, w⟯
  have hz : z ∈ M := subset_adjoin E _ (by simp)
  have hw : w ∈ M := subset_adjoin E _ (by simp)
  have e : z * w = (((⟨z, hz⟩ : M) * ⟨w, hw⟩ : M) : A) := rfl
  have hz' : algDerivFun E z = (((⟨z, hz⟩ : M)′ : M) : A) := algDerivFun_coe M ⟨z, hz⟩
  have hw' : algDerivFun E w = (((⟨w, hw⟩ : M)′ : M) : A) := algDerivFun_coe M ⟨w, hw⟩
  rw [e, algDerivFun_coe M, Derivation.leibniz, IntermediateField.coe_add, hz', hw']
  simp only [smul_eq_mul, IntermediateField.coe_mul]

lemma algDerivFun_algebraMap (e : E) : algDerivFun E (algebraMap E A e) = algebraMap E A e′ := by
  haveI := finiteDimensional_pair (E := E) A (algebraMap E A e) (algebraMap E A e)
  set M : IntermediateField E A := E⟮algebraMap E A e, algebraMap E A e⟯
  rw [show algebraMap E A e = ((algebraMap E M e : M) : A) from rfl, algDerivFun_coe M,
    deriv_algebraMap]
  rfl

/-- **The derivation of an algebraic extension.** -/
@[instance_reducible]
noncomputable def algDifferential : Differential A :=
  ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    (AddMonoidHom.mk' (algDerivFun E) (algDerivFun_add A)))
    fun a b ↦ by
      simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
      exact algDerivFun_mul A a b⟩

lemma algDifferential_deriv (z : A) :
    (letI := algDifferential (E := E) A; z′) = algDerivFun E z := rfl

lemma algDifferentialAlgebra :
    letI := algDifferential (E := E) A
    DifferentialAlgebra E A := by
  letI := algDifferential (E := E) A
  exact ⟨fun e ↦ algDerivFun_algebraMap A e⟩

end Extension

/-- The algebraic closure of a differential field, as a differential field over it. -/
noncomputable instance instDifferentialAlgebraicClosure : Differential (AlgebraicClosure E) :=
  algDifferential (E := E) (AlgebraicClosure E)

instance instDifferentialAlgebraAlgebraicClosure : DifferentialAlgebra E (AlgebraicClosure E) :=
  algDifferentialAlgebra (E := E) (AlgebraicClosure E)

end Differential
