import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Extension of a derivation from an integral domain to its field of fractions.

Mathlib (v4.34.0) provides `Differential` and `Polynomial.implicitDeriv`, but no way to push a
derivation through a localization. This is the first brick of the Risch–Trager–Bronstein
development: every monomial extension `F(t)` gets its derivation from `F[t]` this way.

The construction avoids a hand-rolled quotient rule. A derivation `d : A → K` is the same thing as
a ring hom `A → K[ε]`, `a ↦ a + ε (d a)`, into the dual numbers `TrivSqZeroExt K K`. Nonzero
elements of `A` land on units of `K[ε]` (a unit plus a nilpotent), so the universal property of the
localization extends the ring hom to `K`, and the `ε`-component of the extension is the derivation.
-/

open TrivSqZeroExt

namespace Differential

variable (A K : Type*) [CommRing A] [Differential A] [Field K] [Algebra A K]

/-- The ring hom `A → K[ε]`, `a ↦ a + ε a′`, encoding the derivation of `A` with values in `K`. -/
def dualNumberHom : A →+* TrivSqZeroExt K K where
  toFun a := inl (algebraMap A K a) + inr (algebraMap A K a′)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext
    · simp
    · simp

@[simp] lemma fst_dualNumberHom (a : A) : (dualNumberHom A K a).fst = algebraMap A K a := by
  simp [dualNumberHom]

@[simp] lemma snd_dualNumberHom (a : A) : (dualNumberHom A K a).snd = algebraMap A K a′ := by
  simp [dualNumberHom]

variable [IsDomain A] [IsFractionRing A K]

lemma isUnit_dualNumberHom (y : nonZeroDivisors A) : IsUnit (dualNumberHom A K y) := by
  rw [isUnit_iff_isUnit_fst, fst_dualNumberHom, isUnit_iff_ne_zero]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2

/-- The extension `K → K[ε]` of `dualNumberHom` to the fraction field. -/
noncomputable def fractionDualNumberHom : K →+* TrivSqZeroExt K K :=
  IsLocalization.lift (M := nonZeroDivisors A) (isUnit_dualNumberHom A K)

@[simp] lemma fractionDualNumberHom_algebraMap (a : A) :
    fractionDualNumberHom A K (algebraMap A K a) = dualNumberHom A K a :=
  IsLocalization.lift_eq _ a

@[simp] lemma fst_fractionDualNumberHom (x : K) : (fractionDualNumberHom A K x).fst = x := by
  have h : (fstHom K K K : TrivSqZeroExt K K →+* K).comp (fractionDualNumberHom A K) =
      RingHom.id K :=
    IsLocalization.ringHom_ext (nonZeroDivisors A) (by ext a; simp)
  exact congr($h x)

/-- The derivation of `K = Frac A` extending the one of `A`. -/
noncomputable def fractionRingDerivation : Derivation ℤ K K where
  toFun x := (fractionDualNumberHom A K x).snd
  map_add' x y := by simp
  map_smul' n x := by simp
  map_one_eq_zero' := by simp
  leibniz' x y := by simp [mul_comm]

/-- The `Differential` structure on the fraction field `K` of a differential domain `A`.
Not an instance: `K` is an arbitrary fraction field and may carry other structures. -/
@[reducible] noncomputable def ofFractionRing : Differential K := ⟨fractionRingDerivation A K⟩

lemma ofFractionRing_deriv_algebraMap (a : A) :
    letI := ofFractionRing A K
    (algebraMap A K a)′ = algebraMap A K a′ := by
  simp [Differential.deriv, fractionRingDerivation]

/-- `A → Frac A` is a morphism of differential rings. -/
lemma differentialAlgebra_ofFractionRing :
    letI := ofFractionRing A K
    DifferentialAlgebra A K :=
  letI := ofFractionRing A K
  ⟨ofFractionRing_deriv_algebraMap A K⟩

/-- The quotient rule with denominators cleared: `(a / b)′ = 0` iff `a′ b = a b′`. Stated for
elements of `A` so that it can be used on concrete fraction fields (such as `RatFunc`) whose
`ℤ`-algebra instance is not syntactically `Ring.toIntAlgebra`. -/
lemma ofFractionRing_deriv_div_eq_zero_iff (a b : A) (hb : b ≠ 0) :
    letI := ofFractionRing A K
    (algebraMap A K a / algebraMap A K b)′ = 0 ↔ a′ * b = a * b′ := by
  let _ := ofFractionRing A K
  have hb' : algebraMap A K b ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hb
  rw [Derivation.leibniz_div, ofFractionRing_deriv_algebraMap, ofFractionRing_deriv_algebraMap,
    smul_eq_zero, or_iff_right (by simpa using hb'), smul_eq_mul, smul_eq_mul, sub_eq_zero,
    ← map_mul, ← map_mul, (IsFractionRing.injective A K).eq_iff]
  constructor <;> intro h <;> linear_combination h

/-- The quotient rule for fractions of elements of `A`. -/
lemma ofFractionRing_deriv_div (a b : A) (hb : b ≠ 0) :
    letI := ofFractionRing A K
    (algebraMap A K a / algebraMap A K b)′ =
      algebraMap A K (a′ * b - a * b′) / algebraMap A K b ^ 2 := by
  let _ := ofFractionRing A K
  have hb' : algebraMap A K b ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hb
  rw [Derivation.leibniz_div, ofFractionRing_deriv_algebraMap, ofFractionRing_deriv_algebraMap,
    map_sub, map_mul, map_mul]
  simp only [smul_eq_mul]
  field_simp

omit [Differential A] [IsDomain A] in
/-- Uniqueness: a derivation of `Frac A` is determined by its values on `A`. -/
lemma fractionRing_derivation_ext {D₁ D₂ : Derivation ℤ K K}
    (h : ∀ a : A, D₁ (algebraMap A K a) = D₂ (algebraMap A K a)) : D₁ = D₂ := by
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [Derivation.leibniz_div, h]

end Differential
