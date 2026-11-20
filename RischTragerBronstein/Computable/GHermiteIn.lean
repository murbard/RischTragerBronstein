import RischTragerBronstein.Computable.GHermiteComplete

/-!
# Soundness of generic Hermite reduction in an arbitrary fraction-field model

`hermiteCheck_sound` reads the Hermite certificate in `RatFunc K`. Here the same certificate is read
in **any** differential field `L` that is a fraction field of `K[X]` with `P′ = implicitDeriv W P`
— in particular in the subfields `F⟮t⟯ ⊆ E` over extended constants, as needed for completeness
statements at every tower level.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K L : Type*} [Field K] [CharZero K] [Differential K] {O : COps α} (M : CField α K O)
variable [Field L] [Differential L] [Algebra K[X] L] [IsFractionRing K[X] L]
variable [Differential K[X]] [DifferentialAlgebra K[X] L]

theorem hermiteCheck_sound_in (w A D : GPoly α) (r : HermiteResult α)
    (hD : ∀ P : K[X], P′ = implicitDeriv (toPoly M w) P)
    (hc : hermiteCheck O w A D r = true) :
    algebraMap K[X] L (toPoly M A) / algebraMap K[X] L (toPoly M D) =
      (algebraMap K[X] L (toPoly M r.gn) / algebraMap K[X] L (toPoly M r.gd))′ +
        algebraMap K[X] L (toPoly M r.b) / algebraMap K[X] L (toPoly M r.s) ∧
    Squarefree (toPoly M r.s) := by
  obtain ⟨hD0, hgd0, hs0, hid, hsq⟩ := (hermiteCheck_iff M w A D r).mp hc
  refine ⟨?_, squarefreeCheck_sound M hsq⟩
  have hinj : Function.Injective (algebraMap K[X] L) := IsFractionRing.injective K[X] L
  have h1 : algebraMap K[X] L (toPoly M D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have h2 : algebraMap K[X] L (toPoly M r.gd) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hgd0
  have h3 : algebraMap K[X] L (toPoly M r.s) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  have hidL := congrArg (algebraMap K[X] L) hid
  simp only [map_mul, map_add, map_sub] at hidL
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
  simp only [smul_eq_mul]
  field_simp
  linear_combination hidL

end GPoly
