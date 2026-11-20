import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable

/-!
# The discriminant of the short model of a squarefree cubic

For `p = c₃X³ + c₂X² + c₁X + c₀` (`c₃ ≠ 0`, squarefree, characteristic `0`), the short model
`x³ + a x + b`, `a = c₁c₃ − c₂²/3`, `b = c₀c₃² − c₂c₁c₃/3 + 2c₂³/27`, is nonsingular:
`4a³ + 27b² = −c₃² disc(p) ≠ 0` (`short_disc_ne_zero`).
-/

open Polynomial

namespace CubicDisc

variable {F : Type*} [Field F] [CharZero F]

lemma short_disc_eq (c3 c2 c1 c0 : F) :
    4 * (c1 * c3 - c2 ^ 2 / 3) ^ 3 + 27 * (c0 * c3 ^ 2 - c2 * c1 * c3 / 3 + 2 * c2 ^ 3 / 27) ^ 2 =
      -c3 ^ 2 * (⟨c3, c2, c1, c0⟩ : Cubic F).discr := by
  simp only [Cubic.discr]; ring

/-- **The short model of a squarefree cubic is nonsingular.** -/
theorem short_disc_ne_zero (c3 c2 c1 c0 : F) (hc3 : c3 ≠ 0)
    (hsq : Squarefree (C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0)) :
    4 * (c1 * c3 - c2 ^ 2 / 3) ^ 3 + 27 * (c0 * c3 ^ 2 - c2 * c1 * c3 / 3 + 2 * c2 ^ 3 / 27) ^ 2 ≠ 0 := by
  rw [short_disc_eq]
  refine mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hc3)) ?_
  set P : Cubic F := ⟨c3, c2, c1, c0⟩
  haveI : CharZero (AlgebraicClosure F) :=
    charZero_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective
  set φ := algebraMap F (AlgebraicClosure F)
  have hsplit : (P.toPoly.map φ).Splits := IsAlgClosed.splits _
  rw [Cubic.discr_ne_zero_iff_roots_nodup (φ := φ) hc3 hsplit]
  have hsep : P.toPoly.Separable := by
    rw [show P.toPoly = C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0 from rfl]
    exact PerfectField.separable_iff_squarefree.mpr hsq
  rw [Cubic.roots, Cubic.map_toPoly]
  exact nodup_roots (hsep.map)

end CubicDisc
