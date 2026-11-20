import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Embedding quadratic extensions

For a field `F`, `d ∈ F` and a root `r` of `X² − d` in an `F`-algebra `A`, Mathlib's `lift` gives
the `F`-algebra map `F(√d) = QuadraticAlgebra F d 0 → A`, `a + b√d ↦ a + b r` (`qaEmbed`,
`qaEmbed_apply`). Iterating it embeds the executable multi-quadratic fields `ℚ(√κ₁, √κ₂, …)` of the
height certificate into the constants of a realization containing the roots.
-/

namespace NFEmbed

variable {F A : Type*} [Field F] [Ring A] [Algebra F A]

/-- **The embedding** `F(√d) → A`, `√d ↦ r`. -/
noncomputable def qaEmbed (d : F) (r : A) (hr : r * r = algebraMap F A d) :
    QuadraticAlgebra F d 0 →ₐ[F] A :=
  QuadraticAlgebra.lift ⟨r, by rw [hr, Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]⟩

lemma qaEmbed_apply (d : F) (r : A) (hr : r * r = algebraMap F A d) (z : QuadraticAlgebra F d 0) :
    qaEmbed d r hr z = algebraMap F A z.re + algebraMap F A z.im * r := by
  simp [qaEmbed, QuadraticAlgebra.lift, Algebra.smul_def]

lemma qaEmbed_omega (d : F) (r : A) (hr : r * r = algebraMap F A d) :
    qaEmbed d r hr ⟨0, 1⟩ = r := by
  rw [qaEmbed_apply]; simp

end NFEmbed
