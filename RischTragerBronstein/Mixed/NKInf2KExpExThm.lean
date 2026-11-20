import RischTragerBronstein.Mixed.NKInf2KExpExRes

/-! `NKInf2KExpExample.not_elementary` with its exact-part hypothesis discharged by the kernel check
`NKInf2KExpExRes.hresK`. -/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial Differential

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **`∫ √(e⁴ˣ − e³ˣ + 2e²ˣ + x² eˣ) dx` is not elementary**, with no computational hypothesis
(genus-one curve over `ℚ(x)`). -/
theorem not_elementary_full (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fθ.getD j []) * θ ^ j) :=
  not_elementary T hn θ hθ hgen hresK

end Curves.MT.NKInf2KExpEx
