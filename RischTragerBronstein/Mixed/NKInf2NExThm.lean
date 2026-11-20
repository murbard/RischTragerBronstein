import RischTragerBronstein.Mixed.NKInf2NExRes

/-! `NKInf2NExample.elementary` with its exact-part hypothesis discharged by the staged kernel check
`NKInf2NExRes` (`Stg.hresK`). -/

namespace Curves.MT.NKInf2NEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx Polynomial Differential GTors

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ/x dx` is elementary** for `θ² = 1 − log²x`, with no computational hypothesis. -/
theorem elementary_full (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fp.getD j []) * θ ^ j) :=
  elementary T hn θ hθ hgen Stg.hresK

end Curves.MT.NKInf2NEx
