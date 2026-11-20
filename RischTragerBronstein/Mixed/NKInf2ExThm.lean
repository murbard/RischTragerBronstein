import RischTragerBronstein.Mixed.NKInf2ExRes

/-! `NKInf2Example.not_elementary` with its exact-part hypothesis discharged by the staged kernel
check `NKInf2ExRes.hresK`. -/

namespace Curves.MT.NKInf2Ex

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx Polynomial Differential GTors

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is not elementary** (two places at infinity), with no computational hypothesis. -/
theorem not_elementary_full (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp2.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fp.getD j []) * θ ^ j) :=
  not_elementary T hn θ hθ hgen hresK

end Curves.MT.NKInf2Ex
