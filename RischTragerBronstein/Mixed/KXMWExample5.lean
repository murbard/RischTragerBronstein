import RischTragerBronstein.Mixed.KXMWExample4
import RischTragerBronstein.Mixed.KXCertBridgeCK

/-!
# Example: a constant curve, `D` and `P₊` in the same square class

`∫ √(e³ˣ − eˣ + 4) / (eˣ − 1) dx`: on `θ² = t³ − t + 4` the pole `t = 1` gives `P = (1, 2)` and
`A(0) = 4` gives `P₊ = (0, 2)`, both rational. `kxDecide` answers `none`. The two points are
independent in `E(ℚ)` (`y² = x³ − x + 4`): the two-point certificate with the logarithmic height
over `ℚ` (`QHeight.certG`, level `3`, kernel-checked; parallelogram bound `QHeight.hP_par`) gives the
group condition (`grp_of_chkTK`), so **the integral is not elementary** (`not_elementary_mw5`).
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly Sup Polynomial Differential Tower.NestM

/-- `A(t) = t³ − t + 4`. -/
def A5 : GPoly (LC 0) := [[([4], [1])], cm1, c0, c1]

#guard kxDecide Fc ks lv 0 xc A5 [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none

set_option maxRecDepth 200000 in
lemma hsqc5 : GPoly.squarefreeCheck (MO Fc ks 0) A5 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hdeg35 : degG (MO Fc ks 0) A5 = 3 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hok5 : kxOK Fc ks 0 A5 [c1] 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcst5 : kxConst Fc ks 0 xc A5 [c1] 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hrep5 : kxRepOK Fc ks 0 xc A5 [c1] 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcls5 : (kxCls Fc ks 0 xc A5 [c1] 0 0 [c1]).length = 1 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hz5 : kxZ Fc ks lv 0 A5 = some z4 :=
  @of_decide_eq_true _ ((inferInstance : DecidableEq (Option (GPoly (GFrac ℚ))))
    (kxZ Fc ks lv 0 A5) (some z4)) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- **The two-point certificate over `ℚ`** and the side checks, kernel-checked. -/
lemma hchk5 : kxChkTK Fc ks [0, -1] xc A5 [c1] 0 0 [c1] z4 ([1], [1]) [-1] [4] 3 0 (-1) 4 2 =
    true := by
  decide +kernel

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 2000000 in
/-- **`∫ √(e³ˣ − eˣ + 4) / (eˣ − 1) dx` is not elementary.** -/
theorem not_elementary_mw5 (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 = T.evP 0 A5) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 1 (([c1], kxDen Fc ks 0 A5 0 0 [c1]) : LC 1) * θ) :=
  T.kx_not_elementary_mwC hmonMW.1 hmonMW.2 0 hn hcertMW rfl A5 hsqc5 (by rw [hdeg35]; norm_num)
    (by rw [hdeg35]; norm_num) hdeg35 θ hθ hgen [c1] 0 0 [c1] hok5 hcst5 hrep5
    ⟨0, by rw [hcls5]; norm_num⟩ z4 hz5
    (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkTK [0, -1] xc A5 [c1] 0 0 [c1] z4 ([1], [1]) [-1] [4] 3 (-1) 4 2 rfl hTm
        ⟨0, by rw [hcls5]; norm_num⟩ hchk5 rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

end Curves.MT.KXEx
