import RischTragerBronstein.Mixed.KXMWExample
import RischTragerBronstein.Mixed.KXCertBridgeCK

/-!
# Example: a constant curve in the Mordell–Weil exception

`∫ √(1 + eˣ + e³ˣ) / (eˣ − 1) dx` (`KXExamples`: `kxDecide` answers `none`). The curve
`θ² = t³ + t + 1` has constant coefficients, so function-field heights vanish. The pole `t = 1` gives
`P = (1, √3)` (class `ℚ√3`) and `P₊ = (0, 1)` (class `1`): different classes, so conjugation reduces
the question to the infinite order of `D′ = (3, 9)` on the twist `y² = x³ + 9x + 27` over `ℚ`, which
the logarithmic height certifies (`QHeight.certH`, `H(x(4D′))³ > C`). Kernel-checked:
**the integral is not elementary** (`not_elementary_mw4`).
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly Sup Polynomial Differential Tower.NestM

/-- `A(t) = t³ + t + 1`. -/
def A4 : GPoly (LC 0) := [c1, c1, c0, c1]
/-- `z = 1`. -/
def z4 : GPoly (GFrac ℚ) := [([1, 0], [1])]

#guard kxDecide Fc ks lv 0 xc A4 [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none

set_option maxRecDepth 200000 in
lemma hsqc4 : GPoly.squarefreeCheck (MO Fc ks 0) A4 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hdeg34 : degG (MO Fc ks 0) A4 = 3 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hok4 : kxOK Fc ks 0 A4 [c1] 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcst4 : kxConst Fc ks 0 xc A4 [c1] 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hrep4 : kxRepOK Fc ks 0 xc A4 [c1] 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcls4 : (kxCls Fc ks 0 xc A4 [c1] 0 0 [c1]).length = 1 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hz4 : kxZ Fc ks lv 0 A4 = some z4 :=
  @of_decide_eq_true _ ((inferInstance : DecidableEq (Option (GPoly (GFrac ℚ))))
    (kxZ Fc ks lv 0 A4) (some z4)) (by decide +kernel)

set_option maxRecDepth 200000 in
lemma hs4 : sT Fc ks xc A4 [c1] 0 0 [c1] 0 = 3 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hκ4 : kxKap Fc ks 0 A4 z4 = 1 := by decide +kernel

/-- `3` is not a square. -/
instance fact3 : Fact (¬ IsSquare (sT Fc ks xc A4 [c1] 0 0 [c1] 0 * kxKap Fc ks 0 A4 z4)) :=
  ⟨by rw [hs4, hκ4, mul_one, Rat.isSquare_iff]; decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- **The height certificate over `ℚ`** for `D′ = (3, 9)` on `y² = x³ + 9x + 27`, and the side
checks, kernel-checked. -/
lemma hchk4 : kxChkCK Fc ks [0, -1] xc A4 [c1] 0 0 [c1] z4 (kxKap Fc ks 0 A4 z4) ([1], [1]) [9] [27]
    2 0 9 27 = true := by
  decide +kernel

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 2000000 in
/-- **`∫ √(1 + eˣ + e³ˣ) / (eˣ − 1) dx` is not elementary.** -/
theorem not_elementary_mw4 (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 = T.evP 0 A4) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 1 (([c1], kxDen Fc ks 0 A4 0 0 [c1]) : LC 1) * θ) :=
  T.kx_not_elementary_mwC hmonMW.1 hmonMW.2 0 hn hcertMW rfl A4 hsqc4 (by rw [hdeg34]; norm_num)
    (by rw [hdeg34]; norm_num) hdeg34 θ hθ hgen [c1] 0 0 [c1] hok4 hcst4 hrep4
    ⟨0, by rw [hcls4]; norm_num⟩ z4 hz4
    (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkCK [0, -1] xc A4 [c1] 0 0 [c1] z4 (kxKap Fc ks 0 A4 z4) ([1], [1]) [9]
        [27] 2 9 27 rfl hTm ⟨0, by rw [hcls4]; norm_num⟩ hchk4 rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

end Curves.MT.KXEx
