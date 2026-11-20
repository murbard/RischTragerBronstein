import RischTragerBronstein.Mixed.KXMWExample
import RischTragerBronstein.Mixed.KXCertBridgeK
import RischTragerBronstein.Mixed.KXCertBridgeT

/-!
# Example: the Mordell–Weil exception with an irrational residue class

`∫ √(e³ˣ − eˣ + 2x²) / (x (eˣ − 1)) dx`: the squared residue at `t = 1` is `2` (class `ℚ√2`,
`kxGens = [2]`) and `κ = z² A(0) = 2`, so the points `P = (1, √2 x)`, `P₊ = (0, √2 x)` of
`y² = T³ − T + 2x²` live over `ℚ(√2)(x)`. `kxDecide` answers `none`. Both lie in the class `√2`, so
on the twist by `2` they are rational (`KXCertBridgeT`): the certificate `kxChkT` over `ℚ`
(kernel-checked) proves **the integral is not elementary** (`not_elementary_mw2`). (The direct
certificate over `ℚ(√2)`, `kxChkK`, also passes but its kernel check needs about 34 GB.)
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly Sup Polynomial Differential Tower.NestM

def x22 : GPoly (GFrac ℚ) := [([0, 0, 2], [1])]
/-- `A(t) = t³ − t + 2x²`. -/
def A2 : GPoly (LC 0) := [x22, cm1, c0, c1]

#guard kxDecide Fc ks lv 0 xc A2 Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none

set_option maxRecDepth 200000 in
lemma hsqc2 : GPoly.squarefreeCheck (MO Fc ks 0) A2 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hdeg32 : degG (MO Fc ks 0) A2 = 3 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hok2 : kxOK Fc ks 0 A2 Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcst2 : kxConst Fc ks 0 xc A2 Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hrep2 : kxRepOK Fc ks 0 xc A2 Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcls2 : (kxCls Fc ks 0 xc A2 Bmw 0 0 [c1]).length = 1 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hgens2 : kxGens Fc ks 0 xc A2 Bmw 0 0 [c1] = [2] := by decide +kernel

set_option maxRecDepth 200000 in
lemma hz2 : kxZ Fc ks lv 0 A2 = some zz :=
  @of_decide_eq_true _ ((inferInstance : DecidableEq (Option (GPoly (GFrac ℚ))))
    (kxZ Fc ks lv 0 A2) (some zz)) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- **The height certificate on the twist by `s = 2`** (over `ℚ`: `(2, 4x)` and `(0, 4x)` on
`y² = x³ − 4x + 16x²`), and the side checks, kernel-checked. -/
lemma hchk2 : kxChkT Fc ks [0, -1] xc A2 Bmw 0 0 [c1] zz 1 ([1], [1]) [-4] [0, 0, 16] 3 0 = true := by
  decide +kernel

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 2000000 in
/-- **`∫ √(e³ˣ − eˣ + 2x²) / (x (eˣ − 1)) dx` is not elementary** (the Mordell–Weil exception of
`kxDecide` with residues in `ℚ√2`, decided by the certificate `hchk2` over `ℚ(√2)`). -/
theorem not_elementary_mw2 (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 = T.evP 0 A2) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 1 ((Bmw, kxDen Fc ks 0 A2 0 0 [c1]) : LC 1) * θ) :=
  T.kx_not_elementary_mwC hmonMW.1 hmonMW.2 0 hn hcertMW rfl A2 hsqc2 (by rw [hdeg32]; norm_num)
    (by rw [hdeg32]; norm_num) hdeg32 θ hθ hgen Bmw 0 0 [c1] hok2 hcst2 hrep2
    ⟨0, by rw [hcls2]; norm_num⟩ zz hz2
    (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkT [0, -1] xc A2 Bmw 0 0 [c1] zz 1 ([1], [1]) [-4] [0, 0, 16] 3
        rfl hTm ⟨0, by rw [hcls2]; norm_num⟩ hchk2 rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

end Curves.MT.KXEx
