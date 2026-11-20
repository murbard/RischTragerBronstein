import RischTragerBronstein.Mixed.KXMWExample2
import RischTragerBronstein.Mixed.KXCertBridgeC

/-!
# Example: the Mordell–Weil exception with `D` and `P₊` in different square classes

`∫ √(e³ˣ − (x² + 1) eˣ + 2x²) / (x (eˣ − 1)) dx`: the residue at `t = 1` is rational
(`P = (1, x)`, class `1`) while `κ = 2` (`P₊ = (0, √2 x)`). `kxDecide` answers `none`. Over
`ℚ(√2)(x)` conjugation fixes `P` and negates `P₊`, so a relation would make `P` torsion; the
one-point certificate `ĥ(P) > 0` (`kxChkC`, level `2`, kernel-checked) proves **the integral is not
elementary** (`not_elementary_mw3`, via `grp_of_chkC`).
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly Sup Polynomial Differential Tower.NestM

/-- `A(t) = t³ − (x² + 1) t + 2x²`. -/
def A3 : GPoly (LC 0) := [x22, [([-1, 0, -1], [1])], c0, c1]

#guard kxDecide Fc ks lv 0 xc A3 Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none

set_option maxRecDepth 200000 in
lemma hsqc3 : GPoly.squarefreeCheck (MO Fc ks 0) A3 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hdeg33 : degG (MO Fc ks 0) A3 = 3 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hok3 : kxOK Fc ks 0 A3 Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcst3 : kxConst Fc ks 0 xc A3 Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hrep3 : kxRepOK Fc ks 0 xc A3 Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcls3 : (kxCls Fc ks 0 xc A3 Bmw 0 0 [c1]).length = 1 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hz3 : kxZ Fc ks lv 0 A3 = some zz :=
  @of_decide_eq_true _ ((inferInstance : DecidableEq (Option (GPoly (GFrac ℚ))))
    (kxZ Fc ks lv 0 A3) (some zz)) (by decide +kernel)

set_option maxRecDepth 200000 in
lemma hs3 : sT Fc ks xc A3 Bmw 0 0 [c1] 0 = 1 := by decide +kernel

/-- `2` is not a square. -/
instance fact2' : Fact (¬ IsSquare (sT Fc ks xc A3 Bmw 0 0 [c1] 0 * 2)) :=
  ⟨by rw [hs3, one_mul, Rat.isSquare_iff]; decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- **The one-point certificate** `ĥ(1, x) > 0` and the side checks, kernel-checked. -/
lemma hchk3 : kxChkC Fc ks [0, -1] xc A3 Bmw 0 0 [c1] zz 2 ([1], [1]) [-1, 0, -1] [0, 0, 2] 2 0 =
    true := by
  decide +kernel

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 2000000 in
/-- **`∫ √(e³ˣ − (x² + 1) eˣ + 2x²) / (x (eˣ − 1)) dx` is not elementary.** -/
theorem not_elementary_mw3 (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 = T.evP 0 A3) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 1 ((Bmw, kxDen Fc ks 0 A3 0 0 [c1]) : LC 1) * θ) :=
  T.kx_not_elementary_mwC hmonMW.1 hmonMW.2 0 hn hcertMW rfl A3 hsqc3 (by rw [hdeg33]; norm_num)
    (by rw [hdeg33]; norm_num) hdeg33 θ hθ hgen Bmw 0 0 [c1] hok3 hcst3 hrep3
    ⟨0, by rw [hcls3]; norm_num⟩ zz hz3
    (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkC [0, -1] xc A3 Bmw 0 0 [c1] zz 2 ([1], [1]) [-1, 0, -1] [0, 0, 2] 2
        rfl hTm ⟨0, by rw [hcls3]; norm_num⟩ hchk3 rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

end Curves.MT.KXEx
