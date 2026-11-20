import RischTragerBronstein.Mixed.KXExamples
import RischTragerBronstein.Mixed.KXNotElemMW
import RischTragerBronstein.Mixed.KXCertBridge
import RischTragerBronstein.Mixed.KXMWDecide

/-!
# Example: the Mordell–Weil exception of `kxDecide`, decided by a height certificate

Tower `x`, `t = eˣ`; `θ² = A(t) = t³ − t + x²` (an elliptic curve over `ℚ(x)`, not constant), and the
integrand `θ / (x (t − 1))`, i.e.

  `∫ √(e³ˣ − eˣ + x²) / (x (eˣ − 1)) dx`.

`kxDecide` answers `none` (the Mordell–Weil case, `KXExamples`-style `#guard` below): the pole
`t = 1` gives the point `P = (1, x)` (residue `±1`), which is not torsion, and `A(0) = x²` gives
`P₊ = (0, x)`, also not torsion; whether a combination `2N P + 2μ P₊` vanishes is a Mordell–Weil
question. The height certificate (`kxChk`, `certQ` at level `3`: `(1, x)` and `(0, x)` are
independent on `y² = T³ − T + x²` over `ℚ(x)`) answers it, and `kx_not_elementary_mwC` with
`grp_of_chk` proves **the integral is not elementary**, on every realization of the tower.
Every check is `decide +kernel`.
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly Sup Polynomial Differential Tower.NestM

def x2 : GPoly (GFrac ℚ) := [([0, 0, 1], [1])]
def cm1 : GPoly (GFrac ℚ) := [([-1], [1])]
/-- `1/x`. -/
def ix : GPoly (GFrac ℚ) := [([1], [0, 1])]
/-- `z = 1/x` (`z² A(0) = 1`). -/
def zz : GPoly (GFrac ℚ) := [([0, 1, 0, 0, 0, 0], [0, 0, 1])]
/-- `A(t) = t³ − t + x²`. -/
def Amw : GPoly (LC 0) := [x2, cm1, c0, c1]
/-- `B = 1/x`. -/
def Bmw : GPoly (LC 0) := [ix]

-- The Mordell–Weil case: `kxDecide` does not answer.
#guard kxDecide Fc ks lv 0 xc Amw Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none
-- `kxDecideMW0` (automatic certificate search, correct by `kxDecideMW0_correct`) answers.
#guard kxDecideMW0 Fc ks lv xc Amw Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 = some false
-- `∫ √(e³ˣ − eˣ + 4x²)/(x (eˣ − 1))`: residue `2`, so `D = 2P`; the search certifies `D/2`.
#guard kxDecideMW0 Fc ks lv xc [[([0, 0, 4], [1])], cm1, c0, c1] Bmw 0 0 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 3 = some false
-- A constant curve (`√(1 + eˣ + e³ˣ)/(eˣ − 1)`): heights over `ℚ(x)` vanish, no certificate.
#guard kxDecideMW0 Fc ks lv xc [c1, c1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 = none

set_option maxRecDepth 200000 in
lemma hcertMW : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsqcMW : GPoly.squarefreeCheck (MO Fc ks 0) Amw = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hdeg3MW : degG (MO Fc ks 0) Amw = 3 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hokMW : kxOK Fc ks 0 Amw Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcstMW : kxConst Fc ks 0 xc Amw Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hrepMW : kxRepOK Fc ks 0 xc Amw Bmw 0 0 [c1] = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hclsMW : (kxCls Fc ks 0 xc Amw Bmw 0 0 [c1]).length = 1 := by decide +kernel

set_option maxRecDepth 200000 in
lemma hgensMW : kxGens Fc ks 0 xc Amw Bmw 0 0 [c1] = [] := by decide +kernel

set_option maxRecDepth 200000 in
lemma hzMW : kxZ Fc ks lv 0 Amw = some zz :=
  @of_decide_eq_true _ ((inferInstance : DecidableEq (Option (GPoly (GFrac ℚ))))
    (kxZ Fc ks lv 0 Amw) (some zz)) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- **The height certificate** (and the side checks), kernel-checked. -/
lemma hchkMW : kxChk Fc ks [0, -1] xc Amw Bmw 0 0 [c1] zz 1 ([1], [1]) [-1] [0, 0, 1] 3 0 = true := by
  decide +kernel

lemma hmonMW : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, Fc, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 2000000 in
/-- **`∫ √(e³ˣ − eˣ + x²) / (x (eˣ − 1)) dx` is not elementary** (the Mordell–Weil exception of
`kxDecide`, decided by the height certificate `hchkMW`). -/
theorem not_elementary_mw (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 = T.evP 0 Amw) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 1 ((Bmw, kxDen Fc ks 0 Amw 0 0 [c1]) : LC 1) * θ) :=
  T.kx_not_elementary_mwC hmonMW.1 hmonMW.2 0 hn hcertMW rfl Amw hsqcMW (by rw [hdeg3MW]; norm_num)
    (by rw [hdeg3MW]; norm_num) hdeg3MW θ hθ hgen Bmw 0 0 [c1] hokMW hcstMW hrepMW
    ⟨0, by rw [hclsMW]; norm_num⟩ zz hzMW
    (fun E _ _ _ TE _ hTm rtsF hrl _ b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chk [0, -1] xc Amw Bmw 0 0 [c1] zz 1 ([1], [1]) [-1] [0, 0, 1] 3 rfl hTm
        ⟨0, by rw [hclsMW]; norm_num⟩ hchkMW hgensMW rtsF hrl b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

end Curves.MT.KXEx
