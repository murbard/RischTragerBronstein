import RischTragerBronstein.Mixed.KXMWExample
import RischTragerBronstein.Mixed.KXMWDecideM

/-!
# The Mordell–Weil example decided by the Manin-map certificate

`∫ √(e³ˣ − eˣ + x²) / (x (eˣ − 1)) dx` (`KXMWExample`): the exception points `(1, x)`, `(0, x)` on
`y² = T³ − T + x²` over `ℚ(x)`. `kxDecideMW0M` answers with the Manin certificate alone (`kmax = 0`:
no height search), and `not_elementary_mwM` proves non-elementarity from `kxChkM` (one Wronskian of
Manin images instead of three doublings), kernel-checked.
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly Sup Polynomial Differential Tower.NestM

-- The Manin branch alone answers (no height levels).
#guard kxDecideMW0M Fc ks lv xc Amw Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 0 = some false
#guard kxDecideMW0M Fc ks lv xc [[([0, 0, 4], [1])], cm1, c0, c1] Bmw 0 0 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 0 = some false
-- A constant curve: the Manin map vanishes identically (`β = 0`), no certificate.
#guard kxDecideMW0M Fc ks lv xc [c1, c1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 0 = none

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- **The Manin certificate** (and the side checks), kernel-checked. -/
lemma hchkMWM : kxChkM Fc ks [0, -1] xc Amw Bmw 0 0 [c1] zz 1 ([1], [1]) [-1] [0, 0, 1] 0 = true := by
  decide +kernel

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 2000000 in
/-- **`∫ √(e³ˣ − eˣ + x²) / (x (eˣ − 1)) dx` is not elementary**, by the Manin certificate. -/
theorem not_elementary_mwM (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 = T.evP 0 Amw) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 1 ((Bmw, kxDen Fc ks 0 Amw 0 0 [c1]) : LC 1) * θ) :=
  T.kx_not_elementary_mwC hmonMW.1 hmonMW.2 0 hn hcertMW rfl Amw hsqcMW (by rw [hdeg3MW]; norm_num)
    (by rw [hdeg3MW]; norm_num) hdeg3MW θ hθ hgen Bmw 0 0 [c1] hokMW hcstMW hrepMW
    ⟨0, by rw [hclsMW]; norm_num⟩ zz hzMW
    (fun E _ _ _ TE _ hTm rtsF hrl _ b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkM [0, -1] xc Amw Bmw 0 0 [c1] zz 1 ([1], [1]) [-1] [0, 0, 1] rfl hTm
        ⟨0, by rw [hclsMW]; norm_num⟩ hchkMWM hgensMW rtsF hrl b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

end Curves.MT.KXEx

