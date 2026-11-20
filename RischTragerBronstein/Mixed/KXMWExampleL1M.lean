import RischTragerBronstein.Mixed.KXMWExampleL1KK
import RischTragerBronstein.Mixed.KXMWDecideSM

/-!
# A kernel-checked non-constant Mordell–Weil exception at level `1` (Manin certificate)

Tower `x`, `t₀ = eˣ`, `t₁ = e^{t₀}`; `θ² = t₁³ − t₁ + t₀²` (non-constant over `K₀(t₀)`) and the
integrand `θ / (t₁ − 1)`, i.e. `∫ √(e^{3eˣ} − e^{eˣ} + e^{2x}) / (e^{eˣ} − 1) dx`. The Manin branch of
`kxDecideMWSM` answers alone (`#guard`, no height levels), and the whole Manin search `kxMWOKSM`
is kernel-checked: **the integral is not elementary** (`not_elementary_L1M`), via
`not_elementary_of_MWOKSM`.
-/

namespace Curves.MT.KXL1

open Curves Curves.LT Curves.MT CPoly FFHeight Sup Polynomial Differential Tower.NestM Tower.PrimN Tower.NestP Tower.NestX

#guard kxDecideMWSM Fc ks lv 0 g1 A1 [one1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) 0 = some false

set_option maxRecDepth 200000 in
lemma hsqc1 : GPoly.squarefreeCheck (MO Fc ks 1) A1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hdeg31 : degG (MO Fc ks 1) A1 = 3 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- **The Manin search and side checks at level `1`**, kernel-checked. -/
lemma hokM1 : kxMWOKSM Fc ks lv 0 g1 A1 [one1] 0 0 [one1] = true := by decide +kernel

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **`∫ √(e^{3eˣ} − e^{eˣ} + e^{2x}) / (e^{eˣ} − 1) dx` is not elementary** (non-constant curve at
level `1`, Manin certificate, kernel-checked). -/
theorem not_elementary_L1M (T : MTower Fc ks Cc L) (hn : T.n = 2) (θ : L)
    (hθ : θ ^ 2 = T.evP 1 A1) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 2) {θ}) :
    ¬ HasElementaryIntegral (T.ev 2 (([one1], kxDen Fc ks 1 A1 0 0 [one1]) : LC 2) * θ) :=
  T.not_elementary_of_MWOKSM hmonK.1 hmonK.2 0 hn hcertK rfl A1 hsqc1 (by rw [hdeg31]; norm_num)
    (by rw [hdeg31]; norm_num) θ hθ hgen [one1] 0 0 [one1] hokM1

end Curves.MT.KXL1


