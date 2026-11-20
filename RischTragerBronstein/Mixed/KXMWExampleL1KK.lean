import RischTragerBronstein.Mixed.KXMWExamplesL1K
import RischTragerBronstein.Mixed.KXMWExample

/-!
# A kernel-checked Mordell–Weil exception at level `1`

Tower `x`, `t₀ = eˣ`, `t₁ = e^{t₀}`; `θ² = t₁³ + t₁ + 1` and the integrand `t₀ θ / (t₁ − 1)`, i.e.
`∫ eˣ √(1 + e^{eˣ} + e^{3eˣ}) / (e^{eˣ} − 1) dx`. The side checks, the tower certificate and the
height certificate over `ℚ` (`D′ = (3, 9)` on `y² = x³ + 9x + 27`, through `kxChkCKS`) are
kernel-checked (`decide +kernel`); with `kx_not_elementary_mwC` and `grp_of_chkCKS`:
**the integral is not elementary** (`not_elementary_L1K`).
-/
namespace Curves.MT.KXL1
open Curves Curves.LT Curves.MT CPoly FFHeight Sup Polynomial Differential Tower.NestM Tower.PrimN Tower.NestP Tower.NestX
set_option maxRecDepth 200000 in
lemma hsqcK : GPoly.squarefreeCheck (MO Fc ks 1) AK = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hdeg3K : degG (MO Fc ks 1) AK = 3 := by decide +kernel
set_option maxRecDepth 200000 in
lemma hokK : kxOK Fc ks 1 AK [g1] 0 0 [one1] = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hcstK : kxConst Fc ks 1 g1 AK [g1] 0 0 [one1] = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hrepK : kxRepOK Fc ks 1 g1 AK [g1] 0 0 [one1] = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hclsK : (kxCls Fc ks 1 g1 AK [g1] 0 0 [one1]).length = 1 := by decide +kernel
set_option maxRecDepth 200000 in
lemma hsK : sTS Fc ks 0 g1 AK [g1] 0 0 [one1] 0 = 3 := by decide +kernel
def zK : LC 1 := ([[([1], [1])]], [[([1], [1])]])
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
lemma hzK : kxZ Fc ks lv 1 AK = some zK :=
  @of_decide_eq_true _ ((inferInstance : DecidableEq (Option (GPoly (GPoly (GFrac ℚ))
    × GPoly (GPoly (GFrac ℚ))))) (kxZ Fc ks lv 1 AK) (some zK)) (by decide +kernel)
set_option maxRecDepth 200000 in
lemma hκK : kxKap Fc ks 1 AK zK = 1 := by decide +kernel
set_option maxRecDepth 200000 in
lemma hcertK : certC Fc ks lv 2 = true := by decide +kernel
def uK : Fr (KF Fc 0) := Fr.ofPoly [((1 : ℚ) : KF Fc 0)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
lemma hchkK : kxChkCKS Fc ks 0 g1 AK [g1] 0 0 [one1] zK 1 uK [(((9 : ℤ) : ℚ) : KF Fc 0)]
    [(((27 : ℤ) : ℚ) : KF Fc 0)] 2 0 9 27 = true := by
  decide +kernel

lemma hmonK : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, Fc, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

instance factK : Fact (¬ IsSquare (Rat.cast (sTS Fc ks 0 g1 AK [g1] 0 0 [one1] 0 * 1) : KF Fc 0)) :=
  ⟨not_isSquare_KF' Fc [0, -1] rfl _ (by rw [hsK, mul_one, Rat.isSquare_iff]; decide +kernel) 0⟩

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 4000000 in
/-- **`∫ eˣ √(1 + e^{eˣ} + e^{3eˣ}) / (e^{eˣ} − 1) dx` is not elementary** (kernel-checked
certificates). -/
theorem not_elementary_L1K (T : MTower Fc ks Cc L) (hn : T.n = 2) (θ : L)
    (hθ : θ ^ 2 = T.evP 1 AK) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 2) {θ}) :
    ¬ HasElementaryIntegral (T.ev 2 (([g1], kxDen Fc ks 1 AK 0 0 [one1]) : LC 2) * θ) :=
  T.kx_not_elementary_mwC hmonK.1 hmonK.2 1 hn hcertK rfl AK hsqcK (by rw [hdeg3K]; norm_num)
    (by rw [hdeg3K]; norm_num) hdeg3K θ hθ hgen [g1] 0 0 [one1] hokK hcstK hrepK
    ⟨0, by rw [hclsK]; norm_num⟩ zK hzK
    (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkCKS 0 g1 AK [g1] 0 0 [one1] zK 1 uK [(((9 : ℤ) : ℚ) : KF Fc 0)]
        [(((27 : ℤ) : ℚ) : KF Fc 0)] 2 9 27 hTm ⟨0, by rw [hclsK]; norm_num⟩ hchkK rtsF hrl hrs b₀
        hb₀ hns hns0 N hN μ
      convert h using 3)

end Curves.MT.KXL1
