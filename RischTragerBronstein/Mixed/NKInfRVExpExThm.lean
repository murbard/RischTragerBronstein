import RischTragerBronstein.Mixed.NKInfRVExpExRes

/-!
# `∫ √(e²ˣ + x eˣ) dx` is not elementary (fully kernel-checked)

The decision of `NKInfRVExpExample` as a theorem with no computational hypothesis: every input of
`nk_iffETInfV` (Eisenstein data, shape, units, independence, trace, `certC`) and the exact-part
answer (`hresK`, `NKInfRVExpExRes`) is checked by `decide +kernel`.
-/

namespace Curves.MT.NKInfRVExpEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial Differential

set_option maxRecDepth 200000 in
lemma hck : eisCk Fc ks 0 Pp qE csE sE tE s2E t2E = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsh0 : nkShape0 Fc ks 0 Pp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hU : unitsC Fc ks 0 Pp Us Vs gls dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hJH : indepC Fc ks 0 gls J H = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hs : traceW Fc ks 0 Pp dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hcertC : certC Fc ks lv 1 = true := by decide +kernel

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **`∫ √(e²ˣ + x eˣ) dx` is not elementary** (`θ² = t² + x t`, `t = eˣ`), with no hypothesis
beyond the tower and the definition of `θ`. -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fθ.getD j []) * θ ^ j) := by
  intro h
  have hiff := T.nk_iffETInfV hmonF.1 hmonF.2 0 hn hcertC rfl Pp qE csE sE tE s2E t2E hck hsh0 θ
    Us Vs gls rfl dθW wθW sC hU J H hJH hθ hgen hs fθ Tc Tc false dg r Cg Cg dg0 hresK
  exact absurd (hiff.mp h).1 (by decide)

end Curves.MT.NKInfRVExpEx
