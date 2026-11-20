import RischTragerBronstein.Mixed.NKNonTors
import RischTragerBronstein.Mixed.NKExactExamples
import RischTragerBronstein.Torsion.NonTorsionExample

/-!
# Example: an elliptic integral of the third kind over `log x`

Tower `x`, `t = log x` (`t′ = 1/x`), and `θ² = t (t + 27)(t − 48)` (an elliptic curve over the
logarithm; single place at infinity). The integrand
`f = (1/x) · θ / (72 (t + 24))`, i.e. `θ dt / (72 (t + 24))`, has simple poles at the two points
`(−24, ±72)` with residues `±1` and no other finite poles. The divisor `2 P − ∞ₓ`,
`P = (−24, 72)`, is not torsion (`Curves.NTExample`, certified over `ℚ(i)` at the primes `13` and
`193`), so by `nk_not_elementary` **`∫ f dx` is not elementary** — on any realization of the
tower over an algebraically closed field of constants. Every check is `decide +kernel`.
-/

namespace Curves.MT.NKNonTorsEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx Curves.NTExample
  Curves.RFExampleI Polynomial Differential

/-- `θ² + (1296 t + 21 t² − t³)`. -/
def Fq : BPoly ℚ := [[0, 1296, 21, -1], [], [1]]
/-- `B = θ/72`. -/
def Bq : BPoly ℚ := [[], [1/72]]
/-- `D = t + 24`. -/
def Dq : CPoly ℚ := [24, 1]

set_option maxRecDepth 200000 in
lemma hcert : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hshape : nkShape Fc ks 0 (liftCurve Fc ks 0 2 Fq) = true := by decide +kernel

set_option maxRecDepth 200000 in
/-- The first coordinate `ℚ(i) → ℚ`. -/
def lam0 : QI →ₗ[ℚ] ℚ := EllQuad.QCoords.coord ⟨0, by decide⟩

set_option maxRecDepth 200000 in
lemma hres : resDivCheck TE Fq Bq Dq lam0 1 [1] = true := by decide +kernel

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ/(72 x (log x + 24)) dx` is not elementary** on `θ² = t (t + 27)(t − 48)`,
`t = log x`. -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2,
      T.evP 0 ((liftCurve Fc ks 0 2 Fq).getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 0 ic * ∑ j ∈ Finset.range 2,
      T.evP 0 (liftQC Fc ks 0 (Bq.getD j [])) / T.evP 0 (liftQC Fc ks 0 Dq) * θ ^ j) := by
  have hmZ : toPoly ([1, 0, 1] : CPoly ℚ) =
      (toPoly ([1, 0, 1] : List ℤ)).map (Int.castRingHom ℚ) := by
    simp [toPoly]
  obtain ⟨φ13, h13⟩ := nfFns_valid 13 (toPoly ([1, 0, 1] : List ℤ)) hmZ 5
    (by rw [← Jac.castL_eq, ← Kron.evalC_eq]; decide +kernel)
    (by rw [← Polynomial.derivative_map, ← Jac.castL_eq, ← CPoly.toPoly_deriv, ← Kron.evalC_eq]
        decide +kernel)
  obtain ⟨φ193, h193⟩ := nfFns_valid 193 (toPoly ([1, 0, 1] : List ℤ)) hmZ 81
    (by rw [← Jac.castL_eq, ← Kron.evalC_eq]; decide +kernel)
    (by rw [← Polynomial.derivative_map, ← Jac.castL_eq, ← CPoly.toPoly_deriv, ← Kron.evalC_eq]
        decide +kernel)
  exact T.nk_not_elementary (IsAlgClosed.lift (R := ℚ) (S := QI) (M := Cc)).toRingHom hmonF.1
    hmonF.2 0 hn hcert rfl TE Fq hshape θ hθ hgen hG (by norm_num) _ φ13 h13 P13 hP13 _ φ193 h193 P193 hP193 12 LmE hNP Bq Dq lam0 1 [1]
    hres

end Curves.MT.NKNonTorsEx
