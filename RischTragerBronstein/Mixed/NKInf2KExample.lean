import RischTragerBronstein.Mixed.NKInf2KExChk6

/-!
# Example: `∫ √(log⁴ x − x log³ x − x log² x + x log x + 1) dx` is not elementary

Tower `x`, `t = log x`, `θ² = t⁴ − x t³ − x t² + x t + 1`: a non-constant genus-one curve with two
places at infinity and no units (`NKInf2KExData`: the certificate over `ℚ(x)` that `P₊ − P₋` is
not torsion, checked by the kernel in `NKInf2KExChk1`–`6`). By `nk_iffInf2K` an elementary integral
has no logarithmic part, and `θ` has no exact part in the basis `1, θ/t²` (`exactTLVG`, checked by
`#guard`; its kernel evaluation does not fit in memory, so it enters `not_elementary` as the
hypothesis `hres`): **`∫ θ dx` is not elementary**. Control (`#guard`): `θ′` has an exact part.
The Eisenstein, trace and inversion certificates are evaluated by the kernel.
-/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial
  Differential

/-- **`P₊ − P₋` is not torsion** on the inverted curve over `ℚ(x)`. -/
lemma hcertK : TwoPlaceCertK K0 (invB (shiftB (trCurveK Fc 0 Pp) 0) 2 4) := by
  obtain ⟨φ7, h7⟩ := redAtKF_valid Fc 0 (fun _ ↦ 2) 7 R7 (Option.some_get hRo7).symm
  obtain ⟨φ37, h37⟩ := redAtKF_valid Fc 0 (fun _ ↦ 10) 37 R37 (Option.some_get hRo37).symm
  exact ⟨TT, Pc2, 7, 37, inferInstance, inferInstance, R7, φ7, P7, Q7, R37, φ37, P37, Q37,
    PbL.1, PbL.2, by rw [okFc]; rfl, okG, okPc, by norm_num, h7, okP7, okQ7, h37, okP37, okQ37,
    Or.inr okN, okshape.1, okshape.2.1, okshape.2.2⟩

/-! ## The decision -/

def qE : GPoly (LC 0) := [one0, gx [0, 1] [1], gx [0, -1] [1], gx [0, -1] [1], one0]
def csE : List (GPoly (LC 0)) := [[cq (-1)], []]
def sE : GPoly (LC 0) := []
def tE : GPoly (LC 0) := [cq (-1)]
def dd : List ℚ := [-32, -16, -20, 24, 5]
/-- Bézout: `s₂ P + t₂ P_t = 1`. -/
def s2E : GPoly (LC 0) := [gx [-32, -16, -18, 19] dd, gx [0, 24, 8, 24] dd, gx [0, -16, -32] dd]
def t2E : GPoly (LC 0) :=
  [gx [0, -2, 5, 5] dd, gx [8, 4, 4, -9] dd, gx [0, -6, -3, -8] dd, gx [0, 4, 8] dd]

set_option maxRecDepth 200000 in
lemma hck : eisCk Fc ks 0 Pp qE csE sE tE s2E t2E = true := by decide +kernel

/-- `θ′ = ((4 − x) t³ − 4x t² − x t + x) θ / (2x P)`, `1/(2θ) = θ/(2P)`. -/
def dθW : GPoly (LC 1) := [zer, ([gx [0, 1] [1], gx [0, -1] [1], gx [0, -4] [1], gx [4, -1] [1]],
  [gx [0, 2] [1], gx [0, 0, 2] [1], gx [0, 0, -2] [1], gx [0, 0, -2] [1], gx [0, 2] [1]])]
def wθW : GPoly (LC 1) := [zer, ([one0], [cq 2, gx [0, 2] [1], gx [0, -2] [1], gx [0, -2] [1], cq 2])]
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]

set_option maxRecDepth 200000 in
lemma hs : traceW Fc ks 0 Pp dθW wθW sC = true := by decide +kernel

def Tc : List (List (LC 1)) := [[onec, zer], [zer, onec]]
def mone0 : LC 0 := [([-1], [1])]
def half0 : LC 0 := [([1/2], [1])]
def mhalf0 : LC 0 := [([-1/2], [1])]
/-- The leading coefficients `±1` of `θ/t²` at the two places at infinity. -/
def Cg : List (List (LC 0)) := [[one0, one0], [one0, mone0]]
def Cgi : List (List (LC 0)) := [[half0, half0], [half0, mhalf0]]
def r : ℕ → ℤ := fun i ↦ if i = 1 then 2 else 0
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def fθ : List (GPoly (LC 0)) := [[], [one0]]
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)
def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []

-- control: `θ′` has an exact part
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi r PC Tc Tc
  ((List.range 2).map fun j ↦ dθ'.getD j O1.zero) [] = some true

-- `θ` has no exact part (the kernel evaluation of `exactTLVG` does not fit in memory; it enters
-- `not_elementary` as the hypothesis `hres`)
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi r PC Tc Tc restθ [] = some false

set_option maxRecDepth 200000 in
lemma hinv : InvOK 2 4 0 (shiftB (trCurveK Fc 0 Pp) 0) := invOKb_spec (by decide +kernel)

set_option maxRecDepth 200000 in
lemma hFm : (toB Fm).Monic ∧ (toB Fm).natDegree = 2 :=
  monic_toB_of Fm 2 (by decide +kernel) (by decide +kernel)

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **`∫ √(log⁴ x − x log³ x − x log² x + x log x + 1) dx` is not elementary.** -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi r PC Tc Tc restθ [] = some false) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fθ.getD j []) * θ ^ j) := by
  intro h
  have hiff := T.nk_iffInf2K hmonF.1 hmonF.2 0 hn NKNonTorsEx.hcert rfl Pp qE csE sE tE s2E t2E hck
    θ (by decide) dθW wθW sC hθ hgen hs fθ 2 4 hinv hFm.1 hFm.2 hcertK Tc Tc false [] Cg Cgi r
    hres
  exact absurd (hiff.mp h).1 (by decide)

end Curves.MT.NKInf2KEx
