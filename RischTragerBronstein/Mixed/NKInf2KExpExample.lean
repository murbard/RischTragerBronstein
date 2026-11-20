import RischTragerBronstein.Mixed.NKInf2KExpExChk6
import RischTragerBronstein.Mixed.NKInf2KExpVIff
import RischTragerBronstein.Mixed.NKSplitCand

/-!
# Example: `∫ √(e⁴ˣ − e³ˣ + 2e²ˣ + x² eˣ) dx` is not elementary

Tower `x`, `t = eˣ`, `θ² = t⁴ − t³ + 2t² + x² t`: a non-constant genus-one curve over an
exponential level, with two places at infinity, no units, and a single place above `t = 0`
(`nkShape0`). The certificate over `ℚ(x)` that `P₊ − P₋` is not torsion is `NKInf2KExpExData`
(kernel checks `NKInf2KExpExChk1`–`6`). By `nk_iffET2KV` an elementary integral has no logarithmic
part, and `θ` has no exact part in the basis `θʲ/t^{⌊j/2⌋}` with the gauge `Vᵀ` at infinity
(`exactTLEVG`, checked by `#guard`; it enters `not_elementary` as the hypothesis `hres`):
**`∫ θ dx` is not elementary**. Control (`#guard`): `θ′` has an exact part in the same test.
-/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial
  Differential

/-- **`P₊ − P₋` is not torsion** on the inverted curve over `ℚ(x)`. -/
lemma hcertK : TwoPlaceCertK K0 (invB (shiftB (trCurveK Fc 0 Pp) 0) 2 4) := by
  obtain ⟨φ13, h13⟩ := redAtKF_valid Fc 0 (fun _ ↦ 4) 13 R13 (Option.some_get hRo13).symm
  obtain ⟨φ41, h41⟩ := redAtKF_valid Fc 0 (fun _ ↦ 4) 41 R41 (Option.some_get hRo41).symm
  exact ⟨TT, Pc2, 13, 41, inferInstance, inferInstance, R13, φ13, P13, Q13, R41, φ41, P41, Q41,
    PbL.1, PbL.2, by rw [okFc]; rfl, okG, okPc, by norm_num, h13, okP13, okQ13, h41, okP41, okQ41,
    Or.inr okN, okshape.1, okshape.2.1, okshape.2.2⟩

/-! ## The decision -/

def qE : GPoly (LC 0) := [[], gx [0, 0, 1] [1], cq 2, cq (-1), cq 1]
def csE : List (GPoly (LC 0)) := [[cq (-1)], []]
def sE : GPoly (LC 0) := []
def tE : GPoly (LC 0) := [cq (-1)]
def dd : List ℚ := [0, 0, 0, 0, 28, 0, 32, 0, 27]
/-- Bézout: `s₂ P + t₂ P_t = 1`. -/
def s2E : GPoly (LC 0) := [gx [-224, 0, -242, 0, -193] dd, gx [168, 0, 206, 0, 120] dd,
  gx [-224, 0, -200, 0, -144] dd]
def t2E : GPoly (LC 0) := [gx [1] [0, 0, 1], gx [112, 0, 114, 0, 85] dd, gx [-56, 0, -64, 0, -39] dd,
  gx [56, 0, 50, 0, 36] dd]

set_option maxRecDepth 200000 in
lemma hck : eisCk Fc ks 0 Pp qE csE sE tE s2E t2E = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsh0 : nkShape0 Fc ks 0 Pp = true := by decide +kernel

def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]

set_option maxRecDepth 200000 in
lemma hs : traceC Fc ks 0 PC sC = true := by decide +kernel

def fθ : List (GPoly (LC 0)) := [[], [one0]]
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)
def dθ' : GPoly (LC 1) := (dThetaC (MOr Fc ks 1) PC).getD []

/-! The candidate (as `splitCandsE` without units): basis `θʲ/t^{⌊j d₀/2⌋}` (`d₀ = 1`), shifts
`2j − ⌊j/2⌋`, gauge `Vᵀ` (`V = [[1, 1], [1, −1]]`), permutation at `t = 0`. -/

def γs : List (LC 0) := [[([1], [1])], [([-1], [1])]]
def fl (j : ℕ) : ℕ := j * trailG (MO Fc ks 0) (Pp.getD 0 []) / 2
def Tc : List (List (LC 1)) := (List.range 2).map fun i ↦ (List.range 2).map fun j ↦
  if i = j then tInvPowC Fc ks 0 (fl j) else (MOr Fc ks 1).zero
def Ti : List (List (LC 1)) := (List.range 2).map fun i ↦ (List.range 2).map fun j ↦
  if i = j then tPowC Fc ks 0 (fl j) else (MOr Fc ks 1).zero
def r : ℕ → ℤ := fun j ↦ ((j * 2 : ℕ) : ℤ) - (fl j : ℤ)
def Cg : List (List (LC 0)) := ((splitGaugeS Fc ks 0 γs).map Prod.fst).getD []
def Cgi : List (List (LC 0)) := ((splitGaugeS Fc ks 0 γs).map Prod.snd).getD []
def τ : List ℕ := (List.range 2).insertionSort fun i j ↦
  j * trailG (MO Fc ks 0) (Pp.getD 0 []) % 2 ≤ i * trailG (MO Fc ks 0) (Pp.getD 0 []) % 2
def τi : List ℕ := (List.range 2).map fun a ↦ τ.idxOf a
def C : List (List (LC 0)) := permMatC (MO Fc ks 0) 2 τ
def Ci : List (List (LC 0)) := permMatC (MO Fc ks 0) 2 τi
def dg0 : List (ℚ × ℚ × LC 0) := (List.range 2).map fun a ↦
  let j := τ.getD a 0
  let d0 := trailG (MO Fc ks 0) (Pp.getD 0 [])
  (((j * d0 % 2 : ℕ) : ℚ) / 2, ((j : ℕ) : ℚ) / 2, (Pp.getD 0 []).getD d0 (MO Fc ks 0).zero)

-- `τ(θ) = 0`
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)
-- control: `θ′` has an exact part
#guard exactTLEVG Fc ks 0 xc (prdeC Fc ks lv 0) [] Cg Cgi r C Ci dg0 PC Tc Ti
  ((List.range 2).map fun j ↦ dθ'.getD j (MOr Fc ks 1).zero) [] = some true
-- `θ` has no exact part
#guard exactTLEVG Fc ks 0 xc (prdeC Fc ks lv 0) [] Cg Cgi r C Ci dg0 PC Tc Ti restθ [] = some false

set_option maxRecDepth 200000 in
lemma hcertC : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hinv : InvOK 2 4 0 (shiftB (trCurveK Fc 0 Pp) 0) := invOKb_spec (by decide +kernel)

set_option maxRecDepth 200000 in
lemma hFm : (toB Fm).Monic ∧ (toB Fm).natDegree = 2 :=
  monic_toB_of Fm 2 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 200000 in
lemma ha0K : (toB (trCurveK Fc 0 Pp)).coeff 0 ≠ 0 := by
  have h1 : ((trCurveK Fc 0 Pp).getD 0 []).getD 1 0 ≠ 0 := by decide +kernel
  rw [coeff_toB]
  intro h
  apply h1
  have := congrArg (fun p ↦ Polynomial.coeff p 1) h
  simpa [coeff_toPoly] using this

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **`∫ √(e⁴ˣ − e³ˣ + 2e²ˣ + x² eˣ) dx` is not elementary.** -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactTLEVG Fc ks 0 xc (prdeC Fc ks lv 0) [] Cg Cgi r C Ci dg0 PC Tc Ti restθ [] =
      some false) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fθ.getD j []) * θ ^ j) := by
  intro h
  have hiff := T.nk_iffET2KV hmonF.1 hmonF.2 0 hn hcertC rfl Pp qE csE sE tE s2E t2E hck
    (by decide) hsh0 ha0K 2 4 hinv hFm.1 hFm.2 hcertK θ hθ hgen sC hs fθ Tc Ti false [] Cg Cgi r
    C Ci dg0 hres
  exact absurd (hiff.mp h).1 (by decide)

end Curves.MT.NKInf2KExpEx
