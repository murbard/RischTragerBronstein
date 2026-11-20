import RischTragerBronstein.Mixed.KBWeights
import RischTragerBronstein.Mixed.KBExamples

/-!
# Example: a base change to a non-Eisenstein curve

Over the tower `x`, `t = eˣ`, the pole factor `P = t² + x t − x³ − 1` has the roots `w`, `−x − w`
with `w² + x w = x³ + 1`. This new base curve is not Eisenstein at any `p(x)` (`gcd(x, x³ + 1) = 1`),
but it has a single place at infinity (`n = 2`, `d = 3`), so it is geometrically irreducible
(`geomIrr_of_wt`) and its code-field facts come from `fKc_irr_wt`, `qK_irr_linear_wt`.
For `A = (t + 1) P + 1` (`A = 1` at both poles), `∫ √A(eˣ)/P(eˣ) dx` is not elementary: the
residue `1/(2w + x)` at `(w, 1)` is not constant.
-/

namespace Curves.MT.KBWEx

open Curves Curves.LT Curves.MT CPoly Polynomial Curves.MT.KBEx

abbrev Fw : Sup.BPoly ℚ := [[-1, 0, 0, -1], [0, 1], [1]]

lemma Fw_eq : Sup.toB Fw = X ^ 2 + C X * X + C (-1 - X ^ 3) := by
  simp [Sup.toB_cons, toPoly_cons]; ring

lemma Fw_mon : (Sup.toB Fw).Monic := by
  rw [Fw_eq]; monicity!

lemma Fw_deg : (Sup.toB Fw).natDegree = Fw.length - 1 := by
  rw [Fw_eq]; compute_degree!

lemma Fw_wt : wtC Fw = true := by decide +kernel

instance : Fact (Irreducible (toPoly (fKc Fw))) := ⟨fKc_irr_wt Fw Fw_mon Fw_deg Fw_wt⟩
instance : Fact (Irreducible (toPoly (qK Fc (qOfB Fw)))) :=
  ⟨qK_irr_linear_wt [0, -1] Fw Fw_mon Fw_deg Fw_wt⟩
instance : Fact (Irreducible (toPoly (liftQ Fw 0 M1))) := ⟨liftQ_X_irr Fw 0⟩
instance : Fact (Irreducible (toPoly (liftQ Fw (0 + 1) M1))) := ⟨liftQ_X_irr Fw 1⟩

/-- **The geometric irreducibility** required by `kzDecide_bc_correct`. -/
lemma Fw_geom : GeomIrr.{0} Fw := geomIrr_of_wt Fw Fw_mon Fw_deg Fw_wt

-- The base change checks: `Fw(x, W) = 0` and `Yc(x, W) = y` in `ℚ(x)[W]/(W² + xW − x³ − 1)`.
#guard bcOK Fc (qOfB Fw) Fw Yc = true

def ksW := tauK Fw Yc ks
def wW : NFM Fw 0 M1 := NFK.mk _ [trC Fw 0 wc]
/-- `−x − w`. -/
def wW' : NFM Fw 0 M1 := NFK.mk _ [trC Fw 0 [([0, -1], [1]), ([-1], [1])]]
def csW : List (NFM Fw 0 M1) := [wW, wW']
/-- `P = t² + x t − x³ − 1`. -/
def dW : GPoly (LC 0) := [[([-1, 0, 0, -1], [1])], xc, c1]
/-- `A = (t + 1) P + 1 = t³ + (x + 1) t² + (x − x³ − 1) t − x³`. -/
def AW : GPoly (LC 0) := [[([0, 0, 0, -1], [1])], [([-1, 1, 0, -1], [1])], [([1, 1], [1])], c1]

-- `∫ √A(eˣ)/P(eˣ)` is not elementary: the residue `1/(2w + x)` is not constant.
#guard kzDecide Fw ksW lv' 0 2 1 xc M1 [-1] [[1], [1]] AW B1 0 0 csW dW ps 30 (fun _ ↦ 2) =
  some false

end Curves.MT.KBWEx
