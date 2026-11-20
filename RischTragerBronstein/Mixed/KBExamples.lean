import RischTragerBronstein.Mixed.KBFacts

/-!
# Examples: a pole factor `e²ˣ − x` with non-constant roots

Over the tower `x`, `t = eˣ` (base `ℚ(x)`), the factor `t² − x` has the roots `±√x`. The base curve is
changed to `w² = x` (Eisenstein at `x = 0`; `Q = W² − x`, `y = x`), where the poles are `±w`; the
decision `kzDecide` over the translated tower is correct for the original integral by
`kzDecide_bc_correct` (all `Fact`s proved here from Eisenstein's criterion).
-/
namespace Curves.MT.KBEx
open Curves Curves.LT Curves.MT CPoly Polynomial
abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
abbrev Fc' : Sup.BPoly ℚ := [[0, -1], [], [1]]
lemma Fc'_eq : Sup.toB Fc' = X ^ 2 + C (-X) := by
  simp [Sup.toB_cons, toPoly_cons]; ring
lemma Fc'_mon : (Sup.toB Fc').Monic := by
  rw [Fc'_eq]; exact monic_X_pow_add_C _ (by norm_num)
lemma Fc'_deg : (Sup.toB Fc').natDegree = 2 := by
  rw [Fc'_eq]; exact natDegree_X_pow_add_C
lemma Fc'_eis : eisC Fc' 0 = true := by
  simp [eisC, CPoly.Kron.evalC_eq, CPoly.toPoly_deriv, toPoly_cons, List.range_succ]
instance : Fact (Irreducible (toPoly (fKc Fc'))) :=
  ⟨fKc_irr_eis Fc' Fc'_mon (by rw [Fc'_deg]; rfl) (by rw [Fc'_deg]; norm_num) 0 Fc'_eis⟩
instance : Fact (Irreducible (toPoly (qK Fc (qOfB Fc')))) :=
  ⟨qK_irr_linear [0, -1] Fc' Fc'_mon (by rw [Fc'_deg]; rfl) (by rw [Fc'_deg]; norm_num) 0 Fc'_eis⟩
abbrev M1 : CPoly ℚ := [0, 1]
instance : Fact (Irreducible (toPoly (liftQ Fc' 0 M1))) := ⟨liftQ_X_irr Fc' 0⟩
instance : Fact (Irreducible (toPoly (liftQ Fc' (0 + 1) M1))) := ⟨liftQ_X_irr Fc' 1⟩
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def mxc : GPoly (GFrac ℚ) := [([0, -1], [1])]
def c0 : GPoly (GFrac ℚ) := []
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def Yc : GPoly (GFrac ℚ) := xc
-- The base change checks: `Fc'(x, W) = 0` and `Yc(x, W) = y` in `ℚ(x)[W]/(W² − x)`.
#guard bcOK Fc (qOfB Fc') Fc' Yc = true
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def ks' := tauK Fc' Yc ks
def lv' : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def wc : GPoly (GFrac ℚ) := [([], [1]), ([1], [1])]
def cw : NFM Fc' 0 M1 := NFK.mk _ [trC Fc' 0 wc]
def cs : List (NFM Fc' 0 M1) := [cw, -cw]
def omx : GPoly (GFrac ℚ) := [([1, -1], [1])]
def B' : GPoly (LC 0) := [[([-1, 2], [1])]]
def dC : GPoly (LC 0) := [mxc, c0, c1]
def ps : List ℕ := [7, 11, 13, 17, 19, 23]
/-- `A = (t + 1)(t² − x) + 1`: `A(±w) = 1`, `A(0) = 1 − x` is not a square. -/
def A' : GPoly (LC 0) := [omx, mxc, c1, c1]
def B1 : GPoly (LC 0) := [c1]

-- `∫ √A(eˣ)/(e²ˣ − x)` is not elementary: the residue `1/(2x − 1)` at `(±w, 1)` is not constant.
#guard kzDecide Fc' ks' lv' 0 2 1 xc M1 [-1] [[1], [1]] A' B1 0 0 cs dC ps 30 (fun _ ↦ 2) =
  some false

-- Not in the build (about 10 min, run by `#eval`): `∫ (2x − 1) √A(eˣ)/(e²ˣ − x)` is not elementary
-- (`some false`): the residues are constant (`κ = 1`), but the component is not torsion and
-- `A(0) = 1 − x` has no square root, so the orders over `t = 0` can be killed:
--   kzDecide Fc' ks' lv' 0 2 1 xc M1 [-1] [[1], [1]] A' B' 0 0 cs dC ps 30 (fun _ ↦ 2)
end Curves.MT.KBEx
