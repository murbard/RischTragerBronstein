import RischTragerBronstein.Mixed.NKSearchN
import RischTragerBronstein.Mixed.NKLogCertNExamples

/-!
# Example: an automatically found certificate with irrational residues

Over `θ² = t³ + t + 19/2`, `t = log x`, with `α = √2`: `A(±α)` are squares in `ℚ(α)`
(`(3 ± α/2)²`). The tangent `θ = ℓ(t)` at `P₊ = (α, 3 + α/2)` meets the curve again at
`R = (t_R, θ_R)` over `ℚ(α)`. With `u₁ = θ − ℓ(t)` and its conjugate `u₂`,
`f = θ + α (u₁′/u₁ − u₂′/u₂)` is a rational integrand with residues `2α, α, −2α, −α` at
`P₊, R` and their conjugates.

Given only `f` and the fibres over the four poles, `SearchN.findCertN` finds logarithms over
`ℚ(α)` whose certificate `logCertN` checks, with residue-free remainder `g = θ`
(`resCert`). The trace check holds and `exactG` answers `some false`: by `nk_iffCN'`,
**`∫ f` is not elementary**, with no certificate supplied by hand.
-/

namespace Curves.MT.NKSearchNEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogEx Curves.MT.SearchN

def cst0 (c : ℚ) : LC 0 := [([c], [1])]
def μ2 : List ℤ := [-2, 0]
def O0 := MO Fc ks 0
def ON := nOps O0 μ2
def nc (a b : ℚ) : List (LC 0) := [cst0 a, cst0 b]
def conj (v : List (LC 0)) : List (LC 0) := [v.getD 0 O0.zero, O0.neg (v.getD 1 O0.zero)]
/-- θ² = t³ + t + 19/2 -/
def Pp2 : List (GPoly (LC 0)) := [[cst0 (-19/2), cst0 (-1), [], cst0 (-1)], []]
def P2 : GPoly (LC 1) := nkPC Fc ks 0 Pp2
def dθ2 : GPoly (LC 1) := (dThetaC O1 P2).getD []
def α : List (LC 0) := nc 0 1
def β : List (LC 0) := nc 3 (1/2)
def s : List (LC 0) := ON.mul (nc 7 0) (ON.inv (nc 6 1))
def tR : List (LC 0) := ON.add (ON.mul s s) (ON.neg (nc 0 2))
def ℓ0 : List (LC 0) := ON.add β (ON.neg (ON.mul s α))
def θR : List (LC 0) := ON.add ℓ0 (ON.mul s tR)
def u1 : List (GPoly (List (LC 0))) := [[ON.neg ℓ0, ON.neg s], [ON.one]]
def u2 : List (GPoly (List (LC 0))) := [[conj (ON.neg ℓ0), conj (ON.neg s)], [ON.one]]
def logs0 : List (LogN 0) := [mkLogN Fc ks 0 μ2 P2 dθ2 u1 1 1, mkLogN Fc ks 0 μ2 P2 dθ2 u2 1 (-1)]
def tot0 := NCodes.nRed (θOps Fc ks 0) μ2 (logTotN Fc ks 0 logs0)
def gp2 : List (GPoly (LC 0)) := [[], [one0]]
def pad2 (l : GPoly (LC 1)) : List (LC 1) := (List.range 2).map fun j ↦ l.getD j O1.zero
def fl : List (LC 1) := pad2 (GPoly.add O1 (nkFlR 0 gp2 NKLogCertEx.D1) (remP O1 P2 (tot0.getD 0 [])))

def roots : List (List (LC 0) × List (List (LC 0))) :=
  [(α, [β, ON.neg β]), (conj α, [conj β, conj (ON.neg β)]), (tR, [θR, ON.neg θR]),
   (conj tR, [conj θR, conj (ON.neg θR)])]
def sC2 : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]

/-- The certificate, found by search. -/
def cert := (findCertN Fc ks 0 ic Pp2 μ2 fl roots 8 1 20).getD ([], [], [], [], [], 0, [])

-- (about 4 min)
#guard
  logCertN Fc ks 0 Pp2 μ2 fl (nkFlR 0 cert.2.2.2.1 cert.2.2.2.2.1) cert.1 cert.2.1 cert.2.2.1 &&
  GPoly.squarefreeCheck (MO Fc ks 0) cert.2.2.2.2.1 &&
  resCert Fc ks 0 Pp2 cert.2.2.2.1 cert.2.2.2.2.1 cert.2.2.2.2.2.1 cert.2.2.2.2.2.2 &&
  decide (nkShape Fc ks 0 Pp2 = true) && decide (traceC Fc ks 0 P2 sC2 = true) &&
  decide (exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) P2
    (nkRest Fc ks 0 (nkFlR 0 cert.2.2.2.1 cert.2.2.2.2.1)
      (nkTau Fc ks 0 2 (nkFlR 0 cert.2.2.2.1 cert.2.2.2.2.1) sC2)) = some false)

end Curves.MT.NKSearchNEx
