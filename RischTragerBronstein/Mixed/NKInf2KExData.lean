import RischTragerBronstein.Mixed.NKInf2K
import RischTragerBronstein.Mixed.NKInfRVExample
import RischTragerBronstein.Mixed.NKNonTorsExample
import RischTragerBronstein.Mixed.KEReduce
import RischTragerBronstein.Torsion.AutoPrime
import RischTragerBronstein.Torsion.AutoPipeline

/-!
# Example data: a non-constant curve with two places at infinity and no units

Tower `x`, `t = log x`, `θ² = P = t⁴ − x t³ − x t² + x t + 1` — a genus-one curve over `ℚ(x)(t)`
whose coefficients involve `x` (Risch's mixed case), with two places at infinity (`θ ≈ ±t²`).
Inverted at infinity (`t = 1/T`, `y = θ T²`): `y² = Q = 1 + x T − x T² − x T³ + T⁴` over the code
field `K₀ = ℚ(x)`, the two places becoming `(0, ±1)`. Their difference is **not torsion**,
certified over `K₀` (`TwoPlaceCertK`):
* the integral basis needs **no** special points: the discriminant `−4Q` has only simple roots,
  none of them in `ℚ(x)` (`globalCheckR`, the relaxed check of `IntBasisCheckR`);
* the place certificate: the two branches `±√Q` to precision `20` (`Pc2`, coefficients `ser2Codes`
  computed by the square-root recurrence `sqrtSerF`);
* reductions `x ↦ 2 mod 7` and `x ↦ 10 mod 37`, where `Q` splits with square derivatives at its
  roots, so the ramified branches are explicit (`ramCert`); the class has order `3` and `4` there
  (`Q7`, `Q37`), `pairMult = 1`, and the test at `M = 1` fails over `K₀` (`Lmo`).
The kernel checks are in `NKInf2KExChk1`–`6` (split for memory), the decision in `NKInf2KExample`.
-/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial

instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩

abbrev K0 := KF Fc 0

def cq (q : ℚ) : GPoly (GFrac ℚ) := [([q], [1])]
def gx (n d : List ℚ) : GPoly (GFrac ℚ) := [(n, d)]

/-- `a₀ = −(t⁴ − x t³ − x t² + x t + 1)`, `a₁ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[cq (-1), gx [0, -1] [1], gx [0, 1] [1], gx [0, 1] [1], cq (-1)], []]
/-- The inverted curve over `K₀`. -/
def Fm : BPoly K0 := invB (shiftB (trCurveK Fc 0 Pp) 0) 2 4

/-! ## The certificate over `K₀ = ℚ(x)` -/

def xK : K0 := trC Fc 0 [([0, 1], [1])]
def cands : List K0 := [0, 1, -1, xK, -xK, 2, -2]
/-- Candidate roots (the leading coefficient above infinity is `x²`). -/
def rf : RootFinder K0 := fun P ↦ some (cands.filter fun a ↦ Kron.evalC P a == 0)

def ci : Option (BranchCert K0) := certAtAuto rf (invB Fm 2 4) 0 10 8
def T0 : Option (GlobalCert K0) := ci.bind fun c ↦ (autoIntBasis Fm 2 2 [] c 30).map
  fun I ↦ ⟨Fm, 2, 2, kDOf Fm, I, 0, [], [], [], [], 0⟩

set_option maxRecDepth 200000 in
lemma hT0 : T0.isSome = true := by decide +kernel

def TT : GlobalCert K0 := T0.get hT0

/-- `√h` as a power series (`L` terms), `s₀² = h₀`. -/
def sqrtSerF {F : Type*} [Field F] [DecidableEq F] (h : List F) (s0 : F) : ℕ → List F
  | 0 => []
  | L + 1 =>
    (List.range (L + 1)).foldl (fun acc k ↦
      if k = 0 then [s0] else
      acc ++ [(h.getD k 0 - ∑ i ∈ Finset.Ico 1 k, acc.getD i 0 * acc.getD (k - i) 0) / (2 * s0)]) []

def L2 : ℕ := 20
set_option maxHeartbeats 4000000 in
/-- The coefficients of `√(1 + x T − x T² − x T³ + T⁴)` (computed by `sqrtSerF`, as codes). -/
def ser2Codes : List (GFrac ℚ) := [
  ([1], [1]), ([0, -1/2], [1]), ([0, -1/2, -1/8], [1]), ([0, 1/2, -1/4, -1/16], [1]),
  ([1/2, 0, 1/8, -3/16, -5/128], [1]), ([0, 1/4, 1/4, 0, -5/32, -7/256], [1]),
  ([0, 1/4, 1/16, 5/16, -5/64, -35/256, -21/1024], [1]),
  ([0, -1/4, 3/8, 5/32, 5/16, -35/256, -63/512, -33/2048], [1]),
  ([-1/8, 0, -3/16, 9/32, 85/256, 35/128, -189/1024, -231/2048, -429/32768], [1]),
  ([0, -3/16, -3/8, 1/16, 15/64, 273/512, 105/512, -231/1024, -429/4096, -715/65536], [1]),
  ([0, -3/16, -3/64, -25/32, 25/128, 161/512, 1491/2048, 231/2048, -2145/8192, -6435/65536, -2431/262144], [1]),
  ([0, 3/16, -15/32, -35/128, -15/16, 105/512, 567/1024, 3663/4096, 0, -19305/65536, -12155/131072, -4199/524288], [1]),
  ([1/16, 0, 15/64, -45/128, -1055/1024, -245/256, 357/2048, 3927/4096, 66495/65536, -2145/16384, -85085/262144, -46189/524288, -29393/4194304], [1]),
  ([0, 5/32, 15/32, -5/32, -35/256, -4193/2048, -1029/1024, 231/1024, 12441/8192, 140855/131072, -36465/131072, -46189/131072, -88179/1048576, -52003/8388608], [1]),
  ([0, 5/32, 5/128, 175/128, -175/512, -973/2048, -25683/8192, -4917/4096, 8151/16384, 289575/131072, 556699/524288, -230945/524288, -793611/2097152, -676039/8388608, -185725/33554432], [1]),
  ([0, -5/32, 35/64, 105/256, 245/128, 371/2048, -7077/4096, -70191/16384, -6435/4096, 148005/131072, 785213/262144, 1011959/1048576, -323323/524288, -3380195/8388608, -1300075/16777216, -334305/67108864], [1]),
  ([-5/128, 0, -35/128, 105/256, 4585/2048, 2205/1024, 9345/8192, -65373/16384, -1482195/262144, -66495/32768, 1179035/524288, 4018443/1048576, 6495853/8388608, -3380195/4194304, -14300825/33554432, -5014575/67108864, -9694845/2147483648], [1]),
  ([0, -35/256, -35/64, 35/128, -105/512, 21273/4096, 12747/4096, 14553/8192, -238095/32768, -3937505/524288, -619905/262144, 2078505/524288, 9787869/2097152, 8060465/16777216, -16900975/16777216, -15043725/33554432, -9694845/134217728, -17678835/4294967296], [1]),
  ([0, -35/256, -35/1024, -525/256, 525/1024, 2289/4096, 139419/16384, 96657/16384, 77649/65536, -6116825/524288, -21244509/2097152, -2355639/1048576, 26659451/4194304, 91265265/16777216, 5014575/67108864, -81904725/67108864, -126032985/268435456, -300540195/4294967296, -64822395/17179869184], [1]),
  ([0, 35/256, -315/512, -1155/2048, -105/32, -6279/4096, 36267/8192, 410223/32768, 90519/8192, -778635/524288, -18424549/1048576, -57454917/4194304, -323323/262144, 158869165/16777216, 204111775/33554432, -60509205/134217728, -48474225/33554432, -2103781365/4294967296, -583401555/8589934592, -119409675/34359738368], [1])]
def ser2 : List K0 := ser2Codes.map fun c ↦ trC Fc 0 [c]
/-- The two places above `T = 0`, `Γ = 2 P₊`. -/
def Pc2 : PlaceCert K0 := ⟨[(0, 1)], [(0, (1, (ser2, L2 - 1))), (0, (1, (ser2.map (- ·), L2 - 1)))],
  [[(0, (1, 1)), (1, (1, 1))]], [2, 0], [2], [2], 1, [14]⟩

section Pr
variable {p : ℕ} [Fact p.Prime]

/-- The ramified branches of `y² = Q(T)` at a simple root `a` (`N = 2`). -/
def ramCert (Q : CPoly (ZMod p)) (a : ZMod p) (L prec : ℕ) : Option (BranchCert (ZMod p)) :=
  let h := (compC Q (shiftC a 1)).drop 1
  ((zElems p).find? fun s ↦ s * s = h.getD 0 0 && s ≠ 0).map fun s0 ↦
    let sr := sqrtSerF h s0 L
    let y : CPoly (ZMod p) :=
      (List.range (2 * L)).map fun k ↦ if k % 2 = 1 then sr.getD (k / 2) 0 else 0
    ⟨2, [y, y.map (- ·)], prec⟩

/-- The special points modulo `p` with their branch and basis certificates. -/
def primePts (R : RedFns p K0) (T : GlobalCert K0) (L prec : ℕ) :
    Option (List (ZMod p × BranchCert (ZMod p) × List (List (ZMod p)))) :=
  let Fp := redBL R T.Fc
  let Bp := T.I.Bc.map (redBL R)
  let Dp := T.I.Dc.map R.red
  let Q : CPoly (ZMod p) := (Fp.getD 0 []).map (- ·)
  ((zElems p).filter fun a ↦ Kron.evalC (T.G.map R.red) a = 0).mapM fun a ↦
    (ramCert Q a L prec).bind fun c ↦ (ibLmAt T.n Bp Dp a c).map fun Lm ↦ (a, c, Lm)

/-- `autoPrimeCert` with the special points computed modulo `p`. -/
def primeCertP (R : RedFns p K0) (T : GlobalCert K0) (bad : List K0) : Option (PrimeCert p) := do
  let P0 ← autoPrimeCert R T bad
  let pts ← primePts R T 10 8
  pure { P0 with pts := pts }

end Pr

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

def Ro7 : Option (RedFns 7 K0) := redAtKF Fc 0 (fun _ ↦ 2) 7
def Ro37 : Option (RedFns 37 K0) := redAtKF Fc 0 (fun _ ↦ 10) 37

set_option maxRecDepth 200000 in
lemma hRo7 : Ro7.isSome = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hRo37 : Ro37.isSome = true := by decide +kernel

def R7 : RedFns 7 K0 := Ro7.get hRo7
def R37 : RedFns 37 K0 := Ro37.get hRo37

def Po7 : Option (PrimeCert 7) := primeCertP R7 TT (Pc2.fib.map Prod.fst)
def Po37 : Option (PrimeCert 37) := primeCertP R37 TT (Pc2.fib.map Prod.fst)

set_option maxRecDepth 200000 in
lemma hPo7 : Po7.isSome = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hPo37 : Po37.isSome = true := by decide +kernel

def P7 : PrimeCert 7 := Po7.get hPo7
def P37 : PrimeCert 37 := Po37.get hPo37
/-- The multiplier `m₇ = 3` and its witness (computed by `autoPlaceData R7 TT Pc2 10`). -/
def Q7 : PlaceCert.PrimeData 7 := ⟨3, [[2, 4, 5, 4], [5, 1, 0, 0]]⟩
/-- `m₃₇ = 4` (computed by `autoPlaceData R37 TT Pc2 10`). -/
def Q37 : PlaceCert.PrimeData 37 := ⟨4, [[27, 2, 7, 5, 18], [10, 11, 1, 0, 0]]⟩

def Lmo : Option (ℕ × List (List K0)) :=
  autoLm TT.n (pairMult 7 37 Q7.mp Q37.mp * Pc2.cΓ) (pairMult 7 37 Q7.mp Q37.mp) TT.I.δL
    TT.I.Bc TT.I.Dc Pc2

set_option maxRecDepth 200000 in
lemma hLmo : Lmo.isSome = true := by decide +kernel

def PbL : ℕ × List (List K0) := Lmo.get hLmo

end Curves.MT.NKInf2KEx
