import RischTragerBronstein.Mixed.NKInf2K
import RischTragerBronstein.Mixed.NKExactExamples
import RischTragerBronstein.Mixed.KEReduce
import RischTragerBronstein.Torsion.AutoPrime
import RischTragerBronstein.Torsion.AutoPipeline

/-!
# Example data: a non-constant curve over `eˣ` with two places at infinity and no units

Tower `x`, `t = eˣ`, `θ² = P = t⁴ − t³ + 2t² + x² t` — a genus-one curve over `ℚ(x)(t)` whose
coefficients involve `x`, with two places at infinity (`θ ≈ ±t²`) and a single place above `t = 0`
(`ord₀ P = 1`). Inverted at infinity (`t = 1/T`, `y = θ T²`): `y² = Q = 1 − T + 2T² + x² T³` over
`K₀ = ℚ(x)`, the two places becoming `(0, ±1)`. Their difference is **not torsion**, certified over
`K₀` (`TwoPlaceCertK`): integral basis without special points (`globalCheckR`), place series `±√Q`
to precision `20` (`ser2Codes`), reductions `x ↦ 4 mod 13` and `x ↦ 4 mod 41` with orders `3` and
`4` (`Q13`, `Q41`), `pairMult = 1`, test at `M = 1` failing over `K₀` (`Lmo`). Kernel checks in
`NKInf2KExpExChk1`–`6`, the decision in `NKInf2KExpExample`.
-/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial

instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩

abbrev K0 := KF Fc 0

def cq (q : ℚ) : GPoly (GFrac ℚ) := [([q], [1])]
def gx (n d : List ℚ) : GPoly (GFrac ℚ) := [(n, d)]

/-- `a₀ = −(t⁴ − t³ + 2t² + x² t)`, `a₁ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], gx [0, 0, -1] [1], cq (-2), cq 1, cq (-1)], []]
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
  ([1], [1]), ([-1/2], [1]), ([7/8], [1]), ([7/16, 0, 1/2], [1]), ([-21/128, 0, 1/4], [1]),
  ([-119/256, 0, -5/16], [1]), ([-189/1024, 0, -19/32, 0, -1/8], [1]),
  ([791/2048, 0, -13/256, 0, -3/16], [1]), ([17843/32768, 0, 463/512, 0, 9/64], [1]),
  ([-4011/65536, 0, 1871/2048, 0, 85/128, 0, 1/16], [1]),
  ([-213479/262144, 0, -2875/4096, 0, 405/1024, 0, 5/32], [1]),
  ([-322063/524288, 0, -147901/65536, 0, -2373/2048, 0, -5/128], [1]),
  ([2869055/4194304, 0, -115813/131072, 0, -17843/8192, 0, -175/256, 0, -5/128], [1]),
  ([13003725/8388608, 0, 1689685/524288, 0, 5157/16384, 0, -1645/2048, 0, -35/256], [1]),
  ([10373755/33554432, 0, 4910315/1048576, 0, 1372365/262144, 0, 4683/4096, 0, -35/1024], [1]),
  ([-147774921/67108864, 0, -11918345/8388608, 0, 2530495/524288, 0, 62895/16384, 0, 1365/2048, 0, 7/256], [1]),
  ([-5364343229/2147483648, 0, -167963045/16777216, 0, -13525545/2097152, 0, 45705/32768, 0, 20265/16384, 0, 63/512], [1]),
  ([5795177549/4294967296, 0, -470784905/67108864, 0, -72449325/4194304, 0, -4666365/524288, 0, -26565/32768, 0, 189/2048], [1]),
  ([92773560733/17179869184, 0, 1598063989/134217728, 0, -134858815/33554432, 0, -14788345/1048576, 0, -744975/131072, 0, -2541/4096, 0, -21/1024], [1]),
  ([92816272269/34359738368, 0, 106034172259/4294967296, 0, 2216623815/67108864, 0, 29034005/4194304, 0, -1293435/262144, 0, -54747/32768, 0, -231/2048], [1])]
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

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

def Ro13 : Option (RedFns 13 K0) := redAtKF Fc 0 (fun _ ↦ 4) 13
def Ro41 : Option (RedFns 41 K0) := redAtKF Fc 0 (fun _ ↦ 4) 41

set_option maxRecDepth 200000 in
lemma hRo13 : Ro13.isSome = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hRo41 : Ro41.isSome = true := by decide +kernel

def R13 : RedFns 13 K0 := Ro13.get hRo13
def R41 : RedFns 41 K0 := Ro41.get hRo41

def Po13 : Option (PrimeCert 13) := primeCertP R13 TT (Pc2.fib.map Prod.fst)
def Po41 : Option (PrimeCert 41) := primeCertP R41 TT (Pc2.fib.map Prod.fst)

set_option maxRecDepth 200000 in
lemma hPo13 : Po13.isSome = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma hPo41 : Po41.isSome = true := by decide +kernel

def P13 : PrimeCert 13 := Po13.get hPo13
def P41 : PrimeCert 41 := Po41.get hPo41
/-- The multiplier `m₁₃ = 3` and its witness (computed by `autoPlaceData R13 TT Pc2 10`). -/
def Q13 : PlaceCert.PrimeData 13 := ⟨3, [[4, 10, 4, 2], [9, 1, 0, 0]]⟩
/-- `m₄₁ = 4` (computed by `autoPlaceData R41 TT Pc2 10`). -/
def Q41 : PlaceCert.PrimeData 41 := ⟨4, [[8, 3, 23, 28, 12], [33, 34, 1, 0, 0]]⟩

def Lmo : Option (ℕ × List (List K0)) :=
  autoLm TT.n (pairMult 13 41 Q13.mp Q41.mp * Pc2.cΓ) (pairMult 13 41 Q13.mp Q41.mp) TT.I.δL
    TT.I.Bc TT.I.Dc Pc2

set_option maxRecDepth 200000 in
lemma hLmo : Lmo.isSome = true := by decide +kernel

def PbL : ℕ × List (List K0) := Lmo.get hLmo

end Curves.MT.NKInf2KExpEx
