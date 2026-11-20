import RischTragerBronstein.Torsion.AutoPrime
import RischTragerBronstein.Torsion.AutoPipeline

/-!
# Generating non-torsion certificates for hyperelliptic curves over a code field

Untrusted generators (everything is checked afterwards by `globalCheckR`, `PlaceCert.check`,
`primeCheck`, …) for curves `y² = Q(T)` over a computable field `F` (e.g. `Kₘ = KF Fc m`):
* `sqrtSerG`: the square root of a power series by the recurrence
  `sₖ = (hₖ − ∑_{0<i<k} sᵢ s_{k−i}) / (2 s₀)` (the two branches `±√Q` above `T = 0`);
* `ramCertG`: the ramified branches `y = ±T √(Q(a + T²)/T²)` at a simple root `a` of `Q` modulo `p`
  (needs `Q′(a)` to be a square);
* `primePtsG`, `primeCertG`: `autoPrimeCert` with the special points computed modulo `p` (the global
  certificate may have none, `ibCheckR`).
-/

namespace Curves

open CPoly Sup GTors

/-- `√h` as a power series (`L` terms), `s₀² = h₀`. -/
def sqrtSerG {F : Type*} [Field F] [DecidableEq F] (h : List F) (s0 : F) : ℕ → List F
  | 0 => []
  | L + 1 =>
    (List.range (L + 1)).foldl (fun acc k ↦
      if k = 0 then [s0] else
      acc ++ [(h.getD k 0 - ∑ i ∈ Finset.Ico 1 k, acc.getD i 0 * acc.getD (k - i) 0) / (2 * s0)]) []

section Pr

variable {p : ℕ} [Fact p.Prime]

/-- The ramified branches of `y² = Q(T)` at a simple root `a` (`N = 2`). -/
def ramCertG (Q : CPoly (ZMod p)) (a : ZMod p) (L prec : ℕ) : Option (BranchCert (ZMod p)) :=
  let h := (compC Q (shiftC a 1)).drop 1
  ((zElems p).find? fun s ↦ s * s = h.getD 0 0 && s ≠ 0).map fun s0 ↦
    let sr := sqrtSerG h s0 L
    let y : CPoly (ZMod p) :=
      (List.range (2 * L)).map fun k ↦ if k % 2 = 1 then sr.getD (k / 2) 0 else 0
    ⟨2, [y, y.map (- ·)], prec⟩

variable {F : Type*} [Field F] [DecidableEq F]

/-- The special points modulo `p` (for `y² = Q`), with their branch and basis certificates. -/
def primePtsG (R : RedFns p F) (T : GlobalCert F) (L prec : ℕ) :
    Option (List (ZMod p × BranchCert (ZMod p) × List (List (ZMod p)))) :=
  let Fp := redBL R T.Fc
  let Bp := T.I.Bc.map (redBL R)
  let Dp := T.I.Dc.map R.red
  let Q : CPoly (ZMod p) := (Fp.getD 0 []).map (- ·)
  ((zElems p).filter fun a ↦ Kron.evalC (T.G.map R.red) a = 0).mapM fun a ↦
    (ramCertG Q a L prec).bind fun c ↦ (ibLmAt T.n Bp Dp a c).map fun Lm ↦ (a, c, Lm)

/-- `autoPrimeCert` with the special points computed modulo `p`. -/
def primeCertG (R : RedFns p F) (T : GlobalCert F) (bad : List F) : Option (PrimeCert p) := do
  let P0 ← autoPrimeCert R T bad
  let pts ← primePtsG R T 10 8
  pure { P0 with pts := pts }

end Pr

end Curves
