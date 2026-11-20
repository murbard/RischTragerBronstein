import RischTragerBronstein.Mixed.NKSearch
import RischTragerBronstein.Mixed.NKLogCertN

/-!
# Searching for logarithm certificates with algebraic residues (untrusted)

The search of `NKSearch` over a number field `N = ℚ(α)`, `α` a root of a monic `μ ∈ ℤ[X]`:

* `nOps O μ`: the code operations on `N`-codes (coordinates in `1, α, …, α^{d−1}`) over any code
  field `O` (multiplication reduced modulo `μ`, inverse by Gaussian elimination on the
  multiplication matrix);
* `findCertN`: the residues at the given points (over `N`), split into their `αᵏ`-coordinates;
  for each coordinate `k`, an element `u` of minimal weight with the prescribed orders (`searchWO`
  over `nOps`), giving the logarithms `c αᵏ log u − c αᵏ log den`; the result is in the format of
  `logCertN` (`LogN`) with the residue-free remainder `g` and its `resCert`.

Everything found is checked by `logCertN` and `resCert` (`nk_iffCN'`), so the search carries no
proof obligations.
-/

namespace Curves.MT.SearchN

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.Search

section NOps

variable {α : Type} (O : COps α) (μ : List ℤ)

/-- Ring operations for `N`-codes. -/
def rOps : NCodes.ROps α := ⟨O.add, O.mul, O.neg, O.zero, intC O⟩

/-- Pad an `N`-code to `d` coordinates. -/
def nPad (c : List α) : List α := (List.range μ.length).map fun i ↦ c.getD i O.zero

def nMul (a b : List α) : List α :=
  nPad O μ (NCodes.nRed (rOps O) μ (NCodes.nConv (rOps O) a b))

/-- The inverse, by solving `a · v = 1` (multiplication matrix). -/
def nInv (a : List α) : List α :=
  let d := μ.length
  let cols := (List.range d).map fun j ↦
    nMul O μ a ((List.range d).map fun i ↦ if i = j then O.one else O.zero)
  let rows := (List.range d).map fun i ↦
    (cols.map fun c ↦ c.getD i O.zero) ++ [if i = 0 then O.neg O.one else O.zero]
  match nullVec O (d + 1) rows with
  | some v =>
    let s := O.inv (v.getD d O.zero)
    (List.range d).map fun j ↦ O.mul s (v.getD j O.zero)
  | none => []

/-- **The code operations of `N ⊗ K`.** -/
def nOps : COps (List α) where
  zero := []
  one := [O.one]
  add a b := nPad O μ (NCodes.nAdd (rOps O) a b)
  neg a := a.map O.neg
  mul := nMul O μ
  inv := nInv O μ
  deriv a := a.map O.deriv
  isZero a := a.all O.isZero
  natCast n := [O.natCast n]

/-- `(t − a)ᴱ`. -/
def linPowO (a : α) (E : ℕ) : GPoly α := sysPowC O [O.neg a, O.one] E

/-- The order-conditions search of `NKSearch`, over any code operations. -/
def searchWO (n d Wb : ℕ) (Pp : List (GPoly α)) (pts : List (α × α × ℕ)) :
    Option (List (GPoly α)) :=
  let M := Wb / n
  let L := (pts.map fun p ↦ p.2.2).foldr max 0 + 1
  let cols := (List.range (n * (M + 1))).filter fun col ↦
    n * (col % (M + 1)) + (col / (M + 1)) * d ≤ Wb
  let rows := pts.flatMap fun (a, b, τ) ↦
    let y := branchSer O L Pp a b 6
    let ypow := (List.range n).foldl (fun (acc : List (List α)) _ ↦
      acc ++ [serMul O L y (acc.getD (acc.length - 1) (serT O L [O.one]))]) [serT O L [O.one]]
    let tpow := (List.range (M + 1)).foldl (fun (acc : List (List α)) _ ↦
      acc ++ [serMul O L [a, O.one] (acc.getD (acc.length - 1) (serT O L [O.one]))])
      [serT O L [O.one]]
    (List.range τ).map fun l ↦ cols.map fun col ↦
      (serMul O L (tpow.getD (col % (M + 1)) []) (ypow.getD (col / (M + 1)) [])).getD l O.zero
  (nullVec O cols.length rows).map fun v ↦
    (List.range n).map fun i ↦ (List.range (M + 1)).map fun k ↦
      match cols.idxOf? (i * (M + 1) + k) with
      | some j => v.getD j O.zero
      | none => O.zero

end NOps

variable (Fc : Sup.BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The coordinate `k` of a polynomial with `N`-code coefficients. -/
def coordP {α : Type} (z : α) (k : ℕ) (p : GPoly (List α)) : GPoly α := p.map (·.getD k z)

/-- One logarithm `u` (polynomial in `t, θ` over `N`) in the format `LogN`, with coefficient
`c αᵏ`: the `N`-code of `u`, its inverse and its logarithmic derivative modulo `P`. -/
def mkLogN (m : ℕ) (μ : List ℤ) (P : GPoly (LC (m + 1))) (dθ : GPoly (LC (m + 1)))
    (ps : List (GPoly (List (LC m)))) (k : ℕ) (c : ℚ) : LogN m :=
  let d := μ.length
  let O1 := nOps (MOr Fc ks (m + 1)) μ
  let z := (MO Fc ks m).zero
  let z1 := (MOr Fc ks (m + 1)).zero
  let PN : GPoly (List (LC (m + 1))) := P.map fun c ↦ [c]
  let dθN : GPoly (List (LC (m + 1))) := dθ.map fun c ↦ [c]
  let uN : GPoly (List (LC (m + 1))) := ps.map fun p ↦
    (List.range d).map fun kk ↦ polyCode Fc ks m (coordP z kk p)
  let vN := (invModC O1 PN uN).getD []
  let gN := (logDerC O1 PN dθN uN).getD []
  ((List.range d).map fun kk ↦ ps.map (coordP z kk),
   (List.range d).map fun kk ↦ coordP z1 kk vN,
   (List.range d).map fun kk ↦ coordP z1 kk gN,
   (List.range d).map fun kk ↦ if kk = k then c else 0)

/-- **The certificate search with algebraic residues.** `roots`: the roots `a` (`N`-codes) of the
denominator of `f` with their full fibres `b`; the level is primitive, `t′ = η`. Returns the
logarithms, `dθ`, `wθ`, and `(gp, D, k, U)` for `resCert`, all checked. -/
def findCertN (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (μ : List ℤ) (fl : List (LC (m + 1)))
    (roots : List (List (LC m) × List (List (LC m)))) (prec Kmax Mmax : ℕ) :
    Option (List (LogN m) × GPoly (LC (m + 1)) × GPoly (LC (m + 1)) × List (GPoly (LC m)) ×
      GPoly (LC m) × ℕ × List (GPoly (LC m))) :=
  let d := μ.length
  let Om := MO Fc ks m
  let O := nOps Om μ
  let O1 := MOr Fc ks (m + 1)
  let n := Pp.length
  let P := nkPC Fc ks m Pp
  let PpN : List (GPoly (List (LC m))) := Pp.map fun p ↦ p.map fun c ↦ [c]
  let fr : List (GPoly (List (LC m)) × GPoly (List (LC m))) := (List.range n).map fun j ↦
    let q := fl.getD j O1.zero
    (q.1.map fun c ↦ [c], q.2.map fun c ↦ [c])
  let sD : List (LC m) → List (LC m) := fun a ↦ O.add [η] (O.neg (O.deriv a))
  -- the residues, by coordinates
  let pts : List (List (LC m) × List (LC m) × List (Option ℚ)) := roots.flatMap fun (a, bs) ↦
    bs.map fun b ↦
      let y := branchSer O prec PpN a b 6
      let r := O.mul (Search.resAt O prec fr a y) (O.inv (sD a))
      (a, b, (List.range d).map fun k ↦ ratValC Fc ks m (r.getD k Om.zero))
  if !(pts.all fun p ↦ p.2.2.all Option.isSome) then none else
  match dThetaC O1 P, invModC O1 P (GPoly.derivX O1 P) with
  | some dθ, some wθ =>
    let degA := Tower.NestM.degG Om (Pp.getD 0 [])
    -- the logarithms of the coordinate `k`
    let logsOf : ℕ → Option (List (LogN m)) := fun k ↦
      let rs := pts.map fun p ↦ (p.2.2.getD k none).getD 0
      let nz := rs.filter (· ≠ 0)
      if nz = [] then some [] else
      let c := ratGcd nz
      let ns : List ℤ := rs.map fun r ↦ (r / c).num
      let nmin := ns.foldr min 0
      (List.range Kmax).findSome? fun κ0 ↦
        let κ : ℕ := κ0 + 1
        let E := ((κ : ℤ) * (-nmin)).toNat
        let tg := (pts.zip ns).map fun (p, kk) ↦ (p.1, p.2.1, ((κ : ℤ) * kk + (E : ℤ)).toNat)
        let den := roots.foldr (fun (a, _) acc ↦ GPoly.mul O (linPowO O a E) acc) [O.one]
        (List.range (Mmax + 1)).findSome? fun Wb ↦
          (searchWO O n degA Wb PpN tg).map fun ps ↦
            [mkLogN Fc ks m μ P dθ ps k (c / κ), mkLogN Fc ks m μ P dθ [den] k (-(c / κ))]
    match ((List.range d).map logsOf).allSome with
    | none => none
    | some lss =>
      let logs := lss.flatten
      let tot := NCodes.nRed (θOps Fc ks m) μ (logTotN Fc ks m logs)
      let g := remP O1 P (GPoly.sub O1 fl (tot.getD 0 []))
      let g := (List.range n).map fun j ↦ g.getD j O1.zero
      let D := lcmGL Om (g.map Prod.snd)
      let cofs := g.map fun e ↦ cofC Om D e.2
      if !(cofs.all Prod.fst) then none else
      let gp := (g.zip cofs).map fun (e, cf) ↦ GPoly.mul Om e.1 cf.2
      if !(GPoly.squarefreeCheck Om D) then none else
      match findResCert Fc ks m Pp gp D 4 with
      | none => none
      | some (kc, U) =>
        if logCertN Fc ks m Pp μ fl (nkFlR m gp D) logs dθ wθ then
          some (logs, dθ, wθ, gp, D, kc, U) else none
  | _, _ => none

end Curves.MT.SearchN
