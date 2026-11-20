import RischTragerBronstein.Mixed.NKInfRN
import RischTragerBronstein.Mixed.NKIntBasis
import RischTragerBronstein.Torsion.Front

/-!
# Finding the units (untrusted)

The certificates of the several-places decisions (`nk_iffInf`, `nk_iffRN`, `nk_iff2N`, …) are
computed here; every output is re-checked by the kernel checks of those theorems (`unitCN`,
`logDerChkN`, `indepCN`, `traceW`, `PlaceCert.check`), so nothing in this file needs a proof.

* **Units by linear algebra** (`unitSearch`): a unit `u = ∑ u_{jl} tˡ θʲ` with divisor
  `∑ c_π P_π` supported at the places at infinity (`∑ c_π = 0`) is a solution of the linear
  conditions `ord_π u ≥ c_π` along the Puiseux branches `x′ = s^E`, `y′ = ser(s)` of the inverted
  curve (`t = 1/x′`, `θ = y′/x′ᵏ`): since the divisor has degree `0`, any non-zero solution has
  exactly that divisor and no zero at a finite place. `findUnit` tries multiples `m c` and
  degrees `B`; coefficients lie in the number field `N = ℚ(α)` of the branches.
* `unitCodes`: the `ℚ(α)`-codes `∑ αᵖ Aₚ` of `u` and of `u⁻¹` (normalized by the leading
  coefficients along one branch); `logDerCodes`: the components `gₖ` of `u′/u` (normalized code
  arithmetic, reduction modulo `μ` and `P`); `indepCodes`: the right inverse `H` over `ℚ(α)(x, t)`
  of the coordinate minor (Gauss–Jordan with inverses in `ℚ(α)` through multiplication matrices);
  `placeCertInf`: the place certificate of the fibre above `x′ = 0`.
-/

open Polynomial NCodes

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

section Search

variable {MM : CPoly ℚ} [Fact (Irreducible (toPoly MM))]

/-- Truncated power of a series. -/
def serPowN (s : CPoly (NFC.NF MM)) (j L : ℕ) : CPoly (NFC.NF MM) :=
  (List.range j).foldl (fun acc _ ↦ (mul acc s).take L) [1]

/-- The coefficient of `sᵐ` of `u = ∑ w_{jl} tˡ θʲ` along a branch (`w` indexed `j (B + 1) + l`). -/
def serCoeffU (n k B : ℕ) (w : List (NFC.NF MM)) (b : PBranch (NFC.NF MM)) (m : ℤ) : NFC.NF MM :=
  (List.range n).foldr (fun (j : ℕ) acc ↦ (List.range (B + 1)).foldr (fun (l : ℕ) acc ↦
    let i : ℤ := m + ((b.E * (l + k * j) : ℕ) : ℤ)
    acc + w.getD (j * (B + 1) + l) 0 *
      (if i < 0 then 0 else (serPowN b.ser j (i.toNat + 1)).getD i.toNat 0)) acc) 0

/-- **The linear unit search**: the kernel of the conditions `ord_π u ≥ c_π`. -/
def unitSearch (n k B : ℕ) (reps : List (PBranch (NFC.NF MM))) (c : List ℤ) :
    List (CPoly (NFC.NF MM)) :=
  let unk := (List.range n).flatMap fun j ↦ (List.range (B + 1)).map fun l ↦ (j, l)
  let cols := unk.map fun jl ↦
    (List.range reps.length).flatMap fun π ↦
      let b := reps.getD π ⟨1, []⟩
      let sh : ℤ := b.E * (B + k * (n - 1))
      let cnt : ℕ := (c.getD π 0 + sh).toNat
      let P := serPowN b.ser jl.1 (cnt + b.E * (B + k * n) + 1)
      (List.range cnt).map fun idx ↦
        let i : ℤ := (idx : ℤ) - sh + b.E * (jl.2 + k * jl.1)
        if i < 0 then 0 else P.getD i.toNat 0
  nullBasis cols

/-- A unit with divisor `m c` for the first `m ≤ mmax`, `B ≤ Bmax` that works. -/
def findUnit (n k Bmax mmax : ℕ) (reps : List (PBranch (NFC.NF MM))) (c : List ℤ) :
    Option (ℕ × ℕ × List (NFC.NF MM)) :=
  (List.range mmax).findSome? fun (m : ℕ) ↦ (List.range (Bmax + 1)).findSome? fun B ↦
    ((unitSearch n k B reps (c.map (((m + 1 : ℕ) : ℤ) * ·))).find? fun w ↦ w.any (· ≠ 0)).map
      fun w ↦ (m + 1, B, w)

end Search

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)
variable {MM : CPoly ℚ} [Fact (Irreducible (toPoly MM))]

/-- The `ℚ(α)`-codes `[A₀, …, A_{d−1}]` (each a list of `θ`-coefficients, polynomials in `t`) of
`u = ∑ w_{jl} tˡ θʲ`. -/
def nCodesOf (m n B : ℕ) (w : List (NFC.NF MM)) : List (List (GPoly (LC m))) :=
  (List.range (MM.length - 1)).map fun p ↦ (List.range n).map fun j ↦
    (List.range (B + 1)).map fun l ↦ mcst Fc ks m ((w.getD (j * (B + 1) + l) 0).1.getD p 0)

/-- **The codes of a unit and of its inverse** for the target divisor `c` (`u v = 1`). -/
def unitCodes (m n k Bmax mmax : ℕ) (reps : List (PBranch (NFC.NF MM))) (c : List ℤ) :
    Option (List (List (GPoly (LC m))) × List (List (GPoly (LC m)))) := do
  let (mu, B, w) ← findUnit n k Bmax mmax reps c
  let (_, B', w') ← findUnit n k Bmax 1 reps (c.map ((-(mu : ℤ)) * ·))
  -- normalize `u v = 1` by the leading coefficients along the first branch
  let b := reps.getD 0 ⟨1, []⟩
  let e := (mu : ℤ) * c.getD 0 0
  let κ := serCoeffU n k B w b e * serCoeffU n k B' w' b (-e)
  if κ = 0 then none else
  pure (nCodesOf Fc ks m n B w, nCodesOf Fc ks m n B' (w'.map (κ⁻¹ * ·)))

/-- The derivative code of `A(θ)` given `θ′ = dθ`, with normalized arithmetic. -/
def dCodeR (m : ℕ) (dθ : GPoly (LC (m + 1))) (u : GPoly (LC (m + 1))) : GPoly (LC (m + 1)) :=
  GPoly.add (MOr Fc ks (m + 1)) (GPoly.mapD (MOr Fc ks (m + 1)) u)
    (GPoly.mul (MOr Fc ks (m + 1)) dθ (GPoly.derivX (MOr Fc ks (m + 1)) u))

/-- Ring operations on `θ`-polynomials (normalized). -/
def θOpsR (m : ℕ) : ROps (GPoly (LC (m + 1))) :=
  ⟨GPoly.add (MOr Fc ks (m + 1)), GPoly.mul (MOr Fc ks (m + 1)), GPoly.neg (MOr Fc ks (m + 1)), [],
    fun z ↦ [intC (MOr Fc ks (m + 1)) z]⟩

/-- **The components `gₖ` of `u′/u = u′ v`** (and `θ′`, `1/P_θ`). -/
def logDerCodes (m : ℕ) (Pp : List (GPoly (LC m))) (μ : List ℤ)
    (As Bs : List (List (GPoly (LC m)))) :
    Option (List (GPoly (LC (m + 1))) × GPoly (LC (m + 1)) × GPoly (LC (m + 1))) := do
  let O1 := MOr Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let dθ ← dThetaC O1 P
  let wθ ← invModC O1 P (GPoly.derivX O1 P)
  let R := θOpsR Fc ks m
  let c := nRed R μ (nConv R ((As.map (nkFl Fc ks m)).map (dCodeR Fc ks m dθ)) (Bs.map (nkFl Fc ks m)))
  pure ((List.range μ.length).map fun s ↦ remP O1 P (c.getD s []), dθ, wθ)

/-- Scalar ring operations (normalized). -/
def scOpsR (m : ℕ) : ROps (LC (m + 1)) :=
  ⟨(MOr Fc ks (m + 1)).add, (MOr Fc ks (m + 1)).mul, (MOr Fc ks (m + 1)).neg,
    (MOr Fc ks (m + 1)).zero, intC (MOr Fc ks (m + 1))⟩

/-- `e · f` in `ℚ(α)(x, t)`. -/
def nMulS (m : ℕ) (μ : List ℤ) (e f : List (LC (m + 1))) : List (LC (m + 1)) :=
  let r := nRed (scOpsR Fc ks m) μ (nConv (scOpsR Fc ks m) e f)
  (List.range μ.length).map fun s ↦ r.getD s (MOr Fc ks (m + 1)).zero

/-- `e⁻¹` in `ℚ(α)(x, t)` (the first column of the inverse multiplication matrix). -/
def nInvS (m : ℕ) (μ : List ℤ) (e : List (LC (m + 1))) : Option (List (LC (m + 1))) := do
  let d := μ.length
  let O := MOr Fc ks (m + 1)
  let basis : ℕ → List (LC (m + 1)) := fun l ↦ (List.range d).map fun s ↦ if s = l then O.one else O.zero
  let cols := (List.range d).map fun l ↦ nMulS Fc ks m μ e (basis l)
  let A := (List.range d).map fun s ↦ (List.range d).map fun l ↦ (cols.getD l []).getD s O.zero
  let Ai ← gjInvC Fc ks m d A
  pure ((List.range d).map fun s ↦ (Ai.getD s []).getD 0 O.zero)

/-- Gauss–Jordan inverse over `ℚ(α)(x, t)` (entries `ℚ(α)`-codes). -/
def gjInvN (m : ℕ) (μ : List ℤ) (k : ℕ) (A : List (List (List (LC (m + 1))))) :
    Option (List (List (List (LC (m + 1))))) :=
  let O := MOr Fc ks (m + 1)
  let d := μ.length
  let zN : List (LC (m + 1)) := List.replicate d O.zero
  let oN : List (LC (m + 1)) := O.one :: List.replicate (d - 1) O.zero
  let isZ : List (LC (m + 1)) → Bool := fun e ↦ e.all O.isZero
  let addN : List (LC (m + 1)) → List (LC (m + 1)) → List (LC (m + 1)) := fun e f ↦
    (List.range d).map fun s ↦ O.add (e.getD s O.zero) (f.getD s O.zero)
  let negN : List (LC (m + 1)) → List (LC (m + 1)) := fun e ↦ e.map O.neg
  let aug := (List.range k).map fun i ↦
    ((List.range k).map fun j ↦ (A.getD i []).getD j zN) ++
      (List.range k).map fun j ↦ if i = j then oN else zN
  let step : Option (List (List (List (LC (m + 1))))) → ℕ → Option (List (List (List (LC (m + 1))))) :=
    fun M? c ↦ do
      let M ← M?
      let p ← (List.range k).find? fun r ↦ c ≤ r && !isZ ((M.getD r []).getD c zN)
      let rp := M.getD p []
      let iv ← nInvS Fc ks m μ (rp.getD c zN)
      let rp' := rp.map (nMulS Fc ks m μ iv)
      let M1 := (List.range k).map fun r ↦
        if r = p then M.getD c [] else if r = c then rp' else M.getD r []
      pure ((List.range k).map fun r ↦
        if r = c then rp' else
          let f := (M1.getD r []).getD c zN
          (List.range (2 * k)).map fun j ↦ addN ((M1.getD r []).getD j zN)
            (negN (nMulS Fc ks m μ f (rp'.getD j zN))))
  ((List.range k).foldl step (some aug)).map fun M ↦ M.map fun r ↦ r.drop k

/-- **The independence certificate** `(J, H)` for the units with components `gss`: the first
`k`-subset `J` of the coordinates `1, …, n − 1` with an invertible minor. -/
def indepCodes (m : ℕ) (μ : List ℤ) (n : ℕ) (gss : List (List (GPoly (LC (m + 1))))) :
    Option (List ℕ × List (List (List (LC (m + 1))))) :=
  let k := gss.length
  let subsets : List (List ℕ) := ((List.range (n - 1)).map (· + 1)).sublists.filter (·.length = k)
  subsets.findSome? fun J ↦
    let A := (List.range k).map fun i ↦ J.map fun j ↦ coordN Fc ks m (gss.getD i []) j
    (gjInvN Fc ks m μ k A).map fun H ↦ (J, H)

end Codes

section Place

variable {MM : CPoly ℚ} [Fact (Irreducible (toPoly MM))]

/-- **The place certificate** of the fibre above `x′ = 0` of the inverted curve (one fibre,
places `reps`, `Γ_π = E_π`). -/
def placeCertInf (rf : RootFinder (NFC.NF MM)) (reps : List (PBranch (NFC.NF MM))) (Lp tp : ℕ) :
    Option (PlaceCert (NFC.NF MM)) := do
  let N := reps.foldr (fun b m ↦ Nat.lcm b.E m) 1
  let ω ← primRoot rf N
  let n := reps.foldr (fun b s ↦ b.E + s) 0
  pure ⟨[(0, N)], reps.map fun b ↦ (0, b.E, b.ser, Lp - 1),
    [(List.range reps.length).flatMap fun π ↦
      let b := reps.getD π ⟨1, []⟩
      (List.range b.E).map fun i ↦ (π, N / b.E, ω ^ i)],
    reps.map (·.E), [1], [n], 1, [tp]⟩

end Place

section Driver

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)
variable {MM : CPoly ℚ} [Fact (Irreducible (toPoly MM))]

/-- The certificates of the several-places decision. -/
structure InfUnitsCert (m : ℕ) (F : Type) where
  Ass : List (List (List (GPoly (LC m))))
  Bss : List (List (List (GPoly (LC m))))
  gss : List (List (GPoly (LC (m + 1))))
  dθ : GPoly (LC (m + 1))
  wθ : GPoly (LC (m + 1))
  s : List (LC (m + 1))
  J : List ℕ
  H : List (List (List (LC (m + 1))))
  Pc : PlaceCert F

/-- **All the certificates for the places at infinity**, computed: the places of the inverted curve
`invB (shiftB Fq 0) k0 M` above `x′ = 0` (over `ℚ(α)`, `α` a root of `MM`), units with divisors
`P_i − P_{r−1}` (multiples `≤ mmax`, degrees `≤ Bmax`), their logarithmic derivatives, the
independence certificate, the trace codes and the place certificate. -/
def autoInfUnits (rf : RootFinder (NFC.NF MM)) (m : ℕ) (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ)
    (k0 M Lp Bmax mmax : ℕ) (μ : List ℤ) : Option (InfUnitsCert m (NFC.NF MM)) := do
  let n := Pp.length
  let FcK : BPoly (NFC.NF MM) := (invB (shiftB Fq 0) k0 M).map (·.map (algebraMap ℚ (NFC.NF MM)))
  let bs ← branchesAuto rf FcK 0 Lp
  let reps := placeReps rf Lp bs
  let r := reps.length
  let us ← (List.range (r - 1)).mapM fun i ↦
    unitCodes Fc ks m n k0 Bmax mmax reps ((List.range r).map fun π ↦
      if π = i then 1 else if π = r - 1 then -1 else 0)
  let Ass := us.map (·.1)
  let Bss := us.map (·.2)
  let ls ← (List.range (r - 1)).mapM fun i ↦
    logDerCodes Fc ks m Pp μ (Ass.getD i []) (Bss.getD i [])
  let gss := ls.map (·.1)
  let (dθ, wθ) := match ls.head? with
    | some l => (l.2.1, l.2.2)
    | none => ([], [])
  let JH ← indepCodes Fc ks m μ n gss
  let Pc ← placeCertInf rf reps Lp 4
  pure ⟨Ass, Bss, gss, dθ, wθ, traceCodes Fc ks m (nkPC Fc ks m Pp), JH.1, JH.2, Pc⟩

end Driver

end Curves.MT
