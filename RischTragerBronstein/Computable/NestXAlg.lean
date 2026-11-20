import RischTragerBronstein.Computable.NestMInt
import RischTragerBronstein.Computable.NestP

/-!
# Mixed towers of logarithms and exponentials with nested data (algorithms)

Every level of `ks` is a logarithm `tₘ′ = ηₘ = vₘ′ / vₘ` (`ks m = .prim ηₘ`, `lv m = vₘ`) or an
exponential `tₘ = exp aₘ`. The Risch equation `y′ + f y = ∑ cᵢ wᵢ` is solved for
`f = h′ + ∑ⱼ cⱼ wⱼ′ / wⱼ` with constant `cⱼ` (`FRep`): this class is closed under the recursion
(values at `t = 0` and at infinity, the balanced case at a logarithmic level).

* `prdeX`: the parametric Risch equation (base: linear algebra; exponential level: special bound
  through `pldX`, degree bound, coefficient loop; logarithmic level: degree bound through limited
  integration one level down, coefficient loop);
* `paramLimX`, `paramElemX`: parametric limited / elementary integration with logarithmic steps
  (Hermite reduction, residue test, `paramPoly` / `polyElem`) and exponential steps;
* `certX`: the tower certificate; `elemNX`: the decision.
-/

namespace Tower.NestX

open Tower.PrimN Tower.NestP Tower.NestM CPoly

/-- `f = h′ + ∑ cⱼ wⱼ′ / wⱼ`, the `cⱼ` constants. -/
structure FRep (α : Type) where
  h : α
  logs : List (α × α)

section G

variable {α : Type} (O : COps α)

/-- The code of `f`. -/
def fCode (fr : FRep α) : α :=
  fr.logs.foldr (fun cw acc ↦ O.add (O.mul cw.1 (O.mul (O.deriv cw.2) (O.inv cw.2))) acc)
    (O.deriv fr.h)

/-- `p ^ N`. -/
def powG (p : GPoly α) : ℕ → GPoly α
  | 0 => [O.one]
  | N + 1 => GPoly.mul O p (powG p N)

/-- The leading coefficient `lc(n) / lc(d)` of a fraction. -/
def lcC (w : GPoly α × GPoly α) : α := O.mul (leadG O w.1) (O.inv (leadG O w.2))

/-- The trailing coefficient at `t = 0` of a fraction. -/
def tcC (w : GPoly α × GPoly α) : α :=
  O.mul (w.1.getD (lowZ O w.1) O.zero) (O.inv (w.2.getD (lowZ O w.2) O.zero))

/-- The degree of a fraction. -/
def degZ (w : GPoly α × GPoly α) : ℤ := (degG O w.1 : ℤ) - degG O w.2

/-- The order at `t = 0` of a fraction. -/
def ordZ (w : GPoly α × GPoly α) : ℤ := (lowZ O w.1 : ℤ) - lowZ O w.2

/-- The part of a polynomial prime to `t` (or all of it). -/
def nrmP (dropT : Bool) (p : GPoly α) : GPoly α :=
  if GPoly.isZero O p then [O.one] else if dropT then p.drop (lowZ O p) else p

/-- The product of the numerators and denominators of the `wⱼ` (their normal parts). -/
def logPoly (dropT : Bool) (logs : List ((GPoly α × GPoly α) × (GPoly α × GPoly α))) : GPoly α :=
  logs.foldr (fun cw acc ↦ GPoly.mul O (GPoly.mul O (nrmP O dropT cw.2.1) (nrmP O dropT cw.2.2)) acc)
    [O.one]

/-- `f - Q′ / Q`, cleaned. -/
def peFX (O' : COps (GPoly α × GPoly α)) (fc : GPoly α × GPoly α) (Q : GPoly α) :
    GPoly α × GPoly α :=
  cleanG O (O'.add fc (O'.neg (O'.mul (O'.deriv (Q, [O.one])) (O'.inv (Q, [O.one])))))

/-- The right-hand sides `Q wᵢ`. -/
def peRsX (O' : COps (GPoly α × GPoly α)) (Wc : List (GPoly α × GPoly α)) (Q : GPoly α) :
    List (GPoly α × GPoly α) :=
  Wc.map fun q ↦ cleanG O (O'.mul (Q, [O.one]) q)

/-- The normal denominator bound `gcd(e, e′) · L ^ N`, monic. -/
def peDX (wk e L : GPoly α) (N : ℕ) : GPoly α :=
  monicG O (GPoly.mul O (GPoly.egcd O e (GPoly.derivT O wk e)).1 (powG O L N))

end G

/-- Integer vectors with `|vⱼ| ≤ dⱼ`. -/
def intVecs : List ℕ → List (List ℤ)
  | [] => [[]]
  | d :: ds => (intVecs ds).flatMap fun v ↦ (List.range (2 * d + 1)).map fun i ↦ ((i : ℤ) - d) :: v

/-- The rational value of a constant code, if rational. -/
def ratVal (ks : (m : ℕ) → KindN m) (m : ℕ) (c : Code (m + 1)) : Option ℚ :=
  match (consys ks m [c, (opsM ks m).one]).find? (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u => some (-(u.getD 1 0) / u.getD 0 0)
  | none => none

/-- A bound on the positive integer residues of `∑ cⱼ wⱼ′ / wⱼ` at the normal primes (codes of
level `m + 1`): every residue is `∑ cⱼ vⱼ` with `|vⱼ| ≤ deg wⱼ`. -/
def logBound (ks : (m : ℕ) → KindN m) (m : ℕ) (logs : List (Code (m + 2) × Code (m + 2))) : ℕ :=
  let O := opsM ks m
  let O' := opsM ks (m + 1)
  (intVecs (logs.map fun cw ↦ degG O cw.2.1 + degG O cw.2.2)).foldr (fun (v : List ℤ) acc ↦
    let code := (List.zip v logs).foldr (fun p acc2 ↦
      O'.add (O'.mul (cstN (m + 1) ((p.1 : ℤ) : ℚ)) p.2.1) acc2) O'.zero
    match ratVal ks (m + 1) code with
    | some q => max acc ((natOfQ q).getD 0)
    | none => acc) 0

/-- The same bound at the base. -/
def logBound0 (ks : (m : ℕ) → KindN m) (logs : List (Code 1 × Code 1)) : ℕ :=
  let O := opsM ks 0
  (intVecs (logs.map fun cw ↦ cdeg cw.2.1 + cdeg cw.2.2)).foldr (fun (v : List ℤ) acc ↦
    let code := (List.zip v logs).foldr (fun p acc2 ↦
      O.add (O.mul (cstN 0 ((p.1 : ℤ) : ℚ)) p.2.1) acc2) O.zero
    match ratVal ks 0 code with
    | some q => max acc ((natOfQ q).getD 0)
    | none => acc) 0

/-- The derivatives of the generators below level `m` (`ηᵢ` for a logarithm, `aᵢ′` for an
exponential), as codes of level `m`. -/
def gensD (ks : (m : ℕ) → KindN m) : (m : ℕ) → List (Code (m + 1))
  | 0 => []
  | m + 1 => ((gensD ks m) ++ [match ks m with
      | .exp a => (opsM ks m).deriv a
      | .prim η => η]).map (liftE ks m)

/-- **The logarithmic-derivative bound in mixed towers**: the only rational `μ` for which
`(V + μ a)′` can be a combination of logarithmic derivatives in `Kₘ`. -/
def pldX (ks : (m : ℕ) → KindN m) (m : ℕ) (V a : Code (m + 1)) : Option ℚ :=
  let O := opsM ks m
  match (consys ks m (O.deriv V :: O.deriv a :: gensD ks m)).find? (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u => some (u.getD 1 0 / u.getD 0 0)
  | none => none

/-! ### The Risch equation at the base -/

/-- The body at the base, for `f` and a denominator bound `D`. -/
def prde0BF (fc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : List (List ℚ × GFrac ℚ) :=
  let O := ops₁g ℚ
  let n := Wc.length
  let Dc : GFrac ℚ := (D, [1])
  let F := cleanQ (O.add fc (O.neg (O.mul (O.deriv Dc) (O.inv Dc))))
  let Rs := Wc.map fun w ↦ cleanQ (O.mul Dc w)
  let P := prodD CPoly.mul [1] Rs
  let A := CPoly.mul F.2 P
  let B := CPoly.mul F.1 P
  let Cs := (cross CPoly.mul [1] Rs).map (CPoly.mul F.2)
  let R := (Cs.map cdeg).foldr max 0
  let ys : List (CPoly ℚ) := (List.range (degBoundU A B R + 1)).map (colY A B)
  (nullBasis (Cs.map CPoly.neg ++ ys)).map fun u ↦
    ((List.range n).map (u.getD · 0), (((List.range ys.length).map fun k ↦ u.getD (n + k) 0), D))

/-- **The parametric Risch equation over `ℚ(x)`** for `f = h′ + ∑ cⱼ wⱼ′ / wⱼ`. -/
def prde0X (ks : (m : ℕ) → KindN m) (fr : FRep (GFrac ℚ)) (W : List (GFrac ℚ)) :
    List (List ℚ × GFrac ℚ) :=
  let Wc := W.map cleanQ
  let e := Wc.foldr (fun w acc ↦ lcmQ w.2 acc) [1]
  let L := fr.logs.foldr (fun (cw : GFrac ℚ × GFrac ℚ) (acc : CPoly ℚ) ↦ CPoly.mul (CPoly.mul (if CPoly.isZero cw.2.1 then [1] else cw.2.1)
    (if CPoly.isZero cw.2.2 then [1] else cw.2.2)) acc) [1]
  let D := CPoly.mul (CPoly.egcd e (CPoly.deriv e)).1 ((List.range (logBound0 ks fr.logs)).foldr
    (fun _ acc ↦ CPoly.mul L acc) [1])
  if CPoly.isZero D then [] else prde0BF (fCode (ops₁g ℚ) fr) Wc D

/-! ### The Risch equation over an exponential level -/

/-- The degree bound over an exponential (as `peNb`, the balanced case shifted by `sd = ∑ cⱼ deg wⱼ`). -/
def peNbE {α : Type} (O : COps α) (pl : Option ℚ) (sd : Option ℚ) (A B : GPoly α) (R dDk : ℕ) :
    Option ℕ :=
  let dA := degG O A
  let dB := degG O B
  if GPoly.isZero O B then some (R - dA)
  else if dA < dB then (if dB ≤ R then some (R - dB) else none)
  else if dB < dA then some (R - dA)
  else
    match pl, sd with
    | some μ, some s => match natOfQ (μ - s + (dDk : ℚ)) with
      | some N' => some (max (R - dA) N')
      | none => some (R - dA)
    | _, _ => some (R - dA)

/-- **The parametric Risch equation over an exponential level** `t = exp a`. -/
def prdeExpX (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1))
    (lower : FRep (Code (m + 1)) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (fr : FRep (Code (m + 2))) (W : List (Code (m + 2))) : List (List ℚ × Code (m + 2)) :=
  let O := opsM ks m
  let wk : GPoly (Code (m + 1)) := wK O (ks m)
  let O' := O.monomial wk
  let cst := cstN m
  let fc := fCode O' fr
  let hc := cleanG O fr.h
  let Wc := W.map (cleanG O)
  let n := Wc.length
  let eps := peEps O Wc
  let e := peE O Wc
  let D := peDX O wk e (logPoly O true fr.logs) (logBound ks m fr.logs)
  let dD := degG O D
  -- the logarithms with `w ≠ 0` (a zero `w` contributes nothing to `f`)
  let logsC := (fr.logs.filter fun cw ↦ !GPoly.isZero O cw.2.1 && !GPoly.isZero O cw.2.2).map
    fun cw ↦ (lcC O cw.1, cw.2)
  -- the special bound at `t = 0`
  let sumOrd := logsC.foldr (fun cw acc ↦ O.add (O.mul cw.1 (cst (ordZ O cw.2 : ℚ))) acc) O.zero
  let kap :=
    if !GPoly.isZero O hc.1 && decide (lowZ O hc.1 < lowZ O hc.2) then eps
    else match (pldX ks m (O.neg (peH0 O hc)) a), ratVal ks m sumOrd with
      | some μ, some so => match natOfQ (μ + so) with
        | some k => max eps k
        | none => eps
      | _, _ => eps
  let Q := peQ O kap D
  let F := peFX O O' fc Q
  let Rs := peRsX O O' Wc Q
  let A := peA O F Rs
  let B := peB O F Rs
  let Cs := peCs O F Rs
  let R := (Cs.map (degG O)).foldr max 0
  let dA := degG O A
  let bZ := GPoly.isZero O B
  let dB := degG O B
  let hInf := peHinf O hc
  let sumDeg := logsC.foldr (fun cw acc ↦ O.add (O.mul cw.1 (cst (degZ O cw.2 : ℚ))) acc) O.zero
  let hB := O.add hInf (O.mul (O.add sumDeg (cst (-((dD + kap : ℕ) : ℚ)))) a)
  let logsL := logsC.map fun cw ↦ (cw.1, lcC O cw.2)
  let balancedOk := O.isZero (O.add (fCode O ⟨hB, logsL⟩)
    (O.neg (O.mul (leadG O B) (O.inv (leadG O A)))))
  let Nb := peNbE O (pldX ks m hInf a) (ratVal ks m sumDeg) A B R (dD + kap)
  let alg := !bZ && decide (dA < dB)
  let δ := if alg then dB else dA
  let lower' : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)) := fun k ws ↦
    if bZ || decide (dB < dA) then lower ⟨O.mul (cst (k : ℚ)) a, []⟩ ws
    else lower ⟨O.add hB (O.mul (cst (k : ℚ)) a), logsL⟩ ws
  let init := (List.range n).map fun i ↦ (unitV n i, ([] : GPoly (Code (m + 1))))
  let Bs := match Nb with
    | none => init
    | some N => rdeLoop O cst wk A B Cs n δ alg (leadG O A) (leadG O B) lower' (N + 1) init
  if !bZ && !alg && decide (dA = dB) && !balancedOk then []
  else peOut ks m wk A B Cs n Q Bs

/-! ### The Risch equation over a logarithmic level -/

/-- The largest natural `n` with `z′ + n η = ρ` solvable (read off a limited-integration basis for
`[ρ, η]`). -/
def limN {α : Type} (lim : List α → List (List ℚ × α)) (ρ η : α) : ℕ :=
  (lim [ρ, η]).foldr (fun r acc ↦
    if r.1.getD 0 0 ≠ 0 then max acc ((natOfQ (-(r.1.getD 1 0) / r.1.getD 0 0)).getD 0) else acc) 0

/-- **The parametric Risch equation over a logarithmic level** `t′ = η = v′ / v`. -/
def prdePrimX (ks : (m : ℕ) → KindN m) (m : ℕ) (η v : Code (m + 1))
    (lower : FRep (Code (m + 1)) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (fr : FRep (Code (m + 2))) (W : List (Code (m + 2))) : List (List ℚ × Code (m + 2)) :=
  let O := opsM ks m
  let wk : GPoly (Code (m + 1)) := wK O (ks m)
  let O' := O.monomial wk
  let cst := cstN m
  let fc := fCode O' fr
  let hc := cleanG O fr.h
  let Wc := W.map (cleanG O)
  let n := Wc.length
  let e := lcmList O (Wc.map Prod.snd)
  let D := peDX O wk e (logPoly O false fr.logs) (logBound ks m fr.logs)
  let Q := D
  let F := peFX O O' fc Q
  let Rs := peRsX O O' Wc Q
  let A := peA O F Rs
  let B := peB O F Rs
  let Cs := peCs O F Rs
  let R := (Cs.map (degG O)).foldr max 0
  let dA := degG O A
  let bZ := GPoly.isZero O B
  let dB := degG O B
  let lcA := leadG O A
  let lcB := leadG O B
  let Finf := O.mul lcB (O.inv lcA)
  -- the lower `f` in the balanced case: `h₁ η + h₀′ + ∑ cⱼ lc(wⱼ)′ / lc(wⱼ)`
  let qH := (GPoly.divMod O hc.1 hc.2).1
  let lowF : FRep (Code (m + 1)) :=
    ⟨qH.getD 0 O.zero, (qH.getD 1 O.zero, v) :: fr.logs.map fun cw ↦ (lcC O cw.1, lcC O cw.2)⟩
  let Am := if dA = 0 then O.zero else A.getD (dA - 1) O.zero
  let Bm := if dA = 0 then O.zero else B.getD (dA - 1) O.zero
  let β := O.neg (O.mul (O.add (O.mul Am (O.neg Finf)) Bm) (O.inv lcA))
  let Nb : Option ℕ :=
    if bZ then some (R - dA + 1)
    else if dA < dB then (if dB ≤ R then some (R - dB) else none)
    else if dB + 1 < dA then some (R - dA + 1)
    else if dB + 1 = dA then some (max (R - dA + 1) (limN lim (O.neg Finf) η))
    else some (max (R - dA + 1) (limN lim β η))
  let alg := !bZ && decide (dA < dB)
  let balanced := !bZ && decide (dA = dB)
  let δ := if alg then dB else dA
  let lower' : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)) := fun _ ws ↦
    if balanced then lower lowF ws else lim ws ++ [([], O.one)]
  let init := (List.range n).map fun i ↦ (unitV n i, ([] : GPoly (Code (m + 1))))
  let Bs := match Nb with
    | none => init
    | some N => rdeLoop O cst wk A B Cs n δ alg lcA lcB lower' (N + 1) init
  if balanced && !O.isZero (O.add (fCode O lowF) (O.neg Finf)) then []
  else peOut ks m wk A B Cs n Q Bs

/-! ### Limited integration: steps -/

/-- The exponential step, with a Risch-equation solver `rde h` for `y′ + h′ y`. -/
def expLimStepX (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1))
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (W : List (Code (m + 2))) : List (List ℚ × Code (m + 2)) :=
  let O := opsM ks m
  let O' := opsM ks (m + 1)
  let wk : GPoly (Code (m + 1)) := wK O (ks m)
  let n := W.length
  let Sp := W.map (expSplit O wk)
  let U := consys ks (m + 1) (Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2)))
  let E := U.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
  let S := laurentS Sp
  let Ls := Sp.map (shiftedL O S)
  let Pu := E.map fun e ↦ lcombGP O (cstN m) e Ls
  let top := (Pu.map List.length).foldr max 0
  let A : GPoly (Code (m + 1)) := [O.one]
  let B : GPoly (Code (m + 1)) := [O.mul (cstN m (-(S : ℚ))) (O.deriv a)]
  let solve : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)) := fun i ws ↦
    if i = S then lim ws ++ [([], O.one)]
    else rde (O.mul (cstN m ((i : ℚ) - S)) a) ws
  let init := (List.range E.length).map fun i ↦
    (unitV E.length i, ([] : GPoly (Code (m + 1))))
  (rdeLoop O (cstN m) wk A B Pu E.length 0 false O.one O.one solve (max top S + 1) init).map
    fun b ↦
    let c := vcomb n b.1 E
    (c, O'.add (lcombCode O' (cstN (m + 1)) c (Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))))
      ((b.2, powX O S) : Code (m + 2)))

/-- The logarithmic step: Hermite reduction, the constant system on the simple parts, and the
parametric polynomial problem one level down. -/
def primLimStep (ks : (m : ℕ) → KindN m) (m : ℕ) (η : Code (m + 1))
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (W : List (Code (m + 2))) : List (List ℚ × Code (m + 2)) :=
  let O := opsM ks m
  let O' := opsM ks (m + 1)
  let n := W.length
  let H := W.map fun w ↦
    let w' := cleanG O w
    GPoly.hermite O (wK O (ks m)) w'.1 w'.2
  let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
  let U := consys ks (m + 1) ((List.zip QR H).map fun p ↦ ((p.1.2, p.2.s) : Code (m + 2)))
  let E := U.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
  let Pu := E.map fun e ↦ lcombGP O (cstN m) e (QR.map Prod.fst)
  (paramPoly O (cstN m) η lim Pu).map fun r ↦
    let c := vcomb n r.1 E
    (c, O'.add (lcombCode O' (cstN (m + 1)) c (H.map fun h ↦ ((h.gn, h.gd) : Code (m + 2))))
      ((r.2, [O.one]) : Code (m + 2)))

mutual

/-- **The parametric Risch equation** in mixed towers. -/
def prdeX (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) : (m : ℕ) →
    FRep (Code (m + 1)) → List (Code (m + 1)) → List (List ℚ × Code (m + 1))
  | 0, fr, W => prde0X ks fr W
  | m + 1, fr, W =>
    match ks m with
    | .exp a => prdeExpX ks m a (prdeX ks lv m) fr W
    | .prim η => prdePrimX ks m η (lv m) (prdeX ks lv m) (paramLimX ks lv m) fr W

/-- **Parametric limited integration** in mixed towers. -/
def paramLimX (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) : (m : ℕ) →
    List (Code (m + 1)) → List (List ℚ × Code (m + 1))
  | 0, W => paramLim0 ks W
  | m + 1, W =>
    match ks m with
    | .exp a => expLimStepX ks m a (paramLimX ks lv m) (fun h ↦ prdeX ks lv m ⟨h, []⟩) W
    | .prim η => primLimStep ks m η (paramLimX ks lv m) W

end

/-! ### Elementary integration: steps -/

/-- The exponential step (as `expElemStep`, with the Risch solver as a parameter). -/
def expElemStepX (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1))
    (elem : List (Code (m + 1)) → List (List ℚ))
    (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (W : List (Code (m + 2))) : List (List ℚ) :=
  let O := opsM ks m
  let wk : GPoly (Code (m + 1)) := wK O (ks m)
  let n := W.length
  let Sp := W.map (expSplit O wk)
  let Sd := lcmList O (Sp.map ExpSplit.s)
  if GPoly.squarefreeCheck O Sd &&
      Sp.all (fun e ↦ GPoly.isZero O (GPoly.divMod O Sd e.s).2) then
    let N := Sp.map fun e ↦ GPoly.mul O e.r (GPoly.divMod O Sd e.s).1
    let Tt := N.map fun Ni ↦
      (GPoly.divMod O (residueTestCode O (GPoly.residuePoly O wk Ni Sd) Sd) Sd).2
    let U1 := consys ks (m + 1) (Tt.map fun T ↦ ((T, [O.one]) : Code (m + 2)))
    let E1 := U1.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
    let S := laurentS Sp
    let Ls := Sp.map (shiftedL O S)
    let Pu := E1.map fun e ↦ lcombGP O (cstN m) e Ls
    let top := (Pu.map List.length).foldr max 0
    let solve : ℕ → List (List ℚ) → List (List ℚ) := fun i Bs ↦
      let ws := Bs.map fun β ↦ lcombCode O (cstN m) β (Pu.map fun L ↦ L.getD i O.zero)
      if i = S then elem ws
      else (rde (O.mul (cstN m ((i : ℚ) - S)) a) ws).map Prod.fst
    let init := (List.range E1.length).map (unitV E1.length)
    (elemLoop E1.length solve top init).map fun δ ↦ vcomb n δ E1
  else []

/-- The logarithmic step (Hermite reduction, the residue test, `polyElem`). -/
def primElemStep (ks : (m : ℕ) → KindN m) (m : ℕ) (η : Code (m + 1))
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (elem : List (Code (m + 1)) → List (List ℚ)) (W : List (Code (m + 2))) : List (List ℚ) :=
  let O := opsM ks m
  let n := W.length
  let H := W.map fun w ↦
    let w' := cleanG O w
    GPoly.hermite O (wK O (ks m)) w'.1 w'.2
  let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
  let S := lcmList O (H.map fun h ↦ h.s)
  if GPoly.squarefreeCheck O S && H.all (fun h ↦ GPoly.isZero O (GPoly.divMod O S h.s).2) then
    let N := (List.zip QR H).map fun p ↦ GPoly.mul O p.1.2 (GPoly.divMod O S p.2.s).1
    let Tt := N.map fun Ni ↦
      (GPoly.divMod O (residueTestCode O (GPoly.residuePoly O (wK O (ks m)) Ni S) S) S).2
    let U1 := consys ks (m + 1) (Tt.map fun T ↦ ((T, [O.one]) : Code (m + 2)))
    let E1 := U1.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
    let Pu := E1.map fun e ↦ lcombGP O (cstN m) e (QR.map Prod.fst)
    (polyElem O (cstN m) η lim elem Pu).map fun δ ↦ vcomb n δ E1
  else []

/-- **Parametric elementary integration** in mixed towers. -/
def paramElemX (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) : (m : ℕ) →
    List (Code (m + 1)) → List (List ℚ)
  | 0, W => (List.range W.length).map (unitV W.length)
  | m + 1, W =>
    match ks m with
    | .exp a => expElemStepX ks m a (paramElemX ks lv m) (fun h ↦ prdeX ks lv m ⟨h, []⟩) W
    | .prim η => primElemStep ks m η (paramLimX ks lv m) (paramElemX ks lv m) W

/-- **The tower certificate**: each logarithm `ηₘ = vₘ′ / vₘ` has no antiderivative in `Kₘ`;
each exponent `aₘ′` is not a rational combination of the derivatives of the lower generators. -/
def certX (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) (n : ℕ) : Bool :=
  (List.range n).all fun m ↦
    let O := opsM ks m
    match ks m with
    | .prim η => !O.isZero (lv m) &&
        O.isZero (O.add η (O.neg (O.mul (O.deriv (lv m)) (O.inv (lv m))))) &&
        (paramLimX ks lv m [η]).all fun r ↦ r.1.getD 0 0 == 0
    | .exp a => (consys ks m (O.deriv a :: gensD ks m)).all fun u ↦ u.getD 0 0 == 0

/-- **Does `A ∈ Kₘ` have an elementary integral?** -/
def elemNX (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) (m : ℕ) (A : Code (m + 1)) :
    Bool :=
  (paramElemX ks lv m [A]).any fun e ↦ e.getD 0 0 ≠ 0

end Tower.NestX
