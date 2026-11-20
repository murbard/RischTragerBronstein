import RischTragerBronstein.Mixed.MTBasics
import RischTragerBronstein.Mixed.MTRed
import RischTragerBronstein.Mixed.CurveRdeL
import RischTragerBronstein.Computable.NestXAlg

/-!
# Mixed towers over a curve: the algorithms

Ported from `Tower.NestX` (`NestXAlg`): every level of `ks` is a logarithm (`tₘ′ = ηₘ = vₘ′ / vₘ`,
`lv m = vₘ`) or an exponential `tₘ = exp aₘ`, over the function field of the curve `Fc`.

* `prdeC`: the parametric Risch equation `y′ + f y = ∑ cᵢ wᵢ` for `f = h′ + ∑ cⱼ wⱼ′/wⱼ`
  (base: `curveRdeL`, the coefficients `cⱼ` read off as rationals; exponential level: special bound
  through `pldC`, degree bound, coefficient loop; logarithmic level: degree bound through limited
  integration one level down, coefficient loop);
* `paramLimC`: parametric limited integration (base: `curveRde` with `h = 0`; logarithmic level:
  Hermite reduction, constant system, `paramPoly`; exponential level: Laurent coefficients);
* `certC`: the tower certificate.
-/

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- A code of level `m` as a code of level `m + 1`. -/
def liftEC (m : ℕ) (q : LC m) : LC (m + 1) :=
  (([q] : GPoly (LC m)), ([(MO Fc ks m).one] : GPoly (LC m)))

/-- The final constant system: the combinations of the basis `Bs` with a zero residual. -/
def peOutC (m : ℕ) (w A B : GPoly (LC m)) (Cs : List (GPoly (LC m))) (n : ℕ)
    (Q : GPoly (LC m)) (Bs : List (List ℚ × GPoly (LC m))) : List (List ℚ × LC (m + 1)) :=
  let O := MO Fc ks m
  let U := mrel Fc ks (m + 1) (Bs.map fun b ↦
    ((residE O (mcst Fc ks m) w A B Cs b, [O.one]) : GFrac (LC m)))
  U.map fun u ↦
    let β := (List.range Bs.length).map (u.getD · 0)
    (vcomb n β (Bs.map Prod.fst),
      ((lcombGP O (mcst Fc ks m) β (Bs.map Prod.snd), Q) : GFrac (LC m)))

/-- A bound on the positive integer residues of `∑ cⱼ wⱼ′ / wⱼ` at the normal primes (codes of
level `m + 1`): every residue is `∑ cⱼ vⱼ` with `|vⱼ| ≤ deg wⱼ`. -/
def logBoundC (m : ℕ) (logs : List (LC (m + 1) × LC (m + 1))) : ℕ :=
  let O := MO Fc ks m
  let O' := MO Fc ks (m + 1)
  (intVecs (logs.map fun cw ↦ degG O (cw.2 : GFrac (LC m)).1 + degG O (cw.2 : GFrac (LC m)).2)).foldr
    (fun (v : List ℤ) acc ↦
    let code := (List.zip v logs).foldr (fun p acc2 ↦
      O'.add (O'.mul (mcst Fc ks (m + 1) ((p.1 : ℤ) : ℚ)) p.2.1) acc2) O'.zero
    match ratValC Fc ks (m + 1) code with
    | some q => max acc ((natOfQ q).getD 0)
    | none => acc) 0

/-- The derivatives of the generators below level `m` (`ηᵢ` for a logarithm, `aᵢ′` for an
exponential), as codes of level `m`. -/
def gensDC : (m : ℕ) → List (LC m)
  | 0 => []
  | m + 1 => ((gensDC m) ++ [match ks m with
      | .exp a => (MO Fc ks m).deriv a
      | .prim η => η]).map (liftEC Fc ks m)

/-- **The logarithmic-derivative bound in mixed towers**: the only rational `μ` for which
`(V + μ a)′` can be a combination of logarithmic derivatives in `Kₘ`. -/
def pldC (m : ℕ) (V a : LC m) : Option ℚ :=
  let O := MO Fc ks m
  match (mrel Fc ks m (O.deriv V :: O.deriv a :: gensDC Fc ks m)).find?
      (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u => some (u.getD 1 0 / u.getD 0 0)
  | none => none

/-! ### The Risch equation at the base: the curve -/

/-- The logarithmic part with rational coefficients (a constant curve code is rational); the
logarithms of `0` (which contribute nothing) are dropped. -/
def logsQ (logs : List (LC 0 × LC 0)) : List (ℚ × GPoly (GFrac ℚ)) :=
  (logs.filter fun cw ↦ !(MO Fc ks 0).isZero cw.2).map fun cw ↦
    ((ratValC Fc ks 0 cw.1).getD 0, cw.2)

/-- **The parametric Risch equation on the curve** for `f = h′ + ∑ cⱼ wⱼ′ / wⱼ`. -/
def prde0C (fr : FRep (LC 0)) (W : List (LC 0)) : List (List ℚ × LC 0) :=
  curveRdeL Fc fr.h (logsQ Fc ks fr.logs) W

/-! ### The Risch equation over an exponential level -/

/-- **The parametric Risch equation over an exponential level** `t = exp a`. -/
def prdeExpC (m : ℕ) (a : LC m)
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (fr : FRep (LC (m + 1))) (W : List (LC (m + 1))) : List (List ℚ × LC (m + 1)) :=
  let O := MO Fc ks m
  let wk : GPoly (LC m) := wKC O (ks m)
  let O' := O.monomial wk
  let cst := mcst Fc ks m
  let fc := fCode O' fr
  let hc := cleanG O fr.h
  let Wc := W.map (cleanG O)
  let n := Wc.length
  let eps := peEps O Wc
  let e := peE O Wc
  let D := peDX O wk e (logPoly O true fr.logs) (logBoundC Fc ks m fr.logs)
  let dD := degG O D
  let logsC := (fr.logs.filter fun cw ↦ !GPoly.isZero O (cw.2 : GFrac (LC m)).1 &&
    !GPoly.isZero O (cw.2 : GFrac (LC m)).2).map fun cw ↦ (lcC O cw.1, cw.2)
  let sumOrd := logsC.foldr (fun cw acc ↦ O.add (O.mul cw.1 (cst (ordZ O cw.2 : ℚ))) acc) O.zero
  let kap :=
    if !GPoly.isZero O hc.1 && decide (lowZ O hc.1 < lowZ O hc.2) then eps
    else match (pldC Fc ks m (O.neg (peH0 O hc)) a), ratValC Fc ks m sumOrd with
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
  let Nb := peNbE O (pldC Fc ks m hInf a) (ratValC Fc ks m sumDeg) A B R (dD + kap)
  let alg := !bZ && decide (dA < dB)
  let δ := if alg then dB else dA
  let lower' : ℕ → List (LC m) → List (List ℚ × LC m) := fun k ws ↦
    if bZ || decide (dB < dA) then lower ⟨O.mul (cst (k : ℚ)) a, []⟩ ws
    else lower ⟨O.add hB (O.mul (cst (k : ℚ)) a), logsL⟩ ws
  let init := (List.range n).map fun i ↦ (unitV n i, ([] : GPoly (LC m)))
  let Bs := match Nb with
    | none => init
    | some N => rdeLoop O cst wk A B Cs n δ alg (leadG O A) (leadG O B) lower' (N + 1) init
  if !bZ && !alg && decide (dA = dB) && !balancedOk then []
  else peOutC Fc ks m wk A B Cs n Q Bs

/-! ### The Risch equation over a logarithmic level -/

/-- **The parametric Risch equation over a logarithmic level** `t′ = η = v′ / v`. -/
def prdePrimC (m : ℕ) (η v : LC m)
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (lim : List (LC m) → List (List ℚ × LC m))
    (fr : FRep (LC (m + 1))) (W : List (LC (m + 1))) : List (List ℚ × LC (m + 1)) :=
  let O := MO Fc ks m
  let wk : GPoly (LC m) := wKC O (ks m)
  let O' := O.monomial wk
  let cst := mcst Fc ks m
  let fc := fCode O' fr
  let hc := cleanG O fr.h
  let Wc := W.map (cleanG O)
  let n := Wc.length
  let e := lcmList O (Wc.map Prod.snd)
  let D := peDX O wk e (logPoly O false fr.logs) (logBoundC Fc ks m fr.logs)
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
  let qH := (GPoly.divMod O hc.1 hc.2).1
  let lowF : FRep (LC m) :=
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
  let lower' : ℕ → List (LC m) → List (List ℚ × LC m) := fun _ ws ↦
    if balanced then lower lowF (ws.map (redL Fc ks m))
    else lim (ws.map (redL Fc ks m)) ++ [([], O.one)]
  let init := (List.range n).map fun i ↦ (unitV n i, ([] : GPoly (LC m)))
  let Bs := match Nb with
    | none => init
    | some N => rdeLoop O cst wk A B Cs n δ alg lcA lcB lower' (N + 1) init
  if balanced && !O.isZero (O.add (fCode O lowF) (O.neg Finf)) then []
  else peOutC Fc ks m wk A B Cs n Q Bs

/-! ### Limited integration: steps -/

/-- The exponential step, with a Risch-equation solver `rde h` for `y′ + h′ y`. -/
def expLimStepC (m : ℕ) (a : LC m)
    (lim : List (LC m) → List (List ℚ × LC m))
    (rde : LC m → List (LC m) → List (List ℚ × LC m))
    (W : List (LC (m + 1))) : List (List ℚ × LC (m + 1)) :=
  let O := MO Fc ks m
  let O' := MO Fc ks (m + 1)
  let wk : GPoly (LC m) := wKC O (ks m)
  let n := W.length
  let Sp := W.map (expSplit O wk)
  let U := mrel Fc ks (m + 1) (Sp.map fun e ↦ ((e.r, e.s) : GFrac (LC m)))
  let E := U.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
  let S := laurentS Sp
  let Ls := Sp.map (shiftedL O S)
  let Pu := E.map fun e ↦ lcombGP O (mcst Fc ks m) e Ls
  let top := (Pu.map List.length).foldr max 0
  let A : GPoly (LC m) := [O.one]
  let B : GPoly (LC m) := [O.mul (mcst Fc ks m (-(S : ℚ))) (O.deriv a)]
  let solve : ℕ → List (LC m) → List (List ℚ × LC m) := fun i ws ↦
    if i = S then lim ws ++ [([], O.one)]
    else rde (O.mul (mcst Fc ks m ((i : ℚ) - S)) a) ws
  let init := (List.range E.length).map fun i ↦
    (unitV E.length i, ([] : GPoly (LC m)))
  (rdeLoop O (mcst Fc ks m) wk A B Pu E.length 0 false O.one O.one solve (max top S + 1)
      init).map
    fun b ↦
    let c := vcomb n b.1 E
    (c, O'.add (lcombCode O' (mcst Fc ks (m + 1)) c
        (Sp.map fun e ↦ ((e.gn, e.gd) : GFrac (LC m))))
      ((b.2, powX O S) : GFrac (LC m)))

/-- The logarithmic step: Hermite reduction, the constant system on the simple parts, and the
parametric polynomial problem one level down. -/
def primLimStepC (m : ℕ) (η : LC m)
    (lim : List (LC m) → List (List ℚ × LC m))
    (W : List (LC (m + 1))) : List (List ℚ × LC (m + 1)) :=
  let O := MO Fc ks m
  let O' := MO Fc ks (m + 1)
  let n := W.length
  let H := W.map fun w ↦
    let w' := cleanG O w
    GPoly.hermite O (wKC O (ks m)) w'.1 w'.2
  let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
  let U := mrel Fc ks (m + 1) ((List.zip QR H).map fun p ↦ ((p.1.2, p.2.s) : GFrac (LC m)))
  let E := U.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
  let Pu := E.map fun e ↦ lcombGP O (mcst Fc ks m) e (QR.map Prod.fst)
  (paramPoly O (mcst Fc ks m) η lim Pu).map fun r ↦
    let c := vcomb n r.1 E
    (c, O'.add (lcombCode O' (mcst Fc ks (m + 1)) c
        (H.map fun h ↦ ((h.gn, h.gd) : GFrac (LC m))))
      ((r.2, [O.one]) : GFrac (LC m)))

mutual

/-- **The parametric Risch equation** in mixed towers over a curve. -/
def prdeC : (m : ℕ) → FRep (LC m) → List (LC m) → List (List ℚ × LC m)
  | 0, fr, W => prde0C Fc ks fr W
  | m + 1, fr, W =>
    match ks m with
    | .exp a => prdeExpC Fc ks m a (prdeC m) fr W
    | .prim η => prdePrimC Fc ks m η (lv m) (prdeC m) (paramLimC m) fr W

/-- **Parametric limited integration** in mixed towers over a curve. -/
def paramLimC : (m : ℕ) → List (LC m) → List (List ℚ × LC m)
  | 0, W => curveRde Fc (curveOps Fc).zero W
  | m + 1, W =>
    match ks m with
    | .exp a => expLimStepC Fc ks m a (paramLimC m) (fun h ↦ prdeC m ⟨h, []⟩) W
    | .prim η => primLimStepC Fc ks m η (paramLimC m) W

end

/-- **The tower certificate**: each logarithm `ηₘ = vₘ′ / vₘ` has no antiderivative in `Kₘ`;
each exponent `aₘ′` is not a rational combination of the derivatives of the lower generators. -/
def certC (n : ℕ) : Bool :=
  (List.range n).all fun m ↦
    let O := MO Fc ks m
    match ks m with
    | .prim η => !O.isZero (lv m) &&
        O.isZero (O.add η (O.neg (O.mul (O.deriv (lv m)) (O.inv (lv m))))) &&
        (paramLimC Fc ks lv m [η]).all fun r ↦ r.1.getD 0 0 == 0
    | .exp a => (mrel Fc ks m (O.deriv a :: gensDC Fc ks m)).all fun u ↦ u.getD 0 0 == 0

end Curves.MT
