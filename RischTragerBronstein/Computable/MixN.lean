import RischTragerBronstein.Computable.PrimN
import RischTragerBronstein.Computable.GSplitX
import RischTragerBronstein.Computable.RDERational
import RischTragerBronstein.Computable.RDERationalW
import RischTragerBronstein.Computable.HexpDegenerate
import RischTragerBronstein.Computable.LinSolve
import RischTragerBronstein.Computable.KronCert

/-!
# Mixed towers of primitives and exponentials over `ℚ(x)`, of any height: the algorithm

`K₀ = ℚ(x)`, `Kₘ₊₁ = Kₘ(tₘ)` where each `tₘ` is either a **primitive** `tₘ′ = ηₘ ∈ ℚ(x)`
(`log x`, `arctan x`, …) or an **exponential** `tₘ′ = bₘ tₘ` with `bₘ = aₘ′`, `aₘ ∈ ℚ(x)`
(`exp aₘ`), in any order and any number.

* `rdeM ks m f A`: the Risch differential equation `y′ + f y = A` in `Kₘ`, for
  `f ∈ ℚ(x)` (at the base by the weakly normalised solver `rdeRationalW`; in the applications `f` is a non-trivial integer combination of the `bⱼ`, so the
  solution is unique). The solution is `Y / D` with `D` the denominator of `A` (no new poles can
  appear), and `Y` is found by a top-degree recursion whose coefficient equations are Risch
  equations one level down, with coefficient `f` (primitive level) or `f + (k - deg D) bₘ`
  (exponential level).
* `limIntM ks m A W`: parametric limited integration `y′ + ∑ cᵢ wᵢ = A`, `wᵢ ∈ ℚ(x)`.
  At a primitive level as in `PrimN.limIntP`; at an exponential level: split off the powers of
  `tₘ`, Hermite reduction on the normal part (whose proper part must vanish), then each Laurent
  coefficient `e ≠ 0` by `rdeM` with coefficient `e bₘ`, and the coefficient of `tₘ⁰` by
  `limIntM` one level down.
* `elemM ks m A`: does `A ∈ Kₘ` have an elementary integral? Primitive level as in `PrimN.elemP`;
  exponential level: the residue test, `rdeM` for the non-zero Laurent coefficients, `elemM` one
  level down for the coefficient of `tₘ⁰`.
* `mixCert ks n`: the tower is a tower of monomials with no new constants: each primitive `ηₘ`
  has no antiderivative in `Kₘ`, each exponent `bₘ` is a derivative in `ℚ(x)` (no residues), and
  the exponents are linearly independent over `ℚ` (checked on numerators over a common
  denominator).
-/

namespace Tower.MixN

open CPoly Tower.PrimN

/-- The kind of a generator. -/
inductive Kind where
  /-- `t′ = η`, `η ∈ ℚ(x)` -/
  | prim (η : Code 1)
  /-- `t′ = b t`, `b ∈ ℚ(x)` (`exp ∫ b`) -/
  | exp (b : Code 1)

/-- The kind of `tₘ` (a trivial primitive past the end of the list). -/
def kind (ks : List Kind) (m : ℕ) : Kind := ks.getD m (.prim (([] : CPoly ℚ), ([1] : CPoly ℚ)))

/-- The code of `tₘ′` as a polynomial over `Kₘ` (`z` a code of `0`): `η` or `b X`. -/
def wK' (ks : List Kind) (m : ℕ) (z : Code (m + 1)) : GPoly (Code (m + 1)) :=
  match kind ks m with
  | .prim η => [lift m η]
  | .exp b => [z, lift m b]

/-- The operations of `Kₘ`. -/
def opsM (ks : List Kind) : (m : ℕ) → COps (Code (m + 1))
  | 0 => ops₁g ℚ
  | m + 1 => (opsM ks m).monomial (wK' ks m (opsM ks m).zero)

/-- The code of `tₘ′` as a polynomial over `Kₘ`: `η` or `b X`. -/
def wK (ks : List Kind) (m : ℕ) : GPoly (Code (m + 1)) := wK' ks m (opsM ks m).zero

/-- `z f ∈ ℚ(x)`. -/
def smulQ (z : ℚ) (f : Code 1) : Code 1 := (ops₁g ℚ).mul (([z] : CPoly ℚ), ([1] : CPoly ℚ)) f

/-- `f + z b`. -/
def shiftF (f b : Code 1) (z : ℤ) : Code 1 := (ops₁g ℚ).add f (smulQ (z : ℚ) b)

/-- The coefficient of the Risch equation for the top coefficient, `deg Ap = dA`, `deg D = d₁`. -/
def fkOf (kd : Kind) (f : Code 1) (dA d₁ : ℕ) : Code 1 :=
  match kd with
  | .prim _ => f
  | .exp b => shiftF f b ((dA : ℤ) - 2 * d₁)

/-- The top-degree recursion for `D Y′ + P₀ Y = Ap`, with a solver `rde` for the coefficient
equations one level down. -/
def rdeAux {α : Type} (O : COps α) (w : GPoly α) (kd : Kind) (f : Code 1)
    (rde : Code 1 → α → Option α) (D P₀ : GPoly α) :
    ℕ → GPoly α → GPoly α → Option (GPoly α)
  | 0, Ap, acc => if GPoly.isZero O Ap then some acc else none
  | fuel + 1, Ap, acc =>
    if GPoly.isZero O Ap then some acc
    else
      let dA := (GPoly.trim O Ap).length - 1
      let d₁ := (GPoly.trim O D).length - 1
      if dA < d₁ then none
      else
        let L := GPoly.lead O (GPoly.trim O D)
        match rde (fkOf kd f dA d₁) (O.mul (GPoly.lead O (GPoly.trim O Ap)) (O.inv (O.mul L L))) with
        | none => none
        | some z =>
          let Yd := GPoly.monomial O (dA - d₁) (O.mul L z)
          rdeAux O w kd f rde D P₀ fuel
            (GPoly.sub O Ap (GPoly.add O (GPoly.mul O D (GPoly.derivT O w Yd))
              (GPoly.mul O P₀ Yd)))
            (GPoly.add O acc Yd)

/-- The residue annihilator used by the weakly normalised base solver. -/
def muOf (g : Code 1) : CPoly ℚ := findMu (simplePart g.2) (residuePolyW g.1 g.2)

/-- **The Risch differential equation** `y′ + f y = A` in `Kₘ`, `f ∈ ℚ(x)`. -/
def rdeM (ks : List Kind) : (m : ℕ) → Code 1 → Code (m + 1) → Option (Code (m + 1))
  | 0, f, A =>
    let q := CPoly.normCoeff (R := ℚ) A
    let g := CPoly.normCoeff (R := ℚ) f
    rdeRationalW (R := ℚ) (muOf g) g.1 g.2 q.1 q.2
  | m + 1, f, A =>
    let O := opsM ks m
    if GPoly.isZero O A.2 then some (opsM ks (m + 1)).zero
    else
      let D := A.2
      let P₀ := GPoly.sub O (GPoly.smul O (lift m f) D) (GPoly.derivT O (wK ks m) D)
      let Ap := GPoly.mul O A.1 D
      (rdeAux O (wK ks m) (kind ks m) f (rdeM ks m) D P₀ (Ap.length + 1) Ap []).map
        fun Y ↦ (Y, D)

/-- Solve the Laurent coefficients `j = 0, …, N - 1` of `Λ / t ^ k` (`e = j - k ≠ 0`) by `rdeM`
with coefficient `e b`; the coefficient `j = k` is left as `0` (handled separately). -/
def laurentSolve {α : Type} (O : COps α) (b : Code 1) (rde : Code 1 → α → Option α)
    (Λ : GPoly α) (k : ℕ) : ℕ → Option (GPoly α)
  | 0 => some []
  | N + 1 =>
    match laurentSolve O b rde Λ k N with
    | none => none
    | some Ys =>
      if N = k then some (Ys ++ [O.zero])
      else (rde (smulQ (((N : ℤ) - k : ℤ) : ℚ) b) (Λ.getD N O.zero)).map fun Y ↦ Ys ++ [Y]

/-- **Parametric limited integration** in `Kₘ`. -/
def limIntM (ks : List Kind) : (m : ℕ) → Code (m + 1) → List (Code 1) →
    Option (List ℚ × Code (m + 1))
  | 0, A, W =>
    match limitedCritN (ratInt A).r (ratInt A).s (W.map fun w ↦ ((ratInt w).r, (ratInt w).s)) with
    | none => none
    | some cs => some (cs, ratFold cs W (ratPart (ratInt A)))
  | m + 1, A, W =>
    let O := opsM ks m
    if GPoly.isZero O A.2 then some (W.map fun _ ↦ 0, (opsM ks (m + 1)).zero) else
    match kind ks m with
    | .prim η =>
      let ηc := lift m η
      let h := GPoly.hermite O (wK ks m) A.1 A.2
      let qr := GPoly.divMod O h.b h.s
      if GPoly.isZero O qr.2 then
        match polyDown O ηc η (limIntM ks m) (constC (m + 1)) qr.1 (qr.1.length - 1) O.zero [] with
        | none => none
        | some (Q, Ys) =>
          let G := O.add (qr.1.getD 0 O.zero) (O.neg (O.mul Q ηc))
          match limIntM ks m G (η :: W) with
          | some (e :: cs, Y₀) =>
            some (cs, (opsM ks (m + 1)).add (h.gn, h.gd)
              (Y₀ :: O.add Q (constC (m + 1) e) :: Ys, [O.one]))
          | _ => none
      else none
    | .exp b =>
      let sp := GPoly.expSplit O A.1 A.2
      let k := sp.2.2.1
      let h := GPoly.hermite O (wK ks m) sp.1 sp.2.2.2
      let qr := GPoly.divMod O h.b h.s
      if GPoly.isZero O qr.2 then
        let Λ := GPoly.add O (GPoly.mul O qr.1 (GPoly.monomial O k O.one)) sp.2.1
        match laurentSolve O b (rdeM ks m) Λ k (max Λ.length (k + 1)),
            limIntM ks m (Λ.getD k O.zero) W with
        | some Ys, some (cs, Y₀) =>
          some (cs, (opsM ks (m + 1)).add (h.gn, h.gd)
            (Ys.set k Y₀, GPoly.monomial O k O.one))
        | _, _ => none
      else none

/-- **Does `A ∈ Kₘ` have an elementary integral?** -/
def elemM (ks : List Kind) : (m : ℕ) → Code (m + 1) → Bool
  | 0, _ => true
  | m + 1, A =>
    let O := opsM ks m
    GPoly.isZero O A.2 ||
    match kind ks m with
    | .prim η =>
      let ηc := lift m η
      let h := GPoly.hermite O (wK ks m) A.1 A.2
      let qr := GPoly.divMod O h.b h.s
      GPoly.residueCheck O (wK ks m) qr.2 h.s &&
        match polyDown O ηc η (limIntM ks m) (constC (m + 1)) qr.1 (qr.1.length - 1)
            O.zero [] with
        | none => false
        | some (Q, _) => elemM ks m (O.add (qr.1.getD 0 O.zero) (O.neg (O.mul Q ηc)))
    | .exp b =>
      let sp := GPoly.expSplit O A.1 A.2
      let k := sp.2.2.1
      let h := GPoly.hermite O (wK ks m) sp.1 sp.2.2.2
      let qr := GPoly.divMod O h.b h.s
      let Λ := GPoly.add O (GPoly.mul O qr.1 (GPoly.monomial O k O.one)) sp.2.1
      GPoly.residueCheck O (wK ks m) qr.2 h.s &&
        (laurentSolve O b (rdeM ks m) Λ k (max Λ.length (k + 1))).isSome &&
        elemM ks m (Λ.getD k O.zero)

/-- The exponents `bⱼ` of the exponential levels below `m`. -/
def expsBelow (ks : List Kind) : ℕ → List (Code 1)
  | 0 => []
  | m + 1 => match kind ks m with
    | .prim _ => expsBelow ks m
    | .exp b => expsBelow ks m ++ [b]

/-- All the exponents of the tower. -/
def allExps : List Kind → List (Code 1)
  | [] => []
  | .prim _ :: ks => allExps ks
  | .exp b :: ks => b :: allExps ks

/-- The product of the denominators. -/
def denProdQ (bs : List (GFrac ℚ)) : CPoly ℚ := bs.foldr (fun b acc ↦ mul b.2 acc) [1]

/-- `b` is not in the `ℚ`-span of `bs`: over the common denominator `D` (the product of all the
denominators), the numerators `bᵢ.1 (D / bᵢ.2)` are checked by `linSolve`; the divisions are
checked to be exact. -/
def notSpanCert (bs : List (GFrac ℚ)) (b : GFrac ℚ) : Bool :=
  let D := denProdQ (b :: bs)
  (b :: bs).all (fun q ↦ !CPoly.isZero q.2 && CPoly.isZero (divMod D q.2).2) &&
    (linSolve (bs.map fun q ↦ mul q.1 (divMod D q.2).1) (mul b.1 (divMod D b.2).1)).isNone

/-- `b` is a derivative in `ℚ(x)` (no logarithmic part). -/
def derivCert (b : Code 1) : Bool := CPoly.isZero (ratInt b).r

/-- The certificate for a new exponent `b` over the previous ones `bs`. -/
def expCert (bs : List (GFrac ℚ)) (b : GFrac ℚ) : Bool :=
  !CPoly.isZero b.1 && notSpanCert bs b

/-- The Hermite part `b - r / s` of `b` (as numerator, denominator), with `r / s` the
logarithmic part of `ratInt b`. -/
def hermNum (b : Code 1) : CPoly ℚ :=
  sub (mul (CPoly.normCoeff (R := ℚ) b).1 (ratInt b).s) (mul (ratInt b).r (CPoly.normCoeff (R := ℚ) b).2)

/-- The denominator of the Hermite part. -/
def hermDen (b : Code 1) : CPoly ℚ := mul (CPoly.normCoeff (R := ℚ) b).2 (ratInt b).s

/-- A common squarefree multiple of the simple-pole denominators (untrusted, checked). -/
def sqDen (bs : List (Code 1)) : CPoly ℚ := bs.foldr (fun b acc ↦ lcmSq (ratInt b).s acc) [1]

/-- `∑ aᵢ pᵢ`. -/
def lcombC (a : List ℚ) (ps : List (CPoly ℚ)) : CPoly ℚ :=
  (List.zipWith (fun c p ↦ smul c p) a ps).foldr add []

/-- One step of the elimination: `x = (P, ρ)` is either independent of the kept `P`s, or gives
the residue combination `ρ - ∑ aᵢ ρᵢ` of a relation. -/
def kerStep (st : List (CPoly ℚ × CPoly ℚ) × List (CPoly ℚ)) (x : CPoly ℚ × CPoly ℚ) :
    List (CPoly ℚ × CPoly ℚ) × List (CPoly ℚ) :=
  match linSolve (st.1.map Prod.fst) x.1 with
  | none => (st.1 ++ [x], st.2)
  | some a => (st.1, st.2 ++ [sub x.2 (lcombC a (st.1.map Prod.snd))])

/-- The data of an exponent over the common denominators `DH` (Hermite parts) and `s` (simple
poles): the Hermite numerator `P` and the residue polynomial `ρ`. -/
def kerItem (DH s : CPoly ℚ) (b : Code 1) : CPoly ℚ × CPoly ℚ :=
  (mul (hermNum b) (divMod DH (hermDen b)).1,
    resPoly s (mul (ratInt b).r (divMod s (ratInt b).s).1))

/-- **Independence modulo logarithmic derivatives for exponents with simple poles.** A relation
`∑ nⱼ bⱼ = e′/e` forces `∑ nⱼ Hⱼ = 0` for the Hermite parts, and `∑ nⱼ ρⱼ` to take integer values
at the poles. The relations among the `Hⱼ` are computed by elimination; their residue
combinations `w` must have no non-zero rational combination taking only rational values:
checked by `nonRatVals` (one relation) or the pair certificate `degenCertQ` (two relations). -/
def hermKernelCert (bs : List (Code 1)) : Bool :=
  let s := sqDen bs
  let DH := denProdQ (bs.map fun b ↦ ((hermNum b, hermDen b) : GFrac ℚ))
  !CPoly.isZero s && squarefreeCheck s &&
  bs.all (fun b ↦ !CPoly.isZero (hermDen b) && CPoly.isZero (divMod DH (hermDen b)).2 &&
    CPoly.isZero (divMod s (ratInt b).s).2 &&
    CPoly.isZero (divMod (sub (mul (kerItem DH s b).2 (deriv s))
      (mul (ratInt b).r (divMod s (ratInt b).s).1)) s).2) &&
  match ((bs.map (kerItem DH s)).foldl kerStep ([], [])).2 with
  | [] => true
  | [w] => nonRatVals s w
  | [w₁, w₂] => degenCertQ s w₁ w₂
  | ws => CPoly.Kron.genResCert s ws

/-- **No `ℚ`-combination of the exponents is a logarithmic derivative in `ℚ(x)`**: either all
exponents are derivatives in `ℚ(x)`, or the Hermite-kernel certificate holds. -/
def logIndepCert (bs : List (Code 1)) : Bool := bs.all derivCert || hermKernelCert bs

/-- **The tower certificate**: primitives are not derivatives one level down; the exponents are
derivatives in `ℚ(x)`, nonzero, and linearly independent over `ℚ` (each is not a combination of the
previous ones). -/
def mixCert (ks : List Kind) (n : ℕ) : Bool :=
  logIndepCert (allExps ks) && (List.range n).all fun m ↦
    match kind ks m with
    | .prim η => (limIntM ks m (lift m η) []).isNone
    | .exp b => expCert (expsBelow ks m) b

end Tower.MixN
