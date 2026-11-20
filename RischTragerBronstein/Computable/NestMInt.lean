import RischTragerBronstein.Computable.NestMRde

/-!
# Mixed towers with nested data: parametric integration at exponential levels (algorithm)

At an exponential level `t = exp a` every weight is split as
`w = g′ + r / s + L / tᵏ` (`s` squarefree, `t ∤ s`, `deg r < deg s`): the special part of the
denominator is separated by a Bézout identity (`splitSpecial`), the normal part is
Hermite-reduced. The Laurent coefficients are independent problems one level down:
`yⱼ′ + j a′ yⱼ = ∑ cᵢ Lᵢⱼ` (`prde`) for `j ≠ 0`, and limited / elementary integration for `j = 0`.

* `paramLimM ks m W`: parametric limited integration (`y′ = ∑ cᵢ wᵢ`);
* `paramElemM ks m W`: parametric elementary integration (`∑ cᵢ wᵢ` has a Liouville form);
* `expCertM ks n`: the tower certificate (`exp aₘ` transcendental over `Kₘ`);
* `elemNM ks n A`: does `A` have an elementary integral?
-/

namespace Tower.NestM

open CPoly Tower.PrimN Tower.NestP

section Generic

variable {α : Type} (O : COps α)

/-- The power `tˢ`. -/
def powX (s : ℕ) : GPoly α := List.replicate s O.zero ++ [O.one]

/-- `n / (tˢ d) = r / d + L / tˢ`, `s` the order of the denominator at `t = 0`:
returns `(r, d, L, s)`. -/
def splitSpecial (w : GPoly α × GPoly α) : GPoly α × GPoly α × GPoly α × ℕ :=
  let s := lowZ O w.2
  let d := w.2.drop s
  let rL := GPoly.solveBezout O (powX O s) d w.1
  (rL.1, d, rL.2, s)

end Generic

/-- The decomposition of a weight at an exponential level: Hermite part `g`, simple part `r / s`,
Laurent part `L / tᵏ`. -/
structure ExpSplit (α : Type) where
  gn : GPoly α
  gd : GPoly α
  r : GPoly α
  s : GPoly α
  L : GPoly α
  k : ℕ

/-- Split a weight `w` at an exponential level (`wK = [0, a′]`). -/
def expSplit {α : Type} (O : COps α) (wk : GPoly α) (w : GPoly α × GPoly α) : ExpSplit α :=
  let wc := cleanG O w
  let sp := splitSpecial O wc
  let H := GPoly.hermite O wk sp.1 sp.2.1
  let qr := GPoly.divMod O H.b H.s
  -- `qr.1` is a polynomial: added to the Laurent part `L / tᵏ`
  { gn := H.gn, gd := H.gd, r := qr.2, s := H.s,
    L := GPoly.add O sp.2.2.1 (GPoly.mul O (powX O sp.2.2.2) qr.1), k := sp.2.2.2 }

/-- The common order `S` at `t = 0` of the Laurent parts. -/
def laurentS {α : Type} (l : List (ExpSplit α)) : ℕ := (l.map ExpSplit.k).foldr max 0

/-- The Laurent part of a split over the common denominator `t^S`. -/
def shiftedL {α : Type} (O : COps α) (S : ℕ) (e : ExpSplit α) : GPoly α :=
  List.replicate (S - e.k) O.zero ++ e.L

/-- The parametric limited integration of the base (rational integration and a constant system). -/
def paramLim0 (ks : (m : ℕ) → KindN m) (W : List (Code 1)) : List (List ℚ × Code 1) :=
  (consys ks 0 (W.map logPart)).map fun u ↦
    let e := (List.range W.length).map fun i ↦ u.getD i 0
    (e, lcombCode (ops₁g ℚ) (cstN 0) e (W.map fun w ↦ ratPart (ratInt w)))

/-- One exponential step of parametric limited integration (`t = exp a`), given the solver `lim`
one level down. -/
def expLimStep (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1))
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1))) (W : List (Code (m + 2))) :
    List (List ℚ × Code (m + 2)) :=
  let O := opsM ks m
  let O' := opsM ks (m + 1)
  let wk : GPoly (Code (m + 1)) := [O.zero, O.deriv a]
  let n := W.length
  let Sp := W.map (expSplit O wk)
  let U := consys ks (m + 1) (Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2)))
  let E := U.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
  let S := laurentS Sp
  let Ls := Sp.map (shiftedL O S)
  let Pu := E.map fun e ↦ lcombGP O (cstN m) e Ls
  let top := (Pu.map List.length).foldr max 0
  -- `(Y / tˢ)′ = P / tˢ` is `Y′ - S a′ Y = P`: the loop of the Risch equation with `A = 1`,
  -- `B = -S a′`; coefficient `i` is `yᵢ′ + (i - S) a′ yᵢ = Pᵢ`, a Risch equation one level
  -- down for `i ≠ S`, a limited integration problem (plus the constants) for `i = S`
  let A : GPoly (Code (m + 1)) := [O.one]
  let B : GPoly (Code (m + 1)) := [O.mul (cstN m (-(S : ℚ))) (O.deriv a)]
  let solve : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)) := fun i ws ↦
    if i = S then lim ws ++ [([], O.one)]
    else prde ks m (O.mul (cstN m ((i : ℚ) - S)) a) ws
  let init := (List.range E.length).map fun i ↦
    (unitV E.length i, ([] : GPoly (Code (m + 1))))
  (rdeLoop O (cstN m) wk A B Pu E.length 0 false O.one O.one solve (max top S + 1) init).map
    fun b ↦
    let c := vcomb n b.1 E
    (c, O'.add (lcombCode O' (cstN (m + 1)) c (Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))))
      ((b.2, powX O S) : Code (m + 2)))

/-- **Parametric limited integration** in mixed towers (exponential levels; primitive levels
are not yet treated). -/
def paramLimM (ks : (m : ℕ) → KindN m) : (m : ℕ) → List (Code (m + 1)) →
    List (List ℚ × Code (m + 1))
  | 0, W => paramLim0 ks W
  | m + 1, W =>
    match ks m with
    | .prim _ => []
    | .exp a => expLimStep ks m a (paramLimM ks m) W

/-- The elementary coefficient loop: bases of vectors, `solve i` returning the admissible
combinations for coefficient `i`. -/
def elemLoop (n : ℕ) (solve : ℕ → List (List ℚ) → List (List ℚ)) :
    ℕ → List (List ℚ) → List (List ℚ)
  | 0, Bs => Bs
  | i + 1, Bs => elemLoop n solve i ((solve i Bs).map fun β ↦ vcomb n β Bs)

/-- One exponential step of parametric elementary integration (`t = exp a`), given the solver
`elem` one level down. -/
def expElemStep (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1))
    (elem : List (Code (m + 1)) → List (List ℚ)) (W : List (Code (m + 2))) : List (List ℚ) :=
  let O := opsM ks m
  let wk : GPoly (Code (m + 1)) := [O.zero, O.deriv a]
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
    -- coefficient `i` (exponent `i - S`): for `i ≠ S` a Risch equation must be solvable,
    -- for `i = S` the coefficient must have an elementary integral one level down
    let solve : ℕ → List (List ℚ) → List (List ℚ) := fun i Bs ↦
      let ws := Bs.map fun β ↦ lcombCode O (cstN m) β (Pu.map fun L ↦ L.getD i O.zero)
      if i = S then elem ws
      else (prde ks m (O.mul (cstN m ((i : ℚ) - S)) a) ws).map Prod.fst
    let init := (List.range E1.length).map (unitV E1.length)
    (elemLoop E1.length solve top init).map fun δ ↦ vcomb n δ E1
  else []

/-- **Parametric elementary integration** in mixed towers (exponential levels; primitive levels
are not yet treated). -/
def paramElemM (ks : (m : ℕ) → KindN m) : (m : ℕ) → List (Code (m + 1)) → List (List ℚ)
  | 0, W => (List.range W.length).map (unitV W.length)
  | m + 1, W =>
    match ks m with
    | .prim _ => []
    | .exp a => expElemStep ks m a (paramElemM ks m) W

/-- **The tower certificate**: every level is an exponential `exp aₘ` with `aₘ` not a rational
combination of the previous exponents modulo constants (checked by a constant system). -/
def expCertM (ks : (m : ℕ) → KindN m) (n : ℕ) : Bool :=
  (List.range n).all fun m ↦
    match ks m with
    | .exp a =>
      let O := opsM ks m
      (consys ks m (O.deriv a :: (expsBelow ks m).map O.deriv)).all fun u ↦ u.getD 0 0 == 0
    | .prim _ => false

/-- **Does `A ∈ Kₘ` have an elementary integral?** -/
def elemNM (ks : (m : ℕ) → KindN m) (m : ℕ) (A : Code (m + 1)) : Bool :=
  (paramElemM ks m [A]).any fun e ↦ e.getD 0 0 ≠ 0

end Tower.NestM
