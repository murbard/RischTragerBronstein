import RischTragerBronstein.Mixed.FrontExpr
import RischTragerBronstein.Mixed.MTBaseCurve

/-!
# The front end, with the antiderivative

`frontIntegrate Fc e N`: like `frontDecide`, but when `∫ e` is elementary it returns the pieces
of an antiderivative (`ADW`): per level `tᵢ` the rational part, the polynomial part and the
logarithmic part `∑_{s(α)=0} r(α) log (tᵢ − α)` (with `log (1 − α/tᵢ)` below an exponential),
and the remaining integrand on the curve.

* `frontIntegrate_isSome`: it answers exactly as `frontDecide`;
* `frontIntegrate_valid`: every returned antiderivative is valid (`ValidW`) for the value of `e`
  in every realization of the tower.

`ADW.render` prints the pieces.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup EE

universe u

variable (Fc : BPoly ℚ)

/-- **The front end with the antiderivative.** -/
def frontIntegrate (e : EE) (N : ℕ) : Option (Option (ADW e.nodesOf.length)) :=
  if curveShape Fc && certC Fc (ksOf Fc e) (lvOf Fc e) e.nodesOf.length then
    (comp Fc e.nodesOf (ksOf Fc e) e.nodesOf.length e).bind fun q ↦
      elMW Fc (ksOf Fc e) (lvOf Fc e) e.nodesOf.length q N
  else none

/-- **`frontIntegrate` answers exactly as `frontDecide`.** -/
theorem frontIntegrate_isSome (e : EE) (N : ℕ) :
    (frontIntegrate Fc e N).map Option.isSome = frontDecide Fc e N := by
  unfold frontIntegrate frontDecide
  dsimp only
  split_ifs
  · cases comp Fc e.nodesOf (ksOf Fc e) e.nodesOf.length e with
    | none => rfl
    | some q => exact elMW_isSome Fc _ _ _ q N
  · rfl

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every antiderivative returned by the front end is valid**, in every realization `T` of the
tower of `e` generating `L`: the compiled integrand has the value of `e`, and `w` is a valid
witness for it. -/
theorem frontIntegrate_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (e : EE) (N : ℕ) (w : ADW e.nodesOf.length) (h : frontIntegrate Fc e N = some (some w))
    (T : MTower Fc (ksOf Fc e) Cc L) (hn : T.n = e.nodesOf.length)
    (hgen : ∀ z : L, z ∈ T.F e.nodesOf.length) :
    ∃ q, T.ev e.nodesOf.length q = evE Fc T e.nodesOf e ∧
      T.ValidW e.nodesOf.length q w := by
  unfold frontIntegrate at h
  split_ifs at h with hcs
  simp only [Bool.and_eq_true] at hcs
  obtain ⟨hsh, hc⟩ := hcs
  obtain ⟨q, hq, hw⟩ := Option.bind_eq_some_iff.mp h
  have hTr : T.Tr e.nodesOf.length :=
    (T.mspecs hmon hdeg (lvOf Fc e) e.nodesOf.length (by omega) hc).hyp.tr
  exact ⟨q, comp_spec Fc T e.nodesOf e.nodesOf.length hTr e q hq,
    T.elMW_valid hmon hdeg hsh e.nodesOf.length hn hc hgen e.nodesOf.length le_rfl q N w hw⟩

/-! ### Printing -/

/-- A rational number. -/
def showQ (q : ℚ) : String :=
  if q.den = 1 then toString q.num else "(" ++ toString q.num ++ "/" ++ toString q.den ++ ")"

/-- A sum of terms, `0` if there is none. -/
def joinSum (l : List String) : String :=
  match l with
  | [] => "0"
  | _ => " + ".intercalate l

/-- `c · v^i`. -/
def monoStr (c v : String) (i : ℕ) : String :=
  match i with
  | 0 => c
  | 1 => c ++ "*" ++ v
  | _ => c ++ "*" ++ v ++ "^" ++ toString i

/-- A polynomial over `ℚ` in the variable `v`. -/
def showPQ (p : GPoly ℚ) (v : String) : String :=
  joinSum ((List.range p.length).filterMap fun i ↦
    let c := p.getD i 0
    if c = 0 then none else some (monoStr (showQ c) v i))

/-- A rational function over `ℚ`. -/
def showFQ (f : GFrac ℚ) (v : String) : String :=
  if f.2 = [1] then "(" ++ showPQ f.1 v ++ ")"
  else "(" ++ showPQ f.1 v ++ ")/(" ++ showPQ f.2 v ++ ")"

/-- An element of `ℚ[g]/(M)`. -/
def showNF (M : CPoly ℚ) (a : NFC.NF M) : String := "(" ++ showPQ a.1 "g" ++ ")"

/-- A polynomial over `ℚ[g]/(M)` in `v`. -/
def showPNF (M : CPoly ℚ) (p : CPoly (NFC.NF M)) (v : String) : String :=
  joinSum ((List.range p.length).filterMap fun i ↦
    match p[i]? with
    | some a => if a.1.all (· = 0) then none else some (monoStr (showNF M a) v i)
    | none => none)

/-- A polynomial over `ℚ[g]/(M)` in two variables `vx, vy`. -/
def showBNF (M : CPoly ℚ) (p : BPoly (NFC.NF M)) (vx : String := "x") (vy : String := "y") :
    String :=
  joinSum ((List.range p.length).filterMap fun i ↦
    let r := p.getD i []
    if r.all (fun a ↦ a.1.all (· = 0)) then none
    else some (monoStr ("(" ++ showPNF M r vx ++ ")") vy i))

/-- **The curve antiderivative**: `v + ∑ⱼ cⱼ log uⱼ` over `ℚ[g]/(M)` (for a Möbius certificate,
in the variables `X = 1/(x − e)`, `Y = y Xᵏ⁰`). -/
def renderCurveW (W : CurveWQ) : List String :=
  haveI : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
  let M := W.M.1
  let P := W.P
  let (vx, vy, subst) := match W.mob with
    | none => ("x", "y", "")
    | some (e, k₀, _, _) => ("X", "Y", ", with X = 1/(x - " ++ showNF M e ++ "), Y = y*X^" ++
        toString k₀)
  let v := "(" ++ showBNF M (P.Wsol W.w.cs) vx vy ++ ")/(" ++ showPNF M P.R0 vx ++ ")"
  -- logarithms of constants (`W`, `Q` of degree `0`) contribute nothing and are omitted
  let logs := if W.w.logs then
      (List.finRange (EllQuad.QCoords.dim (NFC.NF M))).filterMap fun j ↦
        let w := CurveProb.witAt W.w.ws j
        if w.W.length ≤ 1 ∧ (w.W.getD 0 []).length ≤ 1 ∧ w.Q.length ≤ 1 then none
        else some (showNF M (CurveProb.cLog w j) ++ " * log((" ++ showBNF M w.W vx vy ++ ")/(" ++
          showPNF M w.Q vx ++ "))")
    else []
  ["base on the curve, over Q(g) with g a root of " ++ showPQ M "g" ++ subst ++ ": " ++
    joinSum (v :: logs)]

variable (ks : (m : ℕ) → KindC m)

/-- A code of level `m`, with the variables `x, y, t0, t1, …`. -/
def showLC : (m : ℕ) → LC m → String
  | 0, c => joinSum ((List.range c.length).filterMap fun i ↦
      let f := c.getD i ([], [1])
      if f.1.all (· = 0) then none else some (monoStr (showFQ f "x") "y" i))
  | m + 1, c =>
    let O := MO Fc ks m
    let sp : GPoly (LC m) → String := fun p ↦ joinSum ((List.range p.length).filterMap fun i ↦
      let a := p.getD i O.zero
      if O.isZero a then none else some (monoStr ("(" ++ showLC m a ++ ")") ("t" ++ toString m) i))
    if GPoly.isZero O (GPoly.sub O (c : GFrac (LC m)).2 [O.one]) then sp (c : GFrac (LC m)).1
    else "(" ++ sp (c : GFrac (LC m)).1 ++ ")/(" ++ sp (c : GFrac (LC m)).2 ++ ")"

/-- A polynomial over level `m` in `tₘ`. -/
def showGP (m : ℕ) (p : GPoly (LC m)) : String :=
  showLC Fc ks (m + 1) ((p, [(MO Fc ks m).one]) : GFrac (LC m))

/-- **The pieces of the antiderivative, top level first** (`N`: the search bound on the curve). -/
def ADW.render (N : ℕ) : (m : ℕ) → ADW m → List String
  | 0, w =>
    match baseRat Fc w with
    | some (I, _) =>
      let rat := if CPoly.isZero I.gn then [] else
        ["(" ++ showPQ I.gn "x" ++ ")/(" ++ showPQ I.gd "x" ++ ")"]
      let pol := if CPoly.isZero I.Q then [] else ["(" ++ showPQ I.Q "x" ++ ")"]
      let lg := if CPoly.isZero I.r then [] else
        ["sum over the roots a of " ++ showPQ I.s "x" ++ " of (" ++ showPQ I.r "a" ++ ")/(" ++
          showPQ (CPoly.deriv I.s) "a" ++ ") * log(x - a)"]
      ["base (rational in x): " ++ joinSum (rat ++ pol ++ lg)]
    | none =>
      match baseCurveW Fc w N with
      | some (some W) => renderCurveW W
      | _ => ["remaining integrand on the curve (elementary integral): " ++ showLC Fc ks 0 w]
  | m + 1, w =>
    let lw : LevelW m := (w : LevelW m × ADW m).1
    let O := MO Fc ks m
    let t := "t" ++ toString m
    let logArg := match ks m with
      | .prim _ => "log(" ++ t ++ " - a)"
      | .exp _ => "log(1 - a/" ++ t ++ ")"
    let ratPart := if GPoly.isZero O lw.gn then [] else
      ["(" ++ showGP Fc ks m lw.gn ++ ")/(" ++ showGP Fc ks m lw.gd ++ ")"]
    let polyPart := if GPoly.isZero O lw.pc then [] else
      ["(" ++ showGP Fc ks m lw.pc ++ ")" ++
        (if lw.kk = 0 then "" else "/" ++ t ++ "^" ++ toString lw.kk)]
    let logPart := if GPoly.isZero O lw.b then []
      else ["sum over the roots a of " ++ showGP Fc ks m lw.s ++ " (as a polynomial in " ++ t ++
        ") of (" ++ showGP Fc ks m lw.r ++ ")[" ++ t ++ " := a] * " ++ logArg]
    ("level " ++ t ++ ": " ++ joinSum (ratPart ++ polyPart ++ logPart)) ::
      ADW.render N m (w : LevelW m × ADW m).2

/-- An expression, as text. -/
def EE.toStr : EE → String
  | EE.x => "x"
  | EE.y => "y"
  | EE.cst c => showQ c
  | EE.add a b => "(" ++ a.toStr ++ " + " ++ b.toStr ++ ")"
  | EE.mul a b => a.toStr ++ "*" ++ b.toStr
  | EE.neg a => "-" ++ a.toStr
  | EE.inv a => "1/(" ++ a.toStr ++ ")"
  | EE.exp a => "exp(" ++ a.toStr ++ ")"
  | EE.log a => "log(" ++ a.toStr ++ ")"

/-- The nodes of the tower: `tᵢ := exp a` or `log a`. -/
def nodesRender (e : EE) : List String :=
  (List.range e.nodesOf.length).map fun i ↦
    "t" ++ toString i ++ " := " ++ (e.nodesOf.getD i (EE.cst 0)).toStr

/-- **Integrate and print**: the answer and, if elementary, the antiderivative. -/
def integrateShow (e : EE) (N : ℕ) : List String :=
  match frontIntegrate Fc e N with
  | none => ["no answer at this bound"]
  | some none => ["not elementary"]
  | some (some w) => "elementary; tower:" :: nodesRender e ++
      "antiderivative = sum of the pieces:" :: ADW.render Fc (ksOf Fc e) N _ w

end Curves.MT.Front
