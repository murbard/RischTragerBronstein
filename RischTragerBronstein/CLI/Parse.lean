import RischTragerBronstein.Mixed.FrontFastW
import RischTragerBronstein.Mixed.FrontSqrtAuto

/-!
# Text input for the integrator

A small recursive-descent parser from text (`x*exp(x^2)`, `1/(x^2+1)`, `1/sqrt(exp(x)+1)`, …) to
the expression types of the front ends, and a dispatcher `integrateText` choosing the front end:

* no radical: `integrateShowF` (towers of `exp`/`log` over `ℚ(x)`, with the antiderivative);
* one square root `√a` (any rational expression in it): `frontSqrtAutoShow`.

The parser is not part of the verified kernel: the answer always starts by echoing the integrand
as it was understood, and the theorems about the front ends speak about that expression.

Grammar: `expr := term (('+'|'-') term)*`, `term := unary (('*'|'/')? unary)*` (juxtaposition is
multiplication), `unary := '-' unary | atom ('^' unary)?`, atoms are numbers (`3`, `2.5`), `x`,
`exp(…)`, `log(…)`/`ln(…)`, `sqrt(…)` and parentheses. Exponents must be constants: integers, or
half-integers (`a^(1/2) = sqrt(a)`).
-/

namespace RTB.CLI

open Curves Curves.MT Curves.MT.Front

/-- Parsed expressions. -/
inductive PE where
  | x
  | num (q : ℚ)
  | add (a b : PE)
  | mul (a b : PE)
  | neg (a : PE)
  | inv (a : PE)
  | exp (a : PE)
  | log (a : PE)
  | sqrt (a : PE)
  deriving Repr, Inhabited, DecidableEq

/-- Tokens. -/
inductive Tok where
  | num (q : ℚ)
  | id (s : String)
  | sym (c : Char)
  deriving Repr, BEq

/-- Read digits: the value and the number of digits. -/
def readDigits : List Char → ℕ → ℕ → ℕ × ℕ × List Char
  | c :: cs, v, k => if c.isDigit then readDigits cs (10 * v + (c.toNat - '0'.toNat)) (k + 1)
      else (v, k, c :: cs)
  | [], v, k => (v, k, [])

def readIdent : List Char → List Char → List Char × List Char
  | c :: cs, acc => if c.isAlphanum || c = '_' then readIdent cs (c :: acc) else (acc.reverse, c :: cs)
  | [], acc => (acc.reverse, [])

/-- The tokenizer. -/
partial def tokenize : List Char → List Tok → Except String (List Tok)
  | [], acc => .ok acc.reverse
  | c :: cs, acc =>
    if c.isWhitespace then tokenize cs acc
    else if c.isDigit then
      let (v, _, r) := readDigits (c :: cs) 0 0
      match r with
      | '.' :: r' =>
        let (w, k, r'') := readDigits r' 0 0
        tokenize r'' (.num ((v : ℚ) + (w : ℚ) / (10 : ℚ) ^ k) :: acc)
      | _ => tokenize r (.num (v : ℚ) :: acc)
    else if c.isAlpha then
      let (s, r) := readIdent (c :: cs) []
      tokenize r (.id (String.ofList s) :: acc)
    else if c = '*' && cs.head? = some '*' then tokenize cs.tail (.sym '^' :: acc)
    else if "+-*/^()".toList.contains c then tokenize cs (.sym c :: acc)
    else .error s!"unexpected character '{c}'"

/-- The value of a constant expression. -/
def PE.const? : PE → Option ℚ
  | .num q => some q
  | .add a b => do pure ((← a.const?) + (← b.const?))
  | .mul a b => do pure ((← a.const?) * (← b.const?))
  | .neg a => do pure (-(← a.const?))
  | .inv a => do let q ← a.const?; if q = 0 then none else pure q⁻¹
  | _ => none

/-- `aᵏ` by repeated multiplication. -/
def PE.npow (a : PE) : ℕ → PE
  | 0 => .num 1
  | 1 => a
  | k + 1 => .mul (PE.npow a k) a

/-- `a ^ q` for a constant `q` (an integer or a half-integer). -/
def PE.qpow (a : PE) (q : ℚ) : Except String PE :=
  if q.den = 1 then
    .ok (if 0 ≤ q.num then a.npow q.num.toNat else .inv (a.npow (-q.num).toNat))
  else if q.den = 2 then
    .ok (if 0 ≤ q.num then (PE.sqrt a).npow q.num.toNat
      else .inv ((PE.sqrt a).npow (-q.num).toNat))
  else .error s!"exponent {q}: only integers and half-integers are supported here"

abbrev P := StateT (List Tok) (Except String)

def peek : P (Option Tok) := do return (← get).head?
def skip : P Unit := modify List.tail
def expect (c : Char) : P Unit := do
  match ← peek with
  | some (.sym d) => if c = d then skip else throw s!"expected '{c}', found '{d}'"
  | _ => throw s!"expected '{c}'"

mutual

partial def pExpr : P PE := do
  let t ← pTerm
  pExprRest t

partial def pExprRest (acc : PE) : P PE := do
  match ← peek with
  | some (.sym '+') => skip; let t ← pTerm; pExprRest (.add acc t)
  | some (.sym '-') => skip; let t ← pTerm; pExprRest (.add acc (.neg t))
  | _ => return acc

partial def pTerm : P PE := do
  let u ← pUnary
  pTermRest u

partial def pTermRest (acc : PE) : P PE := do
  match ← peek with
  | some (.sym '*') => skip; let u ← pUnary; pTermRest (.mul acc u)
  | some (.sym '/') => skip; let u ← pUnary; pTermRest (.mul acc (.inv u))
  | some (.num _) | some (.id _) | some (.sym '(') => let u ← pPower; pTermRest (.mul acc u)
  | _ => return acc

partial def pUnary : P PE := do
  match ← peek with
  | some (.sym '-') => skip; let u ← pUnary; return .neg u
  | some (.sym '+') => skip; pUnary
  | _ => pPower

partial def pPower : P PE := do
  let a ← pAtom
  match ← peek with
  | some (.sym '^') =>
    skip
    let e ← pUnary
    match e.const? with
    | some q => match a.qpow q with
      | .ok r => return r
      | .error m => throw m
    | none => throw "exponents must be constants (write exp(b*log(a)) for a^b)"
  | _ => return a

partial def pAtom : P PE := do
  match ← peek with
  | some (.num q) => skip; return .num q
  | some (.sym '(') => skip; let e ← pExpr; expect ')'; return e
  | some (.id s) =>
    skip
    if s = "x" then return .x
    else if s = "exp" || s = "log" || s = "ln" || s = "sqrt" then
      expect '('
      let e ← pExpr
      expect ')'
      return (if s = "exp" then .exp e else if s = "sqrt" then .sqrt e else .log e)
    else throw s!"unknown name '{s}' (known: x, exp, log, ln, sqrt)"
  | some (.sym c) => throw s!"unexpected '{c}'"
  | none => throw "unexpected end of input"

end

/-- Parse a string. -/
def parse (s : String) : Except String PE := do
  let toks ← tokenize s.toList []
  let (e, rest) ← pExpr.run toks
  if rest.isEmpty then pure e else throw "unexpected trailing input"

/-- Radical-free expressions. -/
def PE.toEE : PE → Option EE
  | .x => some .x
  | .num q => some (.cst q)
  | .add a b => do pure (.add (← a.toEE) (← b.toEE))
  | .mul a b => do pure (.mul (← a.toEE) (← b.toEE))
  | .neg a => do pure (.neg (← a.toEE))
  | .inv a => do pure (.inv (← a.toEE))
  | .exp a => do pure (.exp (← a.toEE))
  | .log a => do pure (.log (← a.toEE))
  | .sqrt _ => none

/-- Radicals replaced by `y` (for a base curve `y² = s(x)`). -/
def PE.toEEy : PE → EE
  | .x => .x
  | .num q => .cst q
  | .add a b => .add a.toEEy b.toEEy
  | .mul a b => .mul a.toEEy b.toEEy
  | .neg a => .neg a.toEEy
  | .inv a => .inv a.toEEy
  | .exp a => .exp a.toEEy
  | .log a => .log a.toEEy
  | .sqrt _ => .y

/-- The distinct radicands, innermost first. -/
def PE.radicands : PE → List PE
  | .x | .num _ => []
  | .add a b | .mul a b =>
    let l := a.radicands
    l ++ b.radicands.filter fun e ↦ !l.contains e
  | .neg a | .inv a | .exp a | .log a => a.radicands
  | .sqrt a => let l := a.radicands; if l.contains a then l else l ++ [a]

/-- Expressions with the single radical `√a` (not inside `exp`, `log`). -/
def PE.toSE (a : PE) : PE → Option SE
  | .x => some .x
  | .num q => some (.cst q)
  | .add u v => do pure (.add (← PE.toSE a u) (← PE.toSE a v))
  | .mul u v => do pure (.mul (← PE.toSE a u) (← PE.toSE a v))
  | .neg u => do pure (.neg (← PE.toSE a u))
  | .inv u => do pure (.inv (← PE.toSE a u))
  | .exp u => do pure (.exp (← u.toEE))
  | .log u => do pure (.log (← u.toEE))
  | .sqrt u => if u = a then some .th else none

/-! ### Radicands that are rational functions of `x`

`√(p/q) = r √s / q` with `p q = s r²`, `s` squarefree (Yun's algorithm). This rewriting is part of
the unverified reading of the input, like the parser. -/

section Rat

open Curves CPoly

/-- A polynomial as an expression (Horner). -/
def PE.ofPoly : List ℚ → PE
  | [] => .num 0
  | [c] => .num c
  | c :: p =>
    let t : PE := if p = [1] then .x else .mul .x (PE.ofPoly p)
    if c = 0 then t else .add (.num c) t

/-- A rational function of `x` as a quotient of polynomials. -/
def PE.rat? : PE → Option (CPoly ℚ × CPoly ℚ)
  | .x => some ([0, 1], [1])
  | .num q => some ([q], [1])
  | .add a b => do
    let (p, q) ← a.rat?
    let (p', q') ← b.rat?
    pure (trim (CPoly.add (CPoly.mul p q') (CPoly.mul p' q)), trim (CPoly.mul q q'))
  | .mul a b => do
    let (p, q) ← a.rat?
    let (p', q') ← b.rat?
    pure (trim (CPoly.mul p p'), trim (CPoly.mul q q'))
  | .neg a => do let (p, q) ← a.rat?; pure (CPoly.neg p, q)
  | .inv a => do let (p, q) ← a.rat?; if (trim p).isEmpty then none else pure (q, p)
  | _ => none

def qgcd (p q : CPoly ℚ) : CPoly ℚ :=
  let g := trim (egcd p q).1
  CPoly.smul (lead g)⁻¹ g

def qdiv (p q : CPoly ℚ) : CPoly ℚ := trim (divMod p q).1

def ppow (p : CPoly ℚ) : ℕ → CPoly ℚ
  | 0 => [1]
  | k + 1 => trim (CPoly.mul (ppow p k) p)

/-- Yun: the factors `a₁, a₂, …` with `f = c ∏ aᵢⁱ`. -/
def yunLoop : ℕ → CPoly ℚ → CPoly ℚ → List (CPoly ℚ)
  | 0, _, _ => []
  | fuel + 1, b, d =>
    if (trim b).length ≤ 1 then [] else
      let a := qgcd b d
      let b' := qdiv b a
      a :: yunLoop fuel b' (trim (CPoly.sub (qdiv d a) (deriv b')))

def yun (f : CPoly ℚ) : List (CPoly ℚ) :=
  let f' := deriv f
  let a0 := qgcd f f'
  let b := qdiv f a0
  yunLoop f.length b (trim (CPoly.sub (qdiv f' a0) (deriv b)))

/-- `f = s r²` with `s` squarefree. -/
def sqSplit (f : CPoly ℚ) : CPoly ℚ × CPoly ℚ :=
  let fs := (yun f).zipIdx
  let r := fs.foldl (fun acc (a, i) ↦ trim (CPoly.mul acc (ppow a ((i + 1) / 2)))) [1]
  (qdiv f (trim (CPoly.mul r r)), r)

/-- A square root in `ℚ`, if there is one. -/
def qsqrt? (c : ℚ) : Option ℚ :=
  if 0 ≤ c.num ∧ c.num.toNat.sqrt ^ 2 = c.num.toNat ∧ c.den.sqrt ^ 2 = c.den then
    some ((c.num.toNat.sqrt : ℚ) / c.den.sqrt)
  else none

/-- Rewrite the radicals with radicands rational in `x`. -/
def PE.simpRad : PE → PE
  | .x => .x
  | .num q => .num q
  | .add a b => .add a.simpRad b.simpRad
  | .mul a b => .mul a.simpRad b.simpRad
  | .neg a => .neg a.simpRad
  | .inv a => .inv a.simpRad
  | .exp a => .exp a.simpRad
  | .log a => .log a.simpRad
  | .sqrt a =>
    let a' := a.simpRad
    match a'.rat? with
    | none => .sqrt a'
    | some (p, q) =>
      let (s, r) := sqSplit (trim (CPoly.mul p q))
      let co : PE := if trim q = [1] then PE.ofPoly r else .mul (PE.ofPoly r) (.inv (PE.ofPoly q))
      let co' : PE := if co = .num 1 then .sqrt (PE.ofPoly s) else .mul co (.sqrt (PE.ofPoly s))
      match s with
      | [] => .num 0
      | [c] => match qsqrt? c with
        | some d => .mul (.num d) co
        | none => co'
      | _ => co'

/-! ### Genus zero: rational parametrisation

For `y² = s(x)` with `deg s ≤ 2` and a rational point (or a square leading coefficient) the
classical substitutions (`Genus0AutoPt`, `Genus0AutoSq`) turn the integrand into one over `ℚ(u)`,
which the fast path over the line integrates. Here the substitution is applied to the parsed
expression (unverified reading of the input, as for the parser; the substituted integrand is
echoed). -/

/-- A parametrisation: `x = X(u)`, `y = Y(u)`, `dx = D(u) du`, and the description of `u`. -/
structure Param where
  X : PE
  Y : PE
  D : PE
  desc : String

def pdiv (p q : List ℚ) : PE := .mul (PE.ofPoly p) (.inv (PE.ofPoly q))

/-- Candidates for the abscissa of a rational point. -/
def ptCands : List ℚ :=
  (List.range 21).flatMap fun n ↦ (List.range 6).flatMap fun d ↦
    [(n : ℚ) / (d + 1), -(n : ℚ) / (d + 1)]

/-- The parametrisation of `y² = c + b x + a x²` (`s = [c, b, a]`), if one is found. -/
def conicParam (s : List ℚ) : Option Param :=
  match s with
  | [c, b] =>
    -- `u = y`, `x = (u² − c)/b`
    some ⟨PE.ofPoly [-c / b, 0, 1 / b], .x, PE.ofPoly [0, 2 / b], "u = y"⟩
  | [c, b, a] =>
    let ev (x0 : ℚ) : ℚ := c + b * x0 + a * x0 * x0
    let roots : List ℚ := match qsqrt? (b * b - 4 * a * c) with
      | some r => [(-b + r) / (2 * a)]
      | none => []
    match (roots ++ ptCands).findSome? fun x0 ↦ (qsqrt? (ev x0)).map fun y0 ↦ (x0, y0) with
    | some (x0, y0) =>
      -- `u = (y − y₀)/(x − x₀)`: `x = x₀ + (d − 2y₀u)/(u² − a)`, `y = y₀ + u (x − x₀)`,
      -- `dx = −2y/(u² − a) du`
      let d := 2 * a * x0 + b
      let den : List ℚ := [-a, 0, 1]
      let X : List ℚ := [d - a * x0, -2 * y0, x0]
      let Y : List ℚ := [-a * y0, d, -y0]
      some ⟨pdiv X den, pdiv Y den, .mul (.num (-2)) (pdiv Y (trim (CPoly.mul den den))),
        s!"u = (y - {y0})/(x - {x0})"⟩
    | none =>
      match qsqrt? a with
      | some s0 =>
        -- `u = y − s₀x`: `x = (c − u²)/(2s₀u − b)`, `y = (s₀u² − bu + s₀c)/(2s₀u − b)`,
        -- `dx = −2(s₀u² − bu + s₀c)/(2s₀u − b)² du`
        let den : List ℚ := [-b, 2 * s0]
        let Y : List ℚ := [s0 * c, -b, s0]
        some ⟨pdiv [c, 0, -1] den, pdiv Y den,
          .mul (.num (-2)) (pdiv Y (trim (CPoly.mul den den))), s!"u = y - {s0}*x"⟩
      | none => none
  | _ => none

/-- Substitute `x ↦ X`, every radical `↦ Y`. -/
def PE.subst (X Y : PE) : PE → PE
  | .x => X
  | .num q => .num q
  | .add a b => .add (PE.subst X Y a) (PE.subst X Y b)
  | .mul a b => .mul (PE.subst X Y a) (PE.subst X Y b)
  | .neg a => .neg (PE.subst X Y a)
  | .inv a => .inv (PE.subst X Y a)
  | .exp a => .exp (PE.subst X Y a)
  | .log a => .log (PE.subst X Y a)
  | .sqrt _ => Y

/-- Rename the variable `x` to `u` in a line of output. -/
def renameU (l : String) : String :=
  ((l.replace "exp" "\x00").replace "x" "u").replace "\x00" "exp"

end Rat

/-- The line `y = x` as base curve. -/
def Fl : Sup.BPoly ℚ := [[0, -1], [1]]

instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩

/-- Primes for the torsion tests of the radical front ends. -/
def primes : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]

/-- Retry with growing search bounds. -/
def withBounds (f : ℕ → List String) : List ℕ → List String
  | [] => ["no answer at the search bounds tried"]
  | [N] => f N
  | N :: Ns => match f N with
    | ["no answer at this bound"] => withBounds f Ns
    | r => r

/-- Over a curve: without `exp`/`log` the curve decider runs once (`baseCurveW`, whose answer
is that of `elM` by `baseCurveW_isSome`); otherwise `integrateShowF`. -/
def curveShow (Fc : Sup.BPoly ℚ) (e : EE) (N : ℕ) : List String :=
  if e.nodesOf.isEmpty then
    if certC Fc (ksOf Fc e) (lvOf Fc e) 0 then
      match comp Fc e.nodesOf (ksOf Fc e) 0 e with
      | none => ["no answer at this bound"]
      | some q =>
        match baseCurveW Fc q N with
        | none => ["no answer at this bound"]
        | some none => ["not elementary"]
        | some (some W) => "elementary; antiderivative:" :: renderCurveW W
    else ["no answer at this bound"]
  else integrateShowF Fc e N

/-- Over the line: the expression as it is, then with `exp`/`log` normalized (`exp(a + b)`,
`log(a b)`, common generators for `exp(q a)`), which removes dependent generators. -/
def lineShow (e : EE) : List String :=
  match withBounds (fun N ↦ integrateShowF Fl e N) [3, 6, 12] with
  | ["no answer at this bound"] =>
    let e' := e.normalize2
    if e' = e then ["integrand = " ++ e.toStr, "no answer at this bound"]
    else ("integrand = " ++ e.toStr) :: ("normalized: " ++ e'.toStr) ::
      withBounds (fun N ↦ integrateShowF Fl e' N) [3, 6, 12]
  | r => ("integrand = " ++ e.toStr) :: r

/-- **Integrate a text formula**: the lines of the answer. -/
def integrateText (s : String) : List String :=
  match parse s with
  | .error m => ["parse error: " ++ m]
  | .ok p0 =>
    let p := p0.simpRad
    match p.radicands with
    | [] =>
      match p.toEE with
      | none => ["internal error"]
      | some e => lineShow e
    | [a] =>
      match a.rat? with
      | some (sp, _) =>
        if sp.length ≤ 1 then
          ["unsupported: the square root of a constant that is not a square in ℚ"]
        else match conicParam sp with
        | some par =>
          match (PE.mul (PE.subst par.X par.Y p) par.D).toEE with
          | none => ["internal error"]
          | some e =>
            ("substitution: y^2 = " ++ (PE.toEEy a).toStr ++ ", " ++ par.desc ++
              "; integrand in u = " ++ renameU e.toStr) ::
              ((lineShow e).drop 1).map renameU
        | none =>
          let Fc : Sup.BPoly ℚ := [CPoly.neg sp, [], [1]]
          let e := p.toEEy
          if curveShape Fc then
            ("integrand = " ++ e.toStr ++ ", where y^2 = " ++ (PE.toEEy a).toStr) ::
              withBounds (fun N ↦ curveShow Fc e N) [3, 6]
          else ["unsupported: the curve y^2 = " ++ (PE.toEEy a).toStr ++ " is not accepted"]
      | none =>
        match a.toEE, PE.toSE a p with
        | some ae, some se => withBounds (fun N ↦
            match frontSqrtAutoShow Fl ae se primes 30 (fun _ ↦ 2) N with
            | [_, "no answer at this bound"] => ["no answer at this bound"]
            | r => r) [3, 6]
        | _, _ => ["unsupported: a radical inside exp, log or another radical"]
    | _ => ["unsupported: several different radicals"]

end RTB.CLI
