import RischTragerBronstein.Computable.NestM

/-!
# Mixed towers with nested data: the parametric Risch differential equation (algorithm)

`prde0 h W`: a basis of the pairs `(c, y)`, `c ∈ ℚⁿ`, `y ∈ ℚ(x)`, with `y′ + h′ y = ∑ cᵢ wᵢ`
(complete over any field of constants). The denominator of `y` divides `D = gcd(e, e′)`
(`e` the common denominator of the `wᵢ`; `h′` has no simple poles), its numerator has degree at
most `N` (from the leading coefficients), and the equation for `(c, Y)`, `y = Y / D`, is a finite
linear system over `ℚ`, solved by `nullBasis`.
-/

namespace Tower.NestM

open CPoly Tower.PrimN Tower.NestP

/-! ### Polynomials over `ℚ` -/

/-- A zero denominator is replaced by `0 / 1`. -/
def cleanQ (w : GFrac ℚ) : GFrac ℚ := if CPoly.isZero w.2 then ([], [1]) else w

/-- A common multiple of two polynomials. -/
def lcmQ (a b : CPoly ℚ) : CPoly ℚ := CPoly.mul a (CPoly.divMod b (CPoly.egcd a b).1).1

/-- The degree (of the trimmed list). -/
def cdeg (p : CPoly ℚ) : ℕ := (CPoly.trim p).length - 1

/-- The leading coefficient. -/
def clead (p : CPoly ℚ) : ℚ := CPoly.lead (CPoly.trim p)

/-- The degree bound for `A Y′ + B Y = ∑ cᵢ Cᵢ` over `ℚ[x]` (`A ≠ 0`); `none` if `Y = 0`. -/
def degBound0 (A B : CPoly ℚ) (R : ℕ) : Option ℕ :=
  let dA := cdeg A
  if CPoly.isZero B then some (R + 1 - dA)
  else
    let dB := cdeg B
    if dA ≤ dB then (if dB ≤ R then some (R - dB) else none)
    else if dB + 1 < dA then some (R + 1 - dA)
    else
      -- `dB = dA - 1`: the top coefficient `N lc(A) + lc(B)` may cancel
      let q := -(clead B / clead A)
      let base := R + 1 - dA
      if q.den = 1 ∧ 0 ≤ q.num then some (max base q.num.toNat) else some base

/-- A natural number, if `q` is one. -/
def natOfQ (q : ℚ) : Option ℕ := if q.den = 1 ∧ 0 ≤ q.num then some q.num.toNat else none

/-- A uniform degree bound for `A Y′ + B Y = ∑ cᵢ Cᵢ` over `ℚ[x]` (`deg Cᵢ ≤ R`): `R + 1`, or the
cancelling degree `-lc(B) / lc(A)` when `deg B = deg A - 1`. -/
def degBoundU (A B : CPoly ℚ) (R : ℕ) : ℕ :=
  max (R + 1) (if !CPoly.isZero B && decide (cdeg B + 1 = cdeg A) then
    ((natOfQ (-(clead B / clead A))).getD 0) else 0)

/-- The column of the unknown `Yₖ`: `A (xᵏ)′ + B xᵏ`. -/
def colY (A B : CPoly ℚ) (k : ℕ) : CPoly ℚ :=
  CPoly.add (CPoly.mul A (CPoly.deriv (CPoly.monomial k 1))) (CPoly.mul B (CPoly.monomial k 1))

/-- The body of `prde0`, for a given denominator bound `D ≠ 0`. -/
def prde0B (h : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : List (List ℚ × GFrac ℚ) :=
  let O := ops₁g ℚ
  let n := Wc.length
  let Dc : GFrac ℚ := (D, [1])
  let F := cleanQ (O.add (O.deriv (cleanQ h)) (O.neg (O.mul (O.deriv Dc) (O.inv Dc))))
  let Rs := Wc.map fun w ↦ cleanQ (O.mul Dc w)
  let P := prodD CPoly.mul [1] Rs
  let A := CPoly.mul F.2 P
  let B := CPoly.mul F.1 P
  let Cs := (cross CPoly.mul [1] Rs).map (CPoly.mul F.2)
  let R := (Cs.map cdeg).foldr max 0
  let ys : List (CPoly ℚ) := (List.range (degBoundU A B R + 1)).map (colY A B)
  (nullBasis (Cs.map CPoly.neg ++ ys)).map fun u ↦
    ((List.range n).map (u.getD · 0), (((List.range ys.length).map fun k ↦ u.getD (n + k) 0), D))

/-- **The parametric Risch equation over `ℚ(x)`**: `y′ + h′ y = ∑ cᵢ wᵢ`. -/
def prde0 (h : GFrac ℚ) (W : List (GFrac ℚ)) : List (List ℚ × GFrac ℚ) :=
  let Wc := W.map cleanQ
  let e := Wc.foldr (fun w acc ↦ lcmQ w.2 acc) [1]
  let D := (CPoly.egcd e (CPoly.deriv e)).1
  if CPoly.isZero D then [] else prde0B h Wc D
/-! ### Generic helpers over a model -/

section Generic

variable {α : Type} (O : COps α)

/-- The number of leading zero coefficients (the order at `t = 0`). -/
def lowZ (p : GPoly α) : ℕ := (p.takeWhile fun c ↦ O.isZero c).length

/-- A zero denominator is replaced by `0 / 1`. -/
def cleanG (w : GPoly α × GPoly α) : GPoly α × GPoly α :=
  if GPoly.isZero O w.2 then ([], [O.one]) else w

/-- The degree (of the trimmed list). -/
def degG (p : GPoly α) : ℕ := (GPoly.trim O p).length - 1

/-- The leading coefficient. -/
def leadG (p : GPoly α) : α := GPoly.lead O (GPoly.trim O p)

/-- The monic associate. -/
def monicG (p : GPoly α) : GPoly α := GPoly.smul O (O.inv (leadG O p)) (GPoly.trim O p)

/-- `A Y′ + B Y - ∑ cᵢ Cᵢ` for a basis element `(c, Y)`. -/
def residE (cst : ℚ → α) (w A B : GPoly α) (Cs : List (GPoly α)) (b : List ℚ × GPoly α) :
    GPoly α :=
  GPoly.sub O (GPoly.add O (GPoly.mul O A (GPoly.derivT O w b.2)) (GPoly.mul O B b.2))
    (lcombGP O cst b.1 Cs)

/-- One step of the coefficient loop: the equation of degree `k + δ`, whose new unknown is `Yₖ`,
either algebraic (`Yₖ = r / lc B`) or a Risch equation one level down (`lower k`). -/
def rdeStep (cst : ℚ → α) (w A B : GPoly α) (Cs : List (GPoly α)) (n δ : ℕ) (alg : Bool)
    (lcA lcB : α) (lower : ℕ → List α → List (List ℚ × α)) (k : ℕ)
    (Bs : List (List ℚ × GPoly α)) : List (List ℚ × GPoly α) :=
  let rk := fun b ↦ O.neg ((residE O cst w A B Cs b).getD (k + δ) O.zero)
  if alg then Bs.map fun b ↦ (b.1, GPoly.add O b.2 (GPoly.monomial O k (O.mul (rk b) (O.inv lcB))))
  else
    (lower k (Bs.map fun b ↦ O.mul (rk b) (O.inv lcA))).map fun r ↦
      (vcomb n r.1 (Bs.map Prod.fst),
        GPoly.add O (lcombGP O cst r.1 (Bs.map Prod.snd)) (GPoly.monomial O k r.2))

/-- The coefficient loop, `k = N, …, 0`. -/
def rdeLoop (cst : ℚ → α) (w A B : GPoly α) (Cs : List (GPoly α)) (n δ : ℕ) (alg : Bool)
    (lcA lcB : α) (lower : ℕ → List α → List (List ℚ × α)) :
    ℕ → List (List ℚ × GPoly α) → List (List ℚ × GPoly α)
  | 0, Bs => Bs
  | k + 1, Bs => rdeLoop cst w A B Cs n δ alg lcA lcB lower k
      (rdeStep O cst w A B Cs n δ alg lcA lcB lower k Bs)

end Generic

/-- A code of level `m` as a code of level `m + 1`. -/
def liftE (ks : (m : ℕ) → KindN m) (m : ℕ) (q : Code (m + 1)) : Code (m + 2) :=
  ([q], [(opsM ks m).one])

/-- The exponents `aᵢ` of the exponential levels below `m`, as codes of level `m`. -/
def expsBelow (ks : (m : ℕ) → KindN m) : (m : ℕ) → List (Code (m + 1))
  | 0 => []
  | m + 1 => ((expsBelow ks m) ++ (match ks m with | .exp a => [a] | .prim _ => [])).map
      (liftE ks m)

/-- **The logarithmic-derivative bound** (structure theorem): the only rational `μ` for which
`exp (V + μ a)` can lie in `Kₘ`, if any (`V + μ a - ∑ qᵢ aᵢ` constant). -/
def pld (ks : (m : ℕ) → KindN m) (m : ℕ) (V a : Code (m + 1)) : Option ℚ :=
  let O := opsM ks m
  match (consys ks m (O.deriv V :: O.deriv a :: (expsBelow ks m).map O.deriv)).find?
      (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u => some (u.getD 1 0 / u.getD 0 0)
  | none => none

/-! ### The Risch equation over an exponential level, piece by piece -/

section PE

variable {α : Type} (O : COps α)

/-- The derivation polynomial `[0, a′]` of `t = exp a`. -/
def peW (a : α) : GPoly α := [O.zero, O.deriv a]

/-- The special bound from the weights: the largest pole order at `t = 0`. -/
def peEps (Wc : List (GPoly α × GPoly α)) : ℕ :=
  Wc.foldr (fun q acc ↦ if GPoly.isZero O q.1 then acc else max acc (lowZ O q.2 - lowZ O q.1)) 0

/-- The normal part of the common denominator. -/
def peE (Wc : List (GPoly α × GPoly α)) : GPoly α :=
  lcmList O (Wc.map fun q ↦ q.2.drop (lowZ O q.2))

/-- The normal denominator bound `D = gcd(e, e′)`, made monic. -/
def peD (a : α) (e : GPoly α) : GPoly α :=
  monicG O (GPoly.egcd O e (GPoly.derivT O (peW O a) e)).1

/-- The value `h(0)` at `t = 0`. -/
def peH0 (hc : GPoly α × GPoly α) : α :=
  O.mul (hc.1.getD (lowZ O hc.2) O.zero) (O.inv (hc.2.getD (lowZ O hc.2) O.zero))

/-- The value `h(∞)` at infinity. -/
def peHinf (hc : GPoly α × GPoly α) : α :=
  if degG O hc.1 = degG O hc.2 ∧ GPoly.isZero O hc.1 = false then
    O.mul (leadG O hc.1) (O.inv (leadG O hc.2)) else O.zero

/-- The denominator `Q = tᵏ D`. -/
def peQ (kap : ℕ) (D : GPoly α) : GPoly α := List.replicate kap O.zero ++ D

/-- `F = h′ - Q′ / Q`. -/
def peF (a : α) (hc : GPoly α × GPoly α) (Q : GPoly α) : GPoly α × GPoly α :=
  let O' := O.monomial (peW O a)
  cleanG O (O'.add (O'.deriv hc) (O'.neg (O'.mul (O'.deriv (Q, [O.one])) (O'.inv (Q, [O.one])))))

/-- The right-hand sides `Q wᵢ`. -/
def peRs (a : α) (Wc : List (GPoly α × GPoly α)) (Q : GPoly α) : List (GPoly α × GPoly α) :=
  Wc.map fun q ↦ cleanG O ((O.monomial (peW O a)).mul (Q, [O.one]) q)

def peA (F : GPoly α × GPoly α) (Rs : List (GPoly α × GPoly α)) : GPoly α :=
  GPoly.mul O F.2 (prodD (GPoly.mul O) [O.one] Rs)
def peB (F : GPoly α × GPoly α) (Rs : List (GPoly α × GPoly α)) : GPoly α :=
  GPoly.mul O F.1 (prodD (GPoly.mul O) [O.one] Rs)
def peCs (F : GPoly α × GPoly α) (Rs : List (GPoly α × GPoly α)) : List (GPoly α) :=
  (cross (GPoly.mul O) [O.one] Rs).map (GPoly.mul O F.2)

end PE

/-- The special bound `κ` (with the logarithmic-derivative bound of the structure theorem). -/
def peKap (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1)) (hc : Code (m + 2)) (eps : ℕ) : ℕ :=
  let O := opsM ks m
  if GPoly.isZero O hc.1 then eps
  else if lowZ O hc.1 < lowZ O hc.2 then eps
  else
    match (pld ks m (O.neg (peH0 O hc)) a).bind natOfQ with
    | some k => max eps k
    | none => eps

/-- The degree bound of the polynomial equation `A Y′ + B Y = ∑ cᵢ Cᵢ` (`deg Cᵢ ≤ R`), with the
logarithmic-derivative bound `pl` for the balanced case (`dDk = deg Q`). -/
def peNb {α : Type} (O : COps α) (pl : Option ℚ) (A B : GPoly α) (R dDk : ℕ) : Option ℕ :=
  let dA := degG O A
  let dB := degG O B
  if GPoly.isZero O B then some (R - dA)
  else if dA < dB then (if dB ≤ R then some (R - dB) else none)
  else if dB < dA then some (R - dA)
  else
    match pl.bind (fun μ ↦ natOfQ (μ + (dDk : ℚ))) with
    | some N' => some (max (R - dA) N')
    | none => some (R - dA)

/-- The final constant system: the combinations of the basis `Bs` with a zero residual. -/
def peOut (ks : (m : ℕ) → KindN m) (m : ℕ) (w A B : GPoly (Code (m + 1)))
    (Cs : List (GPoly (Code (m + 1)))) (n : ℕ) (Q : GPoly (Code (m + 1)))
    (Bs : List (List ℚ × GPoly (Code (m + 1)))) : List (List ℚ × Code (m + 2)) :=
  let O := opsM ks m
  let U := consys ks (m + 1) (Bs.map fun b ↦ ((residE O (cstN m) w A B Cs b, [O.one]) : Code (m + 2)))
  U.map fun u ↦
    let β := (List.range Bs.length).map (u.getD · 0)
    (vcomb n β (Bs.map Prod.fst), ((lcombGP O (cstN m) β (Bs.map Prod.snd), Q) : Code (m + 2)))

/-- **The parametric Risch equation over an exponential level** `t = exp a`:
`y′ + h′ y = ∑ cᵢ wᵢ` in `Kₘ(t)`, with `lower` solving it in `Kₘ`. -/
def prdeExp (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1))
    (lower : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (h : Code (m + 2)) (W : List (Code (m + 2))) : List (List ℚ × Code (m + 2)) :=
  let O := opsM ks m
  let w := peW O a
  let cst := cstN m
  let Wc := W.map (cleanG O)
  let n := Wc.length
  let hc := cleanG O h
  let eps := peEps O Wc
  let D := peD O a (peE O Wc)
  let dD := degG O D
  let kap := peKap ks m a hc eps
  let Q := peQ O kap D
  let F := peF O a hc Q
  let Rs := peRs O a Wc Q
  let A := peA O F Rs
  let B := peB O F Rs
  let Cs := peCs O F Rs
  let R := (Cs.map (degG O)).foldr max 0
  let dA := degG O A
  let bZ := GPoly.isZero O B
  let dB := degG O B
  let hInf := peHinf O hc
  let hB := O.add hInf (O.mul (cst (-((dD + kap : ℕ) : ℚ))) a)
  let balancedOk := O.isZero (O.add (O.deriv hB) (O.neg (O.mul (leadG O B) (O.inv (leadG O A)))))
  let Nb : Option ℕ := peNb O (pld ks m hInf a) A B R (dD + kap)
  let alg := !bZ && decide (dA < dB)
  let δ := if alg then dB else dA
  let lower' : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)) := fun k ws ↦
    if bZ || decide (dB < dA) then lower (O.mul (cst (k : ℚ)) a) ws
    else lower (O.add hB (O.mul (cst (k : ℚ)) a)) ws
  let init := (List.range n).map fun i ↦ (unitV n i, ([] : GPoly (Code (m + 1))))
  let Bs := match Nb with
    | none => init
    | some N => rdeLoop O cst w A B Cs n δ alg (leadG O A) (leadG O B) lower' (N + 1) init
  if !bZ && !alg && decide (dA = dB) && !balancedOk then []
  else peOut ks m w A B Cs n Q Bs

/-- **The parametric Risch equation at every level** (primitive levels: not yet). -/
def prde (ks : (m : ℕ) → KindN m) : (m : ℕ) → Code (m + 1) → List (Code (m + 1)) →
    List (List ℚ × Code (m + 1))
  | 0, h, W => prde0 h W
  | m + 1, h, W =>
    match ks m with
    | .exp a => prdeExp ks m a (prde ks m) h W
    | .prim _ => []

end Tower.NestM
