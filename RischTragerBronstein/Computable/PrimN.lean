import RischTragerBronstein.Computable.TowerLevels
import RischTragerBronstein.Computable.LimitedCritN
import RischTragerBronstein.Computable.GResidueTest
import RischTragerBronstein.Computable.LogResidueDecision

/-!
# Towers of `n` independent primitives over `ℚ(x)`: the algorithm

`K₀ = ℚ(x)`, `Kₘ₊₁ = Kₘ(tₘ₊₁)` with `tₘ₊₁′ = ηₘ₊₁ ∈ ℚ(x)` (`log x`, `log (x + 1)`, …, any
number of them). Codes of `Kₘ` are `Tower.Code (m + 1)`; `opsP ηs m` are the operations of `Kₘ`.

* `limIntP ηs m A W`: **parametric limited integration** in `Kₘ` — constants `c` and `y ∈ Kₘ` with
  `y′ + ∑ cᵢ wᵢ = A`, the `wᵢ ∈ ℚ(x)`. Base `m = 0`: `limitedCritN` on the logarithmic parts.
  Step: Hermite reduction in `tₘ` (the proper part must vanish), then the coefficients of the
  polynomial part from the top (`polyDown`): `Yₖ′ + (k+1) Yₖ₊₁ η = Pₖ` by `limIntP (m-1) · [η]`,
  and `Y₀′ + Y₁ η + ∑ cᵢ wᵢ = P₀` by `limIntP (m-1) · (η :: W)`.
* `elemP ηs m A`: does `A ∈ Kₘ` have an elementary integral? Hermite reduction, the residue test,
  `polyDown`, and `elemP (m-1)` on the remaining `tₘ⁰` coefficient.
-/

namespace Tower.PrimN

open CPoly

/-- `1` at every level. -/
def oneC : (m : ℕ) → Code m
  | 0 => (1 : ℚ)
  | m + 1 => ([oneC m], [oneC m])

/-- A rational constant at every level. -/
def constC : (m : ℕ) → ℚ → Code m
  | 0, c => c
  | m + 1, c => ([constC m c], [oneC m])

/-- A code of `ℚ(x)` at level `m + 1`. -/
def lift : (m : ℕ) → Code 1 → Code (m + 1)
  | 0, q => q
  | m + 1, q => ([lift m q], [oneC (m + 1)])

/-- The derivative `ηₘ₊₁ ∈ ℚ(x)` of `tₘ₊₁`. -/
def eta (ηs : List (Code 1)) (m : ℕ) : Code 1 := ηs.getD m (([] : CPoly ℚ), ([1] : CPoly ℚ))

/-- The operations of `Kₘ`. -/
def opsP (ηs : List (Code 1)) : (m : ℕ) → COps (Code (m + 1))
  | 0 => ops₁g ℚ
  | m + 1 => (opsP ηs m).monomial [lift m (eta ηs m)]

/-- The code of `tₘ₊₁′` as a polynomial over `Kₘ`. -/
def wP (ηs : List (Code 1)) (m : ℕ) : GPoly (Code (m + 1)) := [lift m (eta ηs m)]

/-- The rational integral of an element of `ℚ(x)` (normalised first, so that a zero denominator
is harmless). -/
def ratInt (q : Code 1) : RationalIntegral ℚ :=
  integrateRational (CPoly.normCoeff (R := ℚ) q).1 (CPoly.normCoeff (R := ℚ) q).2

/-- The rational antiderivative `gn / gd + Q` of the Hermite part. -/
def ratPart (I : RationalIntegral ℚ) : Code 1 := (ops₁g ℚ).add (I.gn, I.gd) (I.Q, [1])

/-- `acc - ∑ cᵢ (rational part of wᵢ)`: the particular solution at the base. -/
def ratFold : List ℚ → List (Code 1) → Code 1 → Code 1
  | c :: cs, w :: W, acc =>
    ratFold cs W ((ops₁g ℚ).add acc ((ops₁g ℚ).neg ((ops₁g ℚ).mul ([c], [1]) (ratPart (ratInt w)))))
  | _, _, acc => acc

/-- Levels `k = d-1, …, 1` of the polynomial part: `Yₖ′ + (k+1) Yₖ₊₁ η = Pₖ`, `Yₖ₊₁ = Q + e`.
Returns the particular `Y₁` and the finished `Y₂, …, Y_d` (lowest first). -/
def polyDown {α : Type} (O : COps α) (η : α) (ηc : Code 1)
    (solve : α → List (Code 1) → Option (List ℚ × α)) (cst : ℚ → α) (P : GPoly α) :
    ℕ → α → List α → Option (α × List α)
  | 0, Q, Ys => some (Q, Ys)
  | k + 1, Q, Ys =>
    let G := O.add (P.getD (k + 1) O.zero) (O.neg (O.mul (O.mul (O.natCast (k + 2)) Q) η))
    match solve G [ηc] with
    | some ([e], Y) => polyDown O η ηc solve cst P k Y (O.add Q (cst (e / (k + 2 : ℚ))) :: Ys)
    | _ => none

/-- **Parametric limited integration** in `Kₘ`. -/
def limIntP (ηs : List (Code 1)) : (m : ℕ) → Code (m + 1) → List (Code 1) →
    Option (List ℚ × Code (m + 1))
  | 0, A, W =>
    match limitedCritN (ratInt A).r (ratInt A).s (W.map fun w ↦ ((ratInt w).r, (ratInt w).s)) with
    | none => none
    | some cs =>
      some (cs, ratFold cs W (ratPart (ratInt A)))
  | m + 1, A, W =>
    let O := opsP ηs m
    let η := lift m (eta ηs m)
    if GPoly.isZero O A.2 then some (W.map fun _ ↦ 0, (opsP ηs (m + 1)).zero) else
    let h := GPoly.hermite O (wP ηs m) A.1 A.2
    let qr := GPoly.divMod O h.b h.s
    if GPoly.isZero O qr.2 then
      match polyDown O η (eta ηs m) (limIntP ηs m) (constC (m + 1)) qr.1 (qr.1.length - 1)
          O.zero [] with
      | none => none
      | some (Q, Ys) =>
        let G := O.add (qr.1.getD 0 O.zero) (O.neg (O.mul Q η))
        match limIntP ηs m G (eta ηs m :: W) with
        | some (e :: cs, Y₀) =>
          some (cs, (opsP ηs (m + 1)).add (h.gn, h.gd)
            (Y₀ :: O.add Q (constC (m + 1) e) :: Ys, [O.one]))
        | _ => none
    else none

/-- **Independence certificate** for the tower of height `n`: for each `m < n`, `ηₘ` has no
antiderivative in `Kₘ` (checked by `limIntP` with no parameters). -/
def primCert (ηs : List (Code 1)) (n : ℕ) : Bool :=
  (List.range n).all fun m ↦ (limIntP ηs m (lift m (eta ηs m)) []).isNone

/-- **Does `A ∈ Kₘ` have an elementary integral?** -/
def elemP (ηs : List (Code 1)) : (m : ℕ) → Code (m + 1) → Bool
  | 0, _ => true
  | m + 1, A =>
    let O := opsP ηs m
    let η := lift m (eta ηs m)
    GPoly.isZero O A.2 ||
    let h := GPoly.hermite O (wP ηs m) A.1 A.2
    let qr := GPoly.divMod O h.b h.s
    GPoly.residueCheck O (wP ηs m) qr.2 h.s &&
      match polyDown O η (eta ηs m) (limIntP ηs m) (constC (m + 1)) qr.1 (qr.1.length - 1)
          O.zero [] with
      | none => false
      | some (Q, _) => elemP ηs m (O.add (qr.1.getD 0 O.zero) (O.neg (O.mul Q η)))

end Tower.PrimN
