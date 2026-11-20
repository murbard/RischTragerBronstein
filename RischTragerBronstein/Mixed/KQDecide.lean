import RischTragerBronstein.Mixed.KEDecide

import RischTragerBronstein.Algebraic.SupLocalCert
/-!
# Square roots over a logarithmic level with poles at ordinary places: the algorithm

`kqDecide`: for a certified mixed tower whose top level `t = tₘ` is a logarithm (`t′ = η`),
`θ² = A(t)` (`A ∈ Fₘ[t]` squarefree of odd degree) and the integrand `B(t) θ / (D(t) A(t)ˡ)` with
`D = ∏_q (t − c_q)` (the `c_q ∈ Fₘ` given as codes, distinct, `A(c_q) ≠ 0`, `B(c_q) ≠ 0`):

1. The residue of the integrand at `(c_q, ±√A(c_q))` is `± r_q √A(c_q) / (η − c_q′)`,
   `r_q = B(c_q)/R_q`, `R_q = ∏_{q' ≠ q} (c_q − c_{q'}) A(c_q)ˡ`. Its square
   `Q_q = B(c_q)² A(c_q) / ((η − c_q′) R_q)²` must be a constant (else: not elementary), hence a
   rational `κ_q`.
2. The residues must lie in one class `ℚ √s` (`s = κ₀`, `κ_q / s = m_q²` with `m_q ∈ ℚ`; otherwise
   no answer). With `ỹ = √s θ` (`ỹ² = s A`), the points `(c_q, s m_q (η − c_q′)/r_q)` are rational
   over the code field and carry the residues `m_q √s`.
3. The torsion oracle on `ỹ² = s A(t)` over `Kₘ` for `Γ = ∑ M m_q (c_q, ·)`: not torsion ⇒ not
   elementary; torsion of order `N` with witness `W = W₀ + W₁ ỹ` ⇒ the answer is the parametric
   Risch equation `y′ + ½ (A′/A) y = B/(D Aˡ) + c B_W` (a solution with the first coefficient
   non-zero).
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- The rational square root, if any. -/
def qsqrt (x : ℚ) : Option ℚ :=
  if x < 0 then none else
    if (Nat.sqrt x.num.toNat) * (Nat.sqrt x.num.toNat) = x.num.toNat ∧
        (Nat.sqrt x.den) * (Nat.sqrt x.den) = x.den then
      some ((Nat.sqrt x.num.toNat : ℚ) / (Nat.sqrt x.den : ℚ))
    else none

/-- `aᵏ` for a code. -/
def powC {α : Type} (O : COps α) (a : α) : ℕ → α
  | 0 => O.one
  | k + 1 => O.mul a (powC O a k)

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- `P(c)` (Horner). -/
def evalGC (m : ℕ) (P : GPoly (LC m)) (c : LC m) : LC m :=
  P.foldr (fun a acc ↦ (MO Fc ks m).add a ((MO Fc ks m).mul c acc)) (MO Fc ks m).zero

/-- `X − c`. -/
def linG (m : ℕ) (c : LC m) : GPoly (LC m) := [(MO Fc ks m).neg c, (MO Fc ks m).one]

/-- `∏ (X − c)`. -/
def prodLinG (m : ℕ) (cs : List (LC m)) : GPoly (LC m) :=
  cs.foldr (fun c acc ↦ GPoly.mul (MO Fc ks m) (linG Fc ks m c) acc) [(MO Fc ks m).one]

section Pole

variable (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))

/-- The pole `c_q`. -/
def kqC (q : ℕ) : LC m := cs.getD q (MO Fc ks m).zero

/-- `R_q = ∏_{q' ≠ q} (c_q − c_{q'}) A(c_q)ˡ`. -/
def kqR (q : ℕ) : LC m :=
  normC Fc m ((MO Fc ks m).mul (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q)) (kqC Fc ks m cs q))
    (powC (MO Fc ks m) (evalGC Fc ks m A (kqC Fc ks m cs q)) l))

/-- `η − c_q′`. -/
def kqD (q : ℕ) : LC m := subC (MO Fc ks m) η ((MO Fc ks m).deriv (kqC Fc ks m cs q))

/-- The squared residue `Q_q = B(c_q)² A(c_q) / ((η − c_q′) R_q)²`. -/
def kqQ (q : ℕ) : LC m :=
  let O := MO Fc ks m
  let bq := evalGC Fc ks m B (kqC Fc ks m cs q)
  let dr := O.mul (kqD Fc ks m η cs q) (kqR Fc ks m A l cs q)
  normC Fc m (O.mul (O.mul (O.mul bq bq) (evalGC Fc ks m A (kqC Fc ks m cs q))) (O.inv (O.mul dr dr)))

/-- The rational value `κ_q` of `Q_q`. -/
def kqK (q : ℕ) : ℚ := (ratValC Fc ks m (kqQ Fc ks m η A B l cs q)).getD 0

/-- `m_q = √(κ_q / κ₀)`. -/
def kqM (q : ℕ) : ℚ := (qsqrt (kqK Fc ks m η A B l cs q / kqK Fc ks m η A B l cs 0)).getD 0

/-- The common denominator. -/
def kqDen : ℕ := ((List.range cs.length).map fun q ↦ (kqM Fc ks m η A B l cs q).den).prod

/-- The multiplicity `M m_q ∈ ℕ`. -/
def kqMN (q : ℕ) : ℕ :=
  ((((kqDen Fc ks m η A B l cs / (kqM Fc ks m η A B l cs q).den : ℕ) : ℤ) *
    (kqM Fc ks m η A B l cs q).num)).toNat

/-- The ordinate `s m_q (η − c_q′) R_q / B(c_q)` of the pole on `ỹ² = s A`. -/
def kqB (q : ℕ) : LC m :=
  let O := MO Fc ks m
  normC Fc m (O.mul (mcst Fc ks m (kqK Fc ks m η A B l cs 0 * kqM Fc ks m η A B l cs q))
    (O.mul (kqD Fc ks m η cs q) (O.mul (kqR Fc ks m A l cs q)
      (O.inv (evalGC Fc ks m B (kqC Fc ks m cs q))))))

/-- The twisted polynomial `s A`. -/
def kqAhat : GPoly (LC m) := A.map ((MO Fc ks m).mul (mcst Fc ks m (kqK Fc ks m η A B l cs 0)))

/-- Its code over `Kₘ`. -/
def kqFK : CPoly (KF Fc m) := CPoly.trim ((kqAhat Fc ks m η A B l cs).map (trC Fc m))

/-- The abscissae over `Kₘ`. -/
def kqAl : Fin cs.length → KF Fc m := fun q ↦ trC Fc m (kqC Fc ks m cs q)

/-- The ordinates over `Kₘ`. -/
def kqBe : Fin cs.length → KF Fc m := fun q ↦ trC Fc m (kqB Fc ks m η A B l cs q)

/-- The multiplicities. -/
def kqMq : Fin cs.length → ℕ := fun q ↦ kqMN Fc ks m η A B l cs q

/-- The checks on the data: the `R_q`, `A(c_q)`, `B(c_q)` are non-zero. -/
def kqOK : Bool :=
  (List.range cs.length).all fun q ↦
    !(MO Fc ks m).isZero (kqR Fc ks m A l cs q) &&
    !(MO Fc ks m).isZero (evalGC Fc ks m A (kqC Fc ks m cs q)) &&
    !(MO Fc ks m).isZero (evalGC Fc ks m B (kqC Fc ks m cs q))

/-- Are all squared residues constant? -/
def kqConst : Bool :=
  (List.range cs.length).all fun q ↦
    (MO Fc ks m).isZero ((MO Fc ks m).deriv (kqQ Fc ks m η A B l cs q))

/-- Do all residues lie in one class `ℚ √s`? -/
def kqClass : Bool :=
  (List.range cs.length).all fun q ↦
    (qsqrt (kqK Fc ks m η A B l cs q / kqK Fc ks m η A B l cs 0)).isSome

end Pole

/-- **The decision** (`none`: data not accepted, several residue classes, or the torsion
oracle did not answer within its bounds). -/
def kqDecideC (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) : Option Bool :=
  let O := MO Fc ks m
  let rhs : LC (m + 1) := (B, GPoly.mul O (prodLinG Fc ks m cs) (powG O A l))
  let frA := kpFr Fc ks m 1 2 A
  if cs.length = 0 then none
  else if !kqOK Fc ks m A B l cs then none
  else if !kqConst Fc ks m η A B l cs then some false
  else if !kqClass Fc ks m η A B l cs then none
  else
    let fK := kqFK Fc ks m η A B l cs
    match torsOracleC (redAtKF Fc m rs) (cpf fK) ps bound fK 2
      (gammaL (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) 1) with
    | none => none
    | some none => some false
    | some (some N) =>
      match witW fK 2 (fK.length - 1) (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs)
          (kqMq Fc ks m η A B l cs) N with
      | none => none
      | some Wb =>
        let W0 := (Wb.getD 0 []).map (unTr Fc m)
        let W1 := (Wb.getD 1 []).map (unTr Fc m)
        some ((prdeC Fc ks lv (m + 1) frA [rhs, normC Fc (m + 1)
          (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 O.one)]).any
          fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision** (torsion certificates by search modulo `p`). -/
def kqDecide (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kqDecideC Fc ks lv m η A B l cs ps bound rs fun fK ↦ searchCert fK 2

/-- **The decision with local torsion certificates** (answers for every large bound at suitable
residues, `kqDecideL_decides`). -/
def kqDecideL (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kqDecideC Fc ks lv m η A B l cs ps bound rs fun fK ↦ localCert fK 2

end Curves.MT
