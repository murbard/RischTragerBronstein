import RischTragerBronstein.Mixed.KYCodes

/-!
# Radicals of order `n` with poles in `Kₘ ⊗ N`: the algorithm

As `kyDecide`, for the integrand `B(t) θʲ / (tᵏ D(t) A(t)ˡ)` whose denominator `D ∈ Fₘ[t]` splits
over `Fₘ ⊗ N` as `D = ∏_q (t − c_q)`, `c_q ∈ Kₘ ⊗ N` (checked): the poles need not be in `Fₘ`
(e.g. `D = t² + 1` with `N ∋ i`). The residues, their constancy, `κ_q ∈ N` and the points are
computed in `Kₘ ⊗ N`, with the derivation acting on the coordinates (`nfmD`); the rest (the
components, the torsion oracle over `Kₘ ⊗ N`, the fibre over `t = 0`, the columns) is `kyDecide`'s.
-/

open Polynomial CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Ops

variable (m : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]

/-- The derivation of `Kₘ ⊗ N`, on the coordinates. -/
def nfmD (x : NFM Fc m M) : NFM Fc m M :=
  NFK.mk _ (x.1.map fun a ↦ trC Fc m ((MO Fc ks m).deriv (unTr Fc m a)))

/-- `P(c)` for a code polynomial `P` and `c ∈ Kₘ ⊗ N`. -/
def nfmEval (P : GPoly (LC m)) (c : NFM Fc m M) : NFM Fc m M :=
  P.foldr (fun a acc ↦ embM Fc m M (trC Fc m a) + c * acc) 0

/-- `∏ (X − c)` over `Kₘ ⊗ N`. -/
def nfmProd (cs : List (NFM Fc m M)) : CPoly (NFM Fc m M) :=
  cs.foldr (fun c acc ↦ CPoly.mul [-c, 1] acc) [1]

end Ops

section Res

variable (m n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M))

/-- The pole `c_q`. -/
def kzC (q : ℕ) : NFM Fc m M := cs.getD q 0

/-- `R_q = c_qᵏ ∏_{q' ≠ q} (c_q − c_{q'}) A(c_q)ˡ`. -/
def kzR (q : ℕ) : NFM Fc m M :=
  kzC Fc m M cs q ^ kt * ((cs.eraseIdx q).map fun c ↦ kzC Fc m M cs q - c).prod *
    nfmEval Fc m M A (kzC Fc m M cs q) ^ l

/-- `η c_q − c_q′` (`η = g′`). -/
def kzD (q : ℕ) : NFM Fc m M :=
  embM Fc m M (trC Fc m ((MO Fc ks m).deriv g)) * kzC Fc m M cs q - nfmD Fc ks m M (kzC Fc m M cs q)

/-- `ρ_q = B(c_q) / ((η c_q − c_q′) R_q)`. -/
def kzRho (q : ℕ) : NFM Fc m M :=
  nfmEval Fc m M B (kzC Fc m M cs q) * (kzD Fc ks m M g cs q * kzR Fc m M A kt l cs q)⁻¹

/-- `ρ_qⁿ A(c_q)ʲ`. -/
def kzQ (q : ℕ) : NFM Fc m M :=
  kzRho Fc ks m M g A B kt l cs q ^ n * nfmEval Fc m M A (kzC Fc m M cs q) ^ j

/-- Are all `ρ_qⁿ A(c_q)ʲ` constant? -/
def kzConst : Bool :=
  (List.range cs.length).all fun q ↦ nfmD Fc ks m M (kzQ Fc ks m n j M g A B kt l cs q) == 0

/-- `κ_q ∈ N`: the rational coordinates of `ρ_qⁿ A(c_q)ʲ`. -/
def kzK (q : ℕ) : CPoly ℚ :=
  (kzQ Fc ks m n j M g A B kt l cs q).1.map fun a ↦ (ratValC Fc ks m (unTr Fc m a)).getD 0

/-- The data checks: `A(0) ≠ 0`, `D = ∏ (t − c_q)`, `c_q ≠ 0`, `R_q ≠ 0`, `A(c_q) ≠ 0`,
`B(c_q) ≠ 0`. -/
def kzOK (dC : GPoly (LC m)) : Bool :=
  !(MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) &&
  decide (CPoly.trim (nfmProd Fc m M cs) = kyFA Fc m M dC) &&
  (List.range cs.length).all fun q ↦
    kzC Fc m M cs q != 0 && kzR Fc m M A kt l cs q != 0 &&
    nfmEval Fc m M A (kzC Fc m M cs q) != 0 && nfmEval Fc m M B (kzC Fc m M cs q) != 0

/-- The checks on the number field: `ζ` a primitive `n`-th root of unity, `γ_qⁿ = κ_q`. -/
def kzFieldOK (zN : CPoly ℚ) (gs : List (CPoly ℚ)) : Bool :=
  decide (CPoly.trim M = M) && decide (1 < M.length) &&
  decide (powQ M zN n = NFK.norm M [1]) &&
  (List.range n).all (fun k ↦ k == 0 || !decide (powQ M zN k = NFK.norm M [1])) &&
  decide (gs.length = cs.length) &&
  (List.range cs.length).all fun q ↦
    decide (powQ M (gs.getD q []) n = NFK.norm M (kzK Fc ks m n j M g A B kt l cs q))

/-- The denominator `tᵏ D Aˡ`. -/
def kzDen (dC : GPoly (LC m)) : GPoly (LC m) :=
  GPoly.mul (MO Fc ks m) (GPoly.mul (MO Fc ks m) (monoG Fc ks m kt) dC) (powG (MO Fc ks m) A l)

end Res

section Comp

variable (m n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (zN : CPoly ℚ)
  (gs : List (CPoly ℚ))

/-- `β_q = (γ_q/ρ_q)ᵃ A(c_q)ᵇ`, `aj + bn = 1`. -/
def kzBeta (q : ℕ) : NFM Fc m M :=
  (ofQ Fc m M (gs.getD q []) * (kzRho Fc ks m M g A B kt l cs q)⁻¹) ^ (Nat.gcdA j n) *
    nfmEval Fc m M A (kzC Fc m M cs q) ^ (Nat.gcdB j n)

/-- The points `(c_q, ζᵏβ_q)`, indexed by `i = q n + k`. -/
def kzAl (i : Fin (cs.length * n)) : NFM Fc m M := kzC Fc m M cs (i / n)

def kzBe (i : Fin (cs.length * n)) : NFM Fc m M :=
  ofQ Fc m M zN ^ ((i : ℕ) % n) * kzBeta Fc ks m n j M g A B kt l cs gs (i / n)

/-- The torsion answer of the component `f`. -/
def kzTorsC (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (f : ℕ) : Option (Option ℕ) :=
  torsOracleC (redAtNFM Fc m M rs) (cpf (kyFA Fc m M A)) ps bound (kyFA Fc m M A) n
    (gammaL (kzAl Fc m n M cs) (kzBe Fc ks m n j M g A B kt l cs zN gs)
      (kyMult n j M zN gs cs.length f) 1)

/-- The torsion answer of the component `f` (certificates by search modulo `p`). -/
def kzTors (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (f : ℕ) : Option (Option ℕ) :=
  kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ searchCert fK n) ps bound rs f

/-- The witness of the component `f` (order `N`). -/
def kzWit (f N : ℕ) : Option (BPoly (NFM Fc m M)) :=
  witW (kyFA Fc m M A) n ((kyFA Fc m M A).length - 1) (kzAl Fc m n M cs)
    (kzBe Fc ks m n j M g A B kt l cs zN gs) (kyMult n j M zN gs cs.length f) N

end Comp

/-- The parametric Risch equation with the coordinates of the columns of the components (after
the `extra` columns), when every component has a witness. -/
def kzSolveC (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (extra : List (LC (m + 1))) : Option Bool :=
  let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs)
  let wits := (List.zip comps tors).map fun p ↦
    kzWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0)
  match wits.allSome with
  | none => none
  | some Wbs =>
    match (Wbs.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome with
    | none => none
    | some colss => some ((prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
        (((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) :: (extra ++ colss.flatten))).any
        fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision** (`none`: data not accepted, a torsion oracle did not answer within its
bounds, a runtime check failed, or a component is not torsion while the orders over `t = 0`
cannot be killed). -/
def kzDecideC (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  let O := MO Fc ks m
  let d := M.length - 1
  let comps := (List.range d).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs)
  let solve : List (LC (m + 1)) → Option Bool :=
    kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs
  if !(decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) then none
  else if cs.length = 0 then none
  else if !kzOK Fc ks m M A B kt l cs dC then none
  else if !kzConst Fc ks m n j M g A B kt l cs then some false
  else if !kzFieldOK Fc ks m n j M g A B kt l cs zN gs then none
  else if tors.any (· == none) then none
  else
    let allT := !(tors.any (· == some none))
    match krZ Fc ks lv m n A with
    | none =>
      if allT then solve []
      else if (List.range (n + 1)).all (fun ℓ ↦ !(decide (Nat.Prime ℓ ∧ ℓ ∣ n)) ||
          (krZ Fc ks lv m ℓ A).isNone) then some false
      else none
    | some z =>
      let κ := (ratValC Fc ks m (O.mul (powC O z n) (A.getD 0 O.zero))).getD 0
      if κ = 0 then none
      else
        match kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs with
        | none => none
        | some none =>
          if allT then solve []
          else if kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs then some false else none
        | some (some N0) =>
          if allT then
            match kyWitPsi Fc ks m n M A zN z κ N0 with
            | none => none
            | some W0 =>
              match kyColM Fc ks m n M (krAh Fc ks m n A z κ) z j W0 with
              | none => none
              | some cols0 => solve cols0
          else if kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs then some false else none

/-- The parametric Risch equation (certificates by search modulo `p`). -/
def kzSolve (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (extra : List (LC (m + 1))) : Option Bool :=
  kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC (fun fK ↦ searchCert fK n) ps bound rs extra

/-- **The decision** (certificates by search modulo `p`). -/
def kzDecide (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kzDecideC Fc ks lv m n j g M zN gs A B kt l cs dC (fun fK ↦ searchCert fK n) ps bound rs

/-- **The decision with local torsion certificates** (`kz_decided`). -/
def kzDecideL (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kzDecideC Fc ks lv m n j g M zN gs A B kt l cs dC (fun fK ↦ localCert fK n) ps bound rs

end Curves.MT
