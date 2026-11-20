import RischTragerBronstein.Mixed.KYCodes

/-!
# Radicals of order `n` over a logarithmic level with poles at ordinary places: the algorithm

`kvDecide`: for a certified mixed tower whose top level `t = tₘ` is a logarithm (`t′ = η`),
`θⁿ = A(t)` (`A` squarefree of degree prime to `n`), `0 < j < n` prime to `n`, and the integrand
`B(t) θʲ / (D(t) A(t)ˡ)` with `D = ∏_q (t − c_q)`:

1. The residue at `(c_q, β)` (`βⁿ = A(c_q)`) is `ρ_q βʲ`, `ρ_q = B(c_q)/((η − c_q′) R_q)`; the
   `n`-th powers `ρ_qⁿ A(c_q)ʲ` must be constants (else: not elementary), hence rationals `κ_q`.
2. A number field `N = ℚ[X]/(M)` is supplied with `ζ` (a primitive `n`-th root of unity) and
   `γ_q` (`γ_qⁿ = κ_q`), all checked; the points over `c_q` are `(c_q, ζᵏβ_q)`, with residues
   `ζ^{kj} γ_q`, whose coordinates in the basis `1, X, …` of `N` define the components `D_f`.
3. Every component is asked to the torsion oracle over `Kₘ ⊗ N`; one of them not torsion: not
   elementary (over a logarithm there is a single place at infinity and no other special fibre).
4. All components torsion: the parametric Risch equation with the coordinates of the columns
   `Dⱼ` of the witnesses (`kyColM`).

This is `kyDecideC` (`KYCodes`) with `η − c′` in place of `η c − c′`, no power of `t` in the
denominator and no fibre over `t = 0`.
-/

open Polynomial CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Res

variable (m n j : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))

/-- The denominator `∏ (t − c_q) Aˡ`. -/
def kvDen : GPoly (LC m) := GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)

/-- `ρ_q = B(c_q) / ((η − c_q′) R_q)`. -/
def kvRho (q : ℕ) : LC m :=
  normC Fc m ((MO Fc ks m).mul (evalGC Fc ks m B (kqC Fc ks m cs q))
    ((MO Fc ks m).inv ((MO Fc ks m).mul (kqD Fc ks m η cs q) (kqR Fc ks m A l cs q))))

/-- `ρ_qⁿ A(c_q)ʲ`. -/
def kvQ (q : ℕ) : LC m :=
  normC Fc m ((MO Fc ks m).mul (powC (MO Fc ks m) (kvRho Fc ks m η A B l cs q) n)
    (powC (MO Fc ks m) (evalGC Fc ks m A (kqC Fc ks m cs q)) j))

/-- Are all `ρ_qⁿ A(c_q)ʲ` constant? -/
def kvConst : Bool :=
  (List.range cs.length).all fun q ↦
    (MO Fc ks m).isZero ((MO Fc ks m).deriv (kvQ Fc ks m n j η A B l cs q))

/-- The rational `κ_q`. -/
def kvK (q : ℕ) : ℚ := (ratValC Fc ks m (kvQ Fc ks m n j η A B l cs q)).getD 0

/-- The checks on the number field: `ζ` a primitive `n`-th root of unity, `γ_qⁿ = κ_q`. -/
def kvFieldOK (M zN : CPoly ℚ) (gs : List (CPoly ℚ)) : Bool :=
  decide (CPoly.trim M = M) && decide (1 < M.length) &&
  decide (powQ M zN n = NFK.norm M [1]) &&
  (List.range n).all (fun k ↦ k == 0 || !decide (powQ M zN k = NFK.norm M [1])) &&
  decide (gs.length = cs.length) &&
  (List.range cs.length).all fun q ↦
    decide (powQ M (gs.getD q []) n = NFK.norm M [kvK Fc ks m n j η A B l cs q])

end Res

section Comp

variable (m n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (zN : CPoly ℚ)
  (gs : List (CPoly ℚ))

/-- `β_q = (γ_q/ρ_q)ᵃ A(c_q)ᵇ`, `aj + bn = 1`. -/
def kvBeta (q : ℕ) : NFM Fc m M :=
  (ofQ Fc m M (gs.getD q []) * (embM Fc m M (trC Fc m (kvRho Fc ks m η A B l cs q)))⁻¹) ^
      (Nat.gcdA j n) *
    (embM Fc m M (trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q)))) ^ (Nat.gcdB j n)

/-- The points `(c_q, ζᵏβ_q)`, indexed by `i = q n + k`: the second coordinate. -/
def kvBe (i : Fin (cs.length * n)) : NFM Fc m M :=
  ofQ Fc m M zN ^ ((i : ℕ) % n) * kvBeta Fc ks m n j M η A B l cs gs (i / n)

/-- The torsion answer of the component `f`. -/
def kvTorsC (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (f : ℕ) : Option (Option ℕ) :=
  torsOracleC (redAtNFM Fc m M rs) (cpf (kyFA Fc m M A)) ps bound (kyFA Fc m M A) n
    (gammaL (kyAl Fc ks m n M cs) (kvBe Fc ks m n j M η A B l cs zN gs)
      (kyMult n j M zN gs cs.length f) 1)

/-- The witness of the component `f` (order `N`). -/
def kvWit (f N : ℕ) : Option (BPoly (NFM Fc m M)) :=
  witW (kyFA Fc m M A) n ((kyFA Fc m M A).length - 1) (kyAl Fc ks m n M cs)
    (kvBe Fc ks m n j M η A B l cs zN gs) (kyMult n j M zN gs cs.length f) N

end Comp

/-- The parametric Risch equation with the coordinates of the columns of the components, when
every component has a witness. -/
def kvSolveC (m n j : ℕ) (η : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs)
  let wits := (List.zip comps tors).map fun p ↦
    kvWit Fc ks m n j M η A B l cs zN gs p.1 ((p.2.getD none).getD 0)
  match wits.allSome with
  | none => none
  | some Wbs =>
    match (Wbs.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome with
    | none => none
    | some colss => some ((prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
        (((B, kvDen Fc ks m A l cs) : LC (m + 1)) :: colss.flatten)).any
        fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision** (`none`: data not accepted, a torsion oracle did not answer within its
bounds, or a runtime check failed). -/
def kvDecideC (m n j : ℕ) (η : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs)
  if !(decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) then none
  else if cs.length = 0 then none
  else if !kqOK Fc ks m A B l cs then none
  else if !kvConst Fc ks m n j η A B l cs then some false
  else if !kvFieldOK Fc ks m n j η A B l cs M zN gs then none
  else if tors.any (· == none) then none
  else if tors.any (· == some none) then some false
  else kvSolveC Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs

/-- **The decision** (certificates by search modulo `p`). -/
def kvDecide (m n j : ℕ) (η : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  kvDecideC Fc ks lv m n j η M zN gs A B l cs (fun fK ↦ searchCert fK n) ps bound rs

/-- **The decision with local torsion certificates.** -/
def kvDecideL (m n j : ℕ) (η : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  kvDecideC Fc ks lv m n j η M zN gs A B l cs (fun fK ↦ localCert fK n) ps bound rs

end Curves.MT
