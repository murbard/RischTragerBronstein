import RischTragerBronstein.Mixed.KYField
import RischTragerBronstein.Mixed.KXCodes
import RischTragerBronstein.Algebraic.SupLocalCert

/-!
# Radicals of order `n` over an exponential level with poles at ordinary places: the algorithm

`kyDecide`: for a certified mixed tower whose top level `t = tₘ` is an exponential (`t′ = η t`,
`η = g′`), `θⁿ = A(t)` (`A` squarefree of degree prime to `n`, `A(0) ≠ 0`), `0 < j < n` prime to
`n`, and the integrand `B(t) θʲ / (tᵏ D(t) A(t)ˡ)` with `D = ∏_q (t − c_q)`:

1. The residue at `(c_q, β)` (`βⁿ = A(c_q)`) is `ρ_q βʲ`, `ρ_q = B(c_q)/((η c_q − c_q′) R_q)`; the
   `n`-th powers `ρ_qⁿ A(c_q)ʲ` must be constants (else: not elementary), hence rationals `κ_q`.
2. A number field `N = ℚ[X]/(M)` is supplied with `ζ` (a primitive `n`-th root of unity) and
   `γ_q` (`γ_qⁿ = κ_q`), all checked. With `β_q = (γ_q/ρ_q)ᵃ A(c_q)ᵇ` (`aj + bn = 1`) the points
   over `c_q` are `(c_q, ζᵏβ_q)`, with residues `ζ^{kj} γ_q`, whose coordinates in the basis
   `1, X, …` of `N` define the component divisors `D_f`.
3. Every component is asked to the torsion oracle over `Kₘ ⊗ N`.
4. Over `t = 0` as for `krDecide`; when a component is not torsion the answer is `false` if the
   orders over `t = 0` can be killed (`Xⁿ − A(0)` irreducible, or every point over `0` torsion),
   and `none` otherwise (a Mordell–Weil relation question).
5. All components torsion: the parametric Risch equation with the coordinates of the columns
   `zʲ Dⱼ/g` of the witnesses (`kyColM`).
-/

open Polynomial CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- Multiplication modulo `M` over `ℚ`. -/
def mulQ (M a b : CPoly ℚ) : CPoly ℚ := NFK.norm M (CPoly.mul a b)

/-- Powers modulo `M` over `ℚ`. -/
def powQ (M a : CPoly ℚ) : ℕ → CPoly ℚ
  | 0 => NFK.norm M [1]
  | k + 1 => mulQ M (powQ M a k) a

/-- The least common multiple of a list. -/
def lcmL (l : List ℕ) : ℕ := l.foldr Nat.lcm 1

lemma dvd_lcmL {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ∣ lcmL l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (ih h).trans (Nat.dvd_lcm_right _ _)

lemma lcmL_pos {l : List ℕ} (h : ∀ x ∈ l, 0 < x) : 0 < lcmL l := by
  induction l with
  | nil => simp [lcmL]
  | cons a l ih =>
    exact Nat.lcm_pos (h a (List.mem_cons_self ..)) (ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx))

section Coords

variable (n j : ℕ) (M zN : CPoly ℚ) (gs : List (CPoly ℚ)) (r : ℕ)

/-- The coordinates of the residue `ζ^{kj} γ_q` at `(c_q, ζᵏβ_q)`. -/
def kyRR (q k : ℕ) : CPoly ℚ := mulQ M (powQ M zN (k * j)) (gs.getD q [])

/-- The coordinate `f` of the residue at the point `i = q n + k`. -/
def kyR (f i : ℕ) : ℚ := (kyRR j M zN gs (i / n) (i % n)).getD f 0

/-- A common denominator of the coordinate `f`. -/
def kyDen (f : ℕ) : ℕ := lcmL ((List.range (r * n)).map fun i ↦ (kyR n j M zN gs f i).den)

/-- The integral coefficients `L_f r_{f,i}`. -/
def kyZc (f i : ℕ) : ℤ :=
  (((kyDen n j M zN gs r f / (kyR n j M zN gs f i).den : ℕ) : ℤ) * (kyR n j M zN gs f i).num)

/-- The shift of the fibre over `c_q` making the coefficients non-negative. -/
def kySh (f q : ℕ) : ℤ := ((List.range n).map fun k ↦ -kyZc n j M zN gs r f (q * n + k)).foldr max 0

/-- The multiplicities of the component `f` (shifted). -/
def kyMult (f : ℕ) (i : Fin (r * n)) : ℕ :=
  (kyZc n j M zN gs r f i + kySh n j M zN gs r f (i / n)).toNat

/-- Is the component `f` non-zero? -/
def kyNZ (f : ℕ) : Bool := (List.range (r * n)).any fun i ↦ kyR n j M zN gs f i != 0

end Coords

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Res

variable (m n j : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))

/-- `ρ_q = B(c_q) / ((η c_q − c_q′) R_q)`. -/
def kyRho (q : ℕ) : LC m :=
  normC Fc m ((MO Fc ks m).mul (evalGC Fc ks m B (kqC Fc ks m cs q))
    ((MO Fc ks m).inv ((MO Fc ks m).mul (kxD Fc ks m g cs q) (kxR Fc ks m A kt l cs q))))

/-- `ρ_qⁿ A(c_q)ʲ`. -/
def kyQ (q : ℕ) : LC m :=
  normC Fc m ((MO Fc ks m).mul (powC (MO Fc ks m) (kyRho Fc ks m g A B kt l cs q) n)
    (powC (MO Fc ks m) (evalGC Fc ks m A (kqC Fc ks m cs q)) j))

/-- Are all `ρ_qⁿ A(c_q)ʲ` constant? -/
def kyConst : Bool :=
  (List.range cs.length).all fun q ↦
    (MO Fc ks m).isZero ((MO Fc ks m).deriv (kyQ Fc ks m n j g A B kt l cs q))

/-- The rational `κ_q`. -/
def kyK (q : ℕ) : ℚ := (ratValC Fc ks m (kyQ Fc ks m n j g A B kt l cs q)).getD 0

/-- The checks on the number field: `ζ` a primitive `n`-th root of unity, `γ_qⁿ = κ_q`. -/
def kyFieldOK (M zN : CPoly ℚ) (gs : List (CPoly ℚ)) : Bool :=
  decide (CPoly.trim M = M) && decide (1 < M.length) &&
  decide (powQ M zN n = NFK.norm M [1]) &&
  (List.range n).all (fun k ↦ k == 0 || !decide (powQ M zN k = NFK.norm M [1])) &&
  decide (gs.length = cs.length) &&
  (List.range cs.length).all fun q ↦
    decide (powQ M (gs.getD q []) n = NFK.norm M [kyK Fc ks m n j g A B kt l cs q])

end Res

section Comp

variable (m n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (zN : CPoly ℚ)
  (gs : List (CPoly ℚ))

/-- `A` over `Kₘ ⊗ N`. -/
def kyFA (A' : GPoly (LC m)) : CPoly (NFM Fc m M) :=
  CPoly.trim ((A'.map (trC Fc m)).map (embM Fc m M))

/-- `β_q = (γ_q/ρ_q)ᵃ A(c_q)ᵇ`, `aj + bn = 1`. -/
def kyBeta (q : ℕ) : NFM Fc m M :=
  (ofQ Fc m M (gs.getD q []) * (embM Fc m M (trC Fc m (kyRho Fc ks m g A B kt l cs q)))⁻¹) ^
      (Nat.gcdA j n) *
    (embM Fc m M (trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q)))) ^ (Nat.gcdB j n)

/-- The points `(c_q, ζᵏβ_q)`, indexed by `i = q n + k`. -/
def kyAl (i : Fin (cs.length * n)) : NFM Fc m M :=
  embM Fc m M (trC Fc m (kqC Fc ks m cs (i / n)))

def kyBe (i : Fin (cs.length * n)) : NFM Fc m M :=
  ofQ Fc m M zN ^ ((i : ℕ) % n) * kyBeta Fc ks m n j M g A B kt l cs gs (i / n)

/-- The torsion answer of the component `f`. -/
def kyTorsC (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (f : ℕ) :
    Option (Option ℕ) :=
  torsOracleC (redAtNFM Fc m M rs) (cpf (kyFA Fc m M A)) ps bound (kyFA Fc m M A) n
    (gammaL (kyAl Fc ks m n M cs) (kyBe Fc ks m n j M g A B kt l cs zN gs)
      (kyMult n j M zN gs cs.length f) 1)

/-- The torsion answer of the component `f` (certificates by search modulo `p`). -/
def kyTors (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (f : ℕ) : Option (Option ℕ) :=
  kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ searchCert fK n) ps bound rs f

/-- The witness of the component `f` (order `N`). -/
def kyWit (f N : ℕ) : Option (BPoly (NFM Fc m M)) :=
  witW (kyFA Fc m M A) n ((kyFA Fc m M A).length - 1) (kyAl Fc ks m n M cs)
    (kyBe Fc ks m n j M g A B kt l cs zN gs) (kyMult n j M zN gs cs.length f) N

end Comp

section Column

variable (m n : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]

/-- The coordinates (codes of level `m + 1`) of a coefficient polynomial over `Kₘ ⊗ N`. -/
def kyCoords (d : ℕ) (c : CPoly (NFM Fc m M)) : List (LC (m + 1)) :=
  (List.range d).map fun f ↦ pcP Fc ks m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m))

/-- **The column** `zʲ Dⱼ/g` over `K_{m+1} ⊗ N`, `Dⱼ` the `ỹʲ`-coordinate of `W′/W` on `ỹⁿ = Â`,
by coordinates (`none` if the gcd is not a non-zero constant). -/
def kyColM (Ah : GPoly (LC m)) (z : LC m) (j : ℕ) (W : BPoly (NFM Fc m M)) :
    Option (List (LC (m + 1))) :=
  let d := M.length - 1
  let O := MO Fc ks (m + 1)
  let tr := trC Fc (m + 1)
  let toN : List (LC (m + 1)) → NFM Fc (m + 1) M := fun cf ↦ NFK.mk _ (cf.map tr)
  let Wc : List (List (LC (m + 1))) := W.map (kyCoords Fc ks m M d)
  let Ahc := pcP Fc ks m Ah
  let r := O.mul (mcst Fc ks (m + 1) (1 / n)) (O.mul (O.deriv Ahc) (O.inv Ahc))
  let Wd : List (List (LC (m + 1))) := (List.range Wc.length).map fun i ↦
    (Wc.getD i []).map fun c ↦ O.add (O.deriv c) (O.mul (O.mul (mcst Fc ks (m + 1) i) r) c)
  let WK : CPoly (NFM Fc (m + 1) M) := Wc.map toN
  let WdK : CPoly (NFM Fc (m + 1) M) := Wd.map toN
  let MK : CPoly (NFM Fc (m + 1) M) :=
    (-(embM Fc (m + 1) M (tr Ahc))) :: (List.replicate (n - 1) 0 ++ [1])
  let e := CPoly.egcd WK MK
  let gg := CPoly.trim e.1
  if gg.length = 1 then
    let D := (CPoly.divMod (CPoly.mul WdK e.2.1) MK).2
    let col := embM Fc (m + 1) M (tr (pcP Fc ks m [powC (MO Fc ks m) z j])) *
      (D.getD j 0 * (gg.getD 0 1)⁻¹)
    some ((List.range d).map fun f ↦ normC Fc (m + 1) (unTr Fc (m + 1) (col.1.getD f 0)))
  else none

end Column

section Zero

variable (m n : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (A : GPoly (LC m)) (zN : CPoly ℚ)

/-- The torsion answer for `Ψ = ∑_k (c_n(k) + M₀)(0, ζᵏ)` on the twist over `Kₘ ⊗ N`. -/
def kyTorsPsiC (z : LC m) (κ : ℚ) (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option (Option ℕ) :=
  torsOracleC (redAtNFM Fc m M rs) (cpf (kyFA Fc m M (krAh Fc ks m n A z κ))) ps bound
    (kyFA Fc m M (krAh Fc ks m n A z κ)) n
    (gammaL (fun _ : Fin n ↦ (0 : NFM Fc m M)) (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (ramMult n) 1)

/-- The torsion answer for `Ψ` (certificates by search modulo `p`). -/
def kyTorsPsi (z : LC m) (κ : ℚ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option (Option ℕ) :=
  kyTorsPsiC Fc ks m n M A zN z κ (fun fK ↦ searchCert fK n) ps bound rs

/-- The witness of `N Ψ` on the twist. -/
def kyWitPsi (z : LC m) (κ : ℚ) (N : ℕ) : Option (BPoly (NFM Fc m M)) :=
  witW (kyFA Fc m M (krAh Fc ks m n A z κ)) n ((kyFA Fc m M (krAh Fc ks m n A z κ)).length - 1)
    (fun _ : Fin n ↦ (0 : NFM Fc m M)) (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (ramMult n) N

/-- Is every point `(0, ζᵏ)` of the twist torsion? -/
def kyZeroTorsC (z : LC m) (κ : ℚ) (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Bool :=
  (List.range n).all fun k ↦
    match torsOracleC (redAtNFM Fc m M rs) (cpf (kyFA Fc m M (krAh Fc ks m n A z κ))) ps bound
      (kyFA Fc m M (krAh Fc ks m n A z κ)) n
      (gammaL ![(0 : NFM Fc m M)] ![ofQ Fc m M zN ^ k] ![1] 1) with
    | some (some _) => true
    | _ => false

/-- Is every point `(0, ζᵏ)` of the twist torsion? (certificates by search modulo `p`). -/
def kyZeroTors (z : LC m) (κ : ℚ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Bool :=
  kyZeroTorsC Fc ks m n M A zN z κ (fun fK ↦ searchCert fK n) ps bound rs

end Zero

/-- The parametric Risch equation with the coordinates of the columns of the components (after
the `extra` columns), when every component has a witness. -/
def kySolveC (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (extra : List (LC (m + 1))) : Option Bool :=
  let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs)
  let wits := (List.zip comps tors).map fun p ↦
    kyWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0)
  match wits.allSome with
  | none => none
  | some Wbs =>
    match (Wbs.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome with
    | none => none
    | some colss => some ((prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
        (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: (extra ++ colss.flatten))).any
        fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision** (`none`: data not accepted, a torsion oracle did not answer within its
bounds, a runtime check failed, or a component is not torsion while the orders over `t = 0`
cannot be killed). -/
def kyDecideC (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option Bool :=
  let O := MO Fc ks m
  let d := M.length - 1
  let rhs : LC (m + 1) := (B, kxDen Fc ks m A kt l cs)
  let frA := kpFr Fc ks m j n A
  let comps := (List.range d).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs)
  let solve : List (LC (m + 1)) → Option Bool :=
    kySolveC Fc ks lv m n j g M zN gs A B kt l cs cpf ps bound rs
  if !(decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) then none
  else if cs.length = 0 then none
  else if !kxOK Fc ks m A B kt l cs then none
  else if !kyConst Fc ks m n j g A B kt l cs then some false
  else if !kyFieldOK Fc ks m n j g A B kt l cs M zN gs then none
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
def kySolve (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (extra : List (LC (m + 1))) : Option Bool :=
  kySolveC Fc ks lv m n j g M zN gs A B kt l cs (fun fK ↦ searchCert fK n) ps bound rs extra

/-- **The decision** (certificates by search modulo `p`). -/
def kyDecide (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  kyDecideC Fc ks lv m n j g M zN gs A B kt l cs (fun fK ↦ searchCert fK n) ps bound rs

/-- **The decision with local torsion certificates** (`ky_decided`). -/
def kyDecideL (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  kyDecideC Fc ks lv m n j g M zN gs A B kt l cs (fun fK ↦ localCert fK n) ps bound rs

/-- `torsOracleC_spec` for a provider depending on the curve. -/
lemma torsOracleC_specY {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (redAt : (p : ℕ) → Option (RedFns p K)) (cpf : CPoly K → CertProv K)
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p K), redAt p = some R →
      ∃ φ : K →+* ℚ_[p], RedValid p R φ)
    (ps : List ℕ) (bound : ℕ) {fK : CPoly K} {n : ℕ} (hsq : Squarefree (CPoly.toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) :
    TorsSpecN fK n (torsOracleC redAt (cpf fK) ps bound fK n) :=
  torsOracleC_spec redAt (cpf fK) hred ps bound hsq hcop

end Curves.MT
