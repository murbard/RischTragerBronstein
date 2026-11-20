import RischTragerBronstein.Mixed.KQMCodes

/-!
# Square roots over an exponential level with poles at ordinary places: the algorithm

`kxDecide`: for a certified mixed tower whose top level `t = tₘ` is an exponential
(`t′ = η t`, `η = g′`), `θ² = A(t)` (`A ∈ Fₘ[t]` squarefree of odd degree, `A(0) ≠ 0`) and the
integrand `B(t) θ / (tᵏ D(t) A(t)ˡ)` with `D = ∏_q (t − c_q)` (the `c_q ∈ Fₘ` non-zero codes,
distinct, `A(c_q) ≠ 0`, `B(c_q) ≠ 0`):

1. The squared residues `Q_q = B(c_q)² A(c_q) / ((η c_q − c_q′) R_q)²`,
   `R_q = c_qᵏ ∏_{q' ≠ q} (c_q − c_{q'}) A(c_q)ˡ`, must be constants (else: not elementary), hence
   rationals `κ_q`; they are split into classes modulo squares as for a logarithmic level.
2. Every class is asked to the torsion oracle on its twist `ỹ² = s_T A`.
3. Over `t = 0` (the places `P± = (0, ±√A(0))`, where residues say nothing): if `A(0)` is not a
   constant times a square in `Fₘ`, the logarithms have no `P₊ − P₋` part. Otherwise
   (`κ = z² A(0) ∈ ℚ`) the torsion oracle on `Â = (z²/κ) A` decides whether `P₊ − ∞` is torsion; if
   it is, its witness gives one more column.
4. Some class not torsion: not elementary (with `P₊ − ∞` torsion or `√A(0) ∉ Fₘ`), undecided if
   `P₊ − ∞` is not torsion (a Mordell–Weil relation question). All classes torsion: the answer is
   the parametric Risch equation with one column per class (and one for `P₊ − ∞` when torsion).
-/

open Polynomial CPoly SqrtIndep

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Pole

variable (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))

/-- The denominator `tᵏ ∏ (t − c_q) Aˡ`. -/
def kxDen : GPoly (LC m) :=
  GPoly.mul (MO Fc ks m) (GPoly.mul (MO Fc ks m) (monoG Fc ks m kt) (prodLinG Fc ks m cs))
    (powG (MO Fc ks m) A l)

/-- `R_q = c_qᵏ ∏_{q' ≠ q} (c_q − c_{q'}) A(c_q)ˡ`. -/
def kxR (q : ℕ) : LC m :=
  normC Fc m ((MO Fc ks m).mul
    ((MO Fc ks m).mul (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q)) (kqC Fc ks m cs q))
      (powC (MO Fc ks m) (kqC Fc ks m cs q) kt))
    (powC (MO Fc ks m) (evalGC Fc ks m A (kqC Fc ks m cs q)) l))

/-- `η c_q − c_q′` (`η = g′`). -/
def kxD (q : ℕ) : LC m :=
  subC (MO Fc ks m) ((MO Fc ks m).mul ((MO Fc ks m).deriv g) (kqC Fc ks m cs q))
    ((MO Fc ks m).deriv (kqC Fc ks m cs q))

/-- The squared residue `Q_q = B(c_q)² A(c_q) / ((η c_q − c_q′) R_q)²`. -/
def kxQ (q : ℕ) : LC m :=
  let O := MO Fc ks m
  let bq := evalGC Fc ks m B (kqC Fc ks m cs q)
  let dr := O.mul (kxD Fc ks m g cs q) (kxR Fc ks m A kt l cs q)
  normC Fc m (O.mul (O.mul (O.mul bq bq) (evalGC Fc ks m A (kqC Fc ks m cs q))) (O.inv (O.mul dr dr)))

/-- The rational value `κ_q` of `Q_q`. -/
def kxK (q : ℕ) : ℚ := (ratValC Fc ks m (kxQ Fc ks m g A B kt l cs q)).getD 0

/-- The checks on the data: `A(0) ≠ 0`, and the `c_q`, `R_q`, `A(c_q)`, `B(c_q)` are non-zero. -/
def kxOK : Bool :=
  !(MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) &&
  (List.range cs.length).all fun q ↦
    !(MO Fc ks m).isZero (kqC Fc ks m cs q) &&
    !(MO Fc ks m).isZero (kxR Fc ks m A kt l cs q) &&
    !(MO Fc ks m).isZero (evalGC Fc ks m A (kqC Fc ks m cs q)) &&
    !(MO Fc ks m).isZero (evalGC Fc ks m B (kqC Fc ks m cs q))

/-- Are all squared residues constant? -/
def kxConst : Bool :=
  (List.range cs.length).all fun q ↦
    (MO Fc ks m).isZero ((MO Fc ks m).deriv (kxQ Fc ks m g A B kt l cs q))

/-- The squared residues. -/
def kxKs : List ℚ := (List.range cs.length).map (kxK Fc ks m g A B kt l cs)

/-- The generators of the square classes. -/
def kxGens : List ℚ := gensOf (kxKs Fc ks m g A B kt l cs)

/-- The class `T_q` and the rational `c_q` with `κ_q = c_q² ∏_{T_q} g`. -/
def kxRep (q : ℕ) : List Bool × ℚ :=
  (findRep (kxGens Fc ks m g A B kt l cs) (kxK Fc ks m g A B kt l cs q)).getD ([], 0)

/-- The classes. -/
def kxCls : List (List Bool) :=
  ((List.range cs.length).map fun q ↦ (kxRep Fc ks m g A B kt l cs q).1).dedup

/-- The common denominator of the `c_q`. -/
def kxDenM : ℕ := ((List.range cs.length).map fun q ↦ (kxRep Fc ks m g A B kt l cs q).2.den).prod

/-- The multiplicity `M c_q ∈ ℕ`. -/
def kxMNm (q : ℕ) : ℕ :=
  (((kxDenM Fc ks m g A B kt l cs / (kxRep Fc ks m g A B kt l cs q).2.den : ℕ) : ℤ) *
    (kxRep Fc ks m g A B kt l cs q).2.num).toNat

/-- The class value `s_T = ∏_T g`. -/
def kxS (T : List Bool) : ℚ := prodSub (kxGens Fc ks m g A B kt l cs) T

/-- The ordinate `s_T c_q (η c_q − c_q′) R_q / B(c_q)` on `ỹ² = s_T A`. -/
def kxBm (q : ℕ) : LC m :=
  let O := MO Fc ks m
  normC Fc m (O.mul (mcst Fc ks m (kxS Fc ks m g A B kt l cs (kxRep Fc ks m g A B kt l cs q).1 *
      (kxRep Fc ks m g A B kt l cs q).2))
    (O.mul (kxD Fc ks m g cs q) (O.mul (kxR Fc ks m A kt l cs q)
      (O.inv (evalGC Fc ks m B (kqC Fc ks m cs q))))))

/-- The poles of the class `T`. -/
def kxQs (T : List Bool) : List ℕ :=
  (List.range cs.length).filter fun q ↦ (kxRep Fc ks m g A B kt l cs q).1 == T

/-- The twisted polynomial `s_T A` over `Kₘ`. -/
def kxFKm (T : List Bool) : CPoly (KF Fc m) :=
  CPoly.trim ((A.map ((MO Fc ks m).mul (mcst Fc ks m (kxS Fc ks m g A B kt l cs T)))).map (trC Fc m))

/-- The points of the class `T` over `Kₘ`. -/
def kxAlm (T : List Bool) : Fin (kxQs Fc ks m g A B kt l cs T).length → KF Fc m :=
  fun i ↦ trC Fc m (kqC Fc ks m cs ((kxQs Fc ks m g A B kt l cs T)[i]))

def kxBem (T : List Bool) : Fin (kxQs Fc ks m g A B kt l cs T).length → KF Fc m :=
  fun i ↦ trC Fc m (kxBm Fc ks m g A B kt l cs ((kxQs Fc ks m g A B kt l cs T)[i]))

def kxMqm (T : List Bool) : Fin (kxQs Fc ks m g A B kt l cs T).length → ℕ :=
  fun i ↦ kxMNm Fc ks m g A B kt l cs ((kxQs Fc ks m g A B kt l cs T)[i])

/-- Every squared residue has a representation. -/
def kxRepOK : Bool :=
  (List.range cs.length).all fun q ↦
    (findRep (kxGens Fc ks m g A B kt l cs) (kxK Fc ks m g A B kt l cs q)).isSome

/-- The torsion answer of one class. -/
def kxTorsC (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (T : List Bool) : Option (Option ℕ) :=
  torsOracleC (redAtKF Fc m rs) (cpf (kxFKm Fc ks m g A B kt l cs T)) ps bound
    (kxFKm Fc ks m g A B kt l cs T) 2
    (gammaL (kxAlm Fc ks m g A B kt l cs T) (kxBem Fc ks m g A B kt l cs T)
      (kxMqm Fc ks m g A B kt l cs T) 1)

/-- The witness of one class (order `N`). -/
def kxWit (T : List Bool) (N : ℕ) : Option (BPoly (KF Fc m)) :=
  witW (kxFKm Fc ks m g A B kt l cs T) 2 ((kxFKm Fc ks m g A B kt l cs T).length - 1)
    (kxAlm Fc ks m g A B kt l cs T) (kxBem Fc ks m g A B kt l cs T) (kxMqm Fc ks m g A B kt l cs T) N

/-- The column `B_W` of one class. -/
def kxCol (T : List Bool) (Wb : BPoly (KF Fc m)) : LC (m + 1) :=
  normC Fc (m + 1) (logCol Fc ks m
    (A.map ((MO Fc ks m).mul (mcst Fc ks m (kxS Fc ks m g A B kt l cs T))))
    ((Wb.getD 0 []).map (unTr Fc m)) ((Wb.getD 1 []).map (unTr Fc m)) (MO Fc ks m).one)

end Pole

section Zero

variable (m : ℕ) (A : GPoly (LC m))

/-- A non-zero `z` with `z² A(0)` constant, if any. -/
def kxZ : Option (LC m) :=
  ((prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
    (fun r ↦ !(MO Fc ks m).isZero r.2)).map (·.2)

/-- `κ = z² A(0)` (rational). -/
def kxKap (z : LC m) : ℚ :=
  (ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z) (A.getD 0 (MO Fc ks m).zero))).getD 0

/-- The normalized polynomial `Â = (z²/κ) A` (`Â(0) = 1`). -/
def kxAh (z : LC m) : GPoly (LC m) :=
  A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
    (mcst Fc ks m (kxKap Fc ks m A z)⁻¹)))

/-- Its code over `Kₘ`. -/
def kxFK0 (z : LC m) : CPoly (KF Fc m) := CPoly.trim ((kxAh Fc ks m A z).map (trC Fc m))

/-- The torsion answer for `P₊ − ∞`. -/
def kxTors0C (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (z : LC m) : Option (Option ℕ) :=
  torsOracleC (redAtKF Fc m rs) (cpf (kxFK0 Fc ks m A z)) ps bound (kxFK0 Fc ks m A z) 2
    (gammaL ![(0 : KF Fc m)] ![1] ![1] 1)

/-- The witness of `N (P₊ − ∞)`. -/
def kxWit0 (z : LC m) (N : ℕ) : Option (BPoly (KF Fc m)) :=
  witW (kxFK0 Fc ks m A z) 2 ((kxFK0 Fc ks m A z).length - 1) ![(0 : KF Fc m)] ![1] ![1] N

/-- The column of `P₊ − ∞`. -/
def kxCol0 (z : LC m) (Wb : BPoly (KF Fc m)) : LC (m + 1) :=
  normC Fc (m + 1) (logCol Fc ks m (kxAh Fc ks m A z)
    ((Wb.getD 0 []).map (unTr Fc m)) ((Wb.getD 1 []).map (unTr Fc m)) z)

end Zero

/-- The parametric Risch equation with one column per class (after the `extra` columns), when
every class has a witness. -/
def kxSolveC (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (extra : List (LC (m + 1))) : Option Bool :=
  let cls := kxCls Fc ks m g A B kt l cs
  let tors := cls.map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  let wits := (List.zip cls tors).map fun p ↦
    kxWit Fc ks m g A B kt l cs p.1 ((p.2.getD none).getD 0)
  match wits.allSome with
  | none => none
  | some Wbs =>
    let cols := (List.zip cls Wbs).map fun p ↦ kxCol Fc ks m g A B kt l cs p.1 p.2
    some ((prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: (extra ++ cols))).any
      fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision** (`none`: data not accepted, a torsion oracle did not answer within its
bounds, or a class is not torsion while `P₊ − ∞` is not torsion either). -/
def kxDecideC (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  let tors := (kxCls Fc ks m g A B kt l cs).map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  if cs.length = 0 then none
  else if !kxOK Fc ks m A B kt l cs then none
  else if !kxConst Fc ks m g A B kt l cs then some false
  else if !kxRepOK Fc ks m g A B kt l cs then none
  else if tors.any (· == none) then none
  else
    let allT := !(tors.any (· == some none))
    match kxZ Fc ks lv m A with
    | none => if allT then kxSolveC Fc ks lv m g A B kt l cs cpf ps bound rs [] else some false
    | some z =>
      match kxTors0C Fc ks m A cpf ps bound rs z with
      | none => none
      | some none => if allT then kxSolveC Fc ks lv m g A B kt l cs cpf ps bound rs [] else none
      | some (some N) =>
        match kxWit0 Fc ks m A z N with
        | none => none
        | some W0b =>
          if allT then kxSolveC Fc ks lv m g A B kt l cs cpf ps bound rs [kxCol0 Fc ks m A z W0b]
          else some false

/-- The torsion answer of one class (certificates by search modulo `p`). -/
def kxTors (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (T : List Bool) : Option (Option ℕ) :=
  kxTorsC Fc ks m g A B kt l cs (fun fK ↦ searchCert fK 2) ps bound rs T

/-- The torsion answer for `P₊ − ∞` (certificates by search modulo `p`). -/
def kxTors0 (m : ℕ) (A : GPoly (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (z : LC m) :
    Option (Option ℕ) :=
  kxTors0C Fc ks m A (fun fK ↦ searchCert fK 2) ps bound rs z

/-- The parametric Risch equation per class (certificates by search modulo `p`). -/
def kxSolve (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (extra : List (LC (m + 1))) : Option Bool :=
  kxSolveC Fc ks lv m g A B kt l cs (fun fK ↦ searchCert fK 2) ps bound rs extra

/-- **The decision** (certificates by search modulo `p`). -/
def kxDecide (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kxDecideC Fc ks lv m g A B kt l cs (fun fK ↦ searchCert fK 2) ps bound rs

/-- **The decision with local torsion certificates** (`kxDecideL_decides`). -/
def kxDecideL (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kxDecideC Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs

end Curves.MT
