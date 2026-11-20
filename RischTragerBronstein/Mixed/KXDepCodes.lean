import RischTragerBronstein.Mixed.KXCodes

/-!
# The Mordell–Weil exception with dependent classes: the algorithm

When `P₊ − ∞` is not torsion and a class `Δ_T` is not torsion either, `kxDecide` stays undecided.
The class can only be dependent on `δ₀ = P₊ − P₋` when `s_T κ` is a rational square `r²` (else the
conjugation of `Kₘ(√(s_T κ))` separates them): then `P₊` is the point `(0, ±r/z)` of the twisted
curve `ỹ² = s_T A` over `Kₘ`, and `kxDepSearch` looks for a witness of `N Γ_T + M (0, ±r/z)`
(`N, M ≥ 1`). With such witnesses for the non-torsion classes and the torsion witnesses for the
others, the answer is the parametric Risch equation with one column per class (`kxDecideDep`).
-/

open Polynomial CPoly SqrtIndep

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Dep

variable (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))

/-- The ordinate `r / z` of `P₊` on the twist `ỹ² = s_T A`, when `s_T κ = r²`. -/
def kxBt0 (T : List Bool) (z : LC m) : Option (KF Fc m) :=
  let sk := kxS Fc ks m g A B kt l cs T * kxKap Fc ks m A z
  let r := Rat.sqrt sk
  if r * r == sk then some ((r : KF Fc m) / trC Fc m z) else none

/-- The witness of `N Γ_T + M (0, b)` on the twist. -/
def kxWitD (T : List Bool) (b : KF Fc m) (N M : ℕ) : Option (BPoly (KF Fc m)) :=
  witW (kxFKm Fc ks m g A B kt l cs T) 2 ((kxFKm Fc ks m g A B kt l cs T).length - 1)
    (Fin.cons 0 (kxAlm Fc ks m g A B kt l cs T)) (Fin.cons b (kxBem Fc ks m g A B kt l cs T))
    (Fin.cons M fun i ↦ N * kxMqm Fc ks m g A B kt l cs T i) 1

/-- The candidates `(N, M, ±b)`, `1 ≤ N, M ≤ nmax`. -/
def kxDepCands (b : KF Fc m) (nmax : ℕ) : List (ℕ × ℕ × KF Fc m) :=
  (List.range nmax).flatMap fun N ↦ (List.range nmax).flatMap fun M ↦
    [(N + 1, M + 1, b), (N + 1, M + 1, -b)]

/-- One candidate: the point is checked to lie on the twist, then the witness is searched. -/
def kxDepTry (T : List Bool) (c : ℕ × ℕ × KF Fc m) : Option (BPoly (KF Fc m)) :=
  if c.2.2 * c.2.2 == (kxFKm Fc ks m g A B kt l cs T).getD 0 0 && c.2.2 != 0 then
    kxWitD Fc ks m g A B kt l cs T c.2.2 c.1 c.2.1
  else none

/-- **The search for a relation `N Δ_T ± M δ₀ ∼ 0`** (with its witness). -/
def kxDepSearch (T : List Bool) (z : LC m) (nmax : ℕ) : Option (BPoly (KF Fc m)) :=
  match kxBt0 Fc ks m g A B kt l cs T z with
  | none => none
  | some b => (kxDepCands Fc m b nmax).findSome? (kxDepTry Fc ks m g A B kt l cs T)

/-- The witness of one class: the torsion witness, or a relation with `δ₀`. -/
def kxWitAny (z : LC m) (nmax : ℕ) (T : List Bool) (t : Option (Option ℕ)) :
    Option (BPoly (KF Fc m)) :=
  match t with
  | some (some N) => kxWit Fc ks m g A B kt l cs T N
  | some none => kxDepSearch Fc ks m g A B kt l cs T z nmax
  | none => none

/-- The parametric Risch equation with one column per class, each class having a witness (of a
torsion multiple or of a relation with `δ₀`). -/
def kxSolveDepC (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (z : LC m) (nmax : ℕ) : Option Bool :=
  let cls := kxCls Fc ks m g A B kt l cs
  let tors := cls.map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  let wits := (List.zip cls tors).map fun p ↦ kxWitAny Fc ks m g A B kt l cs z nmax p.1 p.2
  match wits.allSome with
  | none => none
  | some Wbs =>
    let cols := (List.zip cls Wbs).map fun p ↦ kxCol Fc ks m g A B kt l cs p.1 p.2
    some ((prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: cols)).any
      fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision in the dependent case** (`P₊ − ∞` not torsion). -/
def kxDecideDepC (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax : ℕ) : Option Bool :=
  let tors := (kxCls Fc ks m g A B kt l cs).map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  if cs.length = 0 then none
  else if !kxOK Fc ks m A B kt l cs then none
  else if !kxConst Fc ks m g A B kt l cs then none
  else if !kxRepOK Fc ks m g A B kt l cs then none
  else if tors.any (· == none) then none
  else
    match kxZ Fc ks lv m A with
    | none => none
    | some z =>
      match kxTors0C Fc ks m A cpf ps bound rs z with
      | some none => kxSolveDepC Fc ks lv m g A B kt l cs cpf ps bound rs z nmax
      | _ => none

/-- **`kxDecide`, then the dependent case.** -/
def kxDecideD (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax : ℕ) : Option Bool :=
  match kxDecide Fc ks lv m g A B kt l cs ps bound rs with
  | some b => some b
  | none => kxDecideDepC Fc ks lv m g A B kt l cs (fun fK ↦ searchCert fK 2) ps bound rs nmax

/-- **`kxDecideL` (local certificates), then the dependent case.** -/
def kxDecideDL (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax : ℕ) : Option Bool :=
  match kxDecideL Fc ks lv m g A B kt l cs ps bound rs with
  | some b => some b
  | none => kxDecideDepC Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs nmax

end Dep

end Curves.MT
