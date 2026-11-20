import RischTragerBronstein.Mixed.NKSearchW
import RischTragerBronstein.Mixed.NKExactWitE
import RischTragerBronstein.Mixed.NKWronskDecide

/-!
# Exponential levels, non-constant curves: the antiderivative

The decisions `nk_decidesETInfVGPW` (split at infinity), `nk_decidesETInfVRPW` (ramified at
infinity), `nk_decidesETInf0PW` and `nk_decidesETInf0RPW` (also several places above `t = 0`,
S-units `uᵢ t^{−jᵢ}`) made constructive through the generic witness search (`searchPW`) and
`nk_integrate_core`: for every large bound the answer is elementary-ness, and an elementary
answer carries an antiderivative of the trace part (`ValidW`) and units `uᵢ ≠ 0` with an exact
part `(c, Y)`: `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ` (`nk_explicit_core`).
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The checks on a candidate (split at infinity, exponential level). -/
def etvgCond (m : ℕ) (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (c : CandETVG m) : Bool :=
  decide (c.2.2.1.length + 1 = Pp.length) &&
      unitsC Fc ks m Pp c.1 c.2.1 c.2.2.1 dθ wθ s && indepC Fc ks m c.2.2.1 c.2.2.2.1 c.2.2.2.2.1

/-- The exact-part test of a candidate. -/
def etvgEx (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVG m) : Option Bool :=
  exactTLEVG Fc ks m a rde [] c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.1
    (fun i ↦ c.2.2.2.2.2.2.2.1.getD i 0) c.2.2.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.2.2.1
    c.2.2.2.2.2.2.2.2.2.2.2.2 (nkPC Fc ks m Pp) c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 f c.2.2.1

/-- The exact-part test of a candidate, with the witness. -/
def etvgExW (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVG m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLEVGW Fc ks m a rde [] c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.1
    (fun i ↦ c.2.2.2.2.2.2.2.1.getD i 0) c.2.2.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.2.2.1
    c.2.2.2.2.2.2.2.2.2.2.2.2 (nkPC Fc ks m Pp) c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 f c.2.2.1

lemma searchETVGP_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVG m)) (B : ℕ) :
    searchETVGP Fc ks m a rde Pp dθ wθ s f pre B =
      searchPS (etvgCond Fc ks m Pp dθ wθ s) (etvgEx Fc ks m a rde Pp f) pre B := by
  have ht : etvgTry Fc ks m a rde Pp dθ wθ s f = tryS (etvgCond Fc ks m Pp dθ wθ s) (etvgEx Fc ks m a rde Pp f) := funext fun _ ↦ rfl
  have hs : searchETVG Fc ks m a rde Pp dθ wθ s f B = searchS (etvgCond Fc ks m Pp dθ wθ s) (etvgEx Fc ks m a rde Pp f) B := by
    unfold searchETVG searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandETVG m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchETVGP searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (etvgCond Fc ks m Pp dθ wθ s) (etvgEx Fc ks m a rde Pp f)) pre = o
  cases o <;> rfl

/-- **The constructive decision** (split at infinity, exponential level). -/
def nkETVGW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandETVG m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (etvgCond Fc ks m Pp dθ wθ s) (etvgExW Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

/-- The checks on a candidate (ramified at infinity, exponential level). -/
def etvrCond (m : ℕ) (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (c : CandETVR m) : Bool :=
  decide (c.1.2.2.1.length + 1 = Pp.length / e) &&
      unitsC Fc ks m Pp c.1.1 c.1.2.1 c.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.2.2.1 c.1.2.2.2.1 c.1.2.2.2.2.1

def etvrEx (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVR m) : Option Bool :=
  exactTLEVG Fc ks m a rde c.2 c.1.2.2.2.2.2.2.2.2.1 c.1.2.2.2.2.2.2.2.2.2.1
    (fun i ↦ c.1.2.2.2.2.2.2.2.1.getD i 0) c.1.2.2.2.2.2.2.2.2.2.2.1 c.1.2.2.2.2.2.2.2.2.2.2.2.1
    c.1.2.2.2.2.2.2.2.2.2.2.2.2 (nkPC Fc ks m Pp) c.1.2.2.2.2.2.1 c.1.2.2.2.2.2.2.1 f c.1.2.2.1

def etvrExW (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVR m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLEVGW Fc ks m a rde c.2 c.1.2.2.2.2.2.2.2.2.1 c.1.2.2.2.2.2.2.2.2.2.1
    (fun i ↦ c.1.2.2.2.2.2.2.2.1.getD i 0) c.1.2.2.2.2.2.2.2.2.2.2.1 c.1.2.2.2.2.2.2.2.2.2.2.2.1
    c.1.2.2.2.2.2.2.2.2.2.2.2.2 (nkPC Fc ks m Pp) c.1.2.2.2.2.2.1 c.1.2.2.2.2.2.2.1 f c.1.2.2.1

lemma searchETVRP_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVR m)) (B : ℕ) :
    searchETVRP Fc ks m a rde Pp e dθ wθ s f pre B =
      searchPS (etvrCond Fc ks m Pp e dθ wθ s) (etvrEx Fc ks m a rde Pp f) pre B := by
  have ht : etvrTry Fc ks m a rde Pp e dθ wθ s f = tryS (etvrCond Fc ks m Pp e dθ wθ s) (etvrEx Fc ks m a rde Pp f) := funext fun _ ↦ rfl
  have hs : searchETVR Fc ks m a rde Pp e dθ wθ s f B = searchS (etvrCond Fc ks m Pp e dθ wθ s) (etvrEx Fc ks m a rde Pp f) B := by
    unfold searchETVR searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandETVR m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchETVRP searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (etvrCond Fc ks m Pp e dθ wθ s) (etvrEx Fc ks m a rde Pp f)) pre = o
  cases o <;> rfl

def nkETVRW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (etvrCond Fc ks m Pp e dθ wθ s) (etvrExW Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

/-- The checks on a candidate (several places above `t = 0`). -/
def et0Cond (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (cc : CandET0 m) : Bool :=
  let c := cc.2.2.2
  decide (c.2.2.1.length + 2 = 2 * Pp.length) &&
      unitsC0 Fc ks m Pp c.1 c.2.1 cc.1 cc.2.1 ((MO Fc ks m).deriv a) c.2.2.1 dθ wθ s &&
      indepWC Fc ks m c.2.2.1 c.2.2.2.1 cc.2.2.1 c.2.2.2.2.1

def et0ExW (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (cc : CandET0 m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  etvgExW Fc ks m a rde Pp f cc.2.2.2

lemma searchET0P_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0 m)) (B : ℕ) :
    searchET0P Fc ks m a rde Pp dθ wθ s f pre B =
      searchPS (et0Cond Fc ks m a Pp dθ wθ s) (fun cc ↦ etvgEx Fc ks m a rde Pp f cc.2.2.2) pre B := by
  have ht : et0Try Fc ks m a rde Pp dθ wθ s f = tryS (et0Cond Fc ks m a Pp dθ wθ s) (fun cc ↦ etvgEx Fc ks m a rde Pp f cc.2.2.2) := funext fun _ ↦ rfl
  have hs : searchET0 Fc ks m a rde Pp dθ wθ s f B = searchS (et0Cond Fc ks m a Pp dθ wθ s) (fun cc ↦ etvgEx Fc ks m a rde Pp f cc.2.2.2) B := by
    unfold searchET0 searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandET0 m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchET0P searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (et0Cond Fc ks m a Pp dθ wθ s) (fun cc ↦ etvgEx Fc ks m a rde Pp f cc.2.2.2)) pre = o
  cases o <;> rfl

def nkET0W (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandET0 m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (et0Cond Fc ks m a Pp dθ wθ s) (et0ExW Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

/-- The checks on a candidate (ramified at infinity, several places above `t = 0`). -/
def et0RCond (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (cc : CandET0R m) : Bool :=
  let c := cc.2.2.2.1
  decide (c.2.2.1.length + 2 = Pp.length / e + Pp.length) &&
      unitsC0 Fc ks m Pp c.1 c.2.1 cc.1 cc.2.1 ((MO Fc ks m).deriv a) c.2.2.1 dθ wθ s &&
      indepWC Fc ks m c.2.2.1 c.2.2.2.1 cc.2.2.1 c.2.2.2.2.1

def et0RExW (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (cc : CandET0R m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  etvrExW Fc ks m a rde Pp f cc.2.2.2

lemma searchET0RP_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ) :
    searchET0RP Fc ks m a rde Pp e dθ wθ s f pre B =
      searchPS (et0RCond Fc ks m a Pp e dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2) pre B := by
  have ht : et0RTry Fc ks m a rde Pp e dθ wθ s f = tryS (et0RCond Fc ks m a Pp e dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2) := funext fun _ ↦ rfl
  have hs : searchET0R Fc ks m a rde Pp e dθ wθ s f B = searchS (et0RCond Fc ks m a Pp e dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2) B := by
    unfold searchET0R searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandET0R m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchET0RP searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (et0RCond Fc ks m a Pp e dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2)) pre = o
  cases o <;> rfl

def nkET0RW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (et0RCond Fc ks m a Pp e dθ wθ s) (et0RExW Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

lemma etvgExW_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVG m) :
    (etvgExW Fc ks m a rde Pp f c).map Option.isSome = etvgEx Fc ks m a rde Pp f c :=
  exactTLEVGW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma etvrExW_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVR m) :
    (etvrExW Fc ks m a rde Pp f c).map Option.isSome = etvrEx Fc ks m a rde Pp f c :=
  exactTLEVGW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma et0ExW_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandET0 m) :
    (et0ExW Fc ks m a rde Pp f c).map Option.isSome = etvgEx Fc ks m a rde Pp f c.2.2.2 :=
  etvgExW_isSome _ _ _ _ _ _ _ _

lemma et0RExW_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandET0R m) :
    (et0RExW Fc ks m a rde Pp f c).map Option.isSome = etvrEx Fc ks m a rde Pp f c.2.2.2 :=
  etvrExW_isSome _ _ _ _ _ _ _ _

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The explicit antiderivative statement**: `uᵢ ≠ 0` and
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ`. -/
def NKExpl (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp fp : List (GPoly (LC m)))
    (s : List (LC (m + 1))) (u : ℕ → L) (ng : ℕ) (wt : List ℚ × List (LC (m + 1))) : Prop :=
  (∀ i < ng, u i ≠ 0) ∧
  ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
    T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
    (∑ k ∈ Finset.range Pp.length, T.ev (m + 1) (wt.2.getD k (MOr Fc ks (m + 1)).zero) * θ ^ k)′ +
    ∑ i ∈ Finset.range ng, ((wt.1.getD i 0 : ℚ) : L) * logDeriv (u i)

/-- **The explicit antiderivative from an exact part and units.** -/
theorem nk_explicit_core (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (hn0 : 0 < Pp.length) (θ : L) (gls : List (GPoly (LC (m + 1)))) (u : ℕ → L)
    (hui : ∀ i < gls.length, u i ≠ 0 ∧ T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (hgl : ∀ i < gls.length, (gls.getD i []).length ≤ Pp.length)
    (fp : List (GPoly (LC m))) (s : List (LC (m + 1))) (wt : List ℚ × List (LC (m + 1)))
    (hY : T.ExW m h1 ((nkPC Fc ks m Pp).length - 1) (fun k ↦ θ ^ k)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gls wt) :
    T.NKExpl m h1 θ Pp fp s u gls.length wt := by
  classical
  unfold ExW at hY
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  refine ⟨fun i hi ↦ (hui i hi).1, ?_⟩
  have hg : ∑ j ∈ Finset.range Pp.length, (∑ i ∈ Finset.range gls.length,
      ((wt.1.getD i 0 : ℚ) : L) * ((M1.sem ((gls.getD i []).getD j O1.zero) : T.F (m + 1)) : L)) *
        θ ^ j =
      ∑ i ∈ Finset.range gls.length, ((wt.1.getD i 0 : ℚ) : L) * logDeriv (u i) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [logDeriv, ← (hui i hi').2, T.evθ_list_le m h1 θ _ Pp.length (hgl i hi'), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [length_nkPC] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRest m h1 Pp.length hn0] at hY
  have hev : ∀ k, ((M1.sem (wt.2.getD k O1.zero) : T.F (m + 1)) : L) =
      T.ev (m + 1) (wt.2.getD k O1.zero) := fun k ↦ T.sem_MP (m + 1) h1 _
  simp only [hev] at hY
  rw [hY]
  ring

/-- `L = Fₘ₊₁(θ)` is elementary over `F₀`. -/
lemma elem0_of_curve (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (Pp : List (GPoly (LC m))) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ}) :
    IsElementaryExtension (T.F 0) L := by
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ
  exact T.isElementary_alg (lv := lv) hmon hdeg (m + 1) hn hc θ hθi hgen 0 (Nat.zero_le _)

/-- The units of `unitsC` and their logarithmic derivatives. -/
lemma units_logs (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true) :
    ∀ i < gls.length, T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ≠ 0 ∧
      T.evθ m h1 θ (gls.getD i []) = (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])))′ /
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) := by
  intro i hi
  obtain ⟨huv, hgl, -, -⟩ := unitsC_spec hU i hi
  have huvL := T.unitC_sound m h1 θ Pp _ _ hP huv
  exact ⟨left_ne_zero_of_mul_eq_one huvL, T.logDerChk_sound m h1 θ Pp _ _ _ dθ wθ hP huvL hgl⟩

/-- The S-units `uᵢ t^{−jᵢ}` of `unitsC0` and their logarithmic derivatives. -/
lemma units0_logs (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true) :
    ∀ i < gls.length, T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) *
        T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ)) ≠ 0 ∧
      T.evθ m h1 θ (gls.getD i []) = (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) *
        T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ)))′ / (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) *
        T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ))) := by
  have hts : T.ts m ≠ 0 := fun h ↦ htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  intro i hi
  obtain ⟨huv, hgl, -, -, -⟩ := unitsC0_spec hU i hi
  have huvL := T.unitDC_sound m h1 θ Pp _ _ _ hP huv
  have hU0 : T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ≠ 0 := fun h0 ↦
    pow_ne_zero _ hts (by rw [← huvL, h0, zero_mul])
  have hηE : T.ev m ((MO Fc ks m).deriv a) = logDeriv (T.ts m) := by
    rw [logDeriv, T.deriv_ts_L_exp m h1.of_succ hm hk, T.sem_MP m h1.of_succ, mul_div_assoc,
      div_self hts, mul_one]
  refine ⟨mul_ne_zero hU0 (zpow_ne_zero _ hts), ?_⟩
  rw [T.logDerDC_sound m h1 θ Pp _ _ _ _ _ _ dθ wθ hP hts huvL hgl]
  rw [← logDeriv, ← logDeriv, Differential.logDeriv_mul _ _ hU0 (zpow_ne_zero _ hts),
    logDeriv_zpow' _ hts, hηE]
  push_cast
  ring

/-- **The integral over an exponential level, split at infinity, decided and computed.** -/
theorem nk_integrateETInfVGPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkETVGW Fc ks lv m a Pp dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.getD i []))) b.1.2.2.1.length b.2 := by
  have hn0 : 0 < Pp.length := by
    obtain ⟨_, _, gls, hk1, -⟩ := hunits
    omega
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (etvgExW_isSome Fc ks m a _ Pp _) pre N).trans
        (searchETVGP_eq Fc ks m a _ Pp dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInfVGPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit
      hsh0 θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [etvgCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units_logs m h1 θ Pp hP _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

/-- **The integral over an exponential level, ramified at infinity, decided and computed.** -/
theorem nk_integrateETInfVRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length / e ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkETVRW Fc ks lv m a Pp e dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hn0 : 0 < Pp.length := by
    obtain ⟨_, _, gls, hk1, -⟩ := hunits
    rcases Nat.eq_zero_or_pos Pp.length with h0 | h0
    · rw [h0, Nat.zero_div] at hk1; omega
    · exact h0
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (etvrExW_isSome Fc ks m a _ Pp _) pre N).trans
        (searchETVRP_eq Fc ks m a _ Pp e dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInfVRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram
      hsh0 θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [etvrCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units_logs m h1 θ Pp hP _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

/-- **The integral over an exponential level, split at infinity and above `t = 0`, decided and
computed** (S-units `uᵢ t^{−jᵢ}`). -/
theorem nk_integrateETInf0PW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0 m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkET0W Fc ks lv m a Pp dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.2.2.2.1.getD i [])) *
            T.ts m ^ (-((b.1.2.1.getD i 0 : ℕ) : ℤ))) b.1.2.2.2.2.2.1.length b.2 := by
  have hn0 : 0 < Pp.length := by
    obtain ⟨_, _, _, _, gls, hk1, -⟩ := hunits
    omega
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (et0ExW_isSome Fc ks m a _ Pp _) pre N).trans
        (searchET0P_eq Fc ks m a _ Pp dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInf0PW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit βs
      hsp0 θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [et0Cond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units0_logs m h1 (by omega) hk (h1 m (by omega)) θ Pp hP _ _ _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC0_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

/-- **The integral over an exponential level, ramified at infinity and split above `t = 0`,
decided and computed.** -/
theorem nk_integrateETInf0RPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 2 = Pp.length / e + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkET0RW Fc ks lv m a Pp e dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.2.2.2.1.1.getD i [])) *
            T.ts m ^ (-((b.1.2.1.getD i 0 : ℕ) : ℤ))) b.1.2.2.2.1.2.2.1.length b.2 := by
  have hn0 : 0 < Pp.length := by
    obtain ⟨_, _, _, _, gls, hk1, -⟩ := hunits
    rcases Nat.eq_zero_or_pos Pp.length with h0 | h0
    · rw [h0, Nat.zero_div] at hk1; omega
    · exact h0
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (et0RExW_isSome Fc ks m a _ Pp _) pre N).trans
        (searchET0RP_eq Fc ks m a _ Pp e dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInf0RPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram βs
      hsp0 θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [et0RCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units0_logs m h1 (by omega) hk (h1 m (by omega)) θ Pp hP _ _ _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC0_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

end MTower

end Curves.MT
