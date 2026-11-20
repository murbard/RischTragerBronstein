import RischTragerBronstein.Mixed.NKExactWitTL
import RischTragerBronstein.Mixed.MTWitSound

/-!
# Candidate searches with witnesses, generically

The NK decisions search candidates (precomputed ones first, then an enumeration): a candidate `c`
passing the checks `cond c` is answered by an exact-part test `ex c`. `searchPW cond exW` mirrors
`searchPS cond ex` whenever `exW` mirrors `ex` (`searchPW_isSome`) and returns the accepted
candidate with the witness of `exW` (`searchPW_src`). `nk_integrate_core`: a decision of the
shape "trace part (`elM`) and search both answer, elementary iff both are `true`" becomes a
constructive one (`combineW` of `elMW` and the search) returning valid antiderivative pieces.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

section Search

variable {C W : Type*} [Encodable C]

/-- One candidate. -/
def tryS (cond : C → Bool) (ex : C → Option Bool) (c : C) : Option Bool :=
  if cond c = true then ex c else none

/-- One candidate, with the witness. -/
def tryW (cond : C → Bool) (exW : C → Option (Option W)) (c : C) : Option (Option (C × W)) :=
  if cond c = true then (exW c).map (Option.map fun w ↦ (c, w)) else none

/-- The enumeration of the first `B` candidates. -/
def searchS (cond : C → Bool) (ex : C → Option Bool) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option C) with
    | none => none
    | some c => tryS cond ex c

def searchW (cond : C → Bool) (exW : C → Option (Option W)) (B : ℕ) :
    Option (Option (C × W)) :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option C) with
    | none => none
    | some c => tryW cond exW c

/-- Precomputed candidates first, then the enumeration. -/
def searchPS (cond : C → Bool) (ex : C → Option Bool) (pre : List C) (B : ℕ) : Option Bool :=
  match pre.findSome? (tryS cond ex) with
  | some b => some b
  | none => searchS cond ex B

def searchPW (cond : C → Bool) (exW : C → Option (Option W)) (pre : List C) (B : ℕ) :
    Option (Option (C × W)) :=
  match pre.findSome? (tryW cond exW) with
  | some b => some b
  | none => searchW cond exW B

lemma findSome?_mapG {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → γ) :
    (l.findSome? f).map g = l.findSome? fun a ↦ (f a).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.findSome?_cons]
    cases f a <;> simp [ih]

lemma map_map_isSomeG {α β : Type*} (x : Option (Option α)) (g : α → β) :
    (x.map (Option.map g)).map Option.isSome = x.map Option.isSome := by
  cases x with
  | none => rfl
  | some y => cases y <;> rfl

variable (cond : C → Bool) (ex : C → Option Bool) (exW : C → Option (Option W))

lemma tryW_isSome (h : ∀ c, (exW c).map Option.isSome = ex c) (c : C) :
    (tryW cond exW c).map Option.isSome = tryS cond ex c := by
  unfold tryW tryS
  split_ifs
  · rw [map_map_isSomeG, h]
  · rfl

lemma searchW_isSome (h : ∀ c, (exW c).map Option.isSome = ex c) (B : ℕ) :
    (searchW cond exW B).map Option.isSome = searchS cond ex B := by
  unfold searchW searchS
  rw [findSome?_mapG]
  congr 1
  funext k
  cases (Encodable.decode k : Option C) with
  | none => rfl
  | some c => exact tryW_isSome cond ex exW h c

/-- **The search with witnesses answers as the search.** -/
theorem searchPW_isSome (h : ∀ c, (exW c).map Option.isSome = ex c) (pre : List C) (B : ℕ) :
    (searchPW cond exW pre B).map Option.isSome = searchPS cond ex pre B := by
  have hp : pre.findSome? (tryS cond ex) =
      (pre.findSome? (tryW cond exW)).map Option.isSome := by
    rw [findSome?_mapG]
    congr 1
    funext c
    exact (tryW_isSome cond ex exW h c).symm
  unfold searchPW searchPS
  rw [hp]
  cases pre.findSome? (tryW cond exW) with
  | some b => rfl
  | none => exact searchW_isSome cond ex exW h B

lemma tryW_src (c : C) (w : C × W) (h : tryW cond exW c = some (some w)) :
    cond w.1 = true ∧ exW w.1 = some (some w.2) := by
  unfold tryW at h
  split_ifs at h with hc
  obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
  exact ⟨hc, ho⟩

/-- **Provenance**: a returned candidate passes the checks, and its witness comes from `exW`. -/
theorem searchPW_src (pre : List C) (B : ℕ) (w : C × W)
    (h : searchPW cond exW pre B = some (some w)) :
    cond w.1 = true ∧ exW w.1 = some (some w.2) := by
  unfold searchPW at h
  split at h
  · rename_i b hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [h] at hc
    exact tryW_src cond exW c w hc
  · unfold searchW at h
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
    split at hk
    · exact absurd hk (by simp)
    · exact tryW_src cond exW _ w hk

end Search

/-- Both answers, with both witnesses. -/
def combineW {A B : Type*} (a : Option (Option A)) (b : Option (Option B)) :
    Option (Option (A × B)) :=
  match a, b with
  | some a, some b => some (match a, b with
    | some a, some b => some (a, b)
    | _, _ => none)
  | _, _ => none

open CPoly Sup Curves.LT

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **From a decision to a constructive decision**: if for large `N` the trace part `q` (`elM`)
and a search both answer and the integral is elementary iff both answers are `true`, then the
combination of `elMW` and a witness search mirroring the search answers, its answer is
elementary-ness, and an answer carries a valid antiderivative of `q` and a witness of the
search (satisfying whatever `Expl` its returned witnesses satisfy). -/
theorem nk_integrate_core {W : Type*} (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true)
    (hE0 : Differential.IsElementaryExtension (T.F 0) L) (q : LC (m + 1))
    (search : ℕ → Option Bool) (searchW : ℕ → Option (Option W))
    (hS : ∀ N, (searchW N).map Option.isSome = search N) (I : Prop)
    (hdec : ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res, elM Fc ks lv (m + 1) q N = some b ∧
      search N = some res ∧ (I ↔ res = true ∧ b = true))
    (Expl : W → Prop) (hval : ∀ N w, searchW N = some (some w) → Expl w) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, combineW (elMW Fc ks lv (m + 1) q N) (searchW N) = some o ∧
      (I ↔ o.isSome) ∧
      ∀ a b, o = some (a, b) → T.ValidW (m + 1) q a ∧ Expl b := by
  obtain ⟨N₀, hN₀⟩ := hdec
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, hb, hres, hiff⟩ := hN₀ N hN
  rw [← elMW_isSome] at hb
  rw [← hS] at hres
  obtain ⟨oa, hoa, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.mp hres
  refine ⟨_, by unfold combineW; rw [hoa, hob], ?_, ?_⟩
  · rw [hiff]
    cases oa <;> cases ob <;> simp
  · intro a w hw
    have hw' : oa = some a ∧ ob = some w := by
      cases oa <;> cases ob <;> simp_all
    obtain ⟨rfl, rfl⟩ := hw'
    exact ⟨T.elMW_validE hmon hdeg hshF (m + 1) hn hc hE0 (m + 1) le_rfl _ N a hoa,
      hval N w hob⟩

end MTower

end Curves.MT
