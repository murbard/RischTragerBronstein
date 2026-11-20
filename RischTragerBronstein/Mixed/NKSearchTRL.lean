import RischTragerBronstein.Mixed.NKExactTRLExists
import RischTragerBronstein.Mixed.NKSearchTRE

/-!
# Complete searches for the parametric exact tests

`searchTRL` (logarithmic level, `exactTRL`) and `searchTREL` (exponential level, `exactTREL`):
the first answer among the first `B` candidates of an `Encodable` enumeration. Every answer is an
answer of the test (`searchTRL_sound`, `searchTREL_sound`), and for constant curves the searches
answer for every large bound (`searchTRL_complete`, `searchTREL_complete`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

lemma exactWRL_congr_r (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r r' : ℕ → ℤ) (h : ∀ k < N, r k = r' k) :
    exactWRL Fc ks m η lim N Mc f gs r = exactWRL Fc ks m η lim N Mc f gs r' := by
  have hR : ((List.range N).map fun i ↦ (-r i).toNat) = (List.range N).map fun i ↦ (-r' i).toNat :=
    List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.mp hi)]
  have hF : ∀ g, rescaleF Fc ks m N g r = rescaleF Fc ks m N g r' := fun g ↦
    rescaleF_congr Fc ks m N g r r' h
  unfold exactWRL
  simp only [rescaleM_congr Fc ks m η N Mc r r' h, hF, hR]

lemma exactWREL_congr_r (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r r' : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (h : ∀ k < N, r k = r' k) :
    exactWREL Fc ks m a rdeD N Mc f gs r N0 C Ci = exactWREL Fc ks m a rdeD N Mc f gs r' N0 C Ci := by
  have hR : ((List.range N).map fun i ↦ (-r i).toNat) = (List.range N).map fun i ↦ (-r' i).toNat :=
    List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.mp hi)]
  have hM : ∀ bc, rescaleME Fc ks m bc N Mc r = rescaleME Fc ks m bc N Mc r' := fun bc ↦
    rescaleME_congr Fc ks m bc N Mc r r' h
  have hF : ∀ g, rescaleF Fc ks m N g r = rescaleF Fc ks m N g r' := fun g ↦
    rescaleF_congr Fc ks m N g r r' h
  unfold exactWREL
  simp only [hM, hF, hR]

lemma exactTRL_congr_r (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (r r' : ℕ → ℤ) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (h : ∀ k < P.length - 1, r k = r' k) :
    exactTRL Fc ks m η lim r P Tc Ti f gs = exactTRL Fc ks m η lim r' P Tc Ti f gs := by
  have hc : ∀ Mc fw gws, exactWRL Fc ks m η lim (P.length - 1) Mc fw gws r =
      exactWRL Fc ks m η lim (P.length - 1) Mc fw gws r' := fun Mc fw gws ↦
    exactWRL_congr_r Fc ks m η lim _ Mc fw gws r r' h
  unfold exactTRL exactTGL
  simp only [hc]

lemma exactTREL_congr_r (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (r r' : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (h : ∀ k < P.length - 1, r k = r' k) :
    exactTREL Fc ks m a rdeD r N0 C Ci P Tc Ti f gs =
      exactTREL Fc ks m a rdeD r' N0 C Ci P Tc Ti f gs := by
  have hc : ∀ Mc fw gws, exactWREL Fc ks m a rdeD (P.length - 1) Mc fw gws r N0 C Ci =
      exactWREL Fc ks m a rdeD (P.length - 1) Mc fw gws r' N0 C Ci := fun Mc fw gws ↦
    exactWREL_congr_r Fc ks m a rdeD _ Mc fw gws r r' N0 C Ci h
  unfold exactTREL exactTGL
  simp only [hc]

/-- **The parametric search** (logarithmic level). -/
def searchTRL (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (B : ℕ) :
    Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option CandTR) with
    | none => none
    | some c => exactTRL Fc ks m η lim (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1)
        (matL Fc ks m c.2.1) f gs

lemma searchTRL_sound (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (B : ℕ)
    (b : Bool) (h : searchTRL Fc ks m η lim P f gs B = some b) :
    ∃ (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))),
      exactTRL Fc ks m η lim r P Tc Ti f gs = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, hk⟩

lemma searchTRL_complete (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (n : ℕ)
    (hn : P.length - 1 = n) (A B Ai Bi : ℕ → ℕ → ℚ[X]) (r : ℕ → ℤ)
    (h : (exactTRL Fc ks m η lim r P (matQ Fc ks m A B n) (matQ Fc ks m Ai Bi n) f gs).isSome) :
    ∃ B0, ∀ B', B0 ≤ B' → (searchTRL Fc ks m η lim P f gs B').isSome := by
  set c : CandTR := (candMat A B n, candMat Ai Bi n, (List.range n).map r) with hc
  refine ⟨Encodable.encode c + 1, fun B' hB ↦ ?_⟩
  unfold searchTRL
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc, matL_candMat]
  rw [exactTRL_congr_r Fc ks m η lim _ r P _ _ f gs (fun k hk ↦ by
    rw [hn] at hk
    simp [List.getD_eq_getElem?_getD, hk])]
  exact h

/-- **The parametric search** (exponential level). -/
def searchTREL (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (B : ℕ) :
    Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option CandTRE) with
    | none => none
    | some c => exactTREL Fc ks m a rdeD (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.1 c.2.2.2.2.1
        c.2.2.2.2.2 P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f gs

lemma searchTREL_sound (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (B : ℕ)
    (b : Bool) (h : searchTREL Fc ks m a rdeD P f gs B = some b) :
    ∃ (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (Tc Ti : List (List (LC (m + 1)))),
      exactTREL Fc ks m a rdeD r N0 C Ci P Tc Ti f gs = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, _, _, _, hk⟩

lemma searchTREL_complete (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (n : ℕ)
    (hn : P.length - 1 = n) (A B Ai Bi : ℕ → ℕ → ℚ[X]) (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ))
    (h : (exactTREL Fc ks m a rdeD r N0 C Ci P (matQ Fc ks m A B n) (matQ Fc ks m Ai Bi n) f
      gs).isSome) :
    ∃ B0, ∀ B', B0 ≤ B' → (searchTREL Fc ks m a rdeD P f gs B').isSome := by
  set c : CandTRE := (candMat A B n, candMat Ai Bi n, (List.range n).map r, N0, C, Ci) with hc
  refine ⟨Encodable.encode c + 1, fun B' hB ↦ ?_⟩
  unfold searchTREL
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc, matL_candMat]
  rw [exactTREL_congr_r Fc ks m a rdeD _ r N0 C Ci P _ _ f gs (fun k hk ↦ by
    rw [hn] at hk
    simp [List.getD_eq_getElem?_getD, hk])]
  exact h

end Curves.MT
