import RischTragerBronstein.Mixed.NKExactTREExists
import RischTragerBronstein.Mixed.NKSearchTR

/-!
# A complete search for the exact part of constant curves over an exponential

`searchTRE … B`: tries the first `B` candidates `(T, T⁻¹, r, N₀, C, C⁻¹)` (an `Encodable`
enumeration) with `exactTRE` and returns the first answer. Every answer is an answer of `exactTRE`
(`searchTRE_sound`), hence correct (`exactTRE_correct`), and **for a constant curve the search
answers for every large `B`** (`searchTRE_complete`, from `exactTRE_exists`: the shifts only
matter below `N`, `exactTRE_congr_r`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

lemma rescaleME_congr (m : ℕ) (bc : LC m) (N : ℕ) (Mc : List (List (LC (m + 1)))) (r r' : ℕ → ℤ)
    (h : ∀ k < N, r k = r' k) : rescaleME Fc ks m bc N Mc r = rescaleME Fc ks m bc N Mc r' := by
  unfold rescaleME
  refine List.map_congr_left fun i hi ↦ List.map_congr_left fun j hj ↦ ?_
  rw [List.mem_range] at hi hj
  rw [h i hi, h j hj]

lemma exactWRE_congr_r (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r r' : ℕ → ℤ) (N0 : ℕ)
    (C Ci : List (List ℚ)) (h : ∀ k < N, r k = r' k) :
    exactWRE Fc ks m a rdeD N Mc f r N0 C Ci = exactWRE Fc ks m a rdeD N Mc f r' N0 C Ci := by
  have hR : ((List.range N).map fun i ↦ (-r i).toNat) = (List.range N).map fun i ↦ (-r' i).toNat :=
    List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.mp hi)]
  have hM : ∀ bc, rescaleME Fc ks m bc N Mc r = rescaleME Fc ks m bc N Mc r' := fun bc ↦
    rescaleME_congr Fc ks m bc N Mc r r' h
  unfold exactWRE
  simp only [hM, rescaleF_congr Fc ks m N f r r' h, hR]

lemma exactTRE_congr_r (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (r r' : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (h : ∀ k < P.length - 1, r k = r' k) :
    exactTRE Fc ks m a rdeD r N0 C Ci P Tc Ti f = exactTRE Fc ks m a rdeD r' N0 C Ci P Tc Ti f := by
  have hc : ∀ Mc fw, exactWRE Fc ks m a rdeD (P.length - 1) Mc fw r N0 C Ci =
      exactWRE Fc ks m a rdeD (P.length - 1) Mc fw r' N0 C Ci := fun Mc fw ↦
    exactWRE_congr_r Fc ks m a rdeD _ Mc fw r r' N0 C Ci h
  unfold exactTRE exactTG
  simp only [hc]

/-- A candidate: `T`, `T⁻¹` (quotients of coefficient lists over `ℚ`), shifts, `N₀`, `C`, `C⁻¹`. -/
abbrev CandTRE := List (List (List ℚ × List ℚ)) × List (List (List ℚ × List ℚ)) × List ℤ × ℕ ×
  List (List ℚ) × List (List ℚ)

/-- **The search** over the first `B` candidates. -/
def searchTRE (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option CandTRE) with
    | none => none
    | some c => exactTRE Fc ks m a rdeD (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.1 c.2.2.2.2.1
        c.2.2.2.2.2 P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f

/-- **Every answer of the search is an answer of `exactTRE`.** -/
lemma searchTRE_sound (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchTRE Fc ks m a rdeD P f B = some b) :
    ∃ (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (Tc Ti : List (List (LC (m + 1)))),
      exactTRE Fc ks m a rdeD r N0 C Ci P Tc Ti f = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, _, _, _, hk⟩

/-- **Completeness of the search**: if some `exactTRE` on `matQ` codes answers, the search
answers for every large bound. -/
lemma searchTRE_complete (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (n : ℕ) (hn : P.length - 1 = n)
    (A B Ai Bi : ℕ → ℕ → ℚ[X]) (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ))
    (h : (exactTRE Fc ks m a rdeD r N0 C Ci P (matQ Fc ks m A B n) (matQ Fc ks m Ai Bi n) f).isSome) :
    ∃ B0, ∀ B', B0 ≤ B' → (searchTRE Fc ks m a rdeD P f B').isSome := by
  set c : CandTRE := (candMat A B n, candMat Ai Bi n, (List.range n).map r, N0, C, Ci) with hc
  refine ⟨Encodable.encode c + 1, fun B' hB ↦ ?_⟩
  unfold searchTRE
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc, matL_candMat]
  rw [exactTRE_congr_r Fc ks m a rdeD _ r N0 C Ci P _ _ f (fun k hk ↦ by
    rw [hn] at hk
    simp [List.getD_eq_getElem?_getD, hk])]
  exact h

/-- A precomputed candidate: codes of `T`, `T⁻¹`, shifts, `N₀`, `C`, `C⁻¹`. -/
abbrev PreTRE (m : ℕ) := List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ) × ℕ ×
  List (List ℚ) × List (List ℚ)

/-- **The search with precomputed candidates** (untrusted, e.g. an integral basis normal at
infinity), tried first. -/
def searchTREP (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (pre : List (PreTRE m)) (B : ℕ) :
    Option Bool :=
  match pre.findSome? (fun c ↦ exactTRE Fc ks m a rdeD c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2 P
      c.1 c.2.1 f) with
  | some b => some b
  | none => searchTRE Fc ks m a rdeD P f B

lemma searchTREP_sound (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (pre : List (PreTRE m)) (B : ℕ) (b : Bool)
    (h : searchTREP Fc ks m a rdeD P f pre B = some b) :
    ∃ (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (Tc Ti : List (List (LC (m + 1)))),
      exactTRE Fc ks m a rdeD r N0 C Ci P Tc Ti f = some b := by
  unfold searchTREP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    exact ⟨_, _, _, _, _, _, hc⟩
  · exact searchTRE_sound Fc ks m a rdeD P f B b h

lemma searchTREP_complete (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (pre : List (PreTRE m))
    (hB : ∃ B0, ∀ B, B0 ≤ B → (searchTRE Fc ks m a rdeD P f B).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchTREP Fc ks m a rdeD P f pre B).isSome := by
  obtain ⟨B0, hB0⟩ := hB
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold searchTREP
  split
  · rfl
  · exact hB0 B hB

end Curves.MT
