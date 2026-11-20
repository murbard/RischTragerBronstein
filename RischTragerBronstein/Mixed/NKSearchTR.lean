import RischTragerBronstein.Mixed.NKLogDecideTR

/-!
# A complete search for the exact part of constant curves

`searchTR … B`: tries the first `B` candidates `(T, T⁻¹, r)` (matrices of quotients of polynomials
over `ℚ`, integer shifts; an `Encodable` enumeration) with `exactTR` and returns the first answer.
Every answer is an answer of `exactTR` (`searchTR_sound`), hence correct (`exactTR_correct`), and
**for a constant curve the search answers for every large `B`** (`searchTR_complete`, from
`exactTR_exists`: the shifts only matter below `N`, `exactTR_congr_r`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

lemma rescaleM_congr (m : ℕ) (η : LC m) (N : ℕ) (Mc : List (List (LC (m + 1)))) (r r' : ℕ → ℤ)
    (h : ∀ k < N, r k = r' k) : rescaleM Fc ks m η N Mc r = rescaleM Fc ks m η N Mc r' := by
  unfold rescaleM
  refine List.map_congr_left fun i hi ↦ List.map_congr_left fun j hj ↦ ?_
  rw [List.mem_range] at hi hj
  rw [h i hi, h j hj]

lemma rescaleF_congr (m N : ℕ) (f : List (LC (m + 1))) (r r' : ℕ → ℤ)
    (h : ∀ k < N, r k = r' k) : rescaleF Fc ks m N f r = rescaleF Fc ks m N f r' := by
  unfold rescaleF
  refine List.map_congr_left fun j hj ↦ ?_
  rw [List.mem_range] at hj
  rw [h j hj]

lemma exactWR_congr_r (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r r' : ℕ → ℤ)
    (h : ∀ k < N, r k = r' k) : exactWR Fc ks m η lim N Mc f r = exactWR Fc ks m η lim N Mc f r' := by
  have hR : ((List.range N).map fun i ↦ (-r i).toNat) = (List.range N).map fun i ↦ (-r' i).toNat :=
    List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.mp hi)]
  unfold exactWR
  rw [rescaleM_congr Fc ks m η N Mc r r' h, rescaleF_congr Fc ks m N f r r' h, hR]

lemma exactTR_congr_r (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (r r' : ℕ → ℤ) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (h : ∀ k < P.length - 1, r k = r' k) :
    exactTR Fc ks m η lim r P Tc Ti f = exactTR Fc ks m η lim r' P Tc Ti f := by
  have hc : ∀ Mc fw, exactWR Fc ks m η lim (P.length - 1) Mc fw r =
      exactWR Fc ks m η lim (P.length - 1) Mc fw r' := fun Mc fw ↦
    exactWR_congr_r Fc ks m η lim _ Mc fw r r' h
  unfold exactTR exactTG
  simp only [hc]

/-- A candidate: `T`, `T⁻¹` (quotients of coefficient lists over `ℚ`) and shifts. -/
abbrev CandTR := List (List (List ℚ × List ℚ)) × List (List (List ℚ × List ℚ)) × List ℤ

/-- The code of a quotient of coefficient lists. -/
def codeL (m : ℕ) (ab : List ℚ × List ℚ) : LC (m + 1) :=
  (ab.1.map (mcst Fc ks m), ab.2.map (mcst Fc ks m))

/-- The codes of a matrix of quotients. -/
def matL (m : ℕ) (M : List (List (List ℚ × List ℚ))) : List (List (LC (m + 1))) :=
  M.map fun l ↦ l.map (codeL Fc ks m)

/-- **The search** over the first `B` candidates. -/
def searchTR (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option CandTR) with
    | none => none
    | some c => exactTR Fc ks m η lim (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1)
        (matL Fc ks m c.2.1) f

/-- **Every answer of the search is an answer of `exactTR`.** -/
lemma searchTR_sound (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchTR Fc ks m η lim P f B = some b) :
    ∃ (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))), exactTR Fc ks m η lim r P Tc Ti f = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, hk⟩

/-- The coefficient list of a polynomial. -/
def coeffL (A : ℚ[X]) : List ℚ := (List.range (A.natDegree + 1)).map A.coeff

/-- The candidate matrix of `matQ`. -/
def candMat (A B : ℕ → ℕ → ℚ[X]) (n : ℕ) : List (List (List ℚ × List ℚ)) :=
  (List.range n).map fun i ↦ (List.range n).map fun k ↦ (coeffL (A i k), coeffL (B i k))

lemma matL_candMat (m : ℕ) (A B : ℕ → ℕ → ℚ[X]) (n : ℕ) :
    matL Fc ks m (candMat A B n) = matQ Fc ks m A B n := by
  simp only [matL, candMat, matQ, List.map_map]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun k _ ↦ ?_
  simp only [Function.comp_apply, codeL, fracQ, polyQ, coeffL, List.map_map]
  rfl

/-- **Completeness of the search**: if some `exactTR` on `matQ` codes answers, the search
answers for every large bound. -/
lemma searchTR_complete (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (n : ℕ) (hn : P.length - 1 = n)
    (A B Ai Bi : ℕ → ℕ → ℚ[X]) (r : ℕ → ℤ)
    (h : (exactTR Fc ks m η lim r P (matQ Fc ks m A B n) (matQ Fc ks m Ai Bi n) f).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchTR Fc ks m η lim P f B).isSome := by
  set c : CandTR := (candMat A B n, candMat Ai Bi n, (List.range n).map r) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchTR
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc, matL_candMat]
  rw [exactTR_congr_r Fc ks m η lim _ r P _ _ f (fun k hk ↦ by
    rw [hn] at hk
    simp [List.getD_eq_getElem?_getD, hk])]
  exact h

/-- **The search with precomputed candidates** (untrusted, e.g. Trager's integral basis or the
basis normal at infinity of the shape), tried first. -/
def searchTRP (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1)))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ))) (B : ℕ) :
    Option Bool :=
  match pre.findSome? (fun c ↦ exactTR Fc ks m η lim c.2.2 P c.1 c.2.1 f) with
  | some b => some b
  | none => searchTR Fc ks m η lim P f B

lemma searchTRP_sound (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1)))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ))) (B : ℕ) (b : Bool)
    (h : searchTRP Fc ks m η lim P f pre B = some b) :
    ∃ (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))), exactTR Fc ks m η lim r P Tc Ti f = some b := by
  unfold searchTRP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    exact ⟨_, _, _, hc⟩
  · exact searchTR_sound Fc ks m η lim P f B b h

lemma searchTRP_complete (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1)))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ)))
    (hB : ∃ B0, ∀ B, B0 ≤ B → (searchTR Fc ks m η lim P f B).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchTRP Fc ks m η lim P f pre B).isSome := by
  obtain ⟨B0, hB0⟩ := hB
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold searchTRP
  split
  · rfl
  · exact hB0 B hB

end Curves.MT
