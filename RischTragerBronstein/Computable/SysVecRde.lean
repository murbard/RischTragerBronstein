import RischTragerBronstein.Computable.SysVecLim
import RischTragerBronstein.Computable.NestMRdeLoop

/-!
# Coupled Risch systems: diagonal Risch equations for vectors

Given a scalar parametric Risch solver for `y′ + f y = ∑ cₗ wₗ` (`RdeSpecK`, exact), the vector
problem `zᵢ′ + f zᵢ = ∑ₗ cₗ wₗᵢ` is solved by the componentwise refinement of `SysVecLim`
(`vlRun` with the Risch solver in place of `lim`): `vecRde_spec` is the specification of a solver
one level down with `F = f I`, used by the coefficient loop at an exponential level.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

open Tower.NestM Tower.NestP

section Codes

variable {α : Type} (O : COps α) (cst : ℚ → α) {n : ℕ}

/-- **Diagonal Risch equations for vectors.** -/
def vecRde (rde : List α → List (List ℚ × α)) (ws : List (Fin n → α)) :
    List (List ℚ × (Fin n → α)) :=
  (vlRun O cst ws.length rde ws n).map fun ez ↦
    ((ez.1, fun c : Fin n ↦ ez.2.getD c O.zero) : List ℚ × (Fin n → α))

end Codes

section Sem

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = q)
  (f : K) {n : ℕ} (lim : List α → List (List ℚ × α)) (ws : List (Fin n → α))

/-- Soundness of a stage. -/
def VRSound (L i : ℕ) (E : List (List ℚ × List α)) : Prop :=
  ∀ ez ∈ E, ez.1.length = L ∧ ∀ c : Fin n, (c : ℕ) < i →
    (M.sem (ez.2.getD c O.zero))′ + f * M.sem (ez.2.getD c O.zero) =
      ∑ l ∈ Finset.range L, ((ez.1.getD l 0 : ℚ) : K) * wv M ws l c

/-- Completeness of a stage. -/
def VRComplete (L i : ℕ) (E : List (List ℚ × List α)) : Prop :=
  ∀ cv : List Cs, (∀ l, L ≤ l → cv.getD l 0 = 0) → ∀ z : Fin n → K,
    (∀ c : Fin n, (c : ℕ) < i →
      (z c)′ + f * z c = ∑ l ∈ Finset.range L, ι (cv.getD l 0) * wv M ws l c) →
    ∃ β : List Cs,
      (∀ l, cv.getD l 0 = ∑ k ∈ Finset.range E.length,
        β.getD k 0 * algebraMap ℚ Cs ((E.getD k ([], [])).1.getD l 0)) ∧
      ∀ c : Fin n, (c : ℕ) < i → z c = ∑ k ∈ Finset.range E.length,
        ι (β.getD k 0) * M.sem ((E.getD k ([], [])).2.getD c O.zero)

lemma rde_sum_rat (N : ℕ) (a : ℕ → ℚ) (x : ℕ → K) :
    (∑ k ∈ Finset.range N, ((a k : ℚ) : K) * x k)′ + f * ∑ k ∈ Finset.range N, ((a k : ℚ) : K) * x k =
      ∑ k ∈ Finset.range N, ((a k : ℚ) : K) * ((x k)′ + f * x k) := by
  rw [deriv_sum_rat, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

lemma vrInit_sound : VRSound M f ws ws.length 0 (vlInit (α := α) ws.length) := by
  intro ez hez
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hez
  exact ⟨by simp [unitV], fun c hc ↦ absurd hc (Nat.not_lt_zero _)⟩

lemma vrInit_complete : VRComplete ι M f ws ws.length 0 (vlInit (α := α) ws.length) := by
  intro cv hcv z _
  obtain ⟨β, hβ, -⟩ := vlInit_complete ι M ws cv hcv z (fun c hc ↦ absurd hc (Nat.not_lt_zero _))
  exact ⟨β, hβ, fun c hc ↦ absurd hc (Nat.not_lt_zero _)⟩

include hcst in
/-- **A refinement step is sound.** -/
lemma vrStep_sound (hlim : RdeSpecK ι M f lim) (i : Fin n) (E : List (List ℚ × List α))
    (hE : VRSound M f ws ws.length i E) :
    VRSound M f ws ws.length (i + 1) (vlStep O cst ws.length lim ws i E) := by
  intro ez hez
  simp only [vlStep] at hez
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hez
  set fs := E.map fun ez ↦ lcombCode O cst ez.1 (ws.map fun w ↦ w i) with hfs
  have hsem : ∀ k ∈ Finset.range E.length, M.sem (fs.getD k O.zero) =
      ∑ l ∈ Finset.range ws.length, (((E.getD k ([], [])).1.getD l 0 : ℚ) : K) * wv M ws l i :=
    fun k hk ↦ by
      rw [hfs, NestTower.getD_map' _ _ ([], []) _ (Finset.mem_range.mp hk), sem_lcomb_ws M cst hcst]
  refine ⟨length_vcomb _ _ _, fun c hc ↦ ?_⟩
  rcases Nat.lt_or_ge (c : ℕ) i with hci | hci
  · simp only
    rw [zl_lt cst i r E c hci, sem_lcomb_E M cst hcst, rde_sum_rat, ← vcomb_rows]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [(hE _ (by rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _)).2 c hci]
  · have hceq : c = i := Fin.ext (by omega)
    subst hceq
    simp only
    rw [zl_eq, hlim.sound fs r hr, sQ, hfs, List.length_map, ← vcomb_rows]
    exact Finset.sum_congr rfl fun k hk ↦ by rw [← hfs, hsem k hk]

include hcst in
/-- **A refinement step is complete.** -/
lemma vrStep_complete (hlim : RdeSpecK ι M f lim)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (i : Fin n) (E : List (List ℚ × List α))
    (hE : VRComplete ι M f ws ws.length i E) :
    VRComplete ι M f ws ws.length (i + 1) (vlStep O cst ws.length lim ws i E) := by
  intro cv hcv z hz
  obtain ⟨β, hβc, hβz⟩ := hE cv hcv z (fun c hc ↦ hz c (by omega))
  set fs := E.map fun ez ↦ lcombCode O cst ez.1 (ws.map fun w ↦ w i) with hfs
  set R := lim fs with hR
  set βt := (List.range E.length).map fun k ↦ β.getD k 0 with hβt
  have hβtD : ∀ k < E.length, βt.getD k 0 = β.getD k 0 := fun k hk ↦
    NestTower.getD_range_map _ _ hk
  have hsem : ∀ k ∈ Finset.range E.length, M.sem (fs.getD k O.zero) =
      ∑ l ∈ Finset.range ws.length, (((E.getD k ([], [])).1.getD l 0 : ℚ) : K) * wv M ws l i :=
    fun k hk ↦ by
      rw [hfs, NestTower.getD_map' _ _ ([], []) _ (Finset.mem_range.mp hk), sem_lcomb_ws M cst hcst]
  have hzi : (z i)′ + f * z i = sC ι M βt fs := by
    rw [hz i (by simp), sC, hfs, List.length_map]
    have e1 : ∀ l ∈ Finset.range ws.length, ι (cv.getD l 0) * wv M ws l i =
        ∑ k ∈ Finset.range E.length, ι (β.getD k 0) *
          ((((E.getD k ([], [])).1.getD l 0 : ℚ) : K) * wv M ws l i) := fun l _ ↦ by
      rw [hβc l, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul, hιrat]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← hfs, hsem k hk, hβtD k (Finset.mem_range.mp hk), Finset.mul_sum]
  obtain ⟨γ, hγβ, hγz⟩ := hlim.complete fs βt (fun k hk ↦ List.getD_eq_default _ _ (by
    simp only [hβt, List.length_map, List.length_range]; simpa [hfs] using hk)) (z i) hzi
  have hβγ : ∀ k < E.length, β.getD k 0 = ∑ j ∈ Finset.range R.length,
      γ.getD j 0 * algebraMap ℚ Cs ((R.getD j ([], O.zero)).1.getD k 0) := fun k hk ↦ by
    rw [← hβtD k hk, hγβ k]
  have hlen : (vlStep O cst ws.length lim ws i E).length = R.length := by simp [vlStep, hR, hfs]
  refine ⟨γ, fun l ↦ ?_, fun c hc ↦ ?_⟩
  · rw [hlen]
    have e : ∀ j ∈ Finset.range R.length, γ.getD j 0 * algebraMap ℚ Cs
        (((vlStep O cst ws.length lim ws i E).getD j ([], [])).1.getD l 0) =
        γ.getD j 0 * algebraMap ℚ Cs ((vcomb ws.length (R.getD j ([], O.zero)).1
          (E.map Prod.fst)).getD l 0) := fun j hj ↦ by
      rw [getD_vlStep cst lim ws i E j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl e]
    by_cases hl : l < ws.length
    · rw [recombine ws.length E.length R.length (fun k l ↦ (E.getD k ([], [])).1.getD l 0)
        (fun j k ↦ (R.getD j ([], O.zero)).1.getD k 0) (fun l ↦ cv.getD l 0) (fun k ↦ β.getD k 0)
        (fun j ↦ γ.getD j 0) (fun l _ ↦ hβc l) hβγ l hl]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [getD_vcomb, if_pos hl, List.length_map]
      congr 2
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hk)]
    · rw [hcv l (by omega)]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [getD_vcomb, if_neg hl, map_zero, mul_zero]
  · rw [hlen]
    have hcomp : ∀ c' : ℕ, ∀ j ∈ Finset.range R.length, ι (γ.getD j 0) *
        M.sem (((vlStep O cst ws.length lim ws i E).getD j ([], [])).2.getD c' O.zero) =
        ι (γ.getD j 0) * M.sem ((((List.range (i : ℕ)).map fun c ↦ lcombCode O cst
          (R.getD j ([], O.zero)).1 (E.map fun ez ↦ ez.2.getD c O.zero)) ++
            [(R.getD j ([], O.zero)).2]).getD c' O.zero) := fun c' j hj ↦ by
      rw [getD_vlStep cst lim ws i E j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl (hcomp c)]
    rcases Nat.lt_or_ge (c : ℕ) i with hci | hci
    · have e2 : ∑ j ∈ Finset.range R.length, ι (γ.getD j 0) * M.sem ((((List.range (i : ℕ)).map
          fun c ↦ lcombCode O cst (R.getD j ([], O.zero)).1 (E.map fun ez ↦ ez.2.getD c O.zero)) ++
            [(R.getD j ([], O.zero)).2]).getD c O.zero) =
          ∑ k ∈ Finset.range E.length, ι (β.getD k 0) *
            M.sem ((E.getD k ([], [])).2.getD c O.zero) := by
        simp only [zl_lt cst i _ E c hci, sem_lcomb_E M cst hcst, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [hβγ k (Finset.mem_range.mp hk), map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_mul, hιrat]; ring
      rw [e2]
      exact hβz c hci
    · have hceq : c = i := Fin.ext (by omega)
      subst hceq
      simp only [zl_eq]
      exact hγz

include hcst in
/-- **The refinement invariants** after `i ≤ n` components. -/
lemma vrRun_inv (hlim : RdeSpecK ι M f lim) (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    ∀ i ≤ n, VRSound M f ws ws.length i (vlRun O cst ws.length lim ws i) ∧
      VRComplete ι M f ws ws.length i (vlRun O cst ws.length lim ws i)
  | 0, _ => ⟨vrInit_sound M f ws, vrInit_complete ι M f ws⟩
  | i + 1, hi => by
    have ih := vrRun_inv hlim hιrat i (by omega)
    have h : i < n := by omega
    simp only [vlRun, dif_pos h]
    exact ⟨vrStep_sound ι M cst hcst f lim ws hlim ⟨i, h⟩ _ ih.1,
      vrStep_complete ι M cst hcst f lim ws hlim hιrat ⟨i, h⟩ _ ih.2⟩

include hcst in
/-- **Diagonal vector Risch equations meet the specification** (`F = f I`). -/
theorem vecRde_spec (hlim : RdeSpecK ι M f lim) (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    SysSpecAt ι (fun i j ↦ if i = j then f else 0) (ws.map (semVa M))
      (semR M (vecRde O cst lim ws)) := by
  classical
  obtain ⟨hS, hC⟩ := vrRun_inv ι M cst hcst f lim ws hlim hιrat n le_rfl
  set En := vlRun O cst ws.length lim ws n with hEn
  have hmv : ∀ z : Fin n → K, ∀ i, mv (fun i j ↦ if i = j then f else 0) z i = f * z i := fun z i ↦ by
    simp [mv]
  have hlenR : (semR M (vecRde O cst lim ws)).length = En.length := by simp [semR, vecRde, hEn]
  have hget : ∀ k < En.length, (semR M (vecRde O cst lim ws)).getD k ([], 0) =
      ((En.getD k ([], [])).1, fun c : Fin n ↦ M.sem ((En.getD k ([], [])).2.getD c O.zero)) := by
    intro k hk
    simp only [semR, vecRde, List.map_map]
    rw [NestTower.getD_map' _ _ ([], []) _ (by simpa [hEn] using hk)]
    rfl
  refine ⟨fun r hr i ↦ ?_, fun c hc z hz ↦ ?_⟩
  · simp only [semR, vecRde, List.map_map, List.mem_map] at hr
    obtain ⟨ez, hez, rfl⟩ := hr
    simp only [Function.comp_apply]
    rw [hmv, List.length_map]
    simp only [getD_semVa]
    exact (hS ez hez).2 i i.2
  · have hz' : ∀ i : Fin n, (i : ℕ) < n →
        (z i)′ + f * z i = ∑ l ∈ Finset.range ws.length, ι (c.getD l 0) * wv M ws l i := fun i _ ↦ by
      have := hz i
      rw [hmv, List.length_map] at this
      simpa [getD_semVa] using this
    obtain ⟨β, hβc, hβz⟩ := hC c (fun l hl ↦ hc l (by simpa using hl)) z hz'
    refine ⟨β, fun l ↦ ?_, fun i ↦ ?_⟩
    · rw [hlenR, hβc l]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [hget k (Finset.mem_range.mp hk)]
    · rw [hlenR, hβz i i.2]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [hget k (Finset.mem_range.mp hk)]

end Sem

end Tower.Sys
