import RischTragerBronstein.Computable.SysLoopC
import RischTragerBronstein.Computable.NestPElemPoly

/-!
# Coupled Risch systems: parametric integration of vectors

Given a scalar parametric integrator `lim` (`LimSpec`: all `z′ = ∑ cₗ fₗ` up to constants), the
vector problem `zᵢ′ = ∑ₗ cₗ wₗᵢ` (`i < n`) is solved by refining component by component
(`vlStep`, `vlRun`): the relation vectors found for the first `i` components are fed, recombined,
to `lim` for component `i`. With the constant unit vectors appended, `vecLim` meets the
specification of a solver one level down with `F = 0` (`vecLim_spec`), as needed by the coefficient
loop at a primitive level.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

open Tower.NestM Tower.NestP

section Codes

variable {α : Type} (O : COps α) (cst : ℚ → α) {n : ℕ}

/-- **One refinement** (component `i`). -/
def vlStep (L : ℕ) (lim : List α → List (List ℚ × α)) (ws : List (Fin n → α)) (i : Fin n)
    (E : List (List ℚ × List α)) : List (List ℚ × List α) :=
  let fs := E.map fun ez ↦ lcombCode O cst ez.1 (ws.map fun w ↦ w i)
  (lim fs).map fun r ↦ (vcomb L r.1 (E.map Prod.fst),
    ((List.range (i : ℕ)).map fun c ↦ lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero)) ++
      [r.2])

/-- The initial relations (all unit vectors, no components). -/
def vlInit (L : ℕ) : List (List ℚ × List α) := (List.range L).map fun l ↦ (unitV L l, [])

/-- The refinement over the first `i` components. -/
def vlRun (L : ℕ) (lim : List α → List (List ℚ × α)) (ws : List (Fin n → α)) :
    ℕ → List (List ℚ × List α)
  | 0 => vlInit L
  | i + 1 => if h : i < n then vlStep O cst L lim ws ⟨i, h⟩ (vlRun L lim ws i) else vlRun L lim ws i

/-- **Parametric integration of vectors** (with the constant vectors). -/
def vecLim (lim : List α → List (List ℚ × α)) (ws : List (Fin n → α)) :
    List (List ℚ × (Fin n → α)) :=
  ((vlRun O cst ws.length lim ws n).map fun ez ↦
      ((ez.1, fun c : Fin n ↦ ez.2.getD c O.zero) : List ℚ × (Fin n → α))) ++
    (List.finRange n).map fun c ↦
      (((List.range ws.length).map fun _ ↦ (0 : ℚ), fun c' ↦ if c' = c then O.one else O.zero) :
        List ℚ × (Fin n → α))

end Codes

section Sem

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = q)
  {n : ℕ} (lim : List α → List (List ℚ × α)) (ws : List (Fin n → α))

/-- The semantic entries `wₗ c`. -/
noncomputable def wv (l : ℕ) (c : Fin n) : K := M.sem ((ws.getD l fun _ ↦ O.zero) c)

lemma dRat (q : ℚ) : ((q : K))′ = 0 := Tower.NestP.deriv_ratCastK q

/-- Soundness of a stage: each relation `e` integrates the first `i` components. -/
def VLSound (L i : ℕ) (E : List (List ℚ × List α)) : Prop :=
  ∀ ez ∈ E, ez.1.length = L ∧ ∀ c : Fin n, (c : ℕ) < i →
    (M.sem (ez.2.getD c O.zero))′ = ∑ l ∈ Finset.range L, ((ez.1.getD l 0 : ℚ) : K) * wv M ws l c

/-- Completeness of a stage: every relation of the first `i` components is spanned. -/
def VLComplete (L i : ℕ) (E : List (List ℚ × List α)) : Prop :=
  ∀ cv : List Cs, (∀ l, L ≤ l → cv.getD l 0 = 0) → ∀ z : Fin n → K,
    (∀ c : Fin n, (c : ℕ) < i → (z c)′ = ∑ l ∈ Finset.range L, ι (cv.getD l 0) * wv M ws l c) →
    ∃ β : List Cs,
      (∀ l, cv.getD l 0 = ∑ k ∈ Finset.range E.length,
        β.getD k 0 * algebraMap ℚ Cs ((E.getD k ([], [])).1.getD l 0)) ∧
      ∀ c : Fin n, (c : ℕ) < i → (z c - ∑ k ∈ Finset.range E.length,
        ι (β.getD k 0) * M.sem ((E.getD k ([], [])).2.getD c O.zero))′ = 0

lemma getD_map_apply (l : ℕ) (c : Fin n) :
    (ws.map fun w ↦ w c).getD l O.zero = (ws.getD l fun _ ↦ O.zero) c := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[l]? <;> rfl

include hcst in
lemma sem_lcomb_ws (e : List ℚ) (c : Fin n) :
    M.sem (lcombCode O cst e (ws.map fun w ↦ w c)) =
      ∑ l ∈ Finset.range ws.length, ((e.getD l 0 : ℚ) : K) * wv M ws l c := by
  rw [sem_lcombCode M cst hcst, zipWith_sum_getD (fun (q : ℚ) a ↦ (q : K) * M.sem a) 0 O.zero
    (by simp), List.length_map]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [getD_map_apply]; rfl

include hcst in
lemma sem_lcomb_E (r : List ℚ) (E : List (List ℚ × List α)) (f : List ℚ × List α → α) :
    M.sem (lcombCode O cst r (E.map f)) =
      ∑ k ∈ Finset.range E.length, ((r.getD k 0 : ℚ) : K) * M.sem (f (E.getD k ([], []))) := by
  rw [sem_lcombCode M cst hcst, zipWith_sum_getD (fun (q : ℚ) a ↦ (q : K) * M.sem a) 0 O.zero
    (by simp), List.length_map]
  exact Finset.sum_congr rfl fun k hk ↦ by
    rw [NestTower.getD_map' _ _ ([], []) _ (Finset.mem_range.mp hk)]

lemma deriv_sum_rat (N : ℕ) (a : ℕ → ℚ) (x : ℕ → K) :
    (∑ k ∈ Finset.range N, ((a k : ℚ) : K) * x k)′ = ∑ k ∈ Finset.range N, ((a k : ℚ) : K) * (x k)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Derivation.leibniz, dRat, smul_zero, add_zero, smul_eq_mul]

lemma vlInit_sound : VLSound M ws ws.length 0 (vlInit (α := α) ws.length) := by
  intro ez hez
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hez
  exact ⟨by simp [unitV], fun c hc ↦ absurd hc (Nat.not_lt_zero _)⟩

lemma vlInit_complete : VLComplete ι M ws ws.length 0 (vlInit (α := α) ws.length) := by
  intro cv hcv z _
  refine ⟨(List.range ws.length).map fun l ↦ cv.getD l 0, fun l ↦ ?_,
    fun c hc ↦ absurd hc (Nat.not_lt_zero _)⟩
  simp only [vlInit, List.length_map, List.length_range]
  have e : ∀ k ∈ Finset.range ws.length, ((List.range ws.length).map fun l ↦ cv.getD l 0).getD k 0 *
      algebraMap ℚ Cs ((((List.range ws.length).map fun l ↦ ((unitV ws.length l, []) :
        List ℚ × List α)).getD k ([], [])).1.getD l 0) =
      if l = k then (if l < ws.length then cv.getD l 0 else 0) else 0 := fun k hk ↦ by
    have hk' := Finset.mem_range.mp hk
    rw [NestTower.getD_range_map _ _ hk', NestTower.getD_range_map _ _ hk', getD_unitV]
    by_cases hlk : l = k
    · subst hlk; simp [hk']
    · simp [hlk]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
  by_cases hl : l < ws.length
  · simp [hl]
  · simp only [Finset.mem_range, hl, if_false]
    exact hcv l (by omega)

/-- The entries of a new relation vector. -/
lemma vcomb_rows (r : List ℚ) (E : List (List ℚ × List α)) (x : ℕ → K) :
    ∑ k ∈ Finset.range E.length, ((r.getD k 0 : ℚ) : K) *
      ∑ l ∈ Finset.range ws.length, (((E.getD k ([], [])).1.getD l 0 : ℚ) : K) * x l =
    ∑ l ∈ Finset.range ws.length,
      (((vcomb ws.length r (E.map Prod.fst)).getD l 0 : ℚ) : K) * x l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hl), List.length_map]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hk)]
  ring

lemma getD_vlStep (i : Fin n) (E : List (List ℚ × List α)) (j : ℕ)
    (hj : j < (lim (E.map fun ez ↦ lcombCode O cst ez.1 (ws.map fun w ↦ w i))).length) :
    (vlStep O cst ws.length lim ws i E).getD j ([], []) =
      let r := (lim (E.map fun ez ↦ lcombCode O cst ez.1 (ws.map fun w ↦ w i))).getD j ([], O.zero)
      (vcomb ws.length r.1 (E.map Prod.fst),
        ((List.range (i : ℕ)).map fun c ↦ lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero)) ++
          [r.2]) := by
  simp only [vlStep]
  exact NestTower.getD_map' _ _ ([], O.zero) _ hj

lemma zl_lt (i : Fin n) (r : List ℚ × α) (E : List (List ℚ × List α)) (c : ℕ) (hc : c < i) :
    (((List.range (i : ℕ)).map fun c ↦ lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero)) ++
      [r.2]).getD c O.zero = lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero) := by
  rw [List.getD_append _ _ _ _ (by simpa using hc), NestTower.getD_range_map _ _ hc]

lemma zl_eq (i : Fin n) (r : List ℚ × α) (E : List (List ℚ × List α)) :
    (((List.range (i : ℕ)).map fun c ↦ lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero)) ++
      [r.2]).getD i O.zero = r.2 := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

include hcst in
/-- **A refinement step is sound.** -/
lemma vlStep_sound (hlim : LimSpec ι M lim) (i : Fin n) (E : List (List ℚ × List α))
    (hE : VLSound M ws ws.length i E) :
    VLSound M ws ws.length (i + 1) (vlStep O cst ws.length lim ws i E) := by
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
    rw [zl_lt cst i r E c hci, sem_lcomb_E M cst hcst, deriv_sum_rat, ← vcomb_rows]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [(hE _ (by rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _)).2 c hci]
  · have hceq : c = i := Fin.ext (by omega)
    subst hceq
    simp only
    rw [zl_eq, hlim.sound fs r hr, sQ, hfs, List.length_map, ← vcomb_rows]
    exact Finset.sum_congr rfl fun k hk ↦ by rw [← hfs, hsem k hk]

include hcst in
/-- **A refinement step is complete.** -/
lemma vlStep_complete (hlim : LimSpec ι M lim)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (i : Fin n) (E : List (List ℚ × List α))
    (hE : VLComplete ι M ws ws.length i E) :
    VLComplete ι M ws ws.length (i + 1) (vlStep O cst ws.length lim ws i E) := by
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
  have hzi : (z i)′ = sC ι M βt fs := by
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
lemma vlRun_inv (hlim : LimSpec ι M lim) (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    ∀ i ≤ n, VLSound M ws ws.length i (vlRun O cst ws.length lim ws i) ∧
      VLComplete ι M ws ws.length i (vlRun O cst ws.length lim ws i)
  | 0, _ => ⟨vlInit_sound M ws, vlInit_complete ι M ws⟩
  | i + 1, hi => by
    have ih := vlRun_inv hlim hιrat i (by omega)
    have h : i < n := by omega
    simp only [vlRun, dif_pos h]
    exact ⟨vlStep_sound ι M cst hcst lim ws hlim ⟨i, h⟩ _ ih.1,
      vlStep_complete ι M cst hcst lim ws hlim hιrat ⟨i, h⟩ _ ih.2⟩

lemma getD_semVa (l : ℕ) (c : Fin n) : ((ws.map (semVa M)).getD l 0) c = wv M ws l c := by
  rw [wv, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[l]? with
  | none => simp [M.sem_zero]
  | some w => rfl

include hcst in
/-- **Vector parametric integration meets the specification** (with `F = 0`). -/
theorem vecLim_spec (hlim : LimSpec ι M lim) (hιd : ∀ κ : Cs, (ι κ)′ = 0)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))
    (hconst : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ) :
    SysSpecAt ι (0 : Fin n → Fin n → K) (ws.map (semVa M)) (semR M (vecLim O cst lim ws)) := by
  classical
  obtain ⟨hS, hC⟩ := vlRun_inv ι M cst hcst lim ws hlim hιrat n le_rfl
  set En := vlRun O cst ws.length lim ws n with hEn
  have hmv0 : ∀ z : Fin n → K, ∀ i, mv (0 : Fin n → Fin n → K) z i = 0 := fun z i ↦ by simp [mv]
  have hlenR : (semR M (vecLim O cst lim ws)).length = En.length + n := by
    simp [semR, vecLim, hEn]
  have hgetL : ∀ k < En.length, (semR M (vecLim O cst lim ws)).getD k ([], 0) =
      ((En.getD k ([], [])).1, fun c : Fin n ↦ M.sem ((En.getD k ([], [])).2.getD c O.zero)) := by
    intro k hk
    simp only [semR, vecLim, List.map_append]
    rw [List.getD_append _ _ _ _ (by simpa [hEn] using hk), List.map_map,
      NestTower.getD_map' _ _ ([], []) _ (by simpa [hEn] using hk)]
    rfl
  have hgetR : ∀ c : Fin n, (semR M (vecLim O cst lim ws)).getD (En.length + c) ([], 0) =
      ((List.range ws.length).map fun _ ↦ (0 : ℚ),
        fun c' ↦ M.sem (if c' = c then O.one else O.zero)) := by
    intro c
    simp only [semR, vecLim, List.map_append]
    rw [List.getD_append_right _ _ _ _ (by simp [hEn])]
    simp only [List.length_map, ← hEn, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [List.getElem_map, List.getElem_finRange]
  refine ⟨fun r hr i ↦ ?_, fun c hc z hz ↦ ?_⟩
  · simp only [semR, vecLim, List.map_append, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨r0, ⟨ez, hez, rfl⟩, rfl⟩ | ⟨r0, ⟨c, -, rfl⟩, rfl⟩
    · simp only
      rw [hmv0, add_zero, List.length_map]
      simp only [getD_semVa]
      exact (hS ez hez).2 i i.2
    · simp only
      rw [hmv0, add_zero]
      have h0 : (M.sem (if i = c then O.one else O.zero))′ = 0 := by
        split_ifs
        · rw [M.sem_one, Derivation.map_one_eq_zero]
        · rw [M.sem_zero, map_zero]
      rw [h0]
      symm
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      rw [NestTower.getD_range_map _ _ (by simpa using hl)]
      simp
  · have hz' : ∀ i : Fin n, (i : ℕ) < n →
        (z i)′ = ∑ l ∈ Finset.range ws.length, ι (c.getD l 0) * wv M ws l i := fun i _ ↦ by
      have := hz i
      rw [hmv0, add_zero, List.length_map] at this
      simpa [getD_semVa] using this
    obtain ⟨β, hβc, hβz⟩ := hC c (fun l hl ↦ hc l (by simpa using hl)) z hz'
    choose κ hκ using fun i : Fin n ↦ hconst _ (hβz i i.2)
    set βf : List Cs := (List.range En.length).map (fun k ↦ β.getD k 0) ++ (List.finRange n).map κ
      with hβf
    have hβL : ∀ k < En.length, βf.getD k 0 = β.getD k 0 := fun k hk ↦ by
      rw [hβf, List.getD_append _ _ _ _ (by simpa using hk), NestTower.getD_range_map _ _ hk]
    have hβR : ∀ x : Fin n, βf.getD (En.length + x) 0 = κ x := fun x ↦ by
      rw [hβf, List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    refine ⟨βf, fun l ↦ ?_, fun i ↦ ?_⟩
    · rw [hlenR, Finset.sum_range_add]
      have e2 : ∀ x ∈ Finset.range n, βf.getD (En.length + x) 0 * algebraMap ℚ Cs
          (((semR M (vecLim O cst lim ws)).getD (En.length + x) ([], 0)).1.getD l 0) = 0 :=
        fun x hx ↦ by
          have h2 := hgetR ⟨x, Finset.mem_range.mp hx⟩
          simp only at h2
          rw [h2]
          simp only
          by_cases hl : l < ws.length
          · rw [NestTower.getD_range_map _ _ hl]; simp
          · rw [List.getD_eq_default ((List.range ws.length).map fun _ ↦ (0 : ℚ)) _
              (by simpa using hl)]; simp
      rw [Finset.sum_congr rfl e2, Finset.sum_const_zero, add_zero, hβc l]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hβL k (Finset.mem_range.mp hk), hgetL k (Finset.mem_range.mp hk)]
    · rw [hlenR, Finset.sum_range_add]
      have e2 : ∀ x ∈ Finset.range n, ι (βf.getD (En.length + x) 0) *
          ((semR M (vecLim O cst lim ws)).getD (En.length + x) ([], 0)).2 i =
          if (i : ℕ) = x then ι (κ i) else 0 := fun x hx ↦ by
        have hx' := Finset.mem_range.mp hx
        have h1 := hβR ⟨x, hx'⟩
        have h2 := hgetR ⟨x, hx'⟩
        simp only at h1 h2
        rw [h1, h2]
        simp only
        by_cases hix : (i : ℕ) = x
        · have : i = ⟨x, hx'⟩ := Fin.ext hix
          subst this
          simp [M.sem_one]
        · have : i ≠ ⟨x, hx'⟩ := fun h ↦ hix (by rw [h])
          simp [this, hix, M.sem_zero]
      rw [Finset.sum_congr rfl e2, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr i.2), ← hκ i]
      have e1 : ∑ k ∈ Finset.range En.length, ι (βf.getD k 0) *
          ((semR M (vecLim O cst lim ws)).getD k ([], 0)).2 i =
          ∑ k ∈ Finset.range En.length, ι (β.getD k 0) *
            M.sem ((En.getD k ([], [])).2.getD i O.zero) := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [hβL k (Finset.mem_range.mp hk), hgetL k (Finset.mem_range.mp hk)]
      rw [e1]
      ring

end Sem

end Tower.Sys
