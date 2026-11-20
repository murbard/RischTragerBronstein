import RischTragerBronstein.Computable.SysVecRde

/-!
# Coupled Risch systems: triangular systems by back-substitution

For `zᵢ′ + fᵢ zᵢ + ∑_{c > i} Fᵢc z_c = ∑ₗ cₗ wₗᵢ` (upper triangular), given scalar parametric Risch
solvers for each `fᵢ` (`RdeSpecK`, exact), `vtRun` refines the relations component by component
from the last one: for component `i` the family is `∑ₗ eₗ wₗᵢ − ∑_{c > i} Fᵢc z_c` over the
current basis. `triSys_spec`: the specification of a solver one level down with the triangular
matrix `F`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

open Tower.NestM Tower.NestP

section Codes

variable {α : Type} (O : COps α) (cst : ℚ → α) {n : ℕ}

/-- `∑_{c > i} Fᵢc z_c` on codes. -/
def offC (Fc : Fin n → Fin n → α) (i : Fin n) (zl : List α) : α :=
  ((List.range n).filter fun c ↦ decide ((i : ℕ) < c)).foldr
    (fun c acc ↦ O.add (O.mul (if h : c < n then Fc i ⟨c, h⟩ else O.zero) (zl.getD c O.zero)) acc)
    O.zero

/-- **One back-substitution step** (component `i`). -/
def vtStep (L : ℕ) (rde : Fin n → List α → List (List ℚ × α)) (Fc : Fin n → Fin n → α)
    (ws : List (Fin n → α)) (i : Fin n) (E : List (List ℚ × List α)) : List (List ℚ × List α) :=
  let fs := E.map fun ez ↦ O.add (lcombCode O cst ez.1 (ws.map fun w ↦ w i)) (O.neg (offC O Fc i ez.2))
  (rde i fs).map fun r ↦ (vcomb L r.1 (E.map Prod.fst), (List.range n).map fun c ↦
    if c = (i : ℕ) then r.2
    else if (i : ℕ) < c then lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero) else O.zero)

/-- The initial relations. -/
def vtInit (L : ℕ) : List (List ℚ × List α) :=
  (List.range L).map fun l ↦ (unitV L l, (List.range n).map fun _ ↦ O.zero)

/-- After `s` steps: the components `≥ n − s` are processed. -/
def vtRun (L : ℕ) (rde : Fin n → List α → List (List ℚ × α)) (Fc : Fin n → Fin n → α)
    (ws : List (Fin n → α)) : ℕ → List (List ℚ × List α)
  | 0 => vtInit (n := n) O L
  | s + 1 => if h : s < n then vtStep O cst L rde Fc ws ⟨n - 1 - s, by omega⟩ (vtRun L rde Fc ws s)
      else vtRun L rde Fc ws s

/-- **Triangular systems.** -/
def triSys (rde : Fin n → List α → List (List ℚ × α)) (Fc : Fin n → Fin n → α)
    (ws : List (Fin n → α)) : List (List ℚ × (Fin n → α)) :=
  (vtRun O cst ws.length rde Fc ws n).map fun ez ↦ (ez.1, listFn ez.2 O.zero)

end Codes

section Sem

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = q)
  {n : ℕ}

lemma sem_foldr_filter (p : ℕ → Prop) [DecidablePred p] (g : ℕ → α) :
    ∀ N, M.sem (((List.range N).filter fun c ↦ decide (p c)).foldr (fun c acc ↦ O.add (g c) acc)
      O.zero) = ∑ c ∈ Finset.range N, if p c then M.sem (g c) else 0
  | 0 => by simp [M.sem_zero]
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.foldr_append, Finset.sum_range_succ]
    have hf : ∀ (l : List ℕ) (a : α), M.sem (l.foldr (fun c acc ↦ O.add (g c) acc) a) =
        M.sem (l.foldr (fun c acc ↦ O.add (g c) acc) O.zero) + M.sem a := by
      intro l a
      induction l with
      | nil => simp [M.sem_zero]
      | cons x l ih => simp only [List.foldr_cons, M.sem_add, ih]; ring
    rw [hf, sem_foldr_filter p g N]
    congr 1
    by_cases hN : p N <;> simp [hN, M.sem_add, M.sem_zero]

lemma sem_offC (Fc : Fin n → Fin n → α) (i : Fin n) (zl : List α) :
    M.sem (offC O Fc i zl) = ∑ c : Fin n,
      if i < c then M.sem (Fc i c) * M.sem (zl.getD c O.zero) else 0 := by
  unfold offC
  rw [sem_foldr_filter M (fun c ↦ (i : ℕ) < c), ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [Fin.is_lt, dif_pos, Fin.eta, M.sem_mul, Fin.lt_def]

variable (f : Fin n → K) (Fc : Fin n → Fin n → α) (ws : List (Fin n → α))

/-- The off-diagonal part on values. -/
noncomputable def offV (z : Fin n → K) (c : Fin n) : K :=
  ∑ c' : Fin n, if c < c' then M.sem (Fc c c') * z c' else 0

/-- Soundness after processing the components `≥ lo`. -/
def VTSound (L lo : ℕ) (E : List (List ℚ × List α)) : Prop :=
  ∀ ez ∈ E, ez.1.length = L ∧ ∀ c : Fin n, lo ≤ (c : ℕ) →
    (M.sem (ez.2.getD c O.zero))′ + f c * M.sem (ez.2.getD c O.zero) +
      offV M Fc (fun c' ↦ M.sem (ez.2.getD c' O.zero)) c =
      ∑ l ∈ Finset.range L, ((ez.1.getD l 0 : ℚ) : K) * wv M ws l c

/-- Completeness after processing the components `≥ lo`. -/
def VTComplete (L lo : ℕ) (E : List (List ℚ × List α)) : Prop :=
  ∀ cv : List Cs, (∀ l, L ≤ l → cv.getD l 0 = 0) → ∀ z : Fin n → K,
    (∀ c : Fin n, lo ≤ (c : ℕ) →
      (z c)′ + f c * z c + offV M Fc z c = ∑ l ∈ Finset.range L, ι (cv.getD l 0) * wv M ws l c) →
    ∃ β : List Cs,
      (∀ l, cv.getD l 0 = ∑ k ∈ Finset.range E.length,
        β.getD k 0 * algebraMap ℚ Cs ((E.getD k ([], [])).1.getD l 0)) ∧
      ∀ c : Fin n, lo ≤ (c : ℕ) → z c = ∑ k ∈ Finset.range E.length,
        ι (β.getD k 0) * M.sem ((E.getD k ([], [])).2.getD c O.zero)

lemma vtInit_sound : VTSound M f Fc ws ws.length n (vtInit (n := n) O ws.length) := by
  intro ez hez
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hez
  exact ⟨by simp [unitV], fun c hc ↦ absurd hc (by omega)⟩

lemma vtInit_complete : VTComplete ι M f Fc ws ws.length n (vtInit (n := n) O ws.length) := by
  intro cv hcv z _
  obtain ⟨β, hβ, -⟩ := vlInit_complete ι M ws cv hcv z (fun c hc ↦ absurd hc (Nat.not_lt_zero _))
  refine ⟨β, fun l ↦ ?_, fun c hc ↦ absurd hc (by omega)⟩
  rw [hβ l]
  simp only [vtInit, vlInit, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hk),
    NestTower.getD_range_map _ _ (Finset.mem_range.mp hk)]

lemma offV_comb (z : Fin n → K) (N : ℕ) (r : ℕ → K) (sv : ℕ → Fin n → K) (c : Fin n)
    (hz : ∀ c' : Fin n, c < c' → z c' = ∑ k ∈ Finset.range N, r k * sv k c') :
    offV M Fc z c = ∑ k ∈ Finset.range N, r k * offV M Fc (sv k) c := by
  unfold offV
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ ↦ ?_
  split_ifs with hc
  · rw [hz c' hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  · simp

/-- The new component vector of a refinement step. -/
lemma getD_vtNew (i : Fin n) (r : List ℚ × α) (E : List (List ℚ × List α)) (c : Fin n) :
    ((List.range n).map fun c ↦ if c = (i : ℕ) then r.2
      else if (i : ℕ) < c then lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero)
      else O.zero).getD c O.zero =
    if c = i then r.2 else if i < c then lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero)
      else O.zero := by
  rw [NestTower.getD_range_map _ _ c.2]
  simp only [Fin.val_inj, Fin.lt_def]

variable (rde : Fin n → List α → List (List ℚ × α))

include hcst in
/-- **A back-substitution step is sound.** -/
lemma vtStep_sound (hrde : ∀ i, RdeSpecK ι M (f i) (rde i)) (i : Fin n)
    (E : List (List ℚ × List α)) (hE : VTSound M f Fc ws ws.length (i + 1) E) :
    VTSound M f Fc ws ws.length i (vtStep O cst ws.length rde Fc ws i E) := by
  intro ez hez
  simp only [vtStep] at hez
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hez
  set fs := E.map fun ez ↦ O.add (lcombCode O cst ez.1 (ws.map fun w ↦ w i))
    (O.neg (offC O Fc i ez.2)) with hfs
  set sv : ℕ → Fin n → K := fun k c ↦ M.sem ((E.getD k ([], [])).2.getD c O.zero) with hsv
  have hmem : ∀ k ∈ Finset.range E.length, E.getD k ([], []) ∈ E := fun k hk ↦ by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
  have hnew : ∀ c' : Fin n, i < c' → M.sem ((((List.range n).map fun c ↦ if c = (i : ℕ) then r.2
      else if (i : ℕ) < c then lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero)
      else O.zero)).getD c' O.zero) = ∑ k ∈ Finset.range E.length, ((r.1.getD k 0 : ℚ) : K) * sv k c' :=
    fun c' hc' ↦ by
      rw [getD_vtNew, if_neg (ne_of_gt hc'), if_pos hc', sem_lcomb_E M cst hcst]
  refine ⟨length_vcomb _ _ _, fun c hc ↦ ?_⟩
  simp only
  rw [offV_comb M Fc _ E.length (fun k ↦ ((r.1.getD k 0 : ℚ) : K)) sv c (fun c' hc' ↦ hnew c'
    (lt_of_le_of_lt (Fin.le_def.mpr hc) hc'))]
  rcases Nat.lt_or_ge (i : ℕ) c with hic | hic
  · have hic' : i < c := hic
    rw [hnew c hic', rde_sum_rat, ← Finset.sum_add_distrib, ← vcomb_rows]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← mul_add, ← (hE _ (hmem k hk)).2 c (by omega)]
  · have hceq : c = i := Fin.ext (by omega)
    subst hceq
    rw [getD_vtNew, if_pos rfl, (hrde c).sound fs r hr, sQ, hfs, List.length_map, ← vcomb_rows,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← hfs, hfs, NestTower.getD_map' _ _ ([], []) _ (Finset.mem_range.mp hk), M.sem_add,
      M.sem_neg, sem_lcomb_ws M cst hcst, sem_offC]
    simp only [hsv, offV]
    ring

lemma getD_vtStep (i : Fin n) (E : List (List ℚ × List α)) (j : ℕ)
    (hj : j < (rde i (E.map fun ez ↦ O.add (lcombCode O cst ez.1 (ws.map fun w ↦ w i))
      (O.neg (offC O Fc i ez.2)))).length) :
    (vtStep O cst ws.length rde Fc ws i E).getD j ([], []) =
      let r := (rde i (E.map fun ez ↦ O.add (lcombCode O cst ez.1 (ws.map fun w ↦ w i))
        (O.neg (offC O Fc i ez.2)))).getD j ([], O.zero)
      (vcomb ws.length r.1 (E.map Prod.fst), (List.range n).map fun c ↦
        if c = (i : ℕ) then r.2
        else if (i : ℕ) < c then lcombCode O cst r.1 (E.map fun ez ↦ ez.2.getD c O.zero) else O.zero) := by
  simp only [vtStep]
  exact NestTower.getD_map' _ _ ([], O.zero) _ hj

include hcst in
/-- **A back-substitution step is complete.** -/
lemma vtStep_complete (hrde : ∀ i, RdeSpecK ι M (f i) (rde i))
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (i : Fin n) (E : List (List ℚ × List α))
    (hE : VTComplete ι M f Fc ws ws.length (i + 1) E) :
    VTComplete ι M f Fc ws ws.length i (vtStep O cst ws.length rde Fc ws i E) := by
  intro cv hcv z hz
  obtain ⟨β, hβc, hβz⟩ := hE cv hcv z (fun c hc ↦ hz c (by omega))
  set fs := E.map fun ez ↦ O.add (lcombCode O cst ez.1 (ws.map fun w ↦ w i))
    (O.neg (offC O Fc i ez.2)) with hfs
  set R := rde i fs with hR
  set βt := (List.range E.length).map fun k ↦ β.getD k 0 with hβt
  set sv : ℕ → Fin n → K := fun k c ↦ M.sem ((E.getD k ([], [])).2.getD c O.zero) with hsv
  have hβtD : ∀ k < E.length, βt.getD k 0 = β.getD k 0 := fun k hk ↦
    NestTower.getD_range_map _ _ hk
  have hsem : ∀ k ∈ Finset.range E.length, M.sem (fs.getD k O.zero) =
      ∑ l ∈ Finset.range ws.length, (((E.getD k ([], [])).1.getD l 0 : ℚ) : K) * wv M ws l i -
        offV M Fc (sv k) i := fun k hk ↦ by
    rw [hfs, NestTower.getD_map' _ _ ([], []) _ (Finset.mem_range.mp hk), M.sem_add, M.sem_neg,
      sem_lcomb_ws M cst hcst, sem_offC]
    simp only [hsv, offV]
    ring
  have hoff : offV M Fc z i = ∑ k ∈ Finset.range E.length, ι (β.getD k 0) * offV M Fc (sv k) i :=
    offV_comb M Fc z E.length (fun k ↦ ι (β.getD k 0)) sv i (fun c' hc' ↦ hβz c' (by
      have := Fin.lt_def.mp hc'; omega))
  have hzi : (z i)′ + f i * z i = sC ι M βt fs := by
    have h0 := hz i le_rfl
    rw [hoff] at h0
    rw [sC, hfs, List.length_map]
    have e1 : ∀ l ∈ Finset.range ws.length, ι (cv.getD l 0) * wv M ws l i =
        ∑ k ∈ Finset.range E.length, ι (β.getD k 0) *
          ((((E.getD k ([], [])).1.getD l 0 : ℚ) : K) * wv M ws l i) := fun l _ ↦ by
      rw [hβc l, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul, hιrat]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_comm] at h0
    have e2 : ∀ k ∈ Finset.range E.length, ι (βt.getD k 0) * M.sem (fs.getD k O.zero) =
        ∑ l ∈ Finset.range ws.length, ι (β.getD k 0) *
          ((((E.getD k ([], [])).1.getD l 0 : ℚ) : K) * wv M ws l i) -
          ι (β.getD k 0) * offV M Fc (sv k) i := fun k hk ↦ by
      rw [hsem k hk, hβtD k (Finset.mem_range.mp hk), mul_sub, Finset.mul_sum]
    rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib]
    linear_combination h0
  obtain ⟨γ, hγβ, hγz⟩ := (hrde i).complete fs βt (fun k hk ↦ List.getD_eq_default _ _ (by
    simp only [hβt, List.length_map, List.length_range]; simpa [hfs] using hk)) (z i) hzi
  have hβγ : ∀ k < E.length, β.getD k 0 = ∑ j ∈ Finset.range R.length,
      γ.getD j 0 * algebraMap ℚ Cs ((R.getD j ([], O.zero)).1.getD k 0) := fun k hk ↦ by
    rw [← hβtD k hk, hγβ k]
  have hlen : (vtStep O cst ws.length rde Fc ws i E).length = R.length := by simp [vtStep, hR, hfs]
  refine ⟨γ, fun l ↦ ?_, fun c hc ↦ ?_⟩
  · rw [hlen]
    have e : ∀ j ∈ Finset.range R.length, γ.getD j 0 * algebraMap ℚ Cs
        (((vtStep O cst ws.length rde Fc ws i E).getD j ([], [])).1.getD l 0) =
        γ.getD j 0 * algebraMap ℚ Cs ((vcomb ws.length (R.getD j ([], O.zero)).1
          (E.map Prod.fst)).getD l 0) := fun j hj ↦ by
      rw [getD_vtStep (cst := cst) (Fc := Fc) (ws := ws) (rde := rde) i E j (Finset.mem_range.mp hj)]
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
    have hcomp : ∀ j ∈ Finset.range R.length, ι (γ.getD j 0) *
        M.sem (((vtStep O cst ws.length rde Fc ws i E).getD j ([], [])).2.getD c O.zero) =
        ι (γ.getD j 0) * M.sem (if c = i then (R.getD j ([], O.zero)).2 else if i < c then
          lcombCode O cst (R.getD j ([], O.zero)).1 (E.map fun ez ↦ ez.2.getD c O.zero)
          else O.zero) := fun j hj ↦ by
      rw [getD_vtStep (cst := cst) (Fc := Fc) (ws := ws) (rde := rde) i E j (Finset.mem_range.mp hj)]
      simp only
      rw [getD_vtNew]
    rw [Finset.sum_congr rfl hcomp]
    rcases Nat.lt_or_ge (i : ℕ) c with hic | hic
    · have hic' : i < c := hic
      have hci : c ≠ i := ne_of_gt hic'
      simp only [if_neg hci, if_pos hic', sem_lcomb_E M cst hcst, Finset.mul_sum]
      rw [Finset.sum_comm, hβz c (by omega)]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hβγ k (Finset.mem_range.mp hk), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, hιrat]; ring
    · have hceq : c = i := Fin.ext (by omega)
      subst hceq
      simp only [if_pos rfl]
      exact hγz

include hcst in
/-- **The back-substitution invariants** after `s ≤ n` steps. -/
lemma vtRun_inv (hrde : ∀ i, RdeSpecK ι M (f i) (rde i))
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    ∀ s ≤ n, VTSound M f Fc ws ws.length (n - s) (vtRun O cst ws.length rde Fc ws s) ∧
      VTComplete ι M f Fc ws ws.length (n - s) (vtRun O cst ws.length rde Fc ws s)
  | 0, _ => by
    simp only [Nat.sub_zero, vtRun]
    exact ⟨vtInit_sound M f Fc ws, vtInit_complete ι M f Fc ws⟩
  | s + 1, hs => by
    have ih := vtRun_inv hrde hιrat s (by omega)
    have h : s < n := by omega
    simp only [vtRun, dif_pos h]
    have e : n - 1 - s + 1 = n - s := by omega
    have ih1 : VTSound M f Fc ws ws.length ((⟨n - 1 - s, by omega⟩ : Fin n) + 1 : ℕ)
        (vtRun O cst ws.length rde Fc ws s) := by simp only [e]; exact ih.1
    have ih2 : VTComplete ι M f Fc ws ws.length ((⟨n - 1 - s, by omega⟩ : Fin n) + 1 : ℕ)
        (vtRun O cst ws.length rde Fc ws s) := by simp only [e]; exact ih.2
    have e2 : n - (s + 1) = ((⟨n - 1 - s, by omega⟩ : Fin n) : ℕ) := by simp; omega
    rw [e2]
    exact ⟨vtStep_sound ι M cst hcst f Fc ws rde hrde _ _ ih1,
      vtStep_complete ι M cst hcst f Fc ws rde hrde hιrat _ _ ih2⟩

/-- The triangular matrix on values. -/
noncomputable def triF (i j : Fin n) : K :=
  if i = j then f i else if i < j then M.sem (Fc i j) else 0

lemma mv_triF (z : Fin n → K) (i : Fin n) : mv (triF M f Fc) z i = f i * z i + offV M Fc z i := by
  simp only [mv, triF, offV]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), if_pos rfl, add_comm]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [lt_irrefl, if_false, add_zero]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  simp [Ne.symm hji]

include hcst in
/-- **Triangular systems meet the specification** (`F = triF`). -/
theorem triSys_spec (hrde : ∀ i, RdeSpecK ι M (f i) (rde i))
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    SysSpecAt ι (triF M f Fc) (ws.map (semVa M)) (semR M (triSys O cst rde Fc ws)) := by
  classical
  obtain ⟨hS, hC⟩ := vtRun_inv ι M cst hcst f Fc ws rde hrde hιrat n le_rfl
  simp only [Nat.sub_self] at hS hC
  set En := vtRun O cst ws.length rde Fc ws n with hEn
  have hlenR : (semR M (triSys O cst rde Fc ws)).length = En.length := by
    simp [semR, triSys, hEn]
  have hget : ∀ k < En.length, (semR M (triSys O cst rde Fc ws)).getD k ([], 0) =
      ((En.getD k ([], [])).1, fun c : Fin n ↦ M.sem ((En.getD k ([], [])).2.getD c O.zero)) := by
    intro k hk
    simp only [semR, triSys, List.map_map]
    rw [NestTower.getD_map' _ _ ([], []) _ (by simpa [hEn] using hk)]
    rfl
  refine ⟨fun r hr i ↦ ?_, fun c hc z hz ↦ ?_⟩
  · simp only [semR, triSys, List.map_map, List.mem_map] at hr
    obtain ⟨ez, hez, rfl⟩ := hr
    simp only [Function.comp_apply]
    rw [mv_triF, List.length_map]
    simp only [getD_semVa, listFn, ← add_assoc]
    exact (hS ez hez).2 i (Nat.zero_le _)
  · have hz' : ∀ i : Fin n, 0 ≤ (i : ℕ) →
        (z i)′ + f i * z i + offV M Fc z i =
          ∑ l ∈ Finset.range ws.length, ι (c.getD l 0) * wv M ws l i := fun i _ ↦ by
      have := hz i
      rw [mv_triF, List.length_map, ← add_assoc] at this
      simpa [getD_semVa] using this
    obtain ⟨β, hβc, hβz⟩ := hC c (fun l hl ↦ hc l (by simpa using hl)) z hz'
    refine ⟨β, fun l ↦ ?_, fun i ↦ ?_⟩
    · rw [hlenR, hβc l]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [hget k (Finset.mem_range.mp hk)]
    · rw [hlenR, hβz i (Nat.zero_le _)]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [hget k (Finset.mem_range.mp hk)]

end Sem

end Tower.Sys
