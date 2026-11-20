import RischTragerBronstein.Computable.NestPPoly

/-!
# The parametric elementary polynomial problem over a primitive

Generic in a differential field `K` with a model `M`, a primitive `t′ = η` (`η` not a derivative
in `K`), a one-level-down parametric limited-integration solver `lim` and a one-level-down
parametric *elementary* integration solver `elem`. `polyElem` returns a basis of the parameters
`c` for which `∑ cᵢ Pᵢ = Q′ + b` with `Q ∈ K[t]` and `b ∈ K` elementary-integrable one level down
(the polynomial part of Liouville's theorem over a primitive):

* `polyElem_sound`: every returned `δ` gives `∑ δᵢ Pᵢ = Q′ + b` with `b` satisfying the
  one-level-down soundness predicate `EL`;
* `polyElem_complete`: if `∑ cᵢ Pᵢ = Q′ + b` with constant `cᵢ` and `b` satisfying the Liouville
  predicate `LV` (stable under adding derivatives), then `c` is a constant combination of the
  returned vectors.

The degree loop runs down to degree `1` only (`polyDown1`); the equation of degree `0` is left to
`elem`, whose weights are those of the stage-`1` basis (`t⁰` coefficient minus `η` times the `t¹`
coefficient — the free constant of the `t¹` coefficient absorbs the `c₀ η` of Liouville's
theorem).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.NestP

/-- Reassembling a double change of basis (coefficient version). -/
lemma recombine {Cs : Type*} [Field Cs] [CharZero Cs] (n NL NJ : ℕ) (Bv ev : ℕ → ℕ → ℚ)
    (c β γ : ℕ → Cs)
    (hc : ∀ i < n, c i = ∑ l ∈ Finset.range NL, β l * algebraMap ℚ Cs (Bv l i))
    (hβ : ∀ l < NL, β l = ∑ j ∈ Finset.range NJ, γ j * algebraMap ℚ Cs (ev j l)) :
    ∀ i < n, c i = ∑ j ∈ Finset.range NJ,
      γ j * algebraMap ℚ Cs (∑ l ∈ Finset.range NL, ev j l * Bv l i) := by
  intro i hi
  rw [hc i hi]
  have e : ∀ l ∈ Finset.range NL, β l * algebraMap ℚ Cs (Bv l i) = ∑ j ∈ Finset.range NJ,
      γ j * (algebraMap ℚ Cs (ev j l) * algebraMap ℚ Cs (Bv l i)) := fun l hl ↦ by
    rw [hβ l (Finset.mem_range.mp hl), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul]

section Generic

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
variable (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α) (η : α)
  (lim : List α → List (List ℚ × α)) (elem : List α → List (List ℚ))

/-- The stage-`1` basis of `polyElem`. -/
def stage1 (O : COps α) (cst : ℚ → α) (η : α) (lim : List α → List (List ℚ × α))
    (Ps : List (GPoly α)) : List (List ℚ × GPoly α) :=
  polyDown1 O cst η lim Ps.length Ps (max 1 ((Ps.map List.length).foldr max 0) - 1)
    (baseB' O Ps.length (max 1 ((Ps.map List.length).foldr max 0)))

/-- The weights of the equation of degree `0`. -/
def weights0 (O : COps α) (cst : ℚ → α) (η : α) (Ps : List (GPoly α)) (B : List (List ℚ × GPoly α)) : List α :=
  B.map fun b ↦ O.add (lcombCode O cst b.1 (Ps.map fun P ↦ P.getD 0 O.zero))
    (O.neg (O.mul (b.2.getD 1 O.zero) η))

lemma polyElem_eq (Ps : List (GPoly α)) :
    polyElem O cst η lim elem Ps = (elem (weights0 O cst η Ps (stage1 O cst η lim Ps))).map
      fun β ↦ vcomb Ps.length β ((stage1 O cst η lim Ps).map Prod.fst) := rfl

variable {M cst} (hcst : ∀ q, M.sem (cst q) = (q : K))

include hcst in
lemma polyDown1_stage (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (Ps : List (GPoly α)) (L : ℕ) :
    ∀ (k : ℕ) (B : List (List ℚ × GPoly α)), StageSound M η Ps.length Ps (k + 1) B →
      StageComplete ι M η Ps.length L Ps (k + 1) B →
      StageSound M η Ps.length Ps 1 (polyDown1 O cst η lim Ps.length Ps k B) ∧
        StageComplete ι M η Ps.length L Ps 1 (polyDown1 O cst η lim Ps.length Ps k B)
  | 0, B, hs, hc => ⟨hs, hc⟩
  | k + 1, B, hs, hc =>
    polyDown1_stage hspec hconstK hιrat Ps L k _
      (polyStep_sound η lim hcst hspec.sound Ps (k + 1) B hs)
      (polyStep_complete ι η lim hcst hspec hconstK hιrat Ps L (k + 1) B hs hc)

include hcst in
lemma stage1_spec (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (Ps : List (GPoly α)) :
    StageSound M η Ps.length Ps 1 (stage1 O cst η lim Ps) ∧
      StageComplete ι M η Ps.length (max 1 ((Ps.map List.length).foldr max 0)) Ps 1
        (stage1 O cst η lim Ps) := by
  have hb : ∀ i, (Ps.getD i []).length ≤ max 1 ((Ps.map List.length).foldr max 0) :=
    fun i ↦ (length_le_maxLen Ps i).trans (le_max_right _ _)
  have h1 : 1 ≤ max 1 ((Ps.map List.length).foldr max 0) := le_max_left _ _
  unfold stage1
  generalize max 1 ((Ps.map List.length).foldr max 0) = L at hb h1 ⊢
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact polyDown1_stage ι η lim hcst hspec hconstK hιrat Ps (k + 1) k _
    (baseB_sound η Ps (k + 1) hb) (baseB_complete ι η Ps (k + 1) hb hconstK hιrat)

include hcst in
/-- The weight of a basis element in the equation of degree `0`. -/
lemma sem_weight0 (Ps : List (GPoly α)) (b : List ℚ × GPoly α) :
    M.sem (O.add (lcombCode O cst b.1 (Ps.map fun P ↦ P.getD 0 O.zero))
      (O.neg (O.mul (b.2.getD 1 O.zero) η))) =
      (polySumQ M b.1 Ps).coeff 0 - (GPoly.toPoly M b.2).coeff 1 * M.sem η := by
  rw [M.sem_add, M.sem_neg, M.sem_mul, sem_lcombCode M cst hcst,
    zipWith_sum_getD (fun (q : ℚ) (a : α) ↦ (q : K) * M.sem a) 0 O.zero (by simp),
    coeff_polySumQ, coeff_toPoly_getD', List.length_map]
  have e : ∑ i ∈ Finset.range Ps.length, ((b.1.getD i 0 : ℚ) : K) *
      M.sem ((Ps.map fun P ↦ P.getD 0 O.zero).getD i O.zero) =
      ∑ i ∈ Finset.range Ps.length, ((b.1.getD i 0 : ℚ) : K) *
        M.sem ((Ps.getD i []).getD 0 O.zero) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [NestTower.getD_map' _ _ [] O.zero (by simpa using hi)]
  rw [e]
  ring

/-- `Dη` commutes with rational combinations, coefficientwise. -/
lemma coeff_Dη_sum (N : ℕ) (q : ℕ → ℚ) (P : ℕ → K[X]) (k : ℕ) :
    (Dη M η (∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * P l)).coeff k =
      ∑ l ∈ Finset.range N, ((q l : ℚ) : K) * (Dη M η (P l)).coeff k := by
  rw [coeff_Dη, finsetSum_coeff, finsetSum_coeff, map_sum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [coeff_C_mul, coeff_C_mul, coeff_Dη]
  simp only [Derivation.leibniz, deriv_ratCastK, add_zero, smul_eq_mul]
  ring

include hcst in
/-- A stage-`1` basis element: every coefficient equation holds up to the weight in degree `0`. -/
lemma stage1_coeff (Ps : List (GPoly α)) (B : List (List ℚ × GPoly α))
    (hB : StageSound M η Ps.length Ps 1 B) {l : ℕ} (hl : l < B.length) (k : ℕ) :
    (polySumQ M (B.getD l ([], [])).1 Ps).coeff k =
      (Dη M η (GPoly.toPoly M (B.getD l ([], [])).2)).coeff k +
        if k = 0 then M.sem ((weights0 O cst η Ps B).getD l O.zero) else 0 := by
  have hmem : B.getD l ([], []) ∈ B := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
  obtain ⟨-, h0, hk⟩ := hB _ hmem
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [if_pos rfl, weights0, NestTower.getD_map' _ _ ([], []) O.zero hl, sem_weight0 η hcst,
      coeff_Dη, h0 0 Nat.zero_lt_one]
    simp only [Derivation.map_zero, zero_add, Nat.cast_zero]
    ring
  · rw [if_neg (by omega), add_zero, hk k hpos]

include hcst in
/-- **Soundness of the parametric elementary polynomial problem.** -/
theorem polyElem_sound (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (EL : K → Prop)
    (helem : ∀ ws, ∀ β ∈ elem ws, EL (sQ M β ws)) (Ps : List (GPoly α)) :
    ∀ δ ∈ polyElem O cst η lim elem Ps, ∃ (Q : K[X]) (b : K),
      polySumQ M δ Ps = Dη M η Q + C b ∧ EL b := by
  intro δ hδ
  rw [polyElem_eq] at hδ
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hδ
  set B := stage1 O cst η lim Ps with hBdef
  have hS := (stage1_spec ι η lim hcst hspec hconstK hιrat Ps).1
  rw [← hBdef] at hS
  refine ⟨∑ l ∈ Finset.range B.length, C ((β.getD l 0 : ℚ) : K) *
    GPoly.toPoly M (B.getD l ([], [])).2, sQ M β (weights0 O cst η Ps B), ?_, helem _ β hβ⟩
  ext k
  rw [coeff_polySumQ_vcomb, coeff_add, coeff_Dη_sum, coeff_C, List.length_map]
  have e : ∀ l ∈ Finset.range B.length, ((β.getD l 0 : ℚ) : K) *
      (polySumQ M ((B.map Prod.fst).getD l []) Ps).coeff k =
      ((β.getD l 0 : ℚ) : K) * (Dη M η (GPoly.toPoly M (B.getD l ([], [])).2)).coeff k +
        if k = 0 then ((β.getD l 0 : ℚ) : K) * M.sem ((weights0 O cst η Ps B).getD l O.zero)
        else 0 := fun l hl ↦ by
    have hl' := Finset.mem_range.mp hl
    rw [NestTower.getD_map' _ _ ([], []) [] hl', stage1_coeff η hcst Ps B hS hl' k]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
  congr 1
  split_ifs with hk
  · rw [sQ, weights0, List.length_map]
  · simp

include hcst in
/-- **Completeness of the parametric elementary polynomial problem.** -/
theorem polyElem_complete (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (hη : ∀ y : K, y′ ≠ M.sem η)
    (LV : K → Prop) (hLV : ∀ y b, LV b → LV (y′ + b))
    (helem : ∀ ws (c : List Cs), (∀ i, ws.length ≤ i → c.getD i 0 = 0) → LV (sC ι M c ws) →
      ∃ γ : List Cs, ∀ i, c.getD i 0 = ∑ k ∈ Finset.range (elem ws).length,
        γ.getD k 0 * algebraMap ℚ Cs (((elem ws).getD k []).getD i 0))
    (Ps : List (GPoly α)) (c : List Cs) (hc : ∀ i, Ps.length ≤ i → c.getD i 0 = 0) (Q : K[X])
    (b : K) (hQ : polySumC ι M c Ps = Dη M η Q + C b) (hb : LV b) :
    ∃ γ : List Cs, ∀ i, c.getD i 0 = ∑ k ∈ Finset.range (polyElem O cst η lim elem Ps).length,
      γ.getD k 0 * algebraMap ℚ Cs (((polyElem O cst η lim elem Ps).getD k []).getD i 0) := by
  set L := max 1 ((Ps.map List.length).foldr max 0) with hL
  have hconst : ∀ P : K[X], implicitDeriv (C (M.sem η)) P = 0 → ∃ e : K, P = C e :=
    fun P hP ↦ const_of_implicitDeriv_eq_zero (M.sem η) hη hP
  -- the degree bound
  have hdeg : Q.natDegree ≤ L := by
    have hd : (Dη M η Q).natDegree ≤ L - 1 := by
      have hD : Dη M η Q = polySumC ι M c Ps - C b := by rw [hQ]; ring
      rw [hD, natDegree_le_iff_coeff_eq_zero]
      intro k hk
      have hk' : L ≤ k := by
        have : L - 1 < k := by exact_mod_cast hk
        omega
      rw [coeff_sub, coeff_polySumC_ge ι _ _ fun i ↦
        ((length_le_maxLen Ps i).trans (le_max_right _ _)).trans hk', coeff_C,
        if_neg (by have := le_max_left 1 ((Ps.map List.length).foldr max 0); omega), sub_zero]
    have := natDegree_le_succ_of_natDegree_deriv_le (M.sem η) hconst hd
    have := le_max_left 1 ((Ps.map List.length).foldr max 0)
    omega
  set B := stage1 O cst η lim Ps with hBdef
  obtain ⟨hS, hC⟩ := stage1_spec ι η lim hcst hspec hconstK hιrat Ps
  rw [← hBdef] at hS hC
  obtain ⟨β, hβc, hβQ⟩ := hC c hc Q hdeg fun k hk ↦ by
    rw [hQ, coeff_add, coeff_C, if_neg (by omega), add_zero]
  set ws := weights0 O cst η Ps B with hws
  have hlws : ws.length = B.length := by simp [hws, weights0]
  set βt := (List.range B.length).map fun l ↦ β.getD l 0 with hβt
  have hβtD : ∀ l < B.length, βt.getD l 0 = β.getD l 0 := fun l hl ↦ NestTower.getD_range_map _ _ hl
  -- the equation of degree `0`
  have hsC : sC ι M βt ws = (Q.coeff 0)′ + b := by
    have hQ0 := congrArg (fun P : K[X] ↦ P.coeff 0) hQ
    simp only [coeff_add, coeff_C_zero, coeff_Dη, coeff_polySumC] at hQ0
    have hc0 : ∑ i ∈ Finset.range Ps.length, ι (c.getD i 0) * M.sem ((Ps.getD i []).getD 0 O.zero) =
        ∑ l ∈ Finset.range B.length, ι (β.getD l 0) * (polySumQ M (B.getD l ([], [])).1 Ps).coeff 0 := by
      simp only [coeff_polySumQ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [hβc i, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_mul, hιrat]
      ring
    have hq1 : Q.coeff 1 = ∑ l ∈ Finset.range B.length,
        ι (β.getD l 0) * (GPoly.toPoly M (B.getD l ([], [])).2).coeff 1 := hβQ 1 le_rfl
    have hsum : sC ι M βt ws = ∑ l ∈ Finset.range B.length,
        ι (β.getD l 0) * ((polySumQ M (B.getD l ([], [])).1 Ps).coeff 0 -
          (GPoly.toPoly M (B.getD l ([], [])).2).coeff 1 * M.sem η) := by
      rw [sC, hlws]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.mp hl
      rw [hβtD l hl', hws, weights0, NestTower.getD_map' _ _ ([], []) O.zero hl',
        sem_weight0 η hcst]
    rw [hsum]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hfin : ∑ l ∈ Finset.range B.length, ι (β.getD l 0) *
        ((GPoly.toPoly M (B.getD l ([], [])).2).coeff 1 * M.sem η) = M.sem η * Q.coeff 1 := by
      rw [hq1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [← hc0, hQ0, hfin]
    push_cast
    ring
  obtain ⟨γ, hγ⟩ := helem ws βt (fun i hi ↦ List.getD_eq_default _ _ (by simp [hβt]; omega))
    (by rw [hsC]; exact hLV _ _ hb)
  refine ⟨γ, fun i ↦ ?_⟩
  rw [polyElem_eq, List.length_map, ← hBdef, ← hws]
  have e : ∀ k ∈ Finset.range (elem ws).length, γ.getD k 0 * algebraMap ℚ Cs
      ((((elem ws).map fun β ↦ vcomb Ps.length β (B.map Prod.fst)).getD k []).getD i 0) =
      γ.getD k 0 * algebraMap ℚ Cs ((vcomb Ps.length ((elem ws).getD k []) (B.map Prod.fst)).getD i 0) :=
    fun k hk ↦ by rw [NestTower.getD_map' _ _ [] [] (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl e]
  by_cases hi : i < Ps.length
  · have := recombine Ps.length B.length (elem ws).length
      (fun l i ↦ (B.getD l ([], [])).1.getD i 0) (fun j l ↦ ((elem ws).getD j []).getD l 0)
      (fun i ↦ c.getD i 0) (fun l ↦ β.getD l 0) (fun j ↦ γ.getD j 0) (fun i _ ↦ hβc i)
      (fun l hl ↦ by rw [← hβtD l hl, hγ l]) i hi
    rw [this]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [getD_vcomb, if_pos hi, List.length_map]
    congr 2
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl)]
  · rw [hc i (by omega)]
    symm
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [getD_vcomb, if_neg hi, map_zero, mul_zero]

end Generic

end Tower.NestP
