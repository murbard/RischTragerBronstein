import RischTragerBronstein.Computable.NestPParam
import RischTragerBronstein.Liouville.PrimitiveConstants

/-!
# The parametric polynomial problem over a primitive: soundness and completeness

Generic in a differential field `K` with a model `M` of codes, a primitive `t′ = η` (`η` not a
derivative in `K`), constants `ι : C → K`, and a one-level-down parametric solver `lim` meeting
the soundness / completeness specification. `paramPoly` returns a basis of the pairs `(c, Q)`,
`Q ∈ K[t]`, `Q′ = ∑ cᵢ Pᵢ`:

* `paramPoly_sound`: `D (toPoly Q) = ∑ eᵢ Pᵢ` for every returned `(e, Q)`;
* `paramPoly_complete`: every constant solution is a constant combination of the returned pairs.

The proof follows the degree loop: at stage `j` the basis spans the solutions of the coefficient
equations of degree `≥ j`, on the coefficients of degree `≥ j`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.NestP

lemma zipWith_sum_getD {α β γ : Type*} [AddCommMonoid γ] (f : α → β → γ) (d₁ : α) (d₂ : β)
    (hf : ∀ b, f d₁ b = 0) : ∀ (l₁ : List α) (l₂ : List β),
      (List.zipWith f l₁ l₂).sum = ∑ i ∈ Finset.range l₂.length, f (l₁.getD i d₁) (l₂.getD i d₂)
  | [], l₂ => by
    simp only [List.zipWith_nil_left, List.sum_nil, List.getD_nil, hf, Finset.sum_const_zero]
  | a :: l₁, [] => by simp
  | a :: l₁, b :: l₂ => by
    rw [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      zipWith_sum_getD f d₁ d₂ hf l₁ l₂, add_comm]
    simp

section Generic

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
variable (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α) (η : α)
  (lim : List α → List (List ℚ × α))

/-- `∑ eᵢ wᵢ`, rational coefficients. -/
noncomputable def sQ (e : List ℚ) (ws : List α) : K :=
  ∑ i ∈ Finset.range ws.length, ((e.getD i 0 : ℚ) : K) * M.sem (ws.getD i O.zero)

/-- `∑ cᵢ wᵢ`, constant coefficients. -/
noncomputable def sC (c : List Cs) (ws : List α) : K :=
  ∑ i ∈ Finset.range ws.length, ι (c.getD i 0) * M.sem (ws.getD i O.zero)

/-- The specification of a parametric solver. -/
structure LimSpec : Prop where
  sound : ∀ ws, ∀ r ∈ lim ws, (M.sem r.2)′ = sQ M r.1 ws
  complete : ∀ ws (c : List Cs), (∀ i, ws.length ≤ i → c.getD i 0 = 0) → ∀ z : K,
    z′ = sC ι M c ws → ∃ β : List Cs,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (lim ws).length,
        β.getD k 0 * algebraMap ℚ Cs (((lim ws).getD k ([], O.zero)).1.getD i 0)) ∧
      (z - ∑ k ∈ Finset.range (lim ws).length,
        ι (β.getD k 0) * M.sem ((lim ws).getD k ([], O.zero)).2)′ = 0

/-- The derivation of `K[t]`, `t′ = η`. -/
noncomputable abbrev Dη (P : K[X]) : K[X] := implicitDeriv (C (M.sem η)) P

/-- The polynomials `∑ cᵢ Pᵢ`. -/
noncomputable def polySumC (c : List Cs) (Ps : List (GPoly α)) : K[X] :=
  ∑ i ∈ Finset.range Ps.length, C (ι (c.getD i 0)) * GPoly.toPoly M (Ps.getD i [])

/-- The polynomials `∑ eᵢ Pᵢ`. -/
noncomputable def polySumQ (e : List ℚ) (Ps : List (GPoly α)) : K[X] :=
  ∑ i ∈ Finset.range Ps.length, C ((e.getD i 0 : ℚ) : K) * GPoly.toPoly M (Ps.getD i [])

/-- Stage `j`, soundness: vanishing below `j`, the equations of degree `≥ j`. -/
def StageSound (n : ℕ) (Ps : List (GPoly α)) (j : ℕ) (B : List (List ℚ × GPoly α)) : Prop :=
  ∀ b ∈ B, b.1.length = n ∧ (∀ k < j, (GPoly.toPoly M b.2).coeff k = 0) ∧
    ∀ k, j ≤ k → (Dη M η (GPoly.toPoly M b.2)).coeff k = (polySumQ M b.1 Ps).coeff k

/-- Stage `j`, completeness: the solutions of the equations of degree `≥ j` are spanned, on the
coefficients of degree `≥ j`. -/
def StageComplete (n L : ℕ) (Ps : List (GPoly α)) (j : ℕ) (B : List (List ℚ × GPoly α)) :
    Prop :=
  ∀ c : List Cs, (∀ i, n ≤ i → c.getD i 0 = 0) → ∀ Q : K[X], Q.natDegree ≤ L →
    (∀ k, j ≤ k → (Dη M η Q).coeff k = (polySumC ι M c Ps).coeff k) →
    ∃ β : List Cs,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range B.length,
        β.getD k 0 * algebraMap ℚ Cs ((B.getD k ([], [])).1.getD i 0)) ∧
      ∀ k, j ≤ k → Q.coeff k = ∑ l ∈ Finset.range B.length,
        ι (β.getD l 0) * (GPoly.toPoly M (B.getD l ([], [])).2).coeff k

lemma coeff_polySumQ (e : List ℚ) (Ps : List (GPoly α)) (k : ℕ) :
    (polySumQ M e Ps).coeff k = ∑ i ∈ Finset.range Ps.length,
      ((e.getD i 0 : ℚ) : K) * M.sem ((Ps.getD i []).getD k O.zero) := by
  rw [polySumQ, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_C_mul, coeff_toPoly_getD']

lemma coeff_polySumC (c : List Cs) (Ps : List (GPoly α)) (k : ℕ) :
    (polySumC ι M c Ps).coeff k = ∑ i ∈ Finset.range Ps.length,
      ι (c.getD i 0) * M.sem ((Ps.getD i []).getD k O.zero) := by
  rw [polySumC, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_C_mul, coeff_toPoly_getD']

variable {M cst} (hcst : ∀ q, M.sem (cst q) = (q : K))

include hcst in
/-- The weight of a basis element in the equation of degree `j`. -/
lemma sem_weight (Ps : List (GPoly α)) (j : ℕ) (b : List ℚ × GPoly α) :
    M.sem (O.add (lcombCode O cst b.1 (Ps.map fun P ↦ P.getD j O.zero))
      (O.neg (O.mul (cst ((j : ℚ) + 1)) (O.mul (b.2.getD (j + 1) O.zero) η)))) =
      (polySumQ M b.1 Ps).coeff j -
        ((j : K) + 1) * (GPoly.toPoly M b.2).coeff (j + 1) * M.sem η := by
  rw [M.sem_add, M.sem_neg, M.sem_mul, M.sem_mul, hcst, sem_lcombCode M cst hcst,
    zipWith_sum_getD (fun (q : ℚ) (a : α) ↦ (q : K) * M.sem a) 0 O.zero (by simp),
    coeff_polySumQ, coeff_toPoly_getD', List.length_map]
  push_cast
  have e : ∑ i ∈ Finset.range Ps.length, ((b.1.getD i 0 : ℚ) : K) *
      M.sem ((Ps.map fun P ↦ P.getD j O.zero).getD i O.zero) =
      ∑ i ∈ Finset.range Ps.length, ((b.1.getD i 0 : ℚ) : K) * M.sem ((Ps.getD i []).getD j O.zero) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [NestTower.getD_map' _ _ [] O.zero (by simpa using hi)]
  rw [e]
  ring

include hcst in
/-- The polynomial of a new basis element. -/
lemma toPoly_newElem (δ : List ℚ) (B : List (List ℚ × GPoly α)) (j : ℕ) (y : α) :
    GPoly.toPoly M (GPoly.add O (lcombGP O cst δ (B.map Prod.snd)) (GPoly.monomial O j y)) =
      ∑ k ∈ Finset.range B.length,
        C ((δ.getD k 0 : ℚ) : K) * GPoly.toPoly M (B.getD k ([], [])).2 + C (M.sem y) * X ^ j := by
  rw [GPoly.toPoly_add, toPoly_lcombGP M cst hcst,
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly α) ↦ C (q : K) * GPoly.toPoly M p) 0 [] (by simp),
    List.length_map, GPoly.toPoly_monomial]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [NestTower.getD_map' _ _ ([], []) [] (by simpa using hk)]

lemma getD_vcomb (n : ℕ) (δ : List ℚ) (γs : List (List ℚ)) (i : ℕ) :
    (vcomb n δ γs).getD i 0 = if i < n then
      ∑ k ∈ Finset.range γs.length, δ.getD k 0 * (γs.getD k []).getD i 0 else 0 := by
  unfold vcomb
  split_ifs with hi
  · rw [NestTower.getD_range_map _ _ hi,
      zipWith_sum_getD (fun (d : ℚ) (γ : List ℚ) ↦ d * γ.getD i 0) 0 [] (by simp)]
  · exact List.getD_eq_default _ _ (by simpa using hi)

lemma length_vcomb (n : ℕ) (δ : List ℚ) (γs : List (List ℚ)) : (vcomb n δ γs).length = n := by
  simp [vcomb]

/-- The initial basis of the degree loop. -/
def baseB (O : COps α) (n L : ℕ) : List (List ℚ × GPoly α) :=
  ((List.range n).map fun i ↦ (unitV n i, ([] : GPoly α))) ++
    [(List.replicate n 0, GPoly.monomial O L O.one)]

lemma length_baseB (n L : ℕ) : (baseB O n L).length = n + 1 := by simp [baseB]

lemma getD_baseB (n L k : ℕ) (hk : k < n) : (baseB O n L).getD k ([], []) = (unitV n k, []) := by
  rw [baseB, List.getD_append _ _ _ _ (by simpa using hk), NestTower.getD_range_map _ _ hk]

lemma getD_baseB_last (n L : ℕ) :
    (baseB O n L).getD n ([], []) = (List.replicate n 0, GPoly.monomial O L O.one) := by
  rw [baseB, List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma getD_unitV (n i k : ℕ) : (unitV n i).getD k 0 = if k < n ∧ k = i then 1 else 0 := by
  unfold unitV
  by_cases hk : k < n
  · rw [NestTower.getD_range_map _ _ hk]
    by_cases hki : k = i
    · subst hki; simp [hk]
    · simp [hki]
  · rw [List.getD_eq_default _ _ (by simpa using hk)]
    simp [hk]

lemma toPoly_monomial_one (L : ℕ) : GPoly.toPoly M (GPoly.monomial O L O.one) = X ^ L := by
  rw [GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]

lemma coeff_toPoly_ge (p : GPoly α) {k : ℕ} (hk : p.length ≤ k) :
    (GPoly.toPoly M p).coeff k = 0 := by
  rw [coeff_toPoly_getD', List.getD_eq_default _ _ hk, M.sem_zero]

lemma coeff_polySumQ_ge (e : List ℚ) (Ps : List (GPoly α)) {k : ℕ}
    (hk : ∀ i, (Ps.getD i []).length ≤ k) : (polySumQ M e Ps).coeff k = 0 := by
  rw [coeff_polySumQ]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [List.getD_eq_default _ _ (hk i), M.sem_zero, mul_zero]

lemma coeff_polySumC_ge (c : List Cs) (Ps : List (GPoly α)) {k : ℕ}
    (hk : ∀ i, (Ps.getD i []).length ≤ k) : (polySumC ι M c Ps).coeff k = 0 := by
  rw [coeff_polySumC]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [List.getD_eq_default _ _ (hk i), M.sem_zero, mul_zero]

lemma coeff_Dη_X_pow (L k : ℕ) (hk : L ≤ k) : (Dη M η (X ^ L : K[X])).coeff k = 0 := by
  rw [Dη, coeff_implicitDeriv_C, coeff_X_pow, coeff_X_pow, if_neg (show ¬(k + 1 = L) by omega)]
  split_ifs <;> simp

omit hcst in
/-- **The initial stage is sound.** -/
lemma baseB_sound (Ps : List (GPoly α)) (L : ℕ) (hL : ∀ i, (Ps.getD i []).length ≤ L) :
    StageSound M η Ps.length Ps L (baseB O Ps.length L) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    refine ⟨by simp [unitV], fun k _ ↦ by simp, fun k hk ↦ ?_⟩
    rw [coeff_polySumQ_ge (M := M) _ _ fun i' ↦ (hL i').trans hk]
    simp [Dη]
  · simp at hb
    subst hb
    refine ⟨by simp, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · rw [toPoly_monomial_one, coeff_X_pow, if_neg (by omega)]
    · rw [toPoly_monomial_one, coeff_Dη_X_pow η L k hk,
        coeff_polySumQ_ge (M := M) _ _ fun i' ↦ (hL i').trans hk]

omit hcst in
/-- **The initial stage is complete.** -/
lemma baseB_complete (Ps : List (GPoly α)) (L : ℕ) (hL : ∀ i, (Ps.getD i []).length ≤ L)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    StageComplete ι M η Ps.length L Ps L (baseB O Ps.length L) := by
  intro c hc Q hQdeg heq
  have hL' := heq L le_rfl
  rw [coeff_polySumC_ge ι _ _ fun i ↦ hL i, Dη, coeff_implicitDeriv_C,
    coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < L + 1), zero_mul, mul_zero,
    add_zero] at hL'
  obtain ⟨κ, hκ⟩ := hconstK _ hL'
  set n := Ps.length with hn
  have hβk : ∀ k < n, (((List.range n).map fun i ↦ c.getD i 0) ++ [κ]).getD k 0 = c.getD k 0 :=
    fun k hk ↦ by
      rw [List.getD_append _ _ _ _ (by simpa using hk), NestTower.getD_range_map _ _ hk]
  have hβn : (((List.range n).map fun i ↦ c.getD i 0) ++ [κ]).getD n 0 = κ := by
    rw [List.getD_append_right _ _ _ _ (by simp)]; simp
  refine ⟨((List.range n).map fun i ↦ c.getD i 0) ++ [κ], fun i ↦ ?_, fun k hk ↦ ?_⟩
  · rw [length_baseB, Finset.sum_range_succ, getD_baseB_last, hβn]
    have hrep : (List.replicate n (0 : ℚ)).getD i 0 = 0 := by
      by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
      · exact List.getD_eq_default _ _ (by simpa using hi)
    rw [hrep, map_zero, mul_zero, add_zero]
    have e : ∀ k ∈ Finset.range n, (((List.range n).map fun i ↦ c.getD i 0) ++ [κ]).getD k 0 *
        algebraMap ℚ Cs (((baseB O n L).getD k ([], [])).1.getD i 0) =
        if i = k then (if i < n then c.getD i 0 else 0) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [hβk k hk', getD_baseB n L k hk', getD_unitV]
      by_cases hik : i = k
      · subst hik; simp [hk']
      · simp [hik]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
    by_cases hi : i < n
    · simp [hi]
    · have := hc i (by omega)
      simp only [List.getD_eq_getElem?_getD] at this
      simp [hi, this]
  · rw [length_baseB, Finset.sum_range_succ, getD_baseB_last, hβn, toPoly_monomial_one,
      coeff_X_pow]
    have e : ∀ l ∈ Finset.range n, ι ((((List.range n).map fun i ↦ c.getD i 0) ++ [κ]).getD l 0) *
        (GPoly.toPoly M ((baseB O n L).getD l ([], [])).2).coeff k = 0 := by
      intro l hl
      rw [getD_baseB n L l (Finset.mem_range.mp hl)]
      simp
    rw [Finset.sum_eq_zero e, zero_add]
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · simp [hκ]
    · rw [if_neg (by omega), mul_zero, coeff_eq_zero_of_natDegree_lt (by omega)]

omit [CharZero Cs] in
lemma deriv_ratCastK (q : ℚ) : ((q : K))′ = 0 := by
  have hd : ((q.den : ℤ) : K) ≠ 0 := by exact_mod_cast q.den_nz
  have e : (q : K) * ((q.den : ℤ) : K) = ((q.num : ℤ) : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_intCast, ← Rat.cast_mul]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num q
  have := congrArg (fun z : K ↦ z′) e
  simp only [Derivation.leibniz, Derivation.map_intCast, smul_eq_mul, mul_zero, zero_add] at this
  exact (mul_eq_zero.mp this).resolve_left hd

omit hcst in
lemma coeff_polySumQ_vcomb (Ps : List (GPoly α)) (δ : List ℚ) (γs : List (List ℚ)) (k : ℕ) :
    (polySumQ M (vcomb Ps.length δ γs) Ps).coeff k =
      ∑ l ∈ Finset.range γs.length, ((δ.getD l 0 : ℚ) : K) * (polySumQ M (γs.getD l []) Ps).coeff k := by
  simp only [coeff_polySumQ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi)]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

omit hcst in
lemma coeff_Dη (P : K[X]) (k : ℕ) :
    (Dη M η P).coeff k = (P.coeff k)′ + M.sem η * (P.coeff (k + 1) * (k + 1)) :=
  coeff_implicitDeriv_C (M.sem η) P k

include hcst in
/-- **The step of the degree loop is sound.** -/
lemma polyStep_sound (hlim : ∀ ws, ∀ r ∈ lim ws, (M.sem r.2)′ = sQ M r.1 ws)
    (Ps : List (GPoly α)) (j : ℕ) (B : List (List ℚ × GPoly α))
    (hB : StageSound M η Ps.length Ps (j + 1) B) :
    StageSound M η Ps.length Ps j (polyStep O cst η lim Ps.length Ps j B) := by
  intro b hb
  unfold polyStep at hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    have hy := hlim _ r hr
    have hcoef : ∀ m, (GPoly.toPoly M (GPoly.add O (lcombGP O cst r.1 (B.map Prod.snd))
        (GPoly.monomial O j r.2))).coeff m = ∑ l ∈ Finset.range B.length,
          ((r.1.getD l 0 : ℚ) : K) * (GPoly.toPoly M (B.getD l ([], [])).2).coeff m +
            if m = j then M.sem r.2 else 0 := fun m ↦ by
      rw [toPoly_newElem hcst, coeff_add, finset_sum_coeff, coeff_C_mul_X_pow]
      simp only [coeff_C_mul]
    have hBl : ∀ l < B.length, B.getD l ([], []) ∈ B := fun l hl ↦ by
      rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
    refine ⟨length_vcomb _ _ _, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · rw [hcoef, if_neg (by omega), add_zero]
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      rw [(hB _ (hBl l (Finset.mem_range.mp hl))).2.1 k (by omega), mul_zero]
    · rw [coeff_Dη, hcoef, hcoef, if_neg (show ¬(k + 1 = j) by omega),
        coeff_polySumQ_vcomb, List.length_map]
      simp only [add_zero, map_add, map_sum, Derivation.leibniz, deriv_ratCastK, smul_eq_mul,
        mul_zero, add_zero]
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · rw [if_pos rfl, hy, sQ, List.length_map]
        have e1 : ∀ l ∈ Finset.range B.length, ((r.1.getD l 0 : ℚ) : K) *
            ((GPoly.toPoly M (B.getD l ([], [])).2).coeff j)′ = 0 := fun l hl ↦ by
          rw [(hB _ (hBl l (Finset.mem_range.mp hl))).2.1 j (by omega), map_zero, mul_zero]
        rw [Finset.sum_eq_zero e1, zero_add, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [NestTower.getD_map' _ _ ([], []) O.zero (Finset.mem_range.mp hl), sem_weight η hcst,
          NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl)]
        ring
      · rw [if_neg (by omega), map_zero, add_zero, Finset.sum_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        have := (hB _ (hBl l (Finset.mem_range.mp hl))).2.2 k (by omega)
        rw [coeff_Dη] at this
        rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl), ← this]
        ring
  · simp at hb
    subst hb
    refine ⟨by simp, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · rw [toPoly_monomial_one, coeff_X_pow, if_neg (by omega)]
    · rw [toPoly_monomial_one, coeff_Dη_X_pow η j k hk, coeff_polySumQ]
      refine (Finset.sum_eq_zero fun i hi ↦ ?_).symm
      have : (List.replicate Ps.length (0 : ℚ)).getD i 0 = 0 := by
        rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hi)]; simp
      rw [this]; simp

include hcst in
lemma coeff_newElem (δ : List ℚ) (B : List (List ℚ × GPoly α)) (j : ℕ) (y : α) (m : ℕ) :
    (GPoly.toPoly M (GPoly.add O (lcombGP O cst δ (B.map Prod.snd))
      (GPoly.monomial O j y))).coeff m = ∑ l ∈ Finset.range B.length,
        ((δ.getD l 0 : ℚ) : K) * (GPoly.toPoly M (B.getD l ([], [])).2).coeff m +
          if m = j then M.sem y else 0 := by
  rw [toPoly_newElem hcst, coeff_add, finset_sum_coeff, coeff_C_mul_X_pow]
  simp only [coeff_C_mul]

lemma getD_polyStep_lt (n : ℕ) (Ps : List (GPoly α)) (j : ℕ) (B : List (List ℚ × GPoly α))
    (m : ℕ) (hm : m < (lim (B.map fun b ↦ O.add (lcombCode O cst b.1 (Ps.map fun P ↦
      P.getD j O.zero)) (O.neg (O.mul (cst ((j : ℚ) + 1)) (O.mul (b.2.getD (j + 1) O.zero)
        η))))).length) :
    (polyStep O cst η lim n Ps j B).getD m ([], []) =
      let r := (lim (B.map fun b ↦ O.add (lcombCode O cst b.1 (Ps.map fun P ↦
        P.getD j O.zero)) (O.neg (O.mul (cst ((j : ℚ) + 1)) (O.mul (b.2.getD (j + 1) O.zero)
          η))))).getD m ([], O.zero)
      (vcomb n r.1 (B.map Prod.fst),
        GPoly.add O (lcombGP O cst r.1 (B.map Prod.snd)) (GPoly.monomial O j r.2)) := by
  unfold polyStep
  simp only
  rw [List.getD_append _ _ _ _ (by simpa using hm), NestTower.getD_map' _ _ ([], O.zero) _ hm]

lemma getD_polyStep_last (n : ℕ) (Ps : List (GPoly α)) (j : ℕ) (B : List (List ℚ × GPoly α)) :
    (polyStep O cst η lim n Ps j B).getD (lim (B.map fun b ↦ O.add (lcombCode O cst b.1
      (Ps.map fun P ↦ P.getD j O.zero)) (O.neg (O.mul (cst ((j : ℚ) + 1))
        (O.mul (b.2.getD (j + 1) O.zero) η))))).length ([], []) =
      (List.replicate n 0, GPoly.monomial O j O.one) := by
  unfold polyStep
  simp only
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma length_polyStep (n : ℕ) (Ps : List (GPoly α)) (j : ℕ) (B : List (List ℚ × GPoly α)) :
    (polyStep O cst η lim n Ps j B).length = (lim (B.map fun b ↦ O.add (lcombCode O cst b.1
      (Ps.map fun P ↦ P.getD j O.zero)) (O.neg (O.mul (cst ((j : ℚ) + 1))
        (O.mul (b.2.getD (j + 1) O.zero) η))))).length + 1 := by
  simp [polyStep]

include hcst in
/-- **The step of the degree loop is complete.** -/
lemma polyStep_complete (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))
    (Ps : List (GPoly α)) (L j : ℕ) (B : List (List ℚ × GPoly α))
    (hBs : StageSound M η Ps.length Ps (j + 1) B)
    (hBc : StageComplete ι M η Ps.length L Ps (j + 1) B) :
    StageComplete ι M η Ps.length L Ps j (polyStep O cst η lim Ps.length Ps j B) := by
  intro c hc Q hQdeg heq
  obtain ⟨β, hβc, hβQ⟩ := hBc c hc Q hQdeg (fun k hk ↦ heq k (by omega))
  set n := Ps.length with hn
  set ws := B.map fun b ↦ O.add (lcombCode O cst b.1 (Ps.map fun P ↦ P.getD j O.zero))
    (O.neg (O.mul (cst ((j : ℚ) + 1)) (O.mul (b.2.getD (j + 1) O.zero) η))) with hws
  set R := lim ws with hR
  set βt := (List.range B.length).map fun l ↦ β.getD l 0 with hβt
  have hβtD : ∀ l < B.length, βt.getD l 0 = β.getD l 0 := fun l hl ↦
    NestTower.getD_range_map _ _ hl
  have hBl : ∀ l < B.length, B.getD l ([], []) ∈ B := fun l hl ↦ by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
  have hιc : ∀ i, ι (c.getD i 0) = ∑ l ∈ Finset.range B.length,
      ι (β.getD l 0) * (((B.getD l ([], [])).1.getD i 0 : ℚ) : K) := fun i ↦ by
    rw [hβc i, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, hιrat]
  -- the equation of degree `j`
  have hz : (Q.coeff j)′ = sC ι M βt ws := by
    have h1 := heq j le_rfl
    rw [coeff_Dη, coeff_polySumC, hβQ (j + 1) le_rfl] at h1
    rw [sC, List.length_map]
    have e : ∀ l ∈ Finset.range B.length, ι (βt.getD l 0) * M.sem (ws.getD l O.zero) =
        ι (β.getD l 0) * ((polySumQ M (B.getD l ([], [])).1 Ps).coeff j -
          ((j : K) + 1) * (GPoly.toPoly M (B.getD l ([], [])).2).coeff (j + 1) * M.sem η) := by
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [hβtD l hl', hws, NestTower.getD_map' _ _ ([], []) O.zero hl', sem_weight η hcst]
    rw [Finset.sum_congr rfl e]
    simp only [coeff_polySumQ, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∑ i ∈ Finset.range Ps.length, ∑ l ∈ Finset.range B.length, ι (β.getD l 0) *
        ((((B.getD l ([], [])).1.getD i 0 : ℚ) : K) * M.sem ((Ps.getD i []).getD j O.zero)) =
        ∑ i ∈ Finset.range Ps.length, ι (c.getD i 0) * M.sem ((Ps.getD i []).getD j O.zero) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hιc i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      ring
    rw [e2]
    have e3 : ∑ l ∈ Finset.range B.length, ι (β.getD l 0) *
        (((j : K) + 1) * (GPoly.toPoly M (B.getD l ([], [])).2).coeff (j + 1) * M.sem η) =
        M.sem η * ((∑ l ∈ Finset.range B.length, ι (β.getD l 0) *
          (GPoly.toPoly M (B.getD l ([], [])).2).coeff (j + 1)) * ((j : K) + 1)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      ring
    rw [e3]
    push_cast at h1
    linear_combination h1
  obtain ⟨ε, hεβ, hεz⟩ := hspec.complete ws βt (fun i hi ↦ by
    rw [List.length_map] at hi
    exact List.getD_eq_default _ _ (by rw [hβt, List.length_map, List.length_range]; exact hi))
    (Q.coeff j) hz
  obtain ⟨κ, hκ⟩ := hconstK _ hεz
  have hlen := length_polyStep (O := O) (cst := cst) (η := η) (lim := lim) n Ps j B
  rw [← hws, ← hR] at hlen
  set β'' := ((List.range R.length).map fun m ↦ ε.getD m 0) ++ [κ] with hβ''
  have hβ''m : ∀ m < R.length, β''.getD m 0 = ε.getD m 0 := fun m hm ↦ by
    rw [hβ'', List.getD_append _ _ _ _ (by simpa using hm), NestTower.getD_range_map _ _ hm]
  have hβ''last : β''.getD R.length 0 = κ := by
    rw [hβ'', List.getD_append_right _ _ _ _ (by simp)]; simp
  -- `β` in terms of `ε`
  have hβε : ∀ l < B.length, β.getD l 0 = ∑ m ∈ Finset.range R.length,
      ε.getD m 0 * algebraMap ℚ Cs ((R.getD m ([], O.zero)).1.getD l 0) := fun l hl ↦ by
    rw [← hβtD l hl, hεβ l]
  refine ⟨β'', fun i ↦ ?_, fun k hk ↦ ?_⟩
  · rw [hlen, Finset.sum_range_succ, hβ''last,
      show R.length = (lim ws).length from rfl, getD_polyStep_last (η := η) (lim := lim) n Ps j B]
    have hrep : (List.replicate n (0 : ℚ)).getD i 0 = 0 := by
      by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
      · exact List.getD_eq_default _ _ (by simpa using hi)
    rw [hrep, map_zero, mul_zero, add_zero]
    have e : ∀ m ∈ Finset.range R.length, β''.getD m 0 *
        algebraMap ℚ Cs (((polyStep O cst η lim n Ps j B).getD m ([], [])).1.getD i 0) =
        ε.getD m 0 * algebraMap ℚ Cs ((vcomb n (R.getD m ([], O.zero)).1 (B.map Prod.fst)).getD i 0) :=
      fun m hm ↦ by
        rw [hβ''m m (Finset.mem_range.mp hm), getD_polyStep_lt (η := η) (lim := lim) n Ps j B m (Finset.mem_range.mp hm)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · rw [hβc i]
      simp only [getD_vcomb, if_pos hi, List.length_map, map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [hβε l (Finset.mem_range.mp hl), Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl)]
      ring
    · rw [hc i (by omega)]
      symm
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      rw [getD_vcomb, if_neg hi, map_zero, mul_zero]
  · rw [hlen, Finset.sum_range_succ, hβ''last,
      show R.length = (lim ws).length from rfl, getD_polyStep_last (η := η) (lim := lim) n Ps j B,
      toPoly_monomial_one, coeff_X_pow]
    have e : ∀ m ∈ Finset.range R.length, ι (β''.getD m 0) *
        (GPoly.toPoly M ((polyStep O cst η lim n Ps j B).getD m ([], [])).2).coeff k =
        ι (ε.getD m 0) * (∑ l ∈ Finset.range B.length, (((R.getD m ([], O.zero)).1.getD l 0 : ℚ) : K) *
          (GPoly.toPoly M (B.getD l ([], [])).2).coeff k +
            if k = j then M.sem (R.getD m ([], O.zero)).2 else 0) := fun m hm ↦ by
      rw [hβ''m m (Finset.mem_range.mp hm), getD_polyStep_lt (η := η) (lim := lim) n Ps j B m (Finset.mem_range.mp hm)]
      simp only
      rw [coeff_newElem hcst]
    rw [Finset.sum_congr rfl e]
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · -- the coefficient of degree `j`
      have hzero : ∀ l < B.length, (GPoly.toPoly M (B.getD l ([], [])).2).coeff j = 0 :=
        fun l hl ↦ (hBs _ (hBl l hl)).2.1 j (by omega)
      simp only [if_true, mul_one]
      have e2 : ∀ m ∈ Finset.range R.length, ι (ε.getD m 0) *
          (∑ l ∈ Finset.range B.length, (((R.getD m ([], O.zero)).1.getD l 0 : ℚ) : K) *
            (GPoly.toPoly M (B.getD l ([], [])).2).coeff j + M.sem (R.getD m ([], O.zero)).2) =
          ι (ε.getD m 0) * M.sem (R.getD m ([], O.zero)).2 := fun m _ ↦ by
        rw [Finset.sum_eq_zero fun l hl ↦ by rw [hzero l (Finset.mem_range.mp hl), mul_zero],
          zero_add]
      rw [Finset.sum_congr rfl e2]
      linear_combination hκ
    · simp only [if_neg (show ¬(k = j) by omega), add_zero, mul_zero]
      rw [hβQ k (by omega)]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [hβε l (Finset.mem_range.mp hl), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [map_mul, hιrat]
      ring

include hcst in
lemma polyLoop_stage (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (Ps : List (GPoly α)) (L : ℕ) :
    ∀ (j : ℕ) (B : List (List ℚ × GPoly α)), StageSound M η Ps.length Ps j B →
      StageComplete ι M η Ps.length L Ps j B →
      StageSound M η Ps.length Ps 0 (polyLoop O cst η lim Ps.length Ps j B) ∧
        StageComplete ι M η Ps.length L Ps 0 (polyLoop O cst η lim Ps.length Ps j B)
  | 0, B, hs, hc => ⟨hs, hc⟩
  | j + 1, B, hs, hc =>
    polyLoop_stage hspec hconstK hιrat Ps L j _
      (polyStep_sound η lim hcst hspec.sound Ps j B hs)
      (polyStep_complete ι η lim hcst hspec hconstK hιrat Ps L j B hs hc)

lemma length_le_maxLen (Ps : List (GPoly α)) (i : ℕ) :
    (Ps.getD i []).length ≤ (Ps.map List.length).foldr max 0 := by
  by_cases hi : i < Ps.length
  · exact le_foldr_max _ _ (List.mem_map.mpr ⟨_, by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _, rfl⟩)
  · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _

lemma paramPoly_eq (Ps : List (GPoly α)) :
    paramPoly O cst η lim Ps = polyLoop O cst η lim Ps.length Ps ((Ps.map List.length).foldr max 0)
      (baseB O Ps.length ((Ps.map List.length).foldr max 0)) := rfl

include hcst in
/-- **Soundness of the parametric polynomial problem.** -/
theorem paramPoly_sound (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (Ps : List (GPoly α)) :
    ∀ r ∈ paramPoly O cst η lim Ps, Dη M η (GPoly.toPoly M r.2) = polySumQ M r.1 Ps := by
  intro r hr
  rw [paramPoly_eq] at hr
  have := (polyLoop_stage ι η lim hcst hspec hconstK hιrat Ps _ _ _
    (baseB_sound η Ps _ (length_le_maxLen Ps))
    (baseB_complete ι η Ps _ (length_le_maxLen Ps) hconstK hιrat)).1 r hr
  exact Polynomial.ext fun k ↦ this.2.2 k (Nat.zero_le k)

include hcst in
/-- **Completeness of the parametric polynomial problem.** -/
theorem paramPoly_complete (hspec : LimSpec ι M lim)
    (hconstK : ∀ y : K, y′ = 0 → ∃ κ : Cs, y = ι κ)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (hη : ∀ y : K, y′ ≠ M.sem η)
    (Ps : List (GPoly α)) (c : List Cs) (hc : ∀ i, Ps.length ≤ i → c.getD i 0 = 0) (Q : K[X])
    (hQ : Dη M η Q = polySumC ι M c Ps) :
    ∃ β : List Cs,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (paramPoly O cst η lim Ps).length,
        β.getD k 0 * algebraMap ℚ Cs (((paramPoly O cst η lim Ps).getD k ([], [])).1.getD i 0)) ∧
      Q = ∑ k ∈ Finset.range (paramPoly O cst η lim Ps).length,
        C (ι (β.getD k 0)) * GPoly.toPoly M ((paramPoly O cst η lim Ps).getD k ([], [])).2 := by
  set L := (Ps.map List.length).foldr max 0 with hL
  have hconst : ∀ P : K[X], implicitDeriv (C (M.sem η)) P = 0 → ∃ e : K, P = C e :=
    fun P hP ↦ const_of_implicitDeriv_eq_zero (M.sem η) hη hP
  -- the degree bound
  have hdeg : Q.natDegree ≤ L := by
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · have h0 : polySumC ι M c Ps = 0 := by
        refine Polynomial.ext fun k ↦ ?_
        rw [coeff_polySumC_ge ι _ _ fun i ↦ (length_le_maxLen Ps i).trans (by omega)]
        simp
      rw [h0] at hQ
      obtain ⟨e, rfl⟩ := hconst Q hQ
      simp
    · have hd : (Dη M η Q).natDegree ≤ L - 1 := by
        rw [hQ, natDegree_le_iff_coeff_eq_zero]
        intro k hk
        exact coeff_polySumC_ge ι _ _ fun i ↦ (length_le_maxLen Ps i).trans (by omega)
      have := natDegree_le_succ_of_natDegree_deriv_le (M.sem η) hconst hd
      omega
  obtain ⟨-, hcomp⟩ := polyLoop_stage ι η lim hcst hspec hconstK hιrat Ps L L _
    (baseB_sound η Ps L (length_le_maxLen Ps))
    (baseB_complete ι η Ps L (length_le_maxLen Ps) hconstK hιrat)
  obtain ⟨β, hβ, hβQ⟩ := hcomp c hc Q hdeg fun k _ ↦ by rw [hQ]
  refine ⟨β, hβ, Polynomial.ext fun k ↦ ?_⟩
  rw [hβQ k (Nat.zero_le k), finset_sum_coeff]
  simp only [coeff_C_mul]
  rfl

end Generic








end Tower.NestP
