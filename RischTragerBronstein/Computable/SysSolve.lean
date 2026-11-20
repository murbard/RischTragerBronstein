import RischTragerBronstein.Computable.SysRel

/-!
# Coupled Risch systems: polynomial solutions with a degree bound

`polySysC` runs the coefficient loop (`loopC`) from the degree bound down, then keeps the constant
combinations of the resulting basis whose residuals vanish identically, coordinate by coordinate
(`relRun`). `polySysC_sound`: every output solves `A Y′ + B Y = ∑ eₗ Cₗ`; `polySysC_complete`:
every polynomial solution within the degree bound, with constant coefficients, is a constant
combination of the outputs.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

open Tower.NestM Tower.NestP

lemma le_foldr_max (l : List ℕ) : ∀ a ∈ l, a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · exact (ih a ha).trans (by simp)

section Codes

variable {α : Type} (O : COps α) {n : ℕ} (w0 b : α) (A B : Fin n → Fin n → GPoly α)
  (cst : ℚ → α) (Cl : List (Fin n → GPoly α)) (δ : ℕ)

/-- The residual vectors of a basis (computed as data). -/
def residsC (Bs : List (List ℚ × (Fin n → GPoly α))) : List (Fin n → GPoly α) :=
  (Bs.map fun bb ↦ matL fun i ↦ resQVC O w0 b A B cst Cl bb.1 bb.2 i).map fun l ↦ listFn l []

lemma residsC_eq (Bs : List (List ℚ × (Fin n → GPoly α))) :
    residsC O w0 b A B cst Cl Bs = Bs.map fun bb i ↦ resQVC O w0 b A B cst Cl bb.1 bb.2 i := by
  rw [residsC, List.map_map]
  exact List.map_congr_left fun bb _ ↦ by simp only [Function.comp_apply, listFn_matL]

/-- A bound on the lengths of the residual codes. -/
def residLen (Rs : List (Fin n → GPoly α)) : ℕ :=
  (Rs.flatMap fun r ↦ (List.finRange n).map fun i ↦ (r i).length).foldr max 0

/-- Coordinate `x = i Qd + d`: the coefficients of degree `d` of the entries `i`. -/
def residVals (Rs : List (Fin n → GPoly α)) (Qd x : ℕ) : List α :=
  if h : x / Qd < n then Rs.map fun r ↦ (r ⟨x / Qd, h⟩).getD (x % Qd) O.zero
  else Rs.map fun _ ↦ O.zero

/-- **Polynomial solutions of a system** within `N` coefficient steps. -/
def polySysC (alg : Bool) (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (rel : List α → List (List ℚ)) (N : ℕ) : List (List ℚ × (Fin n → GPoly α)) :=
  let Bs := loopC O w0 b A B cst Cl δ alg PA PB lowerC N (initC Cl.length)
  let Rs := residsC O w0 b A B cst Cl Bs
  let Qd := residLen Rs
  let U := relRun O cst rel Bs.length (residVals O Rs Qd) (n * Qd)
  U.map fun u ↦ (vcomb Cl.length u (Bs.map Prod.fst), vecM fun i ↦
    sumC O (List.range Bs.length) fun l ↦
      GPoly.smul O (cst (u.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i))

end Codes

section Sem

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {O : COps α} (M : CField α K O) {n : ℕ} (w0 b : α)
  (A B : Fin n → Fin n → GPoly α) (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = q)
  (Cl : List (Fin n → GPoly α)) (δ : ℕ)

lemma residVals_length (Rs : List (Fin n → GPoly α)) (Qd x : ℕ) :
    (residVals O Rs Qd x).length = Rs.length := by
  unfold residVals; split_ifs <;> simp

lemma residVals_getD (Rs : List (Fin n → GPoly α)) (Qd : ℕ) (hQ : 0 < Qd) (i : Fin n) (d : ℕ)
    (hd : d < Qd) (k : ℕ) (hk : k < Rs.length) :
    (residVals O Rs Qd (i * Qd + d)).getD k O.zero = ((Rs.getD k fun _ ↦ []) i).getD d O.zero := by
  have h1 : (i * Qd + d) / Qd = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hd, zero_add]
  have h2 : (i * Qd + d) % Qd = d := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
  unfold residVals
  rw [dif_pos (by rw [h1]; exact i.2), NestTower.getD_map' _ _ (fun _ ↦ []) _ hk]
  simp only [h1, h2]

lemma residVals_getD' (Rs : List (Fin n → GPoly α)) (Qd x : ℕ) (i : Fin n) (hi : x / Qd = i)
    (k : ℕ) (hk : k < Rs.length) :
    (residVals O Rs Qd x).getD k O.zero = ((Rs.getD k fun _ ↦ []) i).getD (x % Qd) O.zero := by
  unfold residVals
  rw [dif_pos (by rw [hi]; exact i.2), NestTower.getD_map' _ _ (fun _ ↦ []) _ hk]
  simp only [show (⟨x / Qd, by rw [hi]; exact i.2⟩ : Fin n) = i from Fin.ext hi]

lemma LopV_zero' (w0 b : K) (A B : Fin n → Fin n → K[X]) : LopV w0 b A B 0 = 0 := by
  funext i; simp [LopV, DzL]

include hcst in
/-- **Soundness**: every output solves the system exactly. -/
theorem polySysC_sound (alg : Bool) (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (rel : List α → List (List ℚ)) (hrel : RelSpec ι M rel)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (N : ℕ) :
    ∀ r ∈ polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel N,
      resQV (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) r.1 (semV M r.2) = 0 := by
  intro r hr
  simp only [polySysC] at hr
  set Bs := loopC O w0 b A B cst Cl δ alg PA PB lowerC N (initC Cl.length) with hBs
  set Rs := residsC O w0 b A B cst Cl Bs with hRs
  set Qd := residLen Rs with hQd
  set U := relRun O cst rel Bs.length (residVals O Rs Qd) (n * Qd) with hU
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  have hinv := (relRun_inv ι M cst hcst rel Bs.length (residVals O Rs Qd) hrel
    (fun x ↦ by rw [residVals_length, hRs, residsC_eq, List.length_map]) hιrat (n * Qd)).1 u hu
  have hRsD : ∀ k < Bs.length, ∀ i, (Rs.getD k fun _ ↦ []) i =
      resQVC O w0 b A B cst Cl (Bs.getD k ([], fun _ ↦ [])).1 (Bs.getD k ([], fun _ ↦ [])).2 i :=
    fun k hk i ↦ by
      rw [hRs, residsC_eq, NestTower.getD_map' _ _ ([], fun _ ↦ []) _ hk]
  have hlenQ : ∀ k < Bs.length, ∀ i, ((Rs.getD k fun _ ↦ []) i).length ≤ Qd := fun k hk i ↦ by
    refine le_foldr_max _ _ (List.mem_flatMap.mpr ⟨Rs.getD k fun _ ↦ [], ?_, ?_⟩)
    · rw [List.getD_eq_getElem _ _ (by simpa [hRs, residsC_eq] using hk)]; exact List.getElem_mem _
    · exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  -- the semantic combination
  have hW : semV M (vecM fun i ↦ sumC O (List.range Bs.length) fun l ↦
      GPoly.smul O (cst (u.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i)) =
      (fun i ↦ ∑ l ∈ Finset.range (semBs M Bs).length, C ((u.getD l 0 : ℚ) : K) *
        ((semBs M Bs).getD l ([], 0)).2 i) + 0 := by
    funext i
    simp only [semV, vecM_eq, toPoly_sumC_range, GPoly.toPoly_smul, hcst, semBs, List.length_map,
      Pi.add_apply, Pi.zero_apply, add_zero]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [NestTower.getD_map' _ _ ([], fun _ ↦ []) _ (Finset.mem_range.mp hl)]
    rfl
  have hfst : Bs.map Prod.fst = (semBs M Bs).map Prod.fst := by
    simp only [semBs, List.map_map]; rfl
  simp only
  rw [hW, hfst, show Cl.length = (Cl.map (semV M)).length from (List.length_map _).symm,
    resQV_comb, LopV_zero', add_zero]
  funext i
  ext d
  simp only [finsetSum_coeff, coeff_C_mul, Pi.zero_apply, coeff_zero, semBs, List.length_map]
  have e1 : ∀ l ∈ Finset.range Bs.length, ((u.getD l 0 : ℚ) : K) * (resQV (M.sem w0) (M.sem b)
      (semPM M A) (semPM M B) (Cl.map (semV M)) ((Bs.map fun bb ↦ (bb.1, semV M bb.2)).getD l
        ([], 0)).1 ((Bs.map fun bb ↦ (bb.1, semV M bb.2)).getD l ([], 0)).2 i).coeff d =
      ((u.getD l 0 : ℚ) : K) * M.sem (((Rs.getD l fun _ ↦ []) i).getD d O.zero) := fun l hl ↦ by
    rw [NestTower.getD_map' _ _ ([], fun _ ↦ []) _ (Finset.mem_range.mp hl), hRsD l
      (Finset.mem_range.mp hl) i, ← coeff_toPoly_sem, toPoly_resQVC M w0 b A B cst hcst]
  rw [Finset.sum_congr rfl e1]
  by_cases hdQ : d < Qd
  · have hQ : 0 < Qd := by omega
    have hx : (i : ℕ) * Qd + d < n * Qd := by nlinarith [i.2]
    have := hinv (i * Qd + d) hx
    rw [← this]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [residVals_getD Rs Qd hQ i d hdQ l (by simpa [hRs, residsC_eq] using Finset.mem_range.mp hl)]
  · refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [List.getD_eq_default _ _ ((hlenQ l (Finset.mem_range.mp hl) i).trans (by omega)),
      M.sem_zero, mul_zero]

include hcst in
/-- **Completeness**: every polynomial solution within the degree bound is a constant combination
of the outputs. -/
theorem polySysC_complete (hιd : ∀ κ : Cs, (ι κ)′ = 0)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))
    (hA : ∀ i j, (semPM M A i j).natDegree ≤ δ)
    (hB : ∀ i j, (semPM M B i j).natDegree ≤ δ) (alg : Bool) (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (halg : alg = true → (∀ i j, (semPM M A i j).coeff δ = 0) ∧
      (∀ v, mv (fun i j ↦ (semPM M B i j).coeff δ) (mv (fun i j ↦ M.sem (PB i j)) v) = v) ∧
      (∀ v, mv (fun i j ↦ M.sem (PB i j)) (mv (fun i j ↦ (semPM M B i j).coeff δ) v) = v))
    (hdiff : alg = false →
      (∀ v, mv (fun i j ↦ (semPM M A i j).coeff δ) (mv (fun i j ↦ M.sem (PA i j)) v) = v) ∧
      (∀ v, mv (fun i j ↦ M.sem (PA i j)) (mv (fun i j ↦ (semPM M A i j).coeff δ) v) = v) ∧
      ∀ k : ℕ, ∃ F : Fin n → Fin n → K, (∀ z : Fin n → K, ∀ i,
        ∑ j, ((semPM M A i j).coeff δ * ((z j)′ + k * M.sem b * z j) +
          (semPM M B i j).coeff δ * z j) =
          ∑ j, (semPM M A i j).coeff δ * ((z j)′ + mv F z j)) ∧
        ∀ wsC, SysSpecAt ι F (wsC.map (semVa M)) (semR M (lowerC k wsC)))
    (rel : List α → List (List ℚ)) (hrel : RelSpec ι M rel) (N : ℕ)
    (hC : ∀ l < Cl.length, ∀ i, (semV M (Cl.getD l fun _ ↦ []) i).natDegree ≤ N + δ)
    (c : List Cs) (hc : ∀ l, Cl.length ≤ l → c.getD l 0 = 0) (Y : Fin n → K[X])
    (hY : ∀ i, (Y i).natDegree ≤ N)
    (hsol : resCV (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) ι c Y = 0) :
    ∃ β : List Cs,
      (∀ l, c.getD l 0 = ∑ k ∈ Finset.range
          (polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).length,
        β.getD k 0 * algebraMap ℚ Cs
          (((polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).getD k
            ([], fun _ ↦ [])).1.getD l 0)) ∧
      ∀ i, Y i = ∑ k ∈ Finset.range (polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).length,
        C (ι (β.getD k 0)) * semV M ((polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).getD k
          ([], fun _ ↦ [])).2 i := by
  classical
  set ClS := Cl.map (semV M) with hClS
  have hClen : ClS.length = Cl.length := List.length_map _
  set Bs := loopC O w0 b A B cst Cl δ alg PA PB lowerC (N + 1) (initC Cl.length) with hBs
  have hs0 : SStageSound (M.sem w0) (M.sem b) (semPM M A) (semPM M B) ClS δ (N + 1)
      (semBs M (initC Cl.length)) := by
    rw [semBs_initC, ← hClen]
    exact sInit_sound _ _ _ _ _ δ N fun l hl i ↦ by
      rw [hClS, getD_semCl]; exact hC l (by omega) i
  have hc0 : SStageComplete (M.sem w0) (M.sem b) (semPM M A) (semPM M B) ClS δ ι N (N + 1)
      (semBs M (initC Cl.length)) := by
    rw [semBs_initC, ← hClen]
    exact sInit_complete _ _ _ _ _ δ ι N
  obtain ⟨-, hcomp⟩ := loopC_stage M w0 b A B cst hcst Cl δ ι hιd hιrat hA hB alg PA PB lowerC
    halg hdiff N (N + 1) (initC Cl.length) hs0 hc0
  obtain ⟨β, hβc, hβY⟩ := hcomp c (by rwa [hClen]) Y hY (fun d _ i ↦ by rw [hsol]; simp)
  rw [← hBs] at hβc hβY
  set p := Bs.length with hp
  have hpS : (semBs M Bs).length = p := by simp [semBs, hp]
  have hgetS : ∀ k < p, (semBs M Bs).getD k ([], 0) =
      ((Bs.getD k ([], fun _ ↦ [])).1, semV M (Bs.getD k ([], fun _ ↦ [])).2) := fun k hk ↦
    NestTower.getD_map' _ _ ([], fun _ ↦ []) _ hk
  -- `Y` is the combination
  have hYeq : Y = (fun i ↦ ∑ k ∈ Finset.range (semBs M Bs).length, C (ι (β.getD k 0)) *
      ((semBs M Bs).getD k ([], 0)).2 i) + 0 := by
    funext i
    ext m
    rw [Pi.add_apply, Pi.zero_apply, add_zero, finsetSum_coeff, hβY i m (Nat.zero_le _)]
    simp only [coeff_C_mul]
  -- the residuals cancel
  have hres := resCV_comb (M.sem w0) (M.sem b) (semPM M A) (semPM M B) ClS ι hιd hιrat
    (semBs M Bs) c β hβc 0
  rw [← hYeq, hsol, LopV_zero', add_zero] at hres
  set Rs := residsC O w0 b A B cst Cl Bs with hRs
  set Qd := residLen Rs with hQd
  set U := relRun O cst rel p (residVals O Rs Qd) (n * Qd) with hU
  have hRsD : ∀ k < p, ∀ i, (Rs.getD k fun _ ↦ []) i =
      resQVC O w0 b A B cst Cl (Bs.getD k ([], fun _ ↦ [])).1 (Bs.getD k ([], fun _ ↦ [])).2 i :=
    fun k hk i ↦ by
      rw [hRs, residsC_eq, NestTower.getD_map' _ _ ([], fun _ ↦ []) _ hk]
  set βt := (List.range p).map fun k ↦ β.getD k 0 with hβt
  have hβtD : ∀ k < p, βt.getD k 0 = β.getD k 0 := fun k hk ↦ NestTower.getD_range_map _ _ hk
  have hcoord : ∀ y < n * Qd, ∑ k ∈ Finset.range p, ι (βt.getD k 0) *
      M.sem ((residVals O Rs Qd y).getD k O.zero) = 0 := by
    intro y hy
    have hQ : 0 < Qd := by
      rcases Nat.eq_zero_or_pos Qd with h0 | h0
      · rw [h0, mul_zero] at hy; omega
      · exact h0
    have hi : y / Qd < n := (Nat.div_lt_iff_lt_mul hQ).mpr hy
    have hcf := congrArg (fun P : K[X] ↦ P.coeff (y % Qd)) (congrFun hres ⟨y / Qd, hi⟩)
    simp only [finsetSum_coeff, coeff_C_mul, Pi.zero_apply, coeff_zero] at hcf
    rw [hcf, hpS]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [residVals_getD' Rs Qd y ⟨y / Qd, hi⟩ rfl k (by simpa [hRs, residsC_eq] using hk'),
      hβtD k hk', hgetS k hk', hRsD k hk', ← coeff_toPoly_sem, toPoly_resQVC M w0 b A B cst hcst]
  obtain ⟨-, hRC⟩ := relRun_inv ι M cst hcst rel p (residVals O Rs Qd) hrel
    (fun x ↦ by rw [residVals_length, hRs, residsC_eq, List.length_map]) hιrat (n * Qd)
  obtain ⟨γ, hγ⟩ := hRC βt (fun k hk ↦ List.getD_eq_default _ _ (by simpa [hβt] using hk)) hcoord
  have hβγ : ∀ k < p, β.getD k 0 = ∑ j ∈ Finset.range U.length,
      γ.getD j 0 * algebraMap ℚ Cs ((U.getD j []).getD k 0) := fun k hk ↦ by
    rw [← hβtD k hk, hγ k]
  have hout : polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1) =
      U.map fun u ↦ (vcomb Cl.length u (Bs.map Prod.fst), vecM fun i ↦
        sumC O (List.range Bs.length) fun l ↦
          GPoly.smul O (cst (u.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i)) := rfl
  have hlenO : (polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).length = U.length := by
    rw [hout, List.length_map]
  have hgetO : ∀ j < U.length, (polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).getD j
      ([], fun _ ↦ []) = (vcomb Cl.length (U.getD j []) (Bs.map Prod.fst), vecM fun i ↦
        sumC O (List.range Bs.length) fun l ↦
          GPoly.smul O (cst ((U.getD j []).getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i)) :=
    fun j hj ↦ by rw [hout]; exact NestTower.getD_map' _ _ [] _ hj
  refine ⟨γ, fun l ↦ ?_, fun i ↦ ?_⟩
  · rw [hlenO]
    have e : ∀ j ∈ Finset.range U.length, γ.getD j 0 * algebraMap ℚ Cs
        (((polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).getD j
          ([], fun _ ↦ [])).1.getD l 0) =
        γ.getD j 0 * algebraMap ℚ Cs ((vcomb Cl.length (U.getD j []) (Bs.map Prod.fst)).getD l 0) :=
      fun j hj ↦ by rw [hgetO j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl e]
    by_cases hl : l < Cl.length
    · have hβc' : ∀ l < Cl.length, c.getD l 0 = ∑ k ∈ Finset.range p,
          β.getD k 0 * algebraMap ℚ Cs ((Bs.getD k ([], fun _ ↦ [])).1.getD l 0) := fun l _ ↦ by
        rw [hβc l, hpS]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [hgetS k (Finset.mem_range.mp hk)]
      rw [recombine Cl.length p U.length (fun k l ↦ (Bs.getD k ([], fun _ ↦ [])).1.getD l 0)
        (fun j k ↦ (U.getD j []).getD k 0) (fun l ↦ c.getD l 0) (fun k ↦ β.getD k 0)
        (fun j ↦ γ.getD j 0) hβc' hβγ l hl]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [getD_vcomb, if_pos hl, List.length_map]
      congr 2
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [NestTower.getD_map' _ _ ([], fun _ ↦ []) [] (Finset.mem_range.mp hk)]
    · rw [hc l (by omega)]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [getD_vcomb, if_neg hl, map_zero, mul_zero]
  · rw [hlenO, congrFun hYeq i, Pi.add_apply, Pi.zero_apply, add_zero, hpS]
    have e : ∀ j ∈ Finset.range U.length, C (ι (γ.getD j 0)) *
        semV M ((polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel (N + 1)).getD j
          ([], fun _ ↦ [])).2 i =
        ∑ k ∈ Finset.range p, C (ι (γ.getD j 0)) * (C (((U.getD j []).getD k 0 : ℚ) : K) *
          semV M (Bs.getD k ([], fun _ ↦ [])).2 i) := fun j hj ↦ by
      rw [hgetO j (Finset.mem_range.mp hj)]
      simp only [semV, vecM_eq, toPoly_sumC_range, GPoly.toPoly_smul, hcst, Finset.mul_sum]
      rfl
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [hgetS k (Finset.mem_range.mp hk), hβγ k (Finset.mem_range.mp hk), map_sum, map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_mul, hιrat]
    simp only
    ring

end Sem

end Tower.Sys
