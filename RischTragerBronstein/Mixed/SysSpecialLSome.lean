import RischTragerBronstein.Mixed.SysSpecialL
import RischTragerBronstein.Mixed.SysSpecial3

/-!
# The special-degree bound with a limit matrix answers

**`specBoundL_isSome`**: if no non-zero solution `c` of `c′ + Λ c = 0` has `η c` in the image of
`y ↦ y′ + Λ y`, the determinant of `G(X) + H` is not identically zero. Otherwise a non-zero
polynomial kernel vector `v` gives `∑ᵤ (M v)ᵤ² + ∑ₖ (k · v)² = 0`, so the top coefficients `w ≠ 0`
satisfy `Uₐ w = 0` and `k · w = 0` for every relation `k`. Then `(w, 0)` is a combination of the
relations of the family (`ann_dual`), so `η (∑ wⱼ vⱼ)` is in the image; `∑ wⱼ vⱼ ≠ 0` since `w`
would otherwise be a relation, orthogonal to all relations, hence `0`.
-/

open Polynomial CPoly Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP

lemma quad_H (r : ℕ) (v : Fin r → ℚ[X]) :
    ∀ K0 : List (List ℚ), ∑ i : Fin r, v i * ∑ j : Fin r, C (hEntry K0 i j) * v j =
      (K0.map fun k ↦ (∑ j : Fin r, C (k.getD j 0) * v j) ^ 2).sum
  | [] => by simp [hEntry]
  | k :: K0 => by
    have ih := quad_H r v K0
    have e : ∀ i j : Fin r, C (hEntry (k :: K0) i j) = C (k.getD i 0) * C (k.getD j 0) +
        C (hEntry K0 i j) := fun i j ↦ by
      simp only [hEntry, List.map_cons, List.sum_cons, C_add, C_mul]
    have step : ∑ i : Fin r, v i * ∑ j : Fin r, C (hEntry (k :: K0) i j) * v j =
        (∑ j : Fin r, C (k.getD j 0) * v j) ^ 2 +
          ∑ i : Fin r, v i * ∑ j : Fin r, C (hEntry K0 i j) * v j := by
      simp only [e, add_mul, Finset.sum_add_distrib, mul_add]
      congr 1
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [step, ih, List.map_cons, List.sum_cons]

section Sem

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {O : COps α} (M : CField α K O) {n : ℕ}

/-- **`specBoundL` answers** when no non-zero solution `c` of `c′ + Λ c = 0` has `η c` in the image
of `y ↦ y′ + Λ y`. -/
theorem specBoundL_isSome (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = q)
    (rel : List α → List (List ℚ)) (hrel : RelSpec ι M rel) (F : Fin n → Fin n → K)
    (low : List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (hlow : ∀ ws, SysSpecAt ι F (ws.map (semVa M)) (semR M (low ws)))
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) (η : α) (β : Fin n → Fin n → α)
    (hnd : ∀ c : Fin n → K, c ≠ 0 → (∀ i, (c i)′ + mv F c i = 0) →
      ¬ ∃ y : Fin n → K, ∀ i, (y i)′ + mv F y i = M.sem η * c i) :
    (specBoundL O cst rel low η β).isSome := by
  classical
  set R0 := low [] with hR0
  set V := R0.map Prod.snd with hV
  set r := V.length with hr
  set K0 := relRun O cst rel r (vecCoordsL O V) n with hK0
  set ws := specWsL O η β V with hws
  set U := CPoly.nullBasis (transposeL ((low ws).map Prod.fst) (2 * r)) with hU
  unfold specBoundL
  dsimp only
  rw [← hU, ← hK0]
  split_ifs with hz
  swap
  · simp
  exfalso
  have hP : toPoly (gramPolyH U K0 r) = 0 := (CPoly.isZero_iff _).mp hz
  set G : Matrix (Fin r) (Fin r) ℚ[X] :=
    Matrix.of fun i j ↦ (U.map fun u ↦ penL r u i * penL r u j).sum + C (hEntry K0 i j) with hG
  have hdet : G.det = 0 := by
    have := detF_spec [] [1] CPoly.add CPoly.mul CPoly.neg (fun p : CPoly ℚ ↦ toPoly p)
      (by simp) (by simp [CPoly.toPoly]) (fun a b ↦ toPoly_add a b) (fun a b ↦ toPoly_mul a b)
      (fun a ↦ toPoly_neg a) r (gramEntryH U K0 r)
    rw [← hP, gramPolyH, this]
    congr 1
    ext i j
    rw [Matrix.of_apply, hG, Matrix.of_apply]
    have e1 := toPoly_gramEntry r i j U
    simp only [gramEntryH, gramEntry, toPoly_cons, toPoly_nil] at e1 ⊢
    rw [← e1, C_add]
    ring
  obtain ⟨v, hv0, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set s : CPoly ℚ → ℚ[X] := fun u ↦ ∑ j, penL r u j * v j with hs
  set sk : List ℚ → ℚ[X] := fun k ↦ ∑ j : Fin r, C (k.getD j 0) * v j with hsk
  have hsq : (U.map fun u ↦ s u ^ 2).sum + (K0.map fun k ↦ sk k ^ 2).sum = 0 := by
    rw [← quad_gram r v U, ← quad_H r v K0, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have := congrFun hGv i
    simp only [Matrix.mulVec, dotProduct, hG, Matrix.of_apply, Pi.zero_apply, add_mul,
      Finset.sum_add_distrib] at this
    rw [← mul_add, this, mul_zero]
  have hall := sq_sum_eq_zero ((U.map s) ++ (K0.map sk)) (by
    rw [List.map_append, List.sum_append, List.map_map, List.map_map]; exact hsq)
  have hs0 : ∀ u ∈ U, s u = 0 := fun u hu ↦ hall _ (List.mem_append_left _ (List.mem_map.mpr ⟨u, hu, rfl⟩))
  have hsk0 : ∀ k ∈ K0, sk k = 0 := fun k hk ↦
    hall _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, hk, rfl⟩))
  -- the top coefficients
  set D := Finset.univ.sup fun j ↦ (v j).natDegree with hD
  have hdegD : ∀ j, (v j).natDegree ≤ D := fun j ↦ Finset.le_sup (f := fun j ↦ (v j).natDegree)
    (Finset.mem_univ j)
  set w : Fin r → ℚ := fun j ↦ (v j).coeff D with hw
  have hw0 : w ≠ 0 := by
    obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
      by_contra hc; push Not at hc; exact hv0 (funext hc)
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j0, Finset.mem_univ _⟩
    obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_sup _ hne fun j ↦ (v j).natDegree
    intro h0
    by_cases hv1 : v j1 = 0
    · have hD0 : D = 0 := by rw [hD, hj1, hv1, natDegree_zero]
      have := congrFun h0 j0
      simp only [hw, Pi.zero_apply, hD0] at this
      have hd0 : (v j0).natDegree = 0 := by have := hdegD j0; omega
      exact hj0 (by rw [eq_C_of_natDegree_eq_zero hd0, this, C_0])
    · have := congrFun h0 j1
      simp only [hw, Pi.zero_apply] at this
      rw [hD, hj1] at this
      exact hv1 (leadingCoeff_eq_zero.mp this)
  have hUw : ∀ u ∈ U, ∑ j : Fin r, u.getD (j : ℕ) 0 * w j = 0 := by
    intro u hu
    have := congrArg (fun p : ℚ[X] ↦ p.coeff (D + 1)) (hs0 u hu)
    simp only [hs, finsetSum_coeff, coeff_zero] at this
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) this
    rw [penL, add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le (hdegD j)), mul_zero, add_zero]
  have hKw : ∀ k ∈ K0, ∑ j : Fin r, k.getD (j : ℕ) 0 * w j = 0 := by
    intro k hk
    have := congrArg (fun p : ℚ[X] ↦ p.coeff D) (hsk0 k hk)
    simp only [hsk, finsetSum_coeff, coeff_zero, coeff_C_mul] at this
    exact this
  -- the semantic data
  set Vs : ℕ → Fin n → K := fun k i ↦ M.sem ((V.getD k fun _ ↦ O.zero) i) with hVs
  have hrR : R0.length = r := by simp [hr, hV]
  have hsemR0 : ∀ k < r, ((semR M R0).getD k ([], 0)).2 = Vs k := by
    intro k hk
    funext i
    have hk' : k < R0.length := by omega
    simp only [semR, hVs, hV]
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getD_eq_getElem _ _ (by simpa using hk')]
    simp
  have hVhom : ∀ k < r, ∀ i, (Vs k i)′ + mv F (Vs k) i = 0 := by
    intro k hk i
    have hmem : (semR M R0).getD k ([], 0) ∈ semR M R0 := by
      rw [List.getD_eq_getElem _ _ (by simp [semR, hrR]; omega)]; exact List.getElem_mem _
    have := (hlow []).1 _ hmem i
    rw [hsemR0 k hk] at this
    simpa using this
  have hwslen : ws.length = 2 * r := by simp [hws, specWsL, hr]
  have hwsL : ∀ k < r, (ws.map (semVa M)).getD k 0 = fun i ↦ M.sem η * Vs k i := by
    intro k hk
    funext i
    rw [List.getD_eq_getElem _ _ (by simp [hwslen]; omega), List.getElem_map]
    rw [← List.getD_eq_getElem ws (fun _ ↦ O.zero) (by simp [hwslen]; omega), hws, specWsL,
      NestTower.getD_range_map _ _ (by omega)]
    have hk' : k < V.length := hk
    simp only [hk', ↓reduceIte, semVa, M.sem_mul, hVs]
  -- `(w, 0)` is a combination of the relations
  set rels := (low ws).map Prod.fst with hrels
  set x : ℕ → ℚ := fun l ↦ if hl : l < r then w ⟨l, hl⟩ else 0 with hx
  have horth : ∀ a ∈ CPoly.nullBasis (transposeL rels (2 * r)),
      ∑ l ∈ Finset.range (2 * r), a.getD l 0 * x l = 0 := by
    intro a ha
    rw [sum_range_two]
    simp only [hx, Fin.is_lt, dif_pos, show ∀ j : Fin r, ¬ (r + (j : ℕ) < r) from fun j ↦ by omega,
      dif_neg, not_false_eq_true, mul_zero, Finset.sum_const_zero, add_zero]
    exact hUw a ha
  obtain ⟨μ, hμ⟩ := ann_dual rels (2 * r) x horth
  -- the solution
  set Rs := semR M (low ws) with hRs
  have hRlen : Rs.length = rels.length := by simp [hRs, hrels, semR]
  have hRk : ∀ k, (Rs.getD k ([], 0)).1 = rels.getD k [] := fun k ↦ by
    rw [hRs, hrels, semR, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map]
    cases (low ws)[k]? <;> rfl
  set c : Fin n → K := fun i ↦ ∑ j : Fin r, ((w j : ℚ) : K) * Vs j i with hc
  set y : Fin n → K := fun i ↦ ∑ k ∈ Finset.range Rs.length, ((μ k : ℚ) : K) * (Rs.getD k ([], 0)).2 i
    with hy
  have hdq : ∀ q : ℚ, ((q : K))′ = 0 := fun q ↦ deriv_ratCast' q
  have hysol : ∀ i, (y i)′ + mv F y i = M.sem η * c i := by
    intro i
    have hk : ∀ k ∈ Finset.range Rs.length, ((((μ k : ℚ) : K) * (Rs.getD k ([], 0)).2 i))′ +
        ((μ k : ℚ) : K) * mv F (Rs.getD k ([], 0)).2 i = ((μ k : ℚ) : K) *
          ∑ l ∈ Finset.range (2 * r), (((rels.getD k []).getD l 0 : ℚ) : K) *
            ((ws.map (semVa M)).getD l 0) i := by
      intro k hk
      have hmem : Rs.getD k ([], 0) ∈ Rs := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
      have := (hlow ws).1 _ hmem i
      rw [Derivation.leibniz, hdq, smul_zero, add_zero, smul_eq_mul, ← mul_add, this,
        List.length_map, hwslen, hRk]
    have e1 : (y i)′ + mv F y i = ∑ k ∈ Finset.range Rs.length, (((((μ k : ℚ) : K) *
        (Rs.getD k ([], 0)).2 i))′ + ((μ k : ℚ) : K) * mv F (Rs.getD k ([], 0)).2 i) := by
      simp only [hy, map_sum, mv, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e1, Finset.sum_congr rfl hk]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∀ l ∈ Finset.range (2 * r), ∑ k ∈ Finset.range Rs.length, ((μ k : ℚ) : K) *
        ((((rels.getD k []).getD l 0 : ℚ) : K) * ((ws.map (semVa M)).getD l 0) i) =
        ((x l : ℚ) : K) * ((ws.map (semVa M)).getD l 0) i := by
      intro l hl
      rw [hμ l (Finset.mem_range.mp hl), ← hRlen, Rat.cast_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ ↦ by push_cast; ring
    rw [Finset.sum_congr rfl e2, sum_range_two]
    simp only [hx, Fin.is_lt, dif_pos, show ∀ j : Fin r, ¬ (r + (j : ℕ) < r) from fun j ↦ by omega,
      dif_neg, not_false_eq_true, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hwsL j j.2]
    ring
  -- `c` is homogeneous
  have hchom : ∀ i, (c i)′ + mv F c i = 0 := by
    intro i
    simp only [hc, map_sum, Derivation.leibniz, hdq, smul_zero, add_zero, smul_eq_mul, mv,
      Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have := hVhom j j.2 i
    simp only [mv] at this
    have e : ∑ x : Fin n, F i x * (((w j : ℚ) : K) * Vs j x) = ((w j : ℚ) : K) * ∑ x, F i x * Vs j x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [e, mul_zero, add_zero, ← mul_add, this, mul_zero]
  -- `c ≠ 0`
  have hc0 : c ≠ 0 := by
    intro h0
    have hvl : ∀ x, (vecCoordsL O V x).length = r := fun x ↦ by
      unfold vecCoordsL; split_ifs <;> simp [hr]
    obtain ⟨-, hK0c⟩ := relRun_inv ι M cst hcst rel r (vecCoordsL O V) hrel hvl hιrat n
    set βl : List Cs := (List.range r).map fun b ↦ ((x b : ℚ) : Cs) with hβl
    have hβb : ∀ b < r, βl.getD b 0 = ((x b : ℚ) : Cs) := fun b hb ↦ by
      rw [hβl, NestTower.getD_range_map _ _ hb]
    obtain ⟨γ, hγ⟩ := hK0c βl (fun b hb ↦ List.getD_eq_default _ _ (by simp [hβl]; omega))
      (fun yy hyy ↦ by
        have h1 := congrFun h0 ⟨yy, hyy⟩
        simp only [hc, Pi.zero_apply] at h1
        rw [← Fin.sum_univ_eq_sum_range (fun b ↦ ι (βl.getD b 0) *
          M.sem ((vecCoordsL O V yy).getD b O.zero))]
        rw [← h1]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [hβb b b.2, map_ratCast]
        simp only [hx, b.2, dif_pos, Fin.eta]
        congr 1
        simp only [vecCoordsL, hyy, ↓reduceDIte, hVs]
        rw [List.getD_eq_getElem _ _ (by simp; rw [← hr]; exact b.2),
          List.getD_eq_getElem _ _ (by rw [← hr]; exact b.2)]
        simp)
    have hsq0 : (((∑ b : Fin r, w b * w b : ℚ)) : Cs) = 0 := by
      push_cast
      have e : ∀ b : Fin r, ((w b : ℚ) : Cs) = ∑ t ∈ Finset.range K0.length,
          γ.getD t 0 * (((K0.getD t []).getD b 0 : ℚ) : Cs) := fun b ↦ by
        have hxb : ((w b : ℚ) : Cs) = ((x b : ℚ) : Cs) := by simp [hx]
        rw [hxb, ← hβb b b.2, hγ b]
        exact Finset.sum_congr rfl fun t _ ↦ by rw [eq_ratCast]
      have h2 : ∑ b : Fin r, ((w b : ℚ) : Cs) * ((w b : ℚ) : Cs) = ∑ t ∈ Finset.range K0.length,
          γ.getD t 0 * ∑ b : Fin r, (((K0.getD t []).getD b 0 : ℚ) : Cs) * ((w b : ℚ) : Cs) := by
        rw [Finset.sum_congr rfl fun b _ ↦ congrArg (· * ((w b : ℚ) : Cs)) (e b)]
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
      rw [h2]
      refine Finset.sum_eq_zero fun t ht ↦ ?_
      have hkt : K0.getD t [] ∈ K0 := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp ht)]; exact List.getElem_mem _
      have := hKw _ hkt
      have e3 : ∑ b : Fin r, (((K0.getD t []).getD b 0 : ℚ) : Cs) * ((w b : ℚ) : Cs) =
          (((∑ b : Fin r, (K0.getD t []).getD b 0 * w b : ℚ)) : Cs) := by push_cast; rfl
      rw [e3, this, Rat.cast_zero, mul_zero]
    have hsq : ∑ b : Fin r, w b * w b = 0 := by exact_mod_cast hsq0
    apply hw0
    funext b
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ w i * w i := fun i _ ↦ mul_self_nonneg _
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsq b (Finset.mem_univ b))
  exact hnd c hc0 hchom ⟨y, hysol⟩

end Sem

end Curves.MT
