import RischTragerBronstein.Mixed.SysSpecial2
import RischTragerBronstein.Computable.AnnDual

/-!
# The special-degree bound always answers

**`specBound2_isSome`**: if `η` is not a derivative in `Fₘ`, the Gram determinant of the pencil
`M(X) = X Uₐ + U_c` is not identically zero. Otherwise `M(X)ᵀ M(X)` has a non-zero polynomial
kernel vector `v` (`exists_mulVec_eq_zero_iff`), `vᵀ Mᵀ M v = ∑ᵤ (M v)ᵤ² = 0` forces `M v = 0`
(`sq_sum_eq_zero`), and the top coefficients `w` of `v` satisfy `Uₐ w = 0`. Then `(w, 0)` is
orthogonal to every annihilator row, hence a combination of the relations (`ann_dual`), so
`wᵢ η` is a derivative for every `i` (`LimSpec.sound`), and `w = 0`: a contradiction.
-/

open Polynomial CPoly Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP

lemma deriv_ratCast' {E : Type*} [Field E] [Differential E] [CharZero E] (q : ℚ) :
    ((q : E))′ = 0 := by
  have hd : ((q.den : ℕ) : E) ≠ 0 := by exact_mod_cast q.den_nz
  have e : (q : E) * ((q.den : ℕ) : E) = ((q.num : ℤ) : E) := by
    rw [← Rat.cast_natCast, ← Rat.cast_intCast, ← Rat.cast_mul]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num q
  have h := congrArg (fun z : E ↦ z′) e
  simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_natCast, Derivation.map_intCast,
    mul_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hd

lemma list_sum_eq_zero_of_nonneg : ∀ (l : List ℚ), (∀ q ∈ l, 0 ≤ q) → l.sum = 0 → ∀ q ∈ l, q = 0
  | [], _, _, q, hq => by simp at hq
  | a :: l, hnn, hs, q, hq => by
    have ha := hnn a List.mem_cons_self
    have hl : 0 ≤ l.sum := List.sum_nonneg fun x hx ↦ hnn x (List.mem_cons_of_mem _ hx)
    rw [List.sum_cons] at hs
    obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg ha hl).mp hs
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact list_sum_eq_zero_of_nonneg l (fun x hx ↦ hnn x (List.mem_cons_of_mem _ hx)) h2 q hq

/-- A sum of squares of rational polynomials vanishes only if each one does. -/
lemma sq_sum_eq_zero (ps : List ℚ[X]) (h : (ps.map fun p ↦ p ^ 2).sum = 0) :
    ∀ p ∈ ps, p = 0 := by
  intro p hp
  apply Polynomial.funext
  intro a
  have he := congrArg (eval a) h
  rw [eval_zero, ← coe_evalRingHom, map_list_sum, List.map_map] at he
  have hnn : ∀ q ∈ ps.map ((eval a) ∘ fun p ↦ p ^ 2), 0 ≤ q := by
    intro q hq
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hq
    simp only [Function.comp_apply, eval_pow]
    positivity
  have h0 := list_sum_eq_zero_of_nonneg _ hnn he _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simp only [Function.comp_apply, eval_pow] at h0
  rw [eval_zero]
  exact pow_eq_zero_iff (by norm_num) |>.mp h0

/-- The pencil entries `X aᵤⱼ + cᵤⱼ`. -/
noncomputable def penL (n : ℕ) (u : CPoly ℚ) (j : Fin n) : ℚ[X] :=
  C (u.getD j 0) * X + C (u.getD (n + j) 0)

lemma toPoly_gramEntry (n : ℕ) (i j : Fin n) :
    ∀ U : List (CPoly ℚ), toPoly (gramEntry U n i j) = (U.map fun u ↦ penL n u i * penL n u j).sum
  | [] => by simp [gramEntry, CPoly.toPoly]
  | u :: U => by
    have ih := toPoly_gramEntry n i j U
    simp only [gramEntry, toPoly_cons, toPoly_nil, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    simp only [penL, C_add, C_mul]
    ring

lemma quad_gram (n : ℕ) (v : Fin n → ℚ[X]) :
    ∀ U : List (CPoly ℚ), ∑ i, v i * ∑ j, (U.map fun u ↦ penL n u i * penL n u j).sum * v j =
      (U.map fun u ↦ (∑ j, penL n u j * v j) ^ 2).sum
  | [] => by simp
  | u :: U => by
    have ih := quad_gram n v U
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, mul_add] at ih ⊢
    rw [ih, sq, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`specBound2` answers** when `η` is not a derivative in `Fₘ`. -/
theorem specBound2_isSome (m : ℕ) (h : T.Tr m) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim) (n : ℕ) (η : LC m)
    (β : Fin n → Fin n → LC m) (hη : ∀ y : T.F m, y′ ≠ (T.MP m h).sem η) :
    (specBound2 Fc ks m n lim η β).isSome := by
  classical
  set U := specAnn Fc ks m n lim η β with hU
  unfold specBound2
  dsimp only
  rw [← hU]
  split_ifs with hz
  swap
  · simp
  exfalso
  have hP : toPoly (gramPoly U n) = 0 := (CPoly.isZero_iff _).mp hz
  set G : Matrix (Fin n) (Fin n) ℚ[X] :=
    Matrix.of fun i j ↦ (U.map fun u ↦ penL n u i * penL n u j).sum with hG
  have hdet : G.det = 0 := by
    have := detF_spec [] [1] CPoly.add CPoly.mul CPoly.neg (fun p : CPoly ℚ ↦ toPoly p)
      (by simp) (by simp [CPoly.toPoly]) (fun a b ↦ toPoly_add a b) (fun a b ↦ toPoly_mul a b)
      (fun a ↦ toPoly_neg a) n (gramEntry U n)
    rw [← hP, gramPoly, this]
    congr 1
    ext i j
    rw [Matrix.of_apply, toPoly_gramEntry, hG, Matrix.of_apply]
  obtain ⟨v, hv0, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set s : CPoly ℚ → ℚ[X] := fun u ↦ ∑ j, penL n u j * v j with hs
  have hsq : (U.map fun u ↦ s u ^ 2).sum = 0 := by
    rw [← quad_gram n v U]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have := congrFun hGv i
    simp only [Matrix.mulVec, dotProduct, hG, Matrix.of_apply, Pi.zero_apply] at this
    rw [this, mul_zero]
  have hs0 : ∀ u ∈ U, s u = 0 := fun u hu ↦
    sq_sum_eq_zero (U.map s) (by rw [List.map_map]; exact hsq) _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
  -- the top coefficients
  set K := Finset.univ.sup fun j ↦ (v j).natDegree with hK
  have hdegK : ∀ j, (v j).natDegree ≤ K := fun j ↦ Finset.le_sup (f := fun j ↦ (v j).natDegree)
    (Finset.mem_univ j)
  set w : Fin n → ℚ := fun j ↦ (v j).coeff K with hw
  have hw0 : w ≠ 0 := by
    obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
      by_contra hc; push Not at hc; exact hv0 (funext hc)
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j0, Finset.mem_univ _⟩
    obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_sup _ hne fun j ↦ (v j).natDegree
    intro h0
    by_cases hv1 : v j1 = 0
    · have hK0 : K = 0 := by rw [hK, hj1, hv1, natDegree_zero]
      have := congrFun h0 j0
      simp only [hw, Pi.zero_apply, hK0] at this
      have hd0 : (v j0).natDegree = 0 := by have := hdegK j0; omega
      exact hj0 (by rw [eq_C_of_natDegree_eq_zero hd0, this, C_0])
    · have := congrFun h0 j1
      simp only [hw, Pi.zero_apply] at this
      rw [hK, hj1] at this
      exact hv1 (leadingCoeff_eq_zero.mp this)
  have hUw : ∀ u ∈ U, ∑ j : Fin n, u.getD (j : ℕ) 0 * w j = 0 := by
    intro u hu
    have := congrArg (fun p : ℚ[X] ↦ p.coeff (K + 1)) (hs0 u hu)
    simp only [hs, finset_sum_coeff, coeff_zero] at this
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) this
    rw [penL, add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le (hdegK j)), mul_zero, add_zero]
  -- a component with `wᵢ ≠ 0`
  obtain ⟨i, hwi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push Not at hc; exact hw0 (funext hc)
  set ws := specWs Fc ks m n η β i with hws
  set rels := (lim ws).map Prod.fst with hrels
  set x : ℕ → ℚ := fun l ↦ if hl : l < n then w ⟨l, hl⟩ else 0 with hx
  have horth : ∀ a ∈ CPoly.nullBasis (transposeL rels (2 * n)),
      ∑ l ∈ Finset.range (2 * n), a.getD l 0 * x l = 0 := by
    intro a ha
    have haU : a ∈ U := List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ha⟩
    rw [sum_range_two]
    simp only [hx, Fin.is_lt, dif_pos, show ∀ j : Fin n, ¬ (n + (j : ℕ) < n) from fun j ↦ by omega,
      dif_neg, not_false_eq_true, mul_zero, Finset.sum_const_zero, add_zero]
    exact hUw a haU
  obtain ⟨μ, hμ⟩ := ann_dual rels (2 * n) x horth
  -- `wᵢ η` is a derivative
  set M := T.MP m h with hM
  have hlen : ws.length = 2 * n := by simp [hws, specWs]
  set Y : T.F m := ∑ k ∈ Finset.range (lim ws).length,
    (μ k : T.F m) * M.sem ((lim ws).getD k ([], (MO Fc ks m).zero)).2 with hY
  have hYd : Y′ = (w i : T.F m) * M.sem η := by
    have hdq : ∀ q : ℚ, ((q : T.F m))′ = 0 := fun q ↦ deriv_ratCast' q
    rw [hY, map_sum]
    have e1 : ∀ k ∈ Finset.range (lim ws).length,
        ((μ k : T.F m) * M.sem ((lim ws).getD k ([], (MO Fc ks m).zero)).2)′ =
        (μ k : T.F m) * ∑ l ∈ Finset.range (2 * n),
          ((((lim ws).getD k ([], (MO Fc ks m).zero)).1.getD l 0 : ℚ) : T.F m) *
            M.sem (ws.getD l (MO Fc ks m).zero) := by
      intro k hk
      rw [Derivation.leibniz, hdq, smul_zero, add_zero, smul_eq_mul,
        hlim.sound ws _ (getD_memC _ _ (Finset.mem_range.mp hk)), sQ, hlen]
    rw [Finset.sum_congr rfl e1]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∀ l ∈ Finset.range (2 * n), ∑ k ∈ Finset.range (lim ws).length,
        (μ k : T.F m) * (((((lim ws).getD k ([], (MO Fc ks m).zero)).1.getD l 0 : ℚ) : T.F m) *
          M.sem (ws.getD l (MO Fc ks m).zero)) = (x l : T.F m) * M.sem (ws.getD l (MO Fc ks m).zero) := by
      intro l hl
      rw [hμ l (Finset.mem_range.mp hl), show rels.length = (lim ws).length by simp [hrels],
        Rat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have : (rels.getD k []) = ((lim ws).getD k ([], (MO Fc ks m).zero)).1 := by
        rw [hrels, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (lim ws)[k]? <;> rfl
      rw [this]; push_cast; ring
    rw [Finset.sum_congr rfl e2, sum_range_two]
    have hl1 : ∀ j : Fin n, ws.getD j (MO Fc ks m).zero = if j = i then η else (MO Fc ks m).zero :=
      fun j ↦ by
        rw [hws, specWs, NestTower.getD_range_map _ _ (by omega), if_pos j.2]
        simp only [Fin.val_inj]
    simp only [hx, Fin.is_lt, dif_pos, show ∀ j : Fin n, ¬ (n + (j : ℕ) < n) from fun j ↦ by omega,
      dif_neg, not_false_eq_true, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero, hl1]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [if_neg hj, M.sem_zero, mul_zero])
      (by simp), if_pos rfl]
  apply hη ((((w i)⁻¹ : ℚ) : T.F m) * Y)
  rw [Derivation.leibniz, deriv_ratCast', smul_zero, add_zero, smul_eq_mul, hYd, ← mul_assoc]
  have : ((w i : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hwi
  rw [Rat.cast_inv, inv_mul_cancel₀ this, one_mul]

end MTower

end Curves.MT
