import RischTragerBronstein.Curves.ProcRFDecide

/-!
# Norms of bivariate polynomials: `Res_Y(F, W)`

* `natDegree_norm_le`: `deg_x Res_Y(F, W) ≤ n (d_W + k m)` (from the branches above infinity);
* `normRC Fc W n k`: `Res_Y(F, W)` computed by `resC` on the fibres `x = 0, 1, …` and Lagrange
  interpolation (`toPoly_normRC`);
* `branch_norm`: along a split finite fibre, `g(Res_Y(F, W)) = ∏ₖ W(rₖ)`.
-/

open Polynomial HahnSeries

namespace Curves

open CPoly Sup Differential

lemma lowerBd_list_prod {K : Type*} [Field K] (l : List (LaurentSeries K)) (b : ℤ)
    (h : ∀ x ∈ l, LowerBd x b) : LowerBd l.prod (l.length * b) := by
  induction l with
  | nil =>
    simp only [List.prod_nil, List.length_nil, CharP.cast_eq_zero, zero_mul]
    have := lowerBd_C (1 : K)
    rwa [map_one] at this
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons]
    have := (h x List.mem_cons_self).mul (ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy))
    convert this using 1
    push_cast; ring

section Deg

variable {C : Type*} [Field C] [CharZero C]

/-- **Degree bound for norms.** -/
theorem natDegree_norm_le (Fp W : C[X][X]) (hF : Fp.Monic) (k : ℕ)
    (hk : ∀ i, (Fp.coeff i).natDegree ≤ k) (m dW : ℕ) (hWm : W.natDegree ≤ m)
    (hWd : ∀ i, (W.coeff i).natDegree ≤ dW) :
    (resultant Fp W Fp.natDegree m).natDegree ≤ Fp.natDegree * (dW + k * m) := by
  classical
  set K := AlgebraicClosure C
  set R := resultant Fp W Fp.natDegree m with hR
  by_cases hR0 : R = 0
  · rw [hR0, natDegree_zero]; exact Nat.zero_le _
  obtain ⟨N, hN, l, hl, hsplitl, hroots⟩ := split_inf (K := K) Fp hF k hk
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hmap : infSub (K := K) N R = (l.map fun r ↦ (W.map (infSub N)).eval r).prod := by
    rw [hR, ← resultant_map_map, hsplitl, ← hl]
    exact resultant_list_prod l _ m (natDegree_map_le.trans hWm)
  have hr : ∀ r ∈ l, LowerBd r (-((k * N : ℕ) : ℤ)) := fun r hr ↦ by
    obtain ⟨w, hw⟩ := hroots r hr
    rw [hw]
    have := (lowerBd_ofPS w).mul (lowerBd_single (-(k * N : ℤ)) (1 : K))
    rw [zero_add] at this
    push_cast; exact this
  have hev : ∀ r ∈ l, LowerBd ((W.map (infSub N)).eval r) (-((N * (dW + k * m) : ℕ) : ℤ)) := by
    intro r hrl
    refine CurveData.lowerBd_eval _ r _ (by push_cast; nlinarith) (hr r hrl) _ fun i ↦ ?_
    rw [coeff_map]
    by_cases hi : i ≤ m
    · refine (CurveData.lowerBd_infSub N hN0 _).mono ?_
      have h1 := Nat.mul_le_mul_left N (hWd i)
      have h2 : k * N * i ≤ k * N * m := Nat.mul_le_mul_left _ hi
      push_cast at h1 h2 ⊢
      nlinarith
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]; exact lowerBd_zero _
  have hbd : LowerBd (infSub (K := K) N R)
      (-((Fp.natDegree * (N * (dW + k * m)) : ℕ) : ℤ)) := by
    rw [hmap]
    have := lowerBd_list_prod _ _ fun x hx ↦ by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact hev r hr
    rw [List.length_map, hl] at this
    convert this using 1
    push_cast; ring
  have hne : infSub (C := C) (K := K) N R ≠ 0 := infSub_ne_zero N hN0 R hR0
  have hord := order_infSub (C := C) (K := K) N hN0 R hR0
  have hle : ¬ (infSub (K := K) N R).order <
      -((Fp.natDegree * (N * (dW + k * m)) : ℕ) : ℤ) := fun hlt ↦
    HahnSeries.coeff_order_eq_zero.not.mpr hne (hbd _ hlt)
  rw [hord] at hle
  push Not at hle
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN0
  have : (N : ℤ) * R.natDegree ≤ N * (Fp.natDegree * (dW + k * m) : ℕ) := by
    push_cast at hle ⊢; nlinarith
  exact_mod_cast le_of_mul_le_mul_left this hN'

end Deg

section Comp

variable {F : Type*} [Field F] [DecidableEq F]

/-- A bound for the coefficient degrees of `W`. -/
def maxDegB (W : BPoly F) : ℕ := W.foldr (fun c m ↦ max (degT c) m) 0

/-- The norm degree bound `n (d_W + k (len W − 1))`. -/
def normBound (W : BPoly F) (n k : ℕ) : ℕ := n * (maxDegB W + k * (W.length - 1))

/-- **`Res_Y(F, W)` by interpolation.** -/
def normRC (Fc W : BPoly F) (n k : ℕ) : CPoly F :=
  interpC (natPts (normBound W n k))
    ((natPts (normBound W n k)).map fun c ↦ resC (evalFibre Fc c) (evalFibre W c))

lemma degT_le_maxDegB (W : BPoly F) : ∀ i, degT (W.getD i []) ≤ maxDegB W := by
  induction W with
  | nil => intro i; simp [degT, trim]
  | cons c W ih =>
    intro i
    cases i with
    | zero => simp [maxDegB]
    | succ i => simp only [List.getD_cons_succ, maxDegB, List.foldr_cons]; exact (ih i).trans
                  (le_max_right _ _)

end Comp

section Spec

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

lemma natDegree_toB_le_len (W : BPoly F) : (toB W).natDegree ≤ W.length - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    have : W.length - 1 < i := by exact_mod_cast hi
    rw [coeff_toB, List.getD_eq_default _ _ (by omega), toPoly_nil]

lemma resC_fibre (Fc W : BPoly F) (n : ℕ) (hmon : (toB Fc).Monic) (hn : (toB Fc).natDegree = n)
    (c : F) : resC (evalFibre Fc c) (evalFibre W c) =
      (resultant (toB Fc) (toB W) n (W.length - 1)).eval c := by
  rw [resC_eq, toPoly_evalFibre, toPoly_evalFibre]
  have h1 : ((toB Fc).map (evalRingHom c)).natDegree = n := by rw [hmon.natDegree_map, hn]
  have h2 : ((toB W).map (evalRingHom c)).natDegree ≤ W.length - 1 :=
    natDegree_map_le.trans (natDegree_toB_le_len W)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h2
  have hc : ((toB Fc).map (evalRingHom c)).coeff n = 1 := by
    rw [← h1]; exact (hmon.map _).leadingCoeff
  rw [h1, ← coe_evalRingHom, ← resultant_map_map, hj, resultant_add_right_deg _ _ _ _ _ le_rfl, hc,
    one_pow, one_mul]

/-- **`normRC` is the norm.** -/
theorem toPoly_normRC (Fc W : BPoly F) (n k : ℕ) (hmon : (toB Fc).Monic)
    (hn : (toB Fc).natDegree = n) (hk : ∀ i, ((toB Fc).coeff i).natDegree ≤ k) :
    toPoly (normRC Fc W n k) = resultant (toB Fc) (toB W) n (W.length - 1) := by
  set d := normBound W n k with hd
  refine eq_of_natDegree_lt_card_of_eval_eq _ _ (ι := Fin (d + 1)) (f := fun i ↦ ((i : ℕ) : F))
    (fun a b h ↦ Fin.ext (by simpa using h)) (fun i ↦ ?_) ?_
  · have hi : (i : ℕ) < d + 1 := i.2
    have hl : (i : ℕ) < (natPts d : List F).length := by rw [natPts_length]; exact hi
    rw [normRC, ← natPts_getD d i hi, eval_interpC _ _ (natPts_nodup d) i hl,
      List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hl, natPts_getD d i hi, resC_fibre Fc W n hmon hn]
  · rw [Fintype.card_fin]
    refine max_lt ?_ ?_
    · have := natDegree_interpC_lt (natPts d : List F)
        ((natPts d).map fun c ↦ resC (evalFibre Fc c) (evalFibre W c)) (by rw [natPts_length]; omega)
      rwa [natPts_length] at this
    · have := natDegree_norm_le (toB Fc) (toB W) hmon k hk (W.length - 1) (maxDegB W)
        (natDegree_toB_le_len W) (fun i ↦ by rw [coeff_toB, ← degT_eq]; exact degT_le_maxDegB W i)
      rw [hn] at this
      rw [hd, normBound]; omega

end Spec

end Curves
