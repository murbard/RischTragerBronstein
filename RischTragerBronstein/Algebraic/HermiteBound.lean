import RischTragerBronstein.Algebraic.HermitePoly

/-!
# A degree bound for the Hermite numerator

From `2ADS = S L_D(W) + 2D²S B₀ + 2D² ∑ c_α S_α` (`deg B₀ ≤ n − 2`): `deg W ≤ max(deg A, deg D)`
(`hermite_deg_bound`) — the top coefficient of `L_D(W)` is `lc(W) lc(D) lc(p) (2 deg W − 2 deg D + n)`,
non-zero when `deg W > deg D`, and nothing else reaches that degree.
-/

open Polynomial

namespace EllAlgo

lemma nd_mul {P Q : ℚ[X]} {a b : ℕ} (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b) :
    (P * Q).natDegree ≤ a + b := natDegree_mul_le_of_le hP hQ

lemma natDegree_LD_le (p D W : ℚ[X]) (hp1 : 1 ≤ p.natDegree) :
    (LD p D W).natDegree ≤ W.natDegree + D.natDegree + p.natDegree - 1 := by
  set N := W.natDegree + D.natDegree + p.natDegree - 1
  have hW' := natDegree_derivative_le W
  have hD' := natDegree_derivative_le D
  have hp' := natDegree_derivative_le p
  have h1 : (derivative W * D * p).natDegree ≤ N := by
    rcases Nat.eq_zero_or_pos W.natDegree with h0 | hpos
    · rw [show derivative W = 0 by rw [eq_C_of_natDegree_eq_zero h0]; exact derivative_C]
      simp
    · exact (nd_mul (nd_mul hW' le_rfl) le_rfl).trans (by omega)
  have h2 : (W * derivative D * p).natDegree ≤ N := by
    rcases Nat.eq_zero_or_pos D.natDegree with h0 | hpos
    · rw [show derivative D = 0 by rw [eq_C_of_natDegree_eq_zero h0]; exact derivative_C]
      simp
    · exact (nd_mul (nd_mul le_rfl hD') le_rfl).trans (by omega)
  have h3 : (W * D * derivative p).natDegree ≤ N :=
    (nd_mul (nd_mul le_rfl le_rfl) hp').trans (by omega)
  have e : LD p D W = C 2 * (derivative W * D * p) - C 2 * (W * derivative D * p) +
      W * D * derivative p := by
    rw [LD, show (C 2 : ℚ[X]) = 2 from map_ofNat C 2]; ring
  rw [e]
  exact (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le
    ((natDegree_C_mul_le _ _).trans h1) ((natDegree_C_mul_le _ _).trans h2))) h3)

/-- The top coefficient of `L_D(W)`. -/
lemma coeff_top_LD (p D W : ℚ[X]) (hp1 : 1 ≤ p.natDegree) (hDW : D.natDegree < W.natDegree) :
    (LD p D W).coeff (W.natDegree + D.natDegree + p.natDegree - 1) =
      W.leadingCoeff * D.leadingCoeff * p.leadingCoeff *
        (2 * W.natDegree - 2 * D.natDegree + p.natDegree) := by
  set dW := W.natDegree
  set dD := D.natDegree
  set n := p.natDegree
  have hdW : 1 ≤ dW := by omega
  -- the three products
  have c1 : (derivative W * D * p).coeff (dW + dD + n - 1) =
      (dW * W.leadingCoeff) * D.leadingCoeff * p.leadingCoeff := by
    rw [show dW + dD + n - 1 = ((dW - 1) + dD) + n by omega,
      coeff_mul_add_eq_of_natDegree_le (df := (dW - 1) + dD) (dg := n)
        (nd_mul (natDegree_derivative_le W) le_rfl) le_rfl,
      coeff_mul_add_eq_of_natDegree_le (df := dW - 1) (dg := dD) (natDegree_derivative_le W) le_rfl,
      coeff_derivative, show dW - 1 + 1 = dW by omega]
    have hcast : ((dW - 1 : ℕ) : ℚ) + 1 = (dW : ℚ) := by
      rw [Nat.cast_sub hdW]; push_cast; ring
    rw [hcast]
    change W.leadingCoeff * (dW : ℚ) * D.leadingCoeff * p.leadingCoeff = _
    ring
  have c2 : (W * derivative D * p).coeff (dW + dD + n - 1) =
      W.leadingCoeff * (dD * D.leadingCoeff) * p.leadingCoeff := by
    rcases Nat.eq_zero_or_pos dD with h0 | hpos
    · have : derivative D = 0 := by rw [eq_C_of_natDegree_eq_zero h0]; exact derivative_C
      rw [this, mul_zero, zero_mul, coeff_zero, h0]; simp
    · rw [show dW + dD + n - 1 = (dW + (dD - 1)) + n by omega,
        coeff_mul_add_eq_of_natDegree_le (df := dW + (dD - 1)) (dg := n)
          (nd_mul le_rfl (natDegree_derivative_le D)) le_rfl,
        coeff_mul_add_eq_of_natDegree_le (df := dW) (dg := dD - 1) le_rfl
          (natDegree_derivative_le D), coeff_derivative, show dD - 1 + 1 = dD by omega]
      have hcast : ((dD - 1 : ℕ) : ℚ) + 1 = (dD : ℚ) := by
        rw [Nat.cast_sub hpos]; push_cast; ring
      rw [hcast]
      change W.leadingCoeff * (D.leadingCoeff * (dD : ℚ)) * p.leadingCoeff = _
      ring
  have c3 : (W * D * derivative p).coeff (dW + dD + n - 1) =
      W.leadingCoeff * D.leadingCoeff * (n * p.leadingCoeff) := by
    rw [show dW + dD + n - 1 = (dW + dD) + (n - 1) by omega,
      coeff_mul_add_eq_of_natDegree_le (df := dW + dD) (dg := n - 1) (nd_mul le_rfl le_rfl)
        (natDegree_derivative_le p),
      coeff_mul_add_eq_of_natDegree_le (df := dW) (dg := dD) le_rfl le_rfl, coeff_derivative,
      show n - 1 + 1 = n by omega]
    have hcast : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by
      rw [Nat.cast_sub hp1]; push_cast; ring
    rw [hcast]
    change W.leadingCoeff * D.leadingCoeff * (p.leadingCoeff * (n : ℚ)) = _
    ring
  have e : LD p D W = C 2 * (derivative W * D * p) - C 2 * (W * derivative D * p) +
      W * D * derivative p := by
    rw [LD, show (C 2 : ℚ[X]) = 2 from map_ofNat C 2]; ring
  rw [e, coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, c1, c2, c3]
  ring

/-- **The degree bound.** -/
theorem hermite_deg_bound (p : ℚ[X]) (hp1 : 1 ≤ p.natDegree) (A D W B₀ : ℚ[X]) (T : Finset ℚ)
    (c : ℚ → ℚ) (hD : D ≠ 0) (hB : B₀ = 0 ∨ B₀.natDegree + 2 ≤ p.natDegree)
    (hid : 2 * A * D * (∏ α ∈ T, (X - C α)) = (∏ α ∈ T, (X - C α)) * LD p D W +
      2 * D ^ 2 * (∏ α ∈ T, (X - C α)) * B₀ +
      2 * D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)) :
    W.natDegree ≤ max A.natDegree D.natDegree := by
  classical
  by_contra hlt
  push_neg at hlt
  have hWA : A.natDegree < W.natDegree := lt_of_le_of_lt (le_max_left _ _) hlt
  have hWD : D.natDegree < W.natDegree := lt_of_le_of_lt (le_max_right _ _) hlt
  have hW : W ≠ 0 := by rintro rfl; simp at hWD
  set S := ∏ α ∈ T, (X - C α)
  have hSmon : S.Monic := monic_prod_of_monic _ _ fun α _ ↦ monic_X_sub_C α
  have hSdeg : S.natDegree = T.card := by
    rw [natDegree_prod_of_monic _ _ fun α _ ↦ monic_X_sub_C α]; simp
  set N := S.natDegree + (W.natDegree + D.natDegree + p.natDegree - 1)
  -- the `L`-term has a non-zero coefficient at `N`
  have hL : (S * LD p D W).coeff N ≠ 0 := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl (natDegree_LD_le p D W hp1),
      coeff_top_LD p D W hp1 hWD]
    have hp0 : p ≠ 0 := by rintro rfl; simp at hp1
    change S.leadingCoeff * _ ≠ 0
    rw [hSmon.leadingCoeff, one_mul]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hW)
      (leadingCoeff_ne_zero.mpr hD)) (leadingCoeff_ne_zero.mpr hp0)) ?_
    have : (D.natDegree : ℚ) < W.natDegree := by exact_mod_cast hWD
    have : (0 : ℚ) < p.natDegree := by exact_mod_cast (show 0 < p.natDegree by omega)
    linarith
  -- the other terms vanish there
  have hA : (2 * A * D * S).coeff N = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    have h2 : (2 : ℚ[X]).natDegree ≤ 0 := by simp
    calc (2 * A * D * S).natDegree ≤ 0 + A.natDegree + D.natDegree + S.natDegree :=
          nd_mul (nd_mul (nd_mul h2 le_rfl) le_rfl) le_rfl
      _ < N := by omega
  have hB0 : (2 * D ^ 2 * S * B₀).coeff N = 0 := by
    rcases hB with h | h
    · rw [h, mul_zero, coeff_zero]
    · refine coeff_eq_zero_of_natDegree_lt ?_
      have h2 : (2 : ℚ[X]).natDegree ≤ 0 := by simp
      have hD2 : (D ^ 2).natDegree ≤ 2 * D.natDegree := natDegree_pow_le.trans (by omega)
      calc (2 * D ^ 2 * S * B₀).natDegree ≤ 0 + 2 * D.natDegree + S.natDegree + B₀.natDegree :=
            nd_mul (nd_mul (nd_mul h2 hD2) le_rfl) le_rfl
        _ < N := by omega
  have hC0 : (2 * D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)).coeff N = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    have hsum : (∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)).natDegree ≤ S.natDegree - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun α hα ↦ ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_prod_of_monic _ _ fun β _ ↦ monic_X_sub_C β]
      simp [Finset.card_erase_of_mem hα, hSdeg]
    have h2 : (2 : ℚ[X]).natDegree ≤ 0 := by simp
    have hD2 : (D ^ 2).natDegree ≤ 2 * D.natDegree := natDegree_pow_le.trans (by omega)
    calc (2 * D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)).natDegree ≤
          0 + 2 * D.natDegree + (S.natDegree - 1) := nd_mul (nd_mul h2 hD2) hsum
      _ < N := by omega
  have := congrArg (fun P ↦ P.coeff N) hid
  simp only [coeff_add, hA, hB0, hC0, add_zero, zero_add] at this
  exact hL this.symm

end EllAlgo
