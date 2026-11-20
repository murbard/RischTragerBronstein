import RischTragerBronstein.Mixed.NKUnitsInf

/-!
# Curves split at infinity: the leading coefficients of the branches

For `F = Yⁿ + ∑ aᵢ(x) Yⁱ` with `deg aᵢ ≤ (n − i) s` and a branch system `x = T^{-N}` above
infinity with roots `ρ`, the scaled roots `Z_ρ = ρ T^{N s}` are power series, and their constant
terms `γ(ρ)` are the roots of the *leading polynomial* `L(Z) = Zⁿ + ∑ [aᵢ]_{(n−i)s} Zⁱ`:
`L = ∏_ρ (Z − γ(ρ))` (`leadPoly_eq_prod`). When `L` has distinct roots in `C`, the curve is split
at infinity: one branch per root of `L`.
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Series

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- `P(T^{-N}) T^{N k}` as a sum. -/
lemma infSub_mul_single_eq (N k : ℕ) (P : C[X]) :
    infSub (K := K) N P * single ((N * k : ℕ) : ℤ) 1 =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        HahnSeries.C (algebraMap C K (P.coeff j)) * single (((N * k : ℕ) : ℤ) - N * j) 1 := by
  rw [infSub, coe_eval₂RingHom, eval₂_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [RingHom.comp_apply, single_pow, one_pow, mul_assoc, single_mul_single, one_mul]
  congr 2
  push_cast
  ring

/-- Bounded degree: `P(T^{-N}) T^{N k}` is a power series. -/
lemma lowerBd_infSub_mul (N k : ℕ) (P : C[X]) (hP : P.natDegree ≤ k) :
    LowerBd (infSub (K := K) N P * single ((N * k : ℕ) : ℤ) 1) 0 := by
  rw [infSub_mul_single_eq]
  refine lowerBd_sum _ _ fun j hj ↦ ?_
  have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
  have h1 := (lowerBd_single (((N * k : ℕ) : ℤ) - N * j) (1 : K))
  have h2 : (0 : ℤ) ≤ ((N * k : ℕ) : ℤ) - N * j := by
    push_cast; nlinarith
  have := (lowerBd_C (algebraMap C K (P.coeff j))).mul (h1.mono h2)
  simpa using this

/-- The constant term of `P(T^{-N}) T^{N k}` is the coefficient of `xᵏ`. -/
lemma coeff_zero_infSub_mul (N k : ℕ) (hN : 0 < N) (P : C[X]) :
    (infSub (K := K) N P * single ((N * k : ℕ) : ℤ) 1).coeff 0 = algebraMap C K (P.coeff k) := by
  rw [infSub_mul_single_eq, HahnSeries.coeff_sum]
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_single,
    smul_eq_mul]
  by_cases hk : k < P.natDegree + 1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      have : (0 : ℤ) ≠ ((N * k : ℕ) : ℤ) - N * j := by
        push_cast
        intro h
        have : (N : ℤ) * k = N * j := by linarith
        exact hjk (by exact_mod_cast (mul_left_cancel₀ (by exact_mod_cast hN.ne') this).symm)
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hk) h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    have : (0 : ℤ) ≠ ((N * k : ℕ) : ℤ) - N * j := by
      push_cast
      intro h
      have : (N : ℤ) * k = N * j := by linarith
      have := mul_left_cancel₀ (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0) this
      omega
    rw [if_neg this, mul_zero]

end Series

section Lead

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- **The leading polynomial** `L(Z) = ∑ᵢ [aᵢ]_{(n−i)s} Zⁱ`. -/
noncomputable def leadPoly (s : ℕ) (F : C[X][X]) : C[X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1),
    Polynomial.C ((F.coeff i).coeff (s * (F.natDegree - i))) * X ^ i

/-- The scaled polynomial `T^{N n s} F(T^{-N}, T^{-N s} Z)`. -/
noncomputable def gser (N s : ℕ) (F : C[X][X]) : (LaurentSeries K)[X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1), Polynomial.C (infSub (K := K) N (F.coeff i) *
    single ((N * (s * (F.natDegree - i)) : ℕ) : ℤ) 1) * X ^ i

lemma gser_coeff (N s : ℕ) (F : C[X][X]) (i : ℕ) (hi : i ≤ F.natDegree) :
    (gser (K := K) N s F).coeff i =
      infSub (K := K) N (F.coeff i) * single ((N * (s * (F.natDegree - i)) : ℕ) : ℤ) 1 := by
  rw [gser, finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro j _ hji; rw [coeff_C_mul_X_pow, if_neg (Ne.symm hji)]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The scaled roots**: `gser = ∏ (Z − ρ T^{N s})`. -/
lemma gser_eq_prod (N s : ℕ) (F : C[X][X]) (hF : F.Monic) (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    gser (K := K) N s F =
      (l.map fun r ↦ X - Polynomial.C (r * single ((N * s : ℕ) : ℤ) 1)).prod := by
  classical
  set n := F.natDegree with hn
  set a : LaurentSeries K := single (-((N * s : ℕ) : ℤ)) 1 with ha
  set b : LaurentSeries K := single ((N * s : ℕ) : ℤ) 1 with hb
  have hab : a * b = 1 := by rw [ha, hb, single_mul_single, neg_add_cancel, mul_one]; rfl
  have hlen : l.length = n := by
    have := congrArg natDegree hl
    rw [hF.natDegree_map, (list_prod_X_sub_C l).2] at this
    exact this.symm
  set g := infSub (C := C) (K := K) N with hg
  have h1 : gser (K := K) N s F = Polynomial.C (b ^ n) * (F.map g).comp (Polynomial.C a * X) := by
    have hFs : F.map g = ∑ i ∈ Finset.range (n + 1), Polynomial.C (g (F.coeff i)) * X ^ i := by
      conv_lhs => rw [(F.map g).as_sum_range' (n + 1) (by rw [hF.natDegree_map]; omega)]
      simp only [coeff_map, ← C_mul_X_pow_eq_monomial]
    rw [hFs, Polynomial.sum_comp, Finset.mul_sum, gser]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow]
    simp only [← mul_assoc, ← C_mul]
    congr 2
    have hbn : b ^ n = b ^ i * b ^ (n - i) := by rw [← pow_add]; congr 1; omega
    have hba : b ^ i * a ^ i = 1 := by rw [← mul_pow, mul_comm b a, hab, one_pow]
    have hsing : b ^ (n - i) = single (((N * s * (F.natDegree - i)) : ℕ) : ℤ) (1 : K) := by
      rw [hb, single_pow, one_pow, nsmul_eq_mul]
      congr 1
      have hi2 : i ≤ F.natDegree := hi'
      push_cast [Nat.cast_sub hi', Nat.cast_sub hi2]
      congr 1
      rw [hn]
      ring
    rw [← hsing, hbn]
    linear_combination (-(g (F.coeff i) * b ^ (n - i))) * hba
  have h2 : (F.map g).comp (Polynomial.C a * X) = Polynomial.C a ^ n *
      (l.map fun r ↦ X - Polynomial.C (r * b)).prod := by
    rw [hl, list_prod_comp, List.map_map]
    have e : ∀ r : LaurentSeries K, ((fun p ↦ p.comp (Polynomial.C a * X)) ∘
        fun r ↦ X - Polynomial.C r) r = Polynomial.C a * (X - Polynomial.C (r * b)) := by
      intro r
      simp only [Function.comp_apply, sub_comp, X_comp, C_comp, mul_sub, ← C_mul]
      rw [show a * (r * b) = r by rw [mul_comm r b, ← mul_assoc, hab, one_mul]]
    rw [List.map_congr_left fun r _ ↦ e r, List.prod_map_mul, List.map_const', List.prod_replicate, hlen]
  rw [h1, h2, ← mul_assoc, C_pow, ← mul_pow, ← C_mul, mul_comm b a, hab, C_1, one_pow, one_mul]

/-- The power series of a Laurent series without pole. -/
noncomputable def toPS (z : LaurentSeries K) : PowerSeries K := PowerSeries.mk fun k ↦ z.coeff k

lemma ofPS_toPS {z : LaurentSeries K} (hz : LowerBd z 0) : ofPowerSeries ℤ K (toPS z) = z := by
  ext k
  rw [LaurentSeries.coeff_ofPS]
  split_ifs with hk
  · rw [toPS, PowerSeries.coeff_mk, Int.toNat_of_nonneg hk]
  · exact (hz k (by omega)).symm

lemma constantCoeff_toPS (z : LaurentSeries K) : PowerSeries.constantCoeff (toPS z) = z.coeff 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, toPS, PowerSeries.coeff_mk]; rfl

/-- **The scaled roots have no pole and their constant terms are the roots of the leading
polynomial**: `L = ∏_ρ (Z − [ρ T^{N s}]₀)`. -/
theorem leadPoly_eq_prod (N s : ℕ) (hN : 0 < N) (F : C[X][X]) (hF : F.Monic)
    (hdeg : ∀ i < F.natDegree, (F.coeff i).natDegree ≤ s * (F.natDegree - i))
    (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (∀ r ∈ l, LowerBd (r * single ((N * s : ℕ) : ℤ) 1) 0) ∧
    (leadPoly s F).map (algebraMap C K) =
      (l.map fun r ↦ X - Polynomial.C ((r * single ((N * s : ℕ) : ℤ) 1).coeff 0)).prod := by
  classical
  set n := F.natDegree with hn
  set b : LaurentSeries K := single ((N * s : ℕ) : ℤ) 1 with hb
  have hG := gser_eq_prod N s F hF l hl
  have hcoeffLB : ∀ i, LowerBd ((gser (K := K) N s F).coeff i) 0 := by
    intro i
    by_cases hi : i ≤ n
    · rw [gser_coeff N s F i hi, show N * (s * (F.natDegree - i)) = N * (s * (n - i)) from rfl]
      refine lowerBd_infSub_mul N _ _ ?_
      rcases lt_or_eq_of_le hi with h | h
      · exact hdeg i h
      · subst h; rw [hF.coeff_natDegree, natDegree_one]; exact Nat.zero_le _
    · rw [gser, finsetSum_coeff, Finset.sum_eq_zero fun j hj ↦ by
        rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.mp hj; omega)]]
      exact lowerBd_zero 0
  have hGl : (l.map fun r ↦ X - Polynomial.C (r * single ((N * s : ℕ) : ℤ) (1 : K))) =
      ((l.map fun r ↦ r * b).map fun r ↦ X - Polynomial.C r) := by
    rw [List.map_map]; rfl
  have hGm : (gser (K := K) N s F).Monic := by rw [hG, hGl]; exact (list_prod_X_sub_C _).1
  have hroots : ∀ r ∈ l, LowerBd (r * b) 0 := fun r hr ↦
    lowerBd_root _ hGm hcoeffLB _ (by
      rw [hG, eval_list_prod]
      exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩,
        by simp [hb]⟩))
  refine ⟨hroots, ?_⟩
  have hlen : l.length = n := by
    have := congrArg natDegree hl
    rw [hF.natDegree_map, (list_prod_X_sub_C l).2] at this
    exact this.symm
  have hGdeg : (gser (K := K) N s F).natDegree = n := by
    rw [hG, hGl, (list_prod_X_sub_C _).2, List.length_map, hlen]
  -- lift to power series
  set Gp : (PowerSeries K)[X] := ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (toPS ((gser (K := K) N s F).coeff i)) * X ^ i with hGpd
  set Pp : (PowerSeries K)[X] := (l.map fun r ↦ X - Polynomial.C (toPS (r * b))).prod with hPpd
  have hGp : Gp.map (ofPowerSeries ℤ K) = gser (K := K) N s F := by
    rw [hGpd, Polynomial.map_sum]
    conv_rhs => rw [(gser (K := K) N s F).as_sum_range' (n + 1) (by omega)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      ofPS_toPS (hcoeffLB i), C_mul_X_pow_eq_monomial]
  have hPp : Pp.map (ofPowerSeries ℤ K) = gser (K := K) N s F := by
    rw [hPpd, hG, Polynomial.map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun r hr ↦ ?_
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      ofPS_toPS (hroots r hr)]
    rfl
  have hGP : Gp = Pp := Polynomial.map_injective _ (HahnSeries.ofPowerSeries_injective)
    (hGp.trans hPp.symm)
  have h1 := congrArg (Polynomial.map (PowerSeries.constantCoeff (R := K))) hGP
  rw [hGpd, hPpd, Polynomial.map_sum, Polynomial.map_list_prod, List.map_map] at h1
  rw [leadPoly, Polynomial.map_sum]
  convert h1 using 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      constantCoeff_toPS, gser_coeff N s F i hi', coeff_zero_infSub_mul N _ hN]
  · congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      constantCoeff_toPS]

end Lead

end Curves
