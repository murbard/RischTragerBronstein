import RischTragerBronstein.Mixed.NKSplitInf
import RischTragerBronstein.Curves.Reparam

/-!
# Leading coefficients of the branches at infinity for a fractional slope

The version of `leadPoly_eq_prod` with any weight `σ` (the split case is `σ = N s`): for
`F = Yⁿ + ∑ aᵢ(x) Yⁱ` with `N deg aᵢ ≤ σ (n − i)` and a branch system `x = T^{-N}` above infinity
with roots `ρ`, the scaled roots `ρ T^σ` are power series, and their constant terms are the roots
of `L_σ(Z) = ∑ᵢ [aᵢ]_{σ(n−i)/N} Zⁱ` (the coefficient taken when `N ∣ σ(n − i)`, else `0`):
`L_σ = ∏_ρ (Z − [ρ T^σ]₀)` (`leadPolyR_eq_prod`). For a slope `s'/e` one takes `N = e N'`,
`σ = N' s'` (`branchSys_lsub`: a branch system can be reparametrized by `T ↦ Tᵉ`).
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Series

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- `P(T^{-N}) T^m` as a sum. -/
lemma infSub_mul_single_eq' (N m : ℕ) (P : C[X]) :
    infSub (K := K) N P * single (m : ℤ) 1 =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        HahnSeries.C (algebraMap C K (P.coeff j)) * single ((m : ℤ) - N * j) 1 := by
  rw [infSub, coe_eval₂RingHom, eval₂_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [RingHom.comp_apply, single_pow, one_pow, mul_assoc, single_mul_single, one_mul]
  congr 2
  push_cast
  ring

/-- Bounded degree: `P(T^{-N}) T^m` is a power series when `N deg P ≤ m`. -/
lemma lowerBd_infSub_mul' (N m : ℕ) (P : C[X]) (hP : N * P.natDegree ≤ m) :
    LowerBd (infSub (K := K) N P * single (m : ℤ) 1) 0 := by
  rw [infSub_mul_single_eq']
  refine lowerBd_sum _ _ fun j hj ↦ ?_
  have hj' : j ≤ P.natDegree := by have := Finset.mem_range.mp hj; omega
  have h1 := (lowerBd_single ((m : ℤ) - N * j) (1 : K))
  have h2 : (0 : ℤ) ≤ (m : ℤ) - N * j := by
    have : N * j ≤ N * P.natDegree := Nat.mul_le_mul_left _ hj'
    push_cast; omega
  have := (lowerBd_C (algebraMap C K (P.coeff j))).mul (h1.mono h2)
  simpa using this

/-- The constant term of `P(T^{-N}) T^m`: the coefficient of `x^{m/N}` if `N ∣ m`, else `0`. -/
lemma coeff_zero_infSub_mul' (N m : ℕ) (hN : 0 < N) (P : C[X]) :
    (infSub (K := K) N P * single (m : ℤ) 1).coeff 0 =
      if N ∣ m then algebraMap C K (P.coeff (m / N)) else 0 := by
  rw [infSub_mul_single_eq', HahnSeries.coeff_sum]
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_single,
    smul_eq_mul]
  have key : ∀ j : ℕ, ((0 : ℤ) = (m : ℤ) - N * j) ↔ m = N * j := fun j ↦ by
    constructor
    · intro h; exact_mod_cast (show (m : ℤ) = N * j by linarith)
    · intro h; rw [h]; push_cast; ring
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left k hN]
    by_cases hk : k < P.natDegree + 1
    · rw [Finset.sum_eq_single k]
      · simp [key]
      · intro j _ hjk
        rw [if_neg (fun h ↦ hjk ((Nat.eq_of_mul_eq_mul_left hN ((key j).mp h)).symm)), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have hj' := Finset.mem_range.mp hj
      rw [if_neg (fun h ↦ by
        have := Nat.eq_of_mul_eq_mul_left hN ((key j).mp h)
        omega), mul_zero]
  · refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [if_neg (fun h ↦ hdvd ⟨j, (key j).mp h⟩), mul_zero]

end Series

section Lead

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- **The leading polynomial of weight `σ`** `∑ᵢ [aᵢ]_{σ(n−i)/N} Zⁱ` (the terms with
`N ∣ σ (n − i)`). -/
noncomputable def leadPolyR (N σ : ℕ) (F : C[X][X]) : C[X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1),
    Polynomial.C (if N ∣ σ * (F.natDegree - i) then
      (F.coeff i).coeff (σ * (F.natDegree - i) / N) else 0) * X ^ i

/-- The scaled polynomial `T^{σ n} F(T^{-N}, T^{-σ} Z)`. -/
noncomputable def gserR (N σ : ℕ) (F : C[X][X]) : (LaurentSeries K)[X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1), Polynomial.C (infSub (K := K) N (F.coeff i) *
    single ((σ * (F.natDegree - i) : ℕ) : ℤ) 1) * X ^ i

lemma gserR_coeff (N σ : ℕ) (F : C[X][X]) (i : ℕ) (hi : i ≤ F.natDegree) :
    (gserR (K := K) N σ F).coeff i =
      infSub (K := K) N (F.coeff i) * single ((σ * (F.natDegree - i) : ℕ) : ℤ) 1 := by
  rw [gserR, finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro j _ hji; rw [coeff_C_mul_X_pow, if_neg (Ne.symm hji)]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The scaled roots**: `gserR = ∏ (Z − ρ T^σ)`. -/
lemma gserR_eq_prod (N σ : ℕ) (F : C[X][X]) (hF : F.Monic) (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    gserR (K := K) N σ F =
      (l.map fun r ↦ X - Polynomial.C (r * single (σ : ℤ) 1)).prod := by
  classical
  set n := F.natDegree with hn
  set a : LaurentSeries K := single (-(σ : ℤ)) 1 with ha
  set b : LaurentSeries K := single (σ : ℤ) 1 with hb
  have hab : a * b = 1 := by rw [ha, hb, single_mul_single, neg_add_cancel, mul_one]; rfl
  have hlen : l.length = n := by
    have := congrArg natDegree hl
    rw [hF.natDegree_map, (list_prod_X_sub_C l).2] at this
    exact this.symm
  set g := infSub (C := C) (K := K) N with hg
  have h1 : gserR (K := K) N σ F = Polynomial.C (b ^ n) * (F.map g).comp (Polynomial.C a * X) := by
    have hFs : F.map g = ∑ i ∈ Finset.range (n + 1), Polynomial.C (g (F.coeff i)) * X ^ i := by
      conv_lhs => rw [(F.map g).as_sum_range' (n + 1) (by rw [hF.natDegree_map]; omega)]
      simp only [coeff_map, ← C_mul_X_pow_eq_monomial]
    rw [hFs, Polynomial.sum_comp, Finset.mul_sum, gserR]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow]
    simp only [← mul_assoc, ← C_mul]
    congr 2
    have hbn : b ^ n = b ^ i * b ^ (n - i) := by rw [← pow_add]; congr 1; omega
    have hba : b ^ i * a ^ i = 1 := by rw [← mul_pow, mul_comm b a, hab, one_pow]
    have hsing : b ^ (n - i) = single (((σ * (F.natDegree - i)) : ℕ) : ℤ) (1 : K) := by
      rw [hb, single_pow, one_pow, nsmul_eq_mul]
      congr 1
      have hi2 : i ≤ F.natDegree := hi'
      push_cast [Nat.cast_sub hi', Nat.cast_sub hi2]
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
    rw [List.map_congr_left fun r _ ↦ e r, List.prod_map_mul, List.map_const', List.prod_replicate,
      hlen]
  rw [h1, h2, ← mul_assoc, C_pow, ← mul_pow, ← C_mul, mul_comm b a, hab, C_1, one_pow, one_mul]

/-- **The scaled roots have no pole and their constant terms are the roots of the leading
polynomial of weight `σ`**: `L_σ = ∏_ρ (Z − [ρ T^σ]₀)`. -/
theorem leadPolyR_eq_prod (N σ : ℕ) (hN : 0 < N) (F : C[X][X]) (hF : F.Monic)
    (hdeg : ∀ i < F.natDegree, N * (F.coeff i).natDegree ≤ σ * (F.natDegree - i))
    (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (∀ r ∈ l, LowerBd (r * single (σ : ℤ) 1) 0) ∧
    (leadPolyR N σ F).map (algebraMap C K) =
      (l.map fun r ↦ X - Polynomial.C ((r * single (σ : ℤ) 1).coeff 0)).prod := by
  classical
  set n := F.natDegree with hn
  set b : LaurentSeries K := single (σ : ℤ) 1 with hb
  have hG := gserR_eq_prod N σ F hF l hl
  have hcoeffLB : ∀ i, LowerBd ((gserR (K := K) N σ F).coeff i) 0 := by
    intro i
    by_cases hi : i ≤ n
    · rw [gserR_coeff N σ F i hi]
      refine lowerBd_infSub_mul' N _ _ ?_
      rcases lt_or_eq_of_le hi with h | h
      · exact hdeg i h
      · subst h; rw [hF.coeff_natDegree, natDegree_one]; exact Nat.zero_le _
    · rw [gserR, finsetSum_coeff, Finset.sum_eq_zero fun j hj ↦ by
        rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.mp hj; omega)]]
      exact lowerBd_zero 0
  have hGl : (l.map fun r ↦ X - Polynomial.C (r * single (σ : ℤ) (1 : K))) =
      ((l.map fun r ↦ r * b).map fun r ↦ X - Polynomial.C r) := by
    rw [List.map_map]; rfl
  have hGm : (gserR (K := K) N σ F).Monic := by rw [hG, hGl]; exact (list_prod_X_sub_C _).1
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
  -- lift to power series
  set Gp : (PowerSeries K)[X] := ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (toPS ((gserR (K := K) N σ F).coeff i)) * X ^ i with hGpd
  set Pp : (PowerSeries K)[X] := (l.map fun r ↦ X - Polynomial.C (toPS (r * b))).prod with hPpd
  have hGp : Gp.map (ofPowerSeries ℤ K) = gserR (K := K) N σ F := by
    rw [hGpd, Polynomial.map_sum]
    conv_rhs => rw [(gserR (K := K) N σ F).as_sum_range' (n + 1) (by
      rw [hG, hGl, (list_prod_X_sub_C _).2, List.length_map, hlen]; omega)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      ofPS_toPS (hcoeffLB i), C_mul_X_pow_eq_monomial]
  have hPp : Pp.map (ofPowerSeries ℤ K) = gserR (K := K) N σ F := by
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
  rw [leadPolyR, Polynomial.map_sum]
  convert h1 using 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      constantCoeff_toPS, gserR_coeff N σ F i hi', coeff_zero_infSub_mul' N _ hN]
    split_ifs <;> simp
  · congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      constantCoeff_toPS]


/-- The leading polynomial of a monic `F` is monic of the same degree. -/
lemma leadPolyR_monic (N σ : ℕ) (F : C[X][X]) (hF : F.Monic) :
    (leadPolyR N σ F).Monic ∧ (leadPolyR N σ F).natDegree = F.natDegree := by
  classical
  have hc : (leadPolyR N σ F).coeff F.natDegree = 1 := by
    rw [leadPolyR, finsetSum_coeff, Finset.sum_eq_single F.natDegree]
    · rw [coeff_C_mul_X_pow, if_pos rfl, Nat.sub_self, mul_zero, if_pos (dvd_zero N), Nat.zero_div,
        hF.coeff_natDegree, coeff_one_zero]
    · intro j _ hj; rw [coeff_C_mul_X_pow, if_neg (Ne.symm hj)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hle : (leadPolyR N σ F).natDegree ≤ F.natDegree := by
    rw [leadPolyR]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hge : F.natDegree ≤ (leadPolyR N σ F).natDegree :=
    le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero)
  have hdeg : (leadPolyR N σ F).natDegree = F.natDegree := le_antisymm hle hge
  exact ⟨by rw [Monic, Polynomial.leadingCoeff, hdeg, hc], hdeg⟩

end Lead

section Reparam

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- **Reparametrizing a branch system above infinity** by `T ↦ Tᴹ`. -/
lemma branchSys_lsub (F : C[X][X]) (N M : ℕ) (hM : 0 < M) (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    F.map (infSub (N * M)) = ((l.map (lsub M hM)).map fun r ↦ X - Polynomial.C r).prod := by
  rw [← lsub_comp_infSub M hM N, ← Polynomial.map_map, hl, Polynomial.map_list_prod, List.map_map,
    List.map_map]
  congr 1
  refine List.map_congr_left fun r _ ↦ ?_
  simp

end Reparam

end Curves
