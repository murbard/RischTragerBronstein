import RischTragerBronstein.Curves.BranchEval

/-!
# Pole bounds of `W(x, y)/Q(x)` along arbitrary branches

* `root_lowerBd`: a root of `Yⁿ + ∑ cᵢ Yⁱ` with `ord cᵢ ≥ b (n − i)` (`b ≤ 0`) has order `≥ b`;
* the roots of every finite branch system are power series (`fin_root_lowerBd`), those of every
  system above infinity have order `≥ −kN` (`inf_root_lowerBd`, `k` a bound on the degrees of the
  coefficients of `F`);
* hence `W(x, y)/Q(x)` has order `≥ −N mult_a(Q)` along every branch above `a`
  (`lowerBd_fin`), and order `≥ −N (D_W − deg Q)` along every branch above infinity
  (`lowerBd_inf`, `deg Wᵢ + k i ≤ D_W`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Root

variable {K : Type*} [Field K]

/-- **Roots of monic polynomials with bounded coefficients.** -/
theorem root_lowerBd (P : (LaurentSeries K)[X]) (hP : P.Monic) (b : ℤ) (hb : b ≤ 0)
    (hc : ∀ i < P.natDegree, LowerBd (P.coeff i) (b * (P.natDegree - i : ℕ)))
    (r : LaurentSeries K) (hr : P.eval r = 0) : LowerBd r b := by
  by_contra hne
  have hr0 : r ≠ 0 := fun h ↦ hne (by rw [h]; exact lowerBd_zero b)
  set m := r.order with hm
  have hmb : m < b := by
    by_contra h
    push Not at h
    exact hne fun k hk ↦ HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  set n := P.natDegree with hn
  -- `rⁿ = −∑_{i<n} cᵢ rⁱ`
  have heq : r ^ n = -∑ i ∈ Finset.range n, P.coeff i * r ^ i := by
    have h := hr
    rw [eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul] at h
    linear_combination h
  have hlow : LowerBd (-∑ i ∈ Finset.range n, P.coeff i * r ^ i) (n * m + 1) := by
    refine LowerBd.neg (lowerBd_sum _ _ fun i hi ↦ ?_)
    have hi' := Finset.mem_range.mp hi
    have hrm : LowerBd r m := fun j hj ↦ HahnSeries.coeff_eq_zero_of_lt_order hj
    refine ((hc i hi').mul (hrm.pow i)).mono ?_
    have h1 : (b : ℤ) * (n - i : ℕ) ≥ (m + 1) * (n - i : ℕ) := by
      have : (0 : ℤ) ≤ (n - i : ℕ) := by positivity
      nlinarith
    push_cast [Nat.cast_sub hi'.le] at h1 ⊢
    nlinarith
  have hc0 : (r ^ n).coeff (n * m) ≠ 0 := by
    have := HahnSeries.coeff_order_eq_zero.not.mpr (pow_ne_zero n hr0)
    rwa [HahnSeries.order_pow, nsmul_eq_mul] at this
  rw [heq] at hc0
  exact hc0 (hlow _ (by omega))

lemma lowerBd_inv (B : LaurentSeries K) (hB : B ≠ 0) : LowerBd B⁻¹ (-B.order) := by
  set P := B.powerSeriesPart with hP
  have hP0 : PowerSeries.constantCoeff P ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff, Nat.cast_zero,
      add_zero]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hB
  have hB' : single B.order (1 : K) * ofPowerSeries ℤ K P = B :=
    single_order_mul_powerSeriesPart B
  have hinv : B⁻¹ = single (-B.order) (1 : K) * ofPowerSeries ℤ K P⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc B * (single (-B.order) (1 : K) * ofPowerSeries ℤ K P⁻¹)
        = single B.order (1 : K) * ofPowerSeries ℤ K P *
          (single (-B.order) (1 : K) * ofPowerSeries ℤ K P⁻¹) := by rw [hB']
      _ = (single B.order (1 : K) * single (-B.order) 1) * ofPowerSeries ℤ K (P * P⁻¹) := by
          rw [map_mul]; ring
      _ = 1 := by
          rw [single_mul_single, add_neg_cancel, mul_one, PowerSeries.mul_inv_cancel P hP0]
          simp
  rw [hinv]
  have := (lowerBd_single (-B.order) (1 : K)).mul (lowerBd_ofPS P⁻¹)
  rwa [add_zero] at this

end Root

section Systems

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma lowerBd_branchSub_nonneg (N : ℕ) (a : K) (P : C[X]) : LowerBd (branchSub N a P) 0 := by
  rw [branchSub_apply]; exact lowerBd_ofPS _

lemma lowerBd_infSub (N : ℕ) (hN : 0 < N) (P : C[X]) :
    LowerBd (infSub (K := K) N P) (-((N * P.natDegree : ℕ) : ℤ)) := by
  rw [infSub_eq]
  refine ((lowerBd_single _ (1 : K)).mul (lowerBd_ofPS _)).mono ?_
  push_cast; omega

/-- The roots of every finite branch system are power series. -/
theorem fin_root_lowerBd (N : ℕ) (a : K) (r : LaurentSeries K)
    (hr : (S.F.map (branchSub N a)).eval r = 0) : LowerBd r 0 := by
  refine root_lowerBd _ (S.monic.map _) 0 le_rfl (fun i _ ↦ ?_) r hr
  rw [coeff_map, zero_mul]; exact lowerBd_branchSub_nonneg N a _

/-- The roots of every system above infinity have order `≥ −kN`. -/
theorem inf_root_lowerBd (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : ∀ i, (S.F.coeff i).natDegree ≤ k)
    (r : LaurentSeries K) (hr : (S.F.map (infSub N)).eval r = 0) :
    LowerBd r (-((k * N : ℕ) : ℤ)) := by
  refine root_lowerBd _ (S.monic.map _) _ (by push_cast; nlinarith) (fun i hi ↦ ?_) r hr
  rw [coeff_map]
  rw [S.monic.natDegree_map] at hi ⊢
  refine (lowerBd_infSub N hN _).mono ?_
  have h1 : (S.F.coeff i).natDegree ≤ k * (S.F.natDegree - i) :=
    (hk i).trans (Nat.le_mul_of_pos_right k (by omega))
  have h2 := Nat.mul_le_mul_left N h1
  push_cast
  have : ((N * (S.F.coeff i).natDegree : ℕ) : ℤ) ≤ ((N * (k * (S.F.natDegree - i)) : ℕ) : ℤ) := by
    exact_mod_cast h2
  push_cast at this
  nlinarith

lemma lowerBd_eval (P : (LaurentSeries K)[X]) (Y : LaurentSeries K) (b : ℤ) (hb : b ≤ 0)
    (hY : LowerBd Y b) (m : ℤ) (hc : ∀ i, LowerBd (P.coeff i) (m - b * i)) :
    LowerBd (P.eval Y) m := by
  rw [eval_eq_sum_range]
  refine lowerBd_sum _ _ fun i _ ↦ ?_
  have := (hc i).mul (hY.pow i)
  convert this using 1; ring


/-- **Pole bound along any finite branch**: `ord φ(W/Q) ≥ −N mult_a(Q)`. -/
theorem lowerBd_fin (N : ℕ) (hN : 0 < N) (a : K) (Y : LaurentSeries K)
    (hY : (S.F.map (branchSub N a)).eval Y = 0) (z : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (Q : C[X])
    (hQ : Q ≠ 0) (hz : (z : L) * aeval S.x Q = S.evXY W) :
    LowerBd (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY z)
      (-((N * (Q.map (algebraMap C K)).rootMultiplicity a : ℕ) : ℤ)) := by
  have hbr := S.eval_W_branch (branchSub N a) (branchSub_injective N hN a) Y hY z W Q hz
  have hQ0 : branchSub (C := C) N a Q ≠ 0 := (map_ne_zero_iff _ (branchSub_injective N hN a)).mpr hQ
  have hφ : S.embG (branchSub N a) (branchSub_injective N hN a) Y hY z =
      (W.map (branchSub N a)).eval Y * (branchSub N a Q)⁻¹ := by
    rw [hbr, mul_assoc, mul_inv_cancel₀ hQ0, mul_one]
  rw [hφ]
  have h1 : LowerBd ((W.map (branchSub N a)).eval Y) 0 :=
    lowerBd_eval _ Y 0 le_rfl (S.fin_root_lowerBd N a Y hY) 0 fun i ↦ by
      rw [zero_mul, sub_zero, coeff_map]; exact lowerBd_branchSub_nonneg N a _
  have h2 := lowerBd_inv _ hQ0
  rw [order_branchSub N hN a Q hQ] at h2
  have := h1.mul h2
  rwa [zero_add] at this

/-- **Pole bound along any branch above infinity.** -/
theorem lowerBd_inf (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : ∀ i, (S.F.coeff i).natDegree ≤ k)
    (Y : LaurentSeries K) (hY : (S.F.map (infSub N)).eval Y = 0) (z : C⟮S.x⟯⟮S.y⟯)
    (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) (hz : (z : L) * aeval S.x Q = S.evXY W) (DW : ℕ)
    (hDW : ∀ i, W.coeff i ≠ 0 → (W.coeff i).natDegree + k * i ≤ DW) :
    LowerBd (S.embG (infSub N) (infSub_injective N hN) Y hY z)
      (-((N * DW : ℕ) : ℤ) + ((N * Q.natDegree : ℕ) : ℤ)) := by
  have hbr := S.eval_W_branch (infSub N) (infSub_injective N hN) Y hY z W Q hz
  have hQ0 : infSub (C := C) (K := K) N Q ≠ 0 := infSub_ne_zero N hN Q hQ
  have hφ : S.embG (infSub N) (infSub_injective N hN) Y hY z =
      (W.map (infSub N)).eval Y * (infSub N Q)⁻¹ := by
    rw [hbr, mul_assoc, mul_inv_cancel₀ hQ0, mul_one]
  rw [hφ]
  have h1 : LowerBd ((W.map (infSub N)).eval Y) (-((N * DW : ℕ) : ℤ)) := by
    refine lowerBd_eval _ Y _ (by push_cast; nlinarith) (S.inf_root_lowerBd N hN k hk Y hY) _
      fun i ↦ ?_
    rw [coeff_map]
    by_cases hWi : W.coeff i = 0
    · rw [hWi, map_zero]; exact lowerBd_zero _
    refine (lowerBd_infSub N hN _).mono ?_
    have := Nat.mul_le_mul_left N (hDW i hWi)
    push_cast at this ⊢
    nlinarith
  have h2 := lowerBd_inv _ hQ0
  rw [order_infSub N hN Q hQ, neg_neg] at h2
  have := h1.mul h2
  convert this using 1
  push_cast; ring

end CurveData

end Systems

end Curves
