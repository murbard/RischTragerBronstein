import RischTragerBronstein.Mixed.NKSplitInf

/-!
# Initial forms of polynomials over Laurent series (Newton polygons without valuations)

For `G = ∏ᵣ (X − r)` over `K⸨T⸩` and a weight `σ`, the substitution `X = T^{−σ} Z` followed by a
suitable power `T^k` lands in `K⟦T⟧[Z]`, and its reduction modulo `T` (the *initial form*) is
`∏ᵣ fᵣ` with `fᵣ = Z − [r T^σ]₀` when `r` has no term below `T^{−σ}` and `fᵣ = −lc(r)` otherwise
(`initForm`). For `G = F(T^{−N}, X)` the initial form is read off the coefficients of `F`
(`initForm_coeff`): its `i`-th coefficient is the coefficient of `T^{iσ − k}` in `aᵢ(T^{−N})`.

This replaces the Newton polygon: the number of roots of order exactly `−σ` and their leading
coefficients are the non-zero roots of the initial form, and the roots of larger order contribute
the factor `Z^{…}`. It generalizes `leadPoly_eq_prod` (the top slope, where no root has smaller
order) to every slope.
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

variable {K : Type*} [Field K]

open Classical in
lemma coeff_mul_single_one (r : LaurentSeries K) (a k : ℤ) :
    (r * single a (1 : K)).coeff k = r.coeff (k - a) := by
  rw [HahnSeries.coeff_mul_single, mul_one]

lemma lowerBd_iff_le_order {r : LaurentSeries K} (hr : r ≠ 0) (m : ℤ) :
    LowerBd r m ↔ m ≤ r.order := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact hr (HahnSeries.coeff_order_eq_zero.mp (h _ hlt))
  · intro h k hk
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk h)

lemma coeff_zero_ofPS (p : PowerSeries K) :
    (ofPowerSeries ℤ K p).coeff 0 = PowerSeries.constantCoeff p := by
  rw [LaurentSeries.coeff_ofPS]
  simp

open Classical in
/-- The normalized factor of `X − r` for the weight `σ`, over `K⟦T⟧`. -/
noncomputable def initFac (σ : ℤ) (r : LaurentSeries K) : (PowerSeries K)[X] :=
  if LowerBd r (-σ) then X - Polynomial.C (toPS (r * single σ 1))
  else Polynomial.C (toPS (single (-r.order - σ) (1 : K))) * X -
    Polynomial.C (toPS (r * single (-r.order) 1))

open Classical in
/-- The normalizing exponent of `X − r`. -/
noncomputable def initExp (σ : ℤ) (r : LaurentSeries K) : ℤ :=
  if LowerBd r (-σ) then σ else -r.order

open Classical in
/-- The reduction of the normalized factor. -/
noncomputable def initRed (σ : ℤ) (r : LaurentSeries K) : K[X] :=
  if LowerBd r (-σ) then X - Polynomial.C ((r * single σ 1).coeff 0)
  else Polynomial.C (-(r.coeff r.order))

open Classical in
lemma initFac_ofPS (σ : ℤ) (r : LaurentSeries K) (hr : r ≠ 0) :
    (initFac σ r).map (ofPowerSeries ℤ K) = Polynomial.C (single (initExp σ r) 1) *
      (Polynomial.C (single (-σ) 1) * X - Polynomial.C r) := by
  unfold initFac initExp
  split_ifs with h
  · have hLB : LowerBd (r * single σ 1) 0 := fun k hk ↦ by
      rw [coeff_mul_single_one]; exact h _ (by omega)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ofPS_toPS hLB, mul_sub,
      ← mul_assoc, ← Polynomial.C_mul, single_mul_single, add_neg_cancel, mul_one, ← C_mul,
      mul_comm (single σ (1 : K)) r]
    simp
  · have hLB1 : LowerBd (single (-r.order - σ) (1 : K)) 0 := fun k hk ↦ by
      rw [lowerBd_iff_le_order hr] at h
      rw [HahnSeries.coeff_single, if_neg (by omega)]
    have hLB2 : LowerBd (r * single (-r.order) 1) 0 := fun k hk ↦ by
      rw [coeff_mul_single_one]
      exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_C, ofPS_toPS hLB1, ofPS_toPS hLB2, mul_sub, ← mul_assoc, ← Polynomial.C_mul,
      single_mul_single, ← C_mul, mul_comm (single (-r.order) (1 : K)) r]
    congr 3; ring_nf

open Classical in
lemma initFac_red (σ : ℤ) (r : LaurentSeries K) (hr : r ≠ 0) :
    (initFac σ r).map PowerSeries.constantCoeff = initRed σ r := by
  unfold initFac initRed
  split_ifs with h
  · rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, constantCoeff_toPS]
  · have hlt : r.order < -σ := by
      rw [lowerBd_iff_le_order hr] at h; omega
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_C, constantCoeff_toPS, constantCoeff_toPS, HahnSeries.coeff_single,
      if_neg (by omega), coeff_mul_single_one]
    simp

/-- **The initial form of a product of linear factors.** -/
theorem initForm (σ : ℤ) (l : List (LaurentSeries K)) (hl : ∀ r ∈ l, r ≠ 0) :
    ∃ (P : (PowerSeries K)[X]) (k : ℤ),
      P.map (ofPowerSeries ℤ K) = Polynomial.C (single k 1) *
        ((l.map fun r ↦ X - Polynomial.C r).prod).comp (Polynomial.C (single (-σ) 1) * X) ∧
      P.map PowerSeries.constantCoeff = (l.map (initRed σ)).prod := by
  induction l with
  | nil => exact ⟨1, 0, by simp, by simp⟩
  | cons r l ih =>
    obtain ⟨P, k, hP, hPr⟩ := ih fun r' hr' ↦ hl r' (List.mem_cons_of_mem _ hr')
    have hr := hl r (List.mem_cons_self ..)
    refine ⟨initFac σ r * P, initExp σ r + k, ?_, ?_⟩
    · rw [Polynomial.map_mul, initFac_ofPS σ r hr, hP, List.map_cons, List.prod_cons, mul_comp,
        sub_comp, X_comp, C_comp, show single (initExp σ r + k) (1 : K) =
          single (initExp σ r) 1 * single k 1 by rw [single_mul_single, one_mul], C_mul]
      ring
    · rw [Polynomial.map_mul, initFac_red σ r hr, hPr, List.map_cons, List.prod_cons]

/-- **The initial form from the coefficients**: for `G = F(T^{−N}, X)` its `i`-th coefficient is
`[T^{iσ − k}] aᵢ(T^{−N})`. -/
theorem initForm_coeff {C : Type*} [Field C] [Algebra C K] (N : ℕ) (σ : ℤ) (F : C[X][X])
    (l : List (LaurentSeries K)) (hl0 : ∀ r ∈ l, r ≠ 0)
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    ∃ k : ℤ, (∀ i, LowerBd (infSub (K := K) N (F.coeff i) * single (k - i * σ) 1) 0) ∧
      ∑ i ∈ Finset.range (F.natDegree + 1),
        Polynomial.C ((infSub (K := K) N (F.coeff i)).coeff (i * σ - k)) * X ^ i =
      (l.map (initRed σ)).prod := by
  classical
  obtain ⟨P, k, hP, hPr⟩ := initForm σ l hl0
  have hc : ∀ i, ofPowerSeries ℤ K (P.coeff i) =
      infSub (K := K) N (F.coeff i) * single (k - i * σ) 1 := by
    intro i
    have := congrArg (fun Q ↦ Q.coeff i) hP
    simp only [Polynomial.coeff_map] at this
    rw [this, ← hl, Polynomial.coeff_C_mul, comp_C_mul_X_coeff, Polynomial.coeff_map, single_pow,
      one_pow, mul_comm, mul_assoc, single_mul_single, one_mul]
    congr 2
    rw [nsmul_eq_mul]; ring
  refine ⟨k, fun i ↦ ?_, ?_⟩
  · rw [← hc]
    intro j hj
    rw [LaurentSeries.coeff_ofPS, if_neg (by omega)]
  · rw [← hPr]
    ext i
    rw [Polynomial.coeff_map, finsetSum_coeff]
    by_cases hi : i ≤ F.natDegree
    · rw [Finset.sum_eq_single i (fun j _ hji ↦ by rw [coeff_C_mul_X_pow, if_neg (Ne.symm hji)])
        (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h), coeff_C_mul_X_pow, if_pos rfl,
        ← coeff_zero_ofPS, hc, coeff_mul_single_one]
      ring_nf
    · rw [Finset.sum_eq_zero fun j hj ↦ by
        rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.mp hj; omega)]]
      have hz : P.coeff i = 0 := by
        apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
        rw [hc, show F.coeff i = 0 from Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          map_zero, zero_mul, map_zero]
      rw [hz, map_zero]

end Curves
