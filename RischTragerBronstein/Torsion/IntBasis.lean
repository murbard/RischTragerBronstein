import RischTragerBronstein.Curves.ProcLogSem1

/-!
# Integral bases from local independence

For elements `w₀, …, w_{n−1}` of the function field, integral along the branches above `a`:

* `LocIndep w N a r`: the expansions of the `w_j` along the branch system `r` (with `x = a + Tᴺ`)
  are linearly independent modulo `Tᴺ`, i.e. no non-trivial combination is divisible by `x − a`;
* `coords_regular_at`: then, if `z = ∑ q_j w_j` (`q_j ∈ C(x)`) is integral along the branches
  above `a`, every `q_j` is regular at `a`;
* `coords_poly_of_indep`: with local independence above every point, the coordinates of an
  integral `z` are polynomials — `(w_j)` is an integral basis.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Supp

variable {K : Type*} [Field K]

/-- A Laurent series supported on `Nℤ`, bounded below by `m ∈ Nℤ`, minus its `Tᵐ` term, is
bounded below by `m + N`. -/
lemma lowerBd_sub_lead (z : LaurentSeries K) (N : ℕ) (m : ℤ) (hNm : (N : ℤ) ∣ m)
    (hsupp : ∀ i, ¬ (N : ℤ) ∣ i → z.coeff i = 0) (hz : LowerBd z m) :
    LowerBd (z - HahnSeries.C (z.coeff m) * single m (1 : K)) (m + N) := by
  intro i hi
  rw [HahnSeries.coeff_sub, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
    HahnSeries.coeff_single]
  rcases lt_trichotomy i m with h | h | h
  · rw [hz i h, if_neg h.ne, mul_zero, sub_zero]
  · subst h; rw [if_pos rfl, mul_one, sub_self]
  · rw [if_neg h.ne', mul_zero, sub_zero]
    refine hsupp i fun hd ↦ ?_
    obtain ⟨a, ha⟩ := hNm
    obtain ⟨b, hb⟩ := hd
    have : a < b := by
      by_contra hab; push Not at hab
      have := mul_le_mul_of_nonneg_left hab (Int.natCast_nonneg N); omega
    have : a + 1 ≤ b := this
    have := mul_le_mul_of_nonneg_left this (Int.natCast_nonneg N)
    rw [mul_add, mul_one] at this
    omega

end Supp

section Basis

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- `branchSub N a = lsub N ∘ branchSub 1 a` on `C(x)`. -/
lemma embXG_branchSub_lsub (N : ℕ) (hN : 0 < N) (a : K) (q : C⟮S.x⟯) :
    S.embXG (branchSub N a) (branchSub_injective N hN a) q =
      lsub N hN (S.embXG (branchSub 1 a) (branchSub_injective 1 one_pos a) q) := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have h := IsLocalization.ringHom_ext (nonZeroDivisors C[X])
    (j := S.embXG (branchSub N a) (branchSub_injective N hN a))
    (k := (lsub N hN).comp (S.embXG (branchSub 1 a) (branchSub_injective 1 one_pos a)))
    (RingHom.ext fun P ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, S.embXG_algebraMap,
        S.embXG_algebraMap, ← RingHom.comp_apply, lsub_comp_branchSub, one_mul])
  exact RingHom.congr_fun h q

/-- Expansions of elements of `C(x)` along `x = a + Tᴺ` are series in `Tᴺ`. -/
lemma embXG_coeff_not_dvd (N : ℕ) (hN : 0 < N) (a : K) (q : C⟮S.x⟯) (i : ℤ)
    (hi : ¬ (N : ℤ) ∣ i) : (S.embXG (branchSub N a) (branchSub_injective N hN a) q).coeff i = 0 := by
  rw [S.embXG_branchSub_lsub N hN a q]
  exact lsub_coeff_not_dvd N hN _ i hi

/-- **Local independence** of `w` along the branch system `r` above `a`. -/
def LocIndep (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (N : ℕ) (hN : 0 < N) (a : K)
    (r : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k))) : Prop :=
  ∀ c : Fin S.F.natDegree → K,
    (∀ k, LowerBd (∑ j, HahnSeries.C (c j) * S.embG (branchSub N a) (branchSub_injective N hN a)
      (r k) (S.root_of_split _ r hs k) (w j)) N) → c = 0

/-- **Regularity of the coordinates** at a point with local independence. -/
theorem coords_regular_at (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (N : ℕ) (hN : 0 < N) (a : K)
    (r : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k)))
    (hind : S.LocIndep w N hN a r hs)
    (hw : ∀ j k, LowerBd (S.embG (branchSub N a) (branchSub_injective N hN a) (r k)
      (S.root_of_split _ r hs k) (w j)) 0)
    (z : C⟮S.x⟯⟮S.y⟯)
    (hz : ∀ k, LowerBd (S.embG (branchSub N a) (branchSub_injective N hN a) (r k)
      (S.root_of_split _ r hs k) z) 0)
    (q : Fin S.F.natDegree → C⟮S.x⟯) (hzq : z = ∑ j, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (q j) * w j) :
    ∀ j, LowerBd (S.embXG (branchSub N a) (branchSub_injective N hN a) (q j)) 0 := by
  classical
  set E : Fin S.F.natDegree → LaurentSeries K :=
    fun j ↦ S.embXG (branchSub N a) (branchSub_injective N hN a) (q j) with hE
  set φ := fun k ↦ S.embG (branchSub N a) (branchSub_injective N hN a) (r k)
    (S.root_of_split _ r hs k) with hφ
  by_contra hneg
  push Not at hneg
  -- the smallest order
  have hex : ∃ j, E j ≠ 0 ∧ (E j).order < 0 := by
    obtain ⟨j, hj⟩ := hneg
    have hE0 : E j ≠ 0 := by
      intro h0; apply hj; show LowerBd (E j) 0; rw [h0]; exact lowerBd_zero 0
    refine ⟨j, hE0, ?_⟩
    by_contra hge; push Not at hge
    exact hj fun i hi ↦ HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi hge)
  set T := (Finset.univ.filter fun j ↦ E j ≠ 0) with hT
  have hTne : T.Nonempty := by
    obtain ⟨j, hj, -⟩ := hex
    exact ⟨j, by simp [hT, hj]⟩
  set m := T.inf' hTne fun j ↦ (E j).order with hm
  have hmle : ∀ j, LowerBd (E j) m := fun j i hi ↦ by
    by_cases h0 : E j = 0
    · rw [h0, HahnSeries.coeff_zero]
    · refine HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi ?_)
      exact Finset.inf'_le _ (by simp [hT, h0])
  obtain ⟨j0, hj0T, hj0⟩ := Finset.exists_mem_eq_inf' hTne fun j ↦ (E j).order
  have hj0ne : E j0 ≠ 0 := by simpa [hT] using hj0T
  have hm0 : m = (E j0).order := by rw [hm]; exact hj0
  have hmneg : m < 0 := by
    obtain ⟨j, hj, hjo⟩ := hex
    exact lt_of_le_of_lt (Finset.inf'_le _ (by simp [hT, hj])) hjo
  have hsupp : ∀ j i, ¬ (N : ℤ) ∣ i → (E j).coeff i = 0 := fun j i hi ↦
    S.embXG_coeff_not_dvd N hN a (q j) i hi
  have hNm : (N : ℤ) ∣ m := by
    by_contra hnd
    have := hsupp j0 m hnd
    rw [hm0] at this
    exact HahnSeries.coeff_order_eq_zero.not.mpr hj0ne this
  have hmN : m + N ≤ 0 := by
    obtain ⟨c, hc⟩ := hNm
    have hc0 : c < 0 := by
      by_contra h; push Not at h
      have := mul_nonneg (Int.natCast_nonneg N) h; omega
    have : c + 1 ≤ 0 := by omega
    have := mul_le_mul_of_nonneg_left this (Int.natCast_nonneg N)
    rw [mul_add, mul_one, mul_zero] at this
    omega
  set c : Fin S.F.natDegree → K := fun j ↦ (E j).coeff m with hc
  have hcj0 : c j0 ≠ 0 := by
    simp only [hc]
    rw [hm0]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hj0ne
  apply hcj0
  have := hind c fun k ↦ ?_
  · rw [this]; rfl
  -- the leading part along the root `k`
  have hzk : φ k z = ∑ j, E j * φ k (w j) := by
    rw [hzq, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, S.embG_algebraMap]
  have hR : LowerBd (∑ j, (E j - HahnSeries.C (c j) * single m (1 : K)) * φ k (w j)) (m + N) :=
    lowerBd_sum _ _ fun j _ ↦ by
      have := (lowerBd_sub_lead (E j) N m hNm (hsupp j) (hmle j)).mul (hw j k)
      rwa [add_zero] at this
  have hsplit : single m (1 : K) * ∑ j, HahnSeries.C (c j) * φ k (w j) =
      φ k z - ∑ j, (E j - HahnSeries.C (c j) * single m (1 : K)) * φ k (w j) := by
    rw [hzk, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hL : LowerBd (single m (1 : K) * ∑ j, HahnSeries.C (c j) * φ k (w j)) (m + N) := by
    rw [hsplit]
    exact ((hz k).mono hmN).sub hR
  have := (lowerBd_single (-m) (1 : K)).mul hL
  rw [← mul_assoc, single_mul_single, neg_add_cancel, mul_one, show single (0 : ℤ) (1 : K) = 1 from
    rfl, one_mul, show -m + (m + N) = (N : ℤ) by ring] at this
  exact this

/-- **Integral bases**: with local independence above every point, the coordinates of an integral
element are polynomials. -/
theorem coords_poly_of_indep [IsAlgClosed K] (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯)
    (hind : ∀ a : K, ∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
      ∃ hs : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k)),
        S.LocIndep w N hN a r hs ∧ ∀ j k, LowerBd (S.embG (branchSub N a)
          (branchSub_injective N hN a) (r k) (S.root_of_split _ r hs k) (w j)) 0)
    (z : C⟮S.x⟯⟮S.y⟯) (hz : S.RegularFinite K z)
    (q : Fin S.F.natDegree → C⟮S.x⟯) (hzq : z = ∑ j, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (q j) * w j) :
    ∀ j, ∃ P : C[X], (letI := algebraAdjoinSimple (F := C) S.x; algebraMap C[X] C⟮S.x⟯ P) = q j := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  intro j
  obtain ⟨A, B, hB, hq⟩ := IsFractionRing.div_surjective (A := C[X]) (q j)
  have hB0 : B ≠ 0 := nonZeroDivisors.ne_zero hB
  by_cases hA : A = 0
  · refine ⟨0, ?_⟩
    rw [← hq, hA, map_zero, zero_div]
  have hdiv : B ∣ A := by
    refine dvd_of_branch_order (K := K) A B hB0 fun a ↦ ?_
    obtain ⟨N, hN, r, hs, hI, hw⟩ := hind a
    have hzk : ∀ k, LowerBd (S.embG (branchSub N a) (branchSub_injective N hN a) (r k)
        (S.root_of_split _ r hs k) z) 0 := by
      intro k
      have hl : S.F.map (branchSub N a) = ((List.ofFn r).map fun r ↦ X - Polynomial.C r).prod := by
        rw [hs, List.map_ofFn, List.prod_ofFn]; rfl
      have hmem : r k ∈ List.ofFn r := List.mem_ofFn.mpr ⟨k, rfl⟩
      have := hz a N hN.ne' _ hl (r k) hmem
      intro i hi
      exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi this)
    have hreg := S.coords_regular_at w N hN a r hs hI hw z hzk q hzq j
    refine ⟨N, hN.ne', ?_⟩
    have hA' : branchSub (K := K) N a A ≠ 0 := (map_ne_zero_iff _ (branchSub_injective N hN a)).mpr hA
    have hB' : branchSub (K := K) N a B ≠ 0 := (map_ne_zero_iff _ (branchSub_injective N hN a)).mpr hB0
    rw [← hq, map_div₀, S.embXG_algebraMap, S.embXG_algebraMap] at hreg
    have hord : 0 ≤ (branchSub (K := K) N a A / branchSub N a B).order := by
      by_contra hneg; push Not at hneg
      exact HahnSeries.coeff_order_eq_zero.not.mpr (div_ne_zero hA' hB') (hreg _ hneg)
    rw [div_eq_mul_inv, HahnSeries.order_mul hA' (inv_ne_zero hB'), order_inv_laurent _ hB'] at hord
    omega
  obtain ⟨P, hP⟩ := hdiv
  refine ⟨P, ?_⟩
  rw [← hq, hP, map_mul, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective C[X]
    C⟮S.x⟯)).mpr hB0)]

omit [Field L] [Algebra C L] in
/-- The expansion of `P(x)` at infinity: leading term `lc P · T^{−N deg P}`, then steps of `Tᴺ`. -/
lemma infSub_lead (N : ℕ) (hN : 0 < N) (P : C[X]) (hP : P ≠ 0) :
    LowerBd (infSub (K := K) N P) (-((N * P.natDegree : ℕ) : ℤ)) ∧
      LowerBd (infSub (K := K) N P - HahnSeries.C (algebraMap C K P.leadingCoeff) *
        single (-((N * P.natDegree : ℕ) : ℤ)) (1 : K)) (-((N * P.natDegree : ℕ) : ℤ) + N) := by
  have hne : infSub (C := C) (K := K) N P ≠ 0 := infSub_ne_zero N hN P hP
  have hord := order_infSub (C := C) (K := K) N hN P hP
  have hlb : LowerBd (infSub (K := K) N P) (-((N * P.natDegree : ℕ) : ℤ)) := fun i hi ↦
    HahnSeries.coeff_eq_zero_of_lt_order (by rw [hord]; push_cast at hi ⊢; linarith)
  refine ⟨hlb, ?_⟩
  have hsupp : ∀ i, ¬ (N : ℤ) ∣ i → (infSub (K := K) N P).coeff i = 0 := by
    intro i hi
    have e : infSub (C := C) (K := K) N P = lsub N hN (infSub 1 P) := by
      rw [← RingHom.comp_apply, lsub_comp_infSub, one_mul]
    rw [e]; exact lsub_coeff_not_dvd N hN _ i hi
  have hc : (infSub (K := K) N P).coeff (-((N * P.natDegree : ℕ) : ℤ)) =
      algebraMap C K P.leadingCoeff := by
    rw [infSub_eq, LaurentSeries.coeff_single_mul]
    simp only [Nat.cast_mul, sub_self, LaurentSeries.coeff_ofPS, le_refl, if_true,
      Int.toNat_zero, Polynomial.coeff_coe]
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_pow, eval_X, zero_pow hN.ne',
      ← coeff_zero_eq_eval_zero, coeff_map, coeff_zero_reverse]
  have := lowerBd_sub_lead (infSub (K := K) N P) N _ ⟨-(P.natDegree : ℤ), by push_cast; ring⟩
    hsupp hlb
  rwa [hc] at this

/-- **Reduced basis at infinity**: independence of the leading parts. -/
def LocIndepInf (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (δ : Fin S.F.natDegree → ℕ) (N : ℕ)
    (hN : 0 < N) (r : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k))) : Prop :=
  ∀ c : Fin S.F.natDegree → K,
    (∀ k, LowerBd (∑ j, HahnSeries.C (c j) * (single ((N * δ j : ℕ) : ℤ) (1 : K) *
      S.embG (infSub N) (infSub_injective N hN) (r k) (S.root_of_split _ r hs k) (w j))) N) →
      c = 0

/-- **Degree bounds from the pole order at infinity.** -/
theorem natDegree_le_of_indepInf (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (δ : Fin S.F.natDegree → ℕ)
    (N : ℕ) (hN : 0 < N) (r : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k)))
    (hind : S.LocIndepInf w δ N hN r hs)
    (hw : ∀ j k, LowerBd (S.embG (infSub N) (infSub_injective N hN) (r k)
      (S.root_of_split _ r hs k) (w j)) (-((N * δ j : ℕ) : ℤ)))
    (P : Fin S.F.natDegree → C[X]) (M : ℕ)
    (hz : ∀ k, LowerBd (S.embG (infSub N) (infSub_injective N hN) (r k) (S.root_of_split _ r hs k)
      (∑ j, (letI := algebraAdjoinSimple (F := C) S.x;
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ (P j))) * w j))
        (-((N * M : ℕ) : ℤ))) :
    ∀ j, P j ≠ 0 → (P j).natDegree + δ j ≤ M := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  set φ := fun k ↦ S.embG (infSub N) (infSub_injective N hN) (r k) (S.root_of_split _ r hs k)
    with hφ
  by_contra hneg
  push Not at hneg
  set T := Finset.univ.filter fun j ↦ P j ≠ 0 with hT
  have hTne : T.Nonempty := by
    obtain ⟨j, hj, -⟩ := hneg
    exact ⟨j, by simp [hT, hj]⟩
  set e := T.sup' hTne fun j ↦ (P j).natDegree + δ j with he
  have hle : ∀ j, P j ≠ 0 → (P j).natDegree + δ j ≤ e := fun j hj ↦
    Finset.le_sup' (fun j ↦ (P j).natDegree + δ j) (by simp [hT, hj])
  have heM : M < e := by
    obtain ⟨j, hj, hjM⟩ := hneg
    exact lt_of_lt_of_le hjM (hle j hj)
  obtain ⟨j0, hj0T, hj0⟩ := Finset.exists_mem_eq_sup' hTne fun j ↦ (P j).natDegree + δ j
  have hj0ne : P j0 ≠ 0 := by simpa [hT] using hj0T
  set c : Fin S.F.natDegree → K := fun j ↦
    if P j ≠ 0 ∧ (P j).natDegree + δ j = e then algebraMap C K (P j).leadingCoeff else 0 with hc
  have hcj0 : c j0 ≠ 0 := by
    simp only [hc]
    rw [if_pos ⟨hj0ne, hj0.symm⟩]
    exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr (leadingCoeff_ne_zero.mpr hj0ne)
  apply hcj0
  have := hind c fun k ↦ ?_
  · rw [this]; rfl
  -- each term: leading part plus a remainder of order `≥ −N e + N`
  have hterm : ∀ j, LowerBd (φ k (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ (P j)) * w j) -
      single (-((N * e : ℕ) : ℤ)) (1 : K) * (HahnSeries.C (c j) *
        (single ((N * δ j : ℕ) : ℤ) (1 : K) * φ k (w j)))) (-((N * e : ℕ) : ℤ) + N) := by
    intro j
    rw [map_mul, S.embG_algebraMap, S.embXG_algebraMap]
    by_cases hPj : P j = 0
    · have hcj : c j = 0 := by simp only [hc]; rw [if_neg fun h ↦ h.1 hPj]
      rw [hPj, map_zero, zero_mul, hcj, map_zero, zero_mul, mul_zero, sub_zero]
      exact lowerBd_zero _
    obtain ⟨h1, h2⟩ := infSub_lead (K := K) N hN (P j) hPj
    have hjle := hle j hPj
    by_cases htop : (P j).natDegree + δ j = e
    · have hcj : c j = algebraMap C K (P j).leadingCoeff := by
        simp only [hc]; rw [if_pos ⟨hPj, htop⟩]
      have e1 : infSub N (P j) * φ k (w j) - single (-((N * e : ℕ) : ℤ)) (1 : K) *
          (HahnSeries.C (c j) * (single ((N * δ j : ℕ) : ℤ) (1 : K) * φ k (w j))) =
          (infSub N (P j) - HahnSeries.C (algebraMap C K (P j).leadingCoeff) *
            single (-((N * (P j).natDegree : ℕ) : ℤ)) (1 : K)) * φ k (w j) := by
        rw [hcj, ← htop]
        have : single (-((N * ((P j).natDegree + δ j) : ℕ) : ℤ)) (1 : K) *
            single ((N * δ j : ℕ) : ℤ) (1 : K) = single (-((N * (P j).natDegree : ℕ) : ℤ)) 1 := by
          rw [single_mul_single, mul_one]; congr 1; push_cast; ring
        rw [← this]; ring
      rw [e1]
      have := h2.mul (hw j k)
      refine this.mono ?_
      rw [← htop]; push_cast; ring_nf; rfl
    · have hcj : c j = 0 := by simp only [hc]; rw [if_neg fun h ↦ htop h.2]
      rw [hcj, map_zero, zero_mul, mul_zero, sub_zero]
      have hlt : (P j).natDegree + δ j + 1 ≤ e := by omega
      have := h1.mul (hw j k)
      refine this.mono ?_
      have h3 : ((N * ((P j).natDegree + δ j + 1) : ℕ) : ℤ) ≤ ((N * e : ℕ) : ℤ) := by
        exact_mod_cast Nat.mul_le_mul_left N hlt
      push_cast at h3 ⊢
      linarith
  have hsum : LowerBd (φ k (∑ j, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ (P j)) * w j) -
      single (-((N * e : ℕ) : ℤ)) (1 : K) * ∑ j, HahnSeries.C (c j) *
        (single ((N * δ j : ℕ) : ℤ) (1 : K) * φ k (w j))) (-((N * e : ℕ) : ℤ) + N) := by
    rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact lowerBd_sum _ _ fun j _ ↦ hterm j
  have hzk := (hz k).mono (m' := -((N * e : ℕ) : ℤ) + N) (by
    have : ((N * (M + 1) : ℕ) : ℤ) ≤ ((N * e : ℕ) : ℤ) := by exact_mod_cast Nat.mul_le_mul_left N heM
    push_cast at this ⊢; linarith)
  have hL := hzk.sub hsum
  rw [sub_sub_cancel] at hL
  have := (lowerBd_single ((N * e : ℕ) : ℤ) (1 : K)).mul hL
  rw [← mul_assoc, single_mul_single, add_neg_cancel, mul_one,
    show single (0 : ℤ) (1 : K) = 1 from rfl, one_mul,
    show ((N * e : ℕ) : ℤ) + (-((N * e : ℕ) : ℤ) + N) = N by ring] at this
  exact this

end CurveData

end Basis

end Curves
