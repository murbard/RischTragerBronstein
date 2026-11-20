import RischTragerBronstein.Algebraic.SuperIntegral

/-!
# The place at infinity of a superelliptic curve

For `yⁿ = p(x)` with `d = deg p` coprime to `n` there is a single place at infinity, with local
parameter `s`: `x = s⁻ⁿ`, `y = s⁻ᵈ W(s)` where `Wⁿ = (rev p)(sⁿ)`, `W(0)ⁿ = lc p`.

* `infSub m`: the substitution `x ↦ s⁻ᵐ`; `order_infSub`: `ord P(s⁻ᵐ) = −m deg P`;
* `embI`: the expansion at infinity;
* `inf_bound`: if `∑ aᵢ yⁱ` has a pole of order at most `m` at infinity, then every term does:
  `ord aᵢ − d i ≥ −m` (orders of the terms are pairwise distinct mod `n`).
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

section Inf

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The substitution `x ↦ s⁻ᵐ`. -/
noncomputable def infSub (m : ℕ) : C[X] →+* LaurentSeries K :=
  eval₂RingHom ((HahnSeries.C).comp (algebraMap C K)) (single (-(m : ℤ)) 1)

lemma eval₂_single_nat (m : ℕ) (Q : C[X]) :
    Q.eval₂ ((HahnSeries.C).comp (algebraMap C K)) (single (m : ℤ) 1) =
      ofPowerSeries ℤ K (((Q.map (algebraMap C K)).comp (X ^ m) : K[X]) : PowerSeries K) := by
  have h : eval₂RingHom ((HahnSeries.C).comp (algebraMap C K)) (single (m : ℤ) (1 : K)) =
      (ofPowerSeries ℤ K).comp ((Polynomial.coeToPowerSeries.ringHom (R := K)).comp
        ((Polynomial.compRingHom (X ^ m)).comp (Polynomial.mapRingHom (algebraMap C K)))) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, coe_mapRingHom, Polynomial.map_C,
        compRingHom]
      rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, ofPowerSeries_C]
    · simp [ofPowerSeries_X_pow]
  exact congrArg (fun φ : C[X] →+* LaurentSeries K ↦ φ Q) h

/-- `P(s⁻ᵐ) = s^{−m deg P} · (rev P)(sᵐ)`. -/
lemma infSub_eq (m : ℕ) (P : C[X]) :
    infSub (K := K) m P = single (-(m * P.natDegree : ℤ)) 1 *
      ofPowerSeries ℤ K (((P.reverse.map (algebraMap C K)).comp (X ^ m) : K[X]) : PowerSeries K) := by
  let _ : Invertible (single (-(m : ℤ)) (1 : K)) :=
    ⟨single (m : ℤ) 1, by simp [single_mul_single], by simp [single_mul_single]⟩
  have h := eval₂_reverse_mul_pow ((HahnSeries.C).comp (algebraMap C K))
    (single (-(m : ℤ)) (1 : K)) P
  rw [show ⅟(single (-(m : ℤ)) (1 : K)) = single (m : ℤ) 1 from rfl, eval₂_single_nat,
    single_pow, one_pow] at h
  rw [infSub, coe_eval₂RingHom, ← h, mul_comm]
  rw [show P.natDegree • -(m : ℤ) = -(m * P.natDegree : ℤ) by rw [nsmul_eq_mul]; ring]

lemma infRev_const (m : ℕ) (hm : 0 < m) (P : C[X]) :
    PowerSeries.constantCoeff (((P.reverse.map (algebraMap C K)).comp (X ^ m) : K[X]) :
      PowerSeries K) = algebraMap C K P.leadingCoeff := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    coeff_zero_eq_eval_zero, eval_comp, eval_pow, eval_X, zero_pow hm.ne',
    ← coeff_zero_eq_eval_zero, coeff_map, coeff_zero_reverse]

/-- **Order at infinity**: `ord P(s⁻ᵐ) = −m deg P`. -/
theorem order_infSub (m : ℕ) (hm : 0 < m) (P : C[X]) (hP : P ≠ 0) :
    (infSub (K := K) m P).order = -(m * P.natDegree : ℤ) := by
  have hu : PowerSeries.constantCoeff (((P.reverse.map (algebraMap C K)).comp (X ^ m) : K[X]) :
      PowerSeries K) ≠ 0 := by
    rw [infRev_const m hm]
    exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr (leadingCoeff_ne_zero.mpr hP)
  have hu0 : ofPowerSeries ℤ K (((P.reverse.map (algebraMap C K)).comp (X ^ m) : K[X]) :
      PowerSeries K) ≠ 0 := fun h ↦ by
    have hc : (ofPowerSeries ℤ K (((P.reverse.map (algebraMap C K)).comp (X ^ m) : K[X]) :
        PowerSeries K)).coeff 0 ≠ 0 := by
      rw [LaurentSeries.coeff_ofPS, if_pos le_rfl]; simpa using hu
    rw [h] at hc; exact hc rfl
  rw [infSub_eq, HahnSeries.order_single_mul_of_isRegular isRegular_one hu0,
    order_ofPS_unit _ hu, add_zero]

lemma infSub_ne_zero (m : ℕ) (hm : 0 < m) (P : C[X]) (hP : P ≠ 0) : infSub (K := K) m P ≠ 0 := by
  intro h
  have hu : PowerSeries.constantCoeff (((P.reverse.map (algebraMap C K)).comp (X ^ m) : K[X]) :
      PowerSeries K) ≠ 0 := by
    rw [infRev_const m hm]
    exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr (leadingCoeff_ne_zero.mpr hP)
  rw [infSub_eq] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact one_ne_zero (HahnSeries.single_eq_zero_iff.mp h1)
  · have hc : (ofPowerSeries ℤ K (((P.reverse.map (algebraMap C K)).comp (X ^ m) : K[X]) :
        PowerSeries K)).coeff 0 ≠ 0 := by
      rw [LaurentSeries.coeff_ofPS, if_pos le_rfl]; simpa using hu
    rw [h1] at hc; exact hc rfl

lemma infSub_injective (m : ℕ) (hm : 0 < m) : Function.Injective (infSub (C := C) (K := K) m) :=
  (injective_iff_map_eq_zero _).mpr fun P hP ↦ by
    by_contra h0; exact infSub_ne_zero m hm P h0 hP

end Inf

namespace SuperData

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

variable (S : SuperData C L)

/-- The unit `W(s)` with `Wⁿ = (rev p)(sⁿ)`, `W(0) = λ`. -/
noncomputable def infW (lam : K) (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    PowerSeries K :=
  Classical.choose (LaurentSeries.exists_pow_eq S.n S.hn (S.hnK K)
    (((S.p.reverse.map (algebraMap C K)).comp (X ^ S.n) : K[X]) : PowerSeries K) lam hlam
    (by rw [infRev_const S.n S.hn, hlp]))

lemma infW_spec (lam : K) (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    S.infW lam hlam hlp ^ S.n =
      (((S.p.reverse.map (algebraMap C K)).comp (X ^ S.n) : K[X]) : PowerSeries K) ∧
      PowerSeries.constantCoeff (S.infW lam hlam hlp) = lam :=
  Classical.choose_spec (LaurentSeries.exists_pow_eq S.n S.hn (S.hnK K)
    (((S.p.reverse.map (algebraMap C K)).comp (X ^ S.n) : K[X]) : PowerSeries K) lam hlam
    (by rw [infRev_const S.n S.hn, hlp]))

/-- The branch of `y` at infinity: `s⁻ᵈ W(s)`. -/
noncomputable def infY (lam : K) (hlam : lam ≠ 0)
    (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) : LaurentSeries K :=
  single (-(S.p.natDegree : ℤ)) 1 * ofPowerSeries ℤ K (S.infW lam hlam hlp)

lemma infY_pow (lam : K) (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    S.infY lam hlam hlp ^ S.n = infSub S.n S.p := by
  rw [infY, mul_pow, single_pow, one_pow, ← map_pow, (S.infW_spec lam hlam hlp).1, infSub_eq,
    nsmul_eq_mul]
  congr 2
  push_cast; ring

lemma order_infY (lam : K) (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    (S.infY lam hlam hlp).order = -(S.p.natDegree : ℤ) := by
  have hu := (S.infW_spec lam hlam hlp).2
  have hu0 : ofPowerSeries ℤ K (S.infW lam hlam hlp) ≠ 0 := by
    intro h
    have hc : (ofPowerSeries ℤ K (S.infW lam hlam hlp)).coeff 0 ≠ 0 := by
      rw [LaurentSeries.coeff_ofPS, if_pos le_rfl]; simpa [hu] using hlam
    rw [h] at hc; exact hc rfl
  rw [infY, HahnSeries.order_single_mul_of_isRegular isRegular_one hu0,
    order_ofPS_unit _ (by rw [hu]; exact hlam), add_zero]

/-- **The expansion at infinity.** -/
noncomputable def embI (lam : K) (hlam : lam ≠ 0)
    (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K :=
  S.embG (infSub S.n) (infSub_injective S.n S.hn) (S.infY lam hlam hlp) (S.infY_pow lam hlam hlp)

/-- Orders at infinity of elements of `C⟮x⟯` are multiples of `n`. -/
lemma embXG_inf_order (a : C⟮S.x⟯) (ha : a ≠ 0) :
    ∃ k : ℤ, (S.embXG (infSub (K := K) S.n) (infSub_injective S.n S.hn) a).order = S.n * k := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  set Nu := IsFractionRing.num C[X] a
  set De := (IsFractionRing.den C[X] a : C[X])
  have hDe0 : De ≠ 0 := nonZeroDivisors.ne_zero (IsFractionRing.den C[X] a).2
  have hak : algebraMap C[X] C⟮S.x⟯ Nu / algebraMap C[X] C⟮S.x⟯ De = a :=
    IsFractionRing.mk'_num_den' C[X] a
  have hNu0 : Nu ≠ 0 := fun h0 ↦ ha (by rw [← hak, h0, map_zero, zero_div])
  have e1 : S.embXG (infSub (K := K) S.n) (infSub_injective S.n S.hn) a =
      infSub S.n Nu / infSub S.n De := by
    rw [← hak, map_div₀, S.embXG_algebraMap, S.embXG_algebraMap]
  refine ⟨(De.natDegree : ℤ) - Nu.natDegree, ?_⟩
  rw [e1, order_div' _ _ (infSub_ne_zero S.n S.hn Nu hNu0) (infSub_ne_zero S.n S.hn De hDe0),
    order_infSub S.n S.hn Nu hNu0, order_infSub S.n S.hn De hDe0]
  ring

lemma embXG_inf_poly (P : C[X]) (hP : P ≠ 0) :
    letI := algebraAdjoinSimple (F := C) S.x
    (S.embXG (infSub (K := K) S.n) (infSub_injective S.n S.hn) (algebraMap C[X] C⟮S.x⟯ P)).order =
      -(S.n * P.natDegree : ℤ) := by
  rw [S.embXG_algebraMap, order_infSub S.n S.hn P hP]

/-- **Pole bound at infinity**: if `∑ aᵢ yⁱ` has order `≥ c` at infinity (and `gcd(n, deg p) = 1`),
then so has every term. -/
theorem inf_bound (hcop : Nat.Coprime S.n S.p.natDegree) (lam : K) (hlam : lam ≠ 0)
    (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) (a : Fin S.n → C⟮S.x⟯) (c : ℤ)
    (h : (c : WithTop ℤ) ≤ (S.embI lam hlam hlp (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))).orderTop) :
    ∀ i, a i ≠ 0 → c ≤ (S.embXG (infSub (K := K) S.n) (infSub_injective S.n S.hn) (a i)).order -
      S.p.natDegree * i := by
  classical
  set φ := S.embI lam hlam hlp
  set G := S.embXG (infSub (K := K) S.n) (infSub_injective S.n S.hn)
  set t : Fin S.n → LaurentSeries K := fun i ↦ G (a i) * S.infY lam hlam hlp ^ (i : ℕ)
  have hφ : ∀ i, φ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) =
      t i := fun i ↦ by
    rw [map_mul, map_pow]
    simp only [φ, embI, S.embG_algebraMap, S.embG_gen, t, G]
  have hY0 : S.infY lam hlam hlp ≠ 0 := fun h0 ↦ by
    have := S.order_infY lam hlam hlp
    rw [h0, HahnSeries.order_zero] at this
    have := S.hp; omega
  have hord : ∀ i, a i ≠ 0 → (t i).order = (G (a i)).order - S.p.natDegree * i := by
    intro i hi
    have hG : G (a i) ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hi
    simp only [t]
    rw [HahnSeries.order_mul hG (pow_ne_zero _ hY0), HahnSeries.order_pow, S.order_infY]
    ring
  set s := Finset.univ.filter fun i : Fin S.n ↦ a i ≠ 0
  have hsum : φ (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) =
      ∑ i ∈ s, t i := by
    rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ a i ≠ 0)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i ↦ ¬ a i ≠ 0) fun i hi ↦ by
      rw [Finset.mem_filter, not_not] at hi; rw [hφ, show t i = 0 by simp [t, hi.2]], add_zero]
    exact Finset.sum_congr rfl fun i _ ↦ hφ i
  have hne : ∀ i ∈ s, t i ≠ 0 := fun i hi ↦ by
    have hi' : a i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact mul_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr hi') (pow_ne_zero _ hY0)
  have hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (t i).orderTop ≠ (t j).orderTop := by
    intro i hi j hj hij heq
    have hai := (Finset.mem_filter.mp hi).2
    have haj := (Finset.mem_filter.mp hj).2
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero (hne i hi),
      ← HahnSeries.order_eq_orderTop_of_ne_zero (hne j hj),
      WithTop.coe_eq_coe, hord i hai, hord j haj] at heq
    obtain ⟨ki, hki⟩ := S.embXG_inf_order (K := K) (a i) hai
    obtain ⟨kj, hkj⟩ := S.embXG_inf_order (K := K) (a j) haj
    simp only [G] at heq
    rw [hki, hkj] at heq
    -- `n ∣ d (j − i)` with `gcd(n, d) = 1` forces `i = j`
    have hdvd : (S.n : ℤ) ∣ (S.p.natDegree : ℤ) * ((j : ℤ) - i) :=
      ⟨kj - ki, by linear_combination heq⟩
    have h2 : (S.n : ℤ) ∣ (j : ℤ) - i :=
      (Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hcop)).dvd_of_dvd_mul_left hdvd
    have hi2 := i.2
    have hj2 := j.2
    obtain ⟨q, hq⟩ := h2
    have : q = 0 := by
      by_contra hq0
      rcases lt_or_gt_of_ne hq0 with hq0 | hq0
      · have : (S.n : ℤ) * q ≤ -(S.n : ℤ) := by nlinarith
        omega
      · have : (S.n : ℤ) ≤ (S.n : ℤ) * q := by nlinarith
        omega
    subst this
    exact hij (Fin.ext (by omega))
  rw [hsum] at h
  intro i hi
  have hmem : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hts := LaurentSeries.le_orderTop_of_sum_distinct s t hd c h i hmem
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (hne i hmem), hord i hi] at hts
  exact_mod_cast hts

end SuperData

end Differential
