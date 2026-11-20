import RischTragerBronstein.Mixed.NKMultiData

/-!
# The root data at infinity for Newton segments of rational slopes

For a monic `F = Yⁿ + ∑ aᵢ(x) Yⁱ` over `C[x]` and slopes `s₀/e₀ > s₁/e₁ > ⋯` with
`eₖ deg aᵢ + i sₖ ≤ K₀ₖ` and residual polynomials
`∑ᵢ [aᵢ]_{(K₀ₖ − i sₖ)/eₖ} Zⁱ = cₖ Z^{loₖ} ∏_{γ ∈ Γₖ} (Z^{eₖ} − γ)` (the coefficient is `0` when
`eₖ ∤ K₀ₖ − i sₖ`), every root above infinity (`x = T^{−N}`, `eₖ ∣ N`) has order `−(N/eₖ) sₖ` and a
leading coefficient whose `eₖ`-th power is some `γ ∈ Γₖ`; roots with the same order and leading
coefficient are equal; and every `γ ∈ Γₖ` occurs (`multi_hdataR`).
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The coefficient of `P` at `j/e` when `e ∣ j` (`0` otherwise). -/
def coeffZe (P : C[X]) (e : ℕ) (j : ℤ) : C := if (e : ℤ) ∣ j then coeffZ P (j / e) else 0

lemma coeff_infSub_not_dvd (N : ℕ) (P : C[X]) (m : ℤ) (hm : ¬ (N : ℤ) ∣ m) :
    (infSub (K := K) N P).coeff m = 0 := by
  rw [infSub_eq_sum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun b _ ↦ ?_
  rw [HahnSeries.coeff_single, if_neg]
  intro h
  exact hm ⟨-(b : ℤ), by rw [h]; ring⟩

/-- **The residual identity at a segment of rational slope `s/e` determines the initial form.** -/
theorem initForm_segmentR (N : ℕ) (hN : 0 < N) (F : C[X][X]) (l : List (LaurentSeries K))
    (hl0 : ∀ r ∈ l, r ≠ 0) (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (e : ℕ) (he : 0 < e) (hed : e ∣ N)
    (s K0 : ℤ) (hbound : ∀ i ≤ F.natDegree, F.coeff i ≠ 0 →
      (e : ℤ) * (F.coeff i).natDegree + i * s ≤ K0)
    (Q : C[X]) (hQ : Q = ∑ i ∈ Finset.range (F.natDegree + 1),
      Polynomial.C (coeffZe (F.coeff i) e (K0 - i * s)) * X ^ i) (hQ0 : Q ≠ 0) :
    (l.map (initRed (((N / e : ℕ) : ℤ) * s))).prod = Q.map (algebraMap C K) := by
  classical
  set d : ℤ := ((N / e : ℕ) : ℤ) with hd
  have hNd : (N : ℤ) = d * e := by rw [hd]; exact_mod_cast (Nat.div_mul_cancel hed).symm
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Nat.div_pos (Nat.le_of_dvd hN hed) he
  have he0 : (0 : ℤ) < e := by exact_mod_cast he
  obtain ⟨kk, hLB, hSum⟩ := initForm_coeff N (d * s) F l hl0 hl
  -- the leading coefficient of `aᵢ(T^{−N})`
  have hlead : ∀ i, F.coeff i ≠ 0 →
      (infSub (K := K) N (F.coeff i)).coeff (-((N : ℤ) * (F.coeff i).natDegree)) ≠ 0 := by
    intro i hai
    rw [coeff_infSub_negmul N hN, coeffZ, if_pos (by positivity), Int.toNat_natCast]
    exact (_root_.map_ne_zero _).mpr (leadingCoeff_ne_zero.mpr hai)
  -- `kk ≥ d (e deg aᵢ + i s)`
  have hge : ∀ i ≤ F.natDegree, F.coeff i ≠ 0 →
      d * ((e : ℤ) * (F.coeff i).natDegree + i * s) ≤ kk := by
    intro i _ hai
    by_contra hc
    push Not at hc
    apply hlead i hai
    have h1 := hLB i (-((N : ℤ) * (F.coeff i).natDegree) + (kk - i * (d * s))) (by
      rw [hNd]; nlinarith)
    rw [coeff_mul_single_one] at h1
    convert h1 using 2
    ring
  have hPne : (l.map (initRed (d * s))).prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]
    intro h
    obtain ⟨r, hr, h0⟩ := List.mem_map.mp h
    exact initRed_ne_zero _ r (hl0 r hr) h0
  have hle : kk ≤ d * K0 := by
    rw [← hSum] at hPne
    by_contra hc
    push Not at hc
    apply hPne
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi' : i ≤ F.natDegree := by have := Finset.mem_range.mp hi; omega
    by_cases hai : F.coeff i = 0
    · rw [hai, map_zero, HahnSeries.coeff_zero, map_zero, zero_mul]
    · rw [coeff_infSub_lt N hN _ _ (by
        have := hbound i hi' hai
        rw [hNd]; nlinarith), map_zero, zero_mul]
  have hge' : d * K0 ≤ kk := by
    by_contra hc
    push Not at hc
    apply hQ0
    rw [hQ]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi' : i ≤ F.natDegree := by have := Finset.mem_range.mp hi; omega
    by_cases hai : F.coeff i = 0
    · rw [hai]; simp [coeffZe, coeffZ]
    · have h1 := hge i hi' hai
      have h2 : (e : ℤ) * (F.coeff i).natDegree + i * s < K0 := by
        by_contra h3; push Not at h3; nlinarith
      rw [coeffZe]
      split_ifs with hdv
      · obtain ⟨j, hj⟩ := hdv
        rw [hj, Int.mul_ediv_cancel_left _ he0.ne', coeffZ, if_pos (by nlinarith),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by
            have : ((F.coeff i).natDegree : ℤ) < j := by nlinarith
            omega), map_zero, zero_mul]
      · rw [map_zero, zero_mul]
  have hkk : kk = d * K0 := le_antisymm hle hge'
  rw [← hSum, hQ, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hkk]
  congr 2
  rw [show (i : ℤ) * (d * s) - d * K0 = -(d * (K0 - i * s)) by ring, coeffZe]
  split_ifs with hdv
  · obtain ⟨j, hj⟩ := hdv
    rw [hj, Int.mul_ediv_cancel_left _ he0.ne', show -(d * (e * j)) = -((N : ℤ) * j) by
      rw [hNd]; ring, coeff_infSub_negmul N hN]
  · rw [map_zero]
    refine coeff_infSub_not_dvd N _ _ fun ⟨j, hj⟩ ↦ hdv ⟨-j, ?_⟩
    rw [hNd] at hj
    apply mul_left_cancel₀ hd0.ne'
    linear_combination -hj

/-- The residual identity of the last segment (`lo = 0`) forces `a₀ ≠ 0`. -/
lemma coeff0_ne_of_resR (F : C[X][X]) (e : ℕ) (he : 0 < e) (s K0 : ℤ) (c : C) (hc : c ≠ 0)
    (Γ : List C) (hΓ : (0 : C) ∉ Γ)
    (hres : ∑ i ∈ Finset.range (F.natDegree + 1),
      Polynomial.C (coeffZe (F.coeff i) e (K0 - i * s)) * X ^ i =
        Polynomial.C c * X ^ 0 * (Γ.map fun γ ↦ X ^ e - Polynomial.C γ).prod) :
    F.coeff 0 ≠ 0 := by
  intro h0'
  have h1 := congrArg (Polynomial.eval 0) hres
  rw [pow_zero, mul_one, eval_mul, eval_C, eval_list_prod, eval_finset_sum,
    Finset.sum_eq_single 0 (fun b _ hb ↦ by rw [eval_mul, eval_pow, eval_X, zero_pow hb, mul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h), eval_mul, eval_C, pow_zero, eval_one,
    mul_one, h0'] at h1
  have hz : coeffZe (0 : C[X]) e (K0 - ((0 : ℕ) : ℤ) * s) = 0 := by
    unfold coeffZe coeffZ
    split_ifs <;> simp
  rw [hz] at h1
  symm at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hc h2
  · obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h2)
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hv
    simp only [eval_sub, eval_pow, eval_X, eval_C] at hv0
    rw [zero_pow he.ne', zero_sub, neg_eq_zero] at hv0
    exact hΓ (hv0 ▸ hγ)

/-- **The `e`-th roots** of an element of an algebraically closed field of characteristic `0`. -/
lemma exists_eth_roots [IsAlgClosed K] [CharZero K] (e : ℕ) (he : 0 < e) (γ : K) :
    ∃ δs : List K, δs.length = e ∧ (∀ δ ∈ δs, δ ^ e = γ) ∧
      (δs.map fun δ ↦ X - Polynomial.C δ).prod = X ^ e - Polynomial.C γ ∧ (γ ≠ 0 → δs.Nodup) := by
  classical
  set p : K[X] := X ^ e - Polynomial.C γ with hp
  have hmon : p.Monic := monic_X_pow_sub_C γ he.ne'
  have hdeg : p.natDegree = e := natDegree_X_pow_sub_C
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨p.roots.toList, by rw [Multiset.length_toList, hcard, hdeg], fun δ hδ ↦ ?_, ?_,
    fun hγ ↦ ?_⟩
  · rw [Multiset.mem_toList, mem_roots hmon.ne_zero, IsRoot.def, hp, eval_sub, eval_pow, eval_X,
      eval_C, sub_eq_zero] at hδ
    exact hδ
  · have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
    rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe] at h
    exact h
  · rw [← Multiset.coe_nodup, Multiset.coe_toList]
    exact nodup_roots (separable_X_pow_sub_C γ (by exact_mod_cast he.ne') hγ)

/-- **The root data at infinity from the residual polynomials of segments of rational slopes.** -/
theorem multi_hdataR [IsAlgClosed K] [CharZero K] (N : ℕ) (hN : 0 < N) (F : C[X][X])
    (hF : F.Monic) (hF0 : F.coeff 0 ≠ 0)
    (l : List (LaurentSeries K)) (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {q : ℕ} (e : Fin (q + 1) → ℕ) (he : ∀ k, 0 < e k) (hed : ∀ k, e k ∣ N)
    (s : Fin (q + 1) → ℤ) (hs : StrictAnti fun k ↦ ((N / e k : ℕ) : ℤ) * s k)
    (K0 : Fin (q + 1) → ℤ) (c : Fin (q + 1) → C) (hc : ∀ k, c k ≠ 0) (lo : Fin (q + 1) → ℕ)
    (Γ : Fin (q + 1) → List C) (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : C) ∉ Γ k)
    (hbound : ∀ k, ∀ i ≤ F.natDegree, F.coeff i ≠ 0 →
      (e k : ℤ) * (F.coeff i).natDegree + i * s k ≤ K0 k)
    (hres : ∀ k, ∑ i ∈ Finset.range (F.natDegree + 1),
      Polynomial.C (coeffZe (F.coeff i) (e k) (K0 k - i * s k)) * X ^ i =
        Polynomial.C (c k) * X ^ (lo k) * ((Γ k).map fun γ ↦ X ^ (e k) - Polynomial.C γ).prod)
    (htop : lo 0 + e 0 * (Γ 0).length = F.natDegree)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + e k.succ * (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0) :
    (∀ ρ ∈ l, ∃ k, ρ.order = -(((N / e k : ℕ) : ℤ) * s k) ∧
      ∃ γ ∈ Γ k, (ρ.coeff ρ.order) ^ e k = algebraMap C K γ) ∧
    (∀ ρ ∈ l, ∀ ρ' ∈ l, ρ.order = ρ'.order → ρ.coeff ρ.order = ρ'.coeff ρ'.order → ρ = ρ') ∧
    (∀ k, ∀ γ ∈ Γ k, ∃ ρ ∈ l, ρ.order = -(((N / e k : ℕ) : ℤ) * s k) ∧
      (ρ.coeff ρ.order) ^ e k = algebraMap C K γ) := by
  classical
  -- the roots are non-zero
  have hl0 : ∀ r ∈ l, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h1 : (F.map (infSub (K := K) N)).eval 0 = 0 := by
      rw [hl, eval_list_prod]
      exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨0, hr, rfl⟩, by simp⟩)
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h1
    exact hF0 ((infSub_injective N hN) (by rw [h1, map_zero]))
  have hlen : l.length = F.natDegree := by
    have := congrArg natDegree hl
    rw [hF.natDegree_map, (list_prod_X_sub_C l).2] at this
    exact this.symm
  set ι := algebraMap C K with hι
  have hιi : Function.Injective ι := (algebraMap C K).injective
  -- the `eₖ`-th roots of the `γ ∈ Γₖ`
  choose R hRlen hRpow hRprod hRnd using fun (k : Fin (q + 1)) (γ : C) ↦
    exists_eth_roots (K := K) (e k) (he k) (ι γ)
  set Γ' : Fin (q + 1) → List K := fun k ↦ (Γ k).flatMap (R k) with hΓ'
  have hprod : ∀ k (G : List C), ((G.flatMap (R k)).map fun γ ↦ X - Polynomial.C γ).prod =
      (G.map fun γ ↦ X ^ (e k) - Polynomial.C (ι γ)).prod := by
    intro k G
    induction G with
    | nil => simp
    | cons g G ih => rw [List.flatMap_cons, List.map_append, List.prod_append, ih, hRprod,
        List.map_cons, List.prod_cons]
  have hlenΓ : ∀ k (G : List C), (G.flatMap (R k)).length = e k * G.length := by
    intro k G
    induction G with
    | nil => simp
    | cons g G ih => rw [List.flatMap_cons, List.length_append, ih, hRlen, List.length_cons]; ring
  have hmemΓ : ∀ k δ, δ ∈ Γ' k ↔ ∃ γ ∈ Γ k, δ ∈ R k γ := fun k δ ↦ by
    simp [hΓ', List.mem_flatMap]
  have hΓK : ∀ k, (Γ' k).Nodup ∧ (0 : K) ∉ Γ' k := by
    intro k
    refine ⟨List.nodup_flatMap.mpr ⟨fun γ hγ ↦ hRnd k γ ((_root_.map_ne_zero ι).mpr
      (fun h0 ↦ (hΓ k).2 (h0 ▸ hγ))), ?_⟩, fun h0 ↦ ?_⟩
    · refine (hΓ k).1.imp_of_mem fun {a b} ha hb hab ↦ ?_
      intro δ hδa hδb
      apply hab
      apply hιi
      rw [← hRpow k a δ hδa, ← hRpow k b δ hδb]
    · obtain ⟨γ, hγ, h0⟩ := (hmemΓ k 0).mp h0
      have := hRpow k γ 0 h0
      rw [zero_pow (he k).ne'] at this
      exact (hΓ k).2 (by rwa [show γ = 0 from hιi (by rw [← this, map_zero])] at hγ)
  have hR : ∀ k, ∃ cK : K, cK ≠ 0 ∧ (l.map (initRed (((N / e k : ℕ) : ℤ) * s k))).prod =
      Polynomial.C cK * X ^ (lo k) * ((Γ' k).map fun γ ↦ X - Polynomial.C γ).prod := by
    intro k
    have hQ0 : (∑ i ∈ Finset.range (F.natDegree + 1),
        Polynomial.C (coeffZe (F.coeff i) (e k) (K0 k - i * s k)) * X ^ i) ≠ 0 := by
      rw [hres k]
      refine mul_ne_zero (mul_ne_zero (by rw [Ne, Polynomial.C_eq_zero]; exact hc k)
        (pow_ne_zero _ X_ne_zero)) ?_
      rw [Ne, List.prod_eq_zero_iff]
      intro h
      obtain ⟨γ, -, h0⟩ := List.mem_map.mp h
      have := congrArg natDegree h0
      rw [natDegree_X_pow_sub_C, natDegree_zero] at this
      exact (he k).ne' this
    refine ⟨ι (c k), (_root_.map_ne_zero _).mpr (hc k), ?_⟩
    rw [initForm_segmentR N hN F l hl0 hl (e k) (he k) (hed k) (s k) (K0 k) (hbound k) _ rfl hQ0,
      hres k, hΓ', hprod]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_list_prod, List.map_map]
    congr 2
    refine List.map_congr_left fun γ _ ↦ ?_
    simp [hι]
  have hlenK : ∀ k, (Γ' k).length = e k * (Γ k).length := fun k ↦ hlenΓ k (Γ k)
  obtain ⟨hord, huniq⟩ := roots_of_segments l hl0 (fun k ↦ ((N / e k : ℕ) : ℤ) * s k) hs lo Γ' hΓK
    hR (by rw [hlen, ← htop, hlenK]) (fun k ↦ by rw [hchain k, hlenK]) hlast
  refine ⟨fun ρ hρ ↦ ?_, fun ρ hρ ρ' hρ' ho hc' ↦ huniq ρ hρ ρ' hρ' ho hc', fun k γ hγ ↦ ?_⟩
  · obtain ⟨k, hk, hlc⟩ := hord ρ hρ
    obtain ⟨γ, hγ, hδ⟩ := (hmemΓ k _).mp hlc
    exact ⟨k, hk, γ, hγ, hRpow k γ _ hδ⟩
  · -- every `γ` occurs
    obtain ⟨cK, hcK, hRk⟩ := hR k
    have hM := initForm_roots _ l hl0 (lo k) (Γ' k) cK hcK hRk
    obtain ⟨δ, hδ⟩ : ∃ δ, δ ∈ R k γ := by
      apply List.exists_mem_of_ne_nil
      intro h0
      have := hRlen k γ
      rw [h0, List.length_nil] at this
      exact (he k).ne' this.symm
    have hδΓ : δ ∈ Γ' k := (hmemΓ k δ).mpr ⟨γ, hγ, hδ⟩
    have hδ0 : δ ≠ 0 := fun h0 ↦ (hΓK k).2 (h0 ▸ hδΓ)
    have hmem : δ ∈ (((l.filter fun r ↦ decide (LowerBd r (-(((N / e k : ℕ) : ℤ) * s k)))).map
        fun r ↦ r.coeff (-(((N / e k : ℕ) : ℤ) * s k)) : List K) : Multiset K) := by
      rw [hM]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_coe.mpr hδΓ))
    obtain ⟨ρ, hρf, hρδ⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
    obtain ⟨hρ, hρLB⟩ := List.mem_filter.mp hρf
    have hρLB' : LowerBd ρ (-(((N / e k : ℕ) : ℤ) * s k)) := of_decide_eq_true hρLB
    have hρ0 := hl0 ρ hρ
    have hord' : ρ.order = -(((N / e k : ℕ) : ℤ) * s k) := by
      apply le_antisymm
      · exact HahnSeries.order_le_of_coeff_ne_zero (by rw [hρδ]; exact hδ0)
      · exact (lowerBd_iff_le_order hρ0 _).mp hρLB'
    refine ⟨ρ, hρ, hord', ?_⟩
    rw [hord', hρδ]
    exact hRpow k γ δ hδ

end Curves
