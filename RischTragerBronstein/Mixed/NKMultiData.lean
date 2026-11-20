import RischTragerBronstein.Mixed.NKMultiRoots
import RischTragerBronstein.Mixed.NKMultiGauge

/-!
# The root data at infinity from the residual polynomials of the Newton segments

For a monic `F = Yⁿ + ∑ aᵢ(x) Yⁱ` over `C[x]` and integer slopes `s₀ > s₁ > ⋯` with
`deg aᵢ + i sₖ ≤ K₀ₖ` and residual polynomials `∑ᵢ [aᵢ]_{K₀ₖ − i sₖ} Zⁱ = cₖ Z^{loₖ} ∏_{γ ∈ Γₖ} (Z − γ)`
(`cₖ ≠ 0`, `Γₖ ⊆ C` without repetition and without `0`, `lo₀ + |Γ₀| = n`,
`loₖ = loₖ₊₁ + |Γₖ₊₁|`, `lo_last = 0`), every root above infinity (`x = T^{−N}`) has order
`−N sₖ` and leading coefficient in `Γₖ` for some `k`, and roots with the same order and leading
coefficient are equal (`multi_hdata`): the hypothesis of `multi_gauge`.
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The coefficient of a polynomial at an integer index (`0` below `0`). -/
def coeffZ (P : C[X]) (j : ℤ) : C := if 0 ≤ j then P.coeff j.toNat else 0

lemma infSub_eq_sum (N : ℕ) (P : C[X]) :
    infSub (K := K) N P = ∑ i ∈ Finset.range (P.natDegree + 1),
      single (-((N : ℤ) * i)) (algebraMap C K (P.coeff i)) := by
  rw [infSub, coe_eval₂RingHom, eval₂_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RingHom.comp_apply, single_pow, one_pow, HahnSeries.C_apply, single_mul_single, zero_add,
    mul_one]
  congr 1
  rw [nsmul_eq_mul]; ring

lemma coeff_infSub_negmul (N : ℕ) (hN : 0 < N) (P : C[X]) (j : ℤ) :
    (infSub (K := K) N P).coeff (-((N : ℤ) * j)) = algebraMap C K (coeffZ P j) := by
  rw [infSub_eq_sum, HahnSeries.coeff_sum]
  simp only [HahnSeries.coeff_single]
  unfold coeffZ
  split_ifs with hj
  · obtain ⟨jn, rfl⟩ : ∃ jn : ℕ, j = jn := ⟨j.toNat, by omega⟩
    by_cases hjd : jn < P.natDegree + 1
    · rw [Finset.sum_eq_single jn (fun b _ hb ↦ by
        rw [if_neg (fun h ↦ hb (by
          have : (N : ℤ) * b = N * jn := by linarith
          exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hN.ne') this))])
        (fun h ↦ absurd (Finset.mem_range.mpr hjd) h), if_pos rfl, Int.toNat_natCast]
    · rw [Finset.sum_eq_zero fun b hb ↦ by
        rw [if_neg (fun h ↦ by
          have hb' := Finset.mem_range.mp hb
          have : (N : ℤ) * b = N * jn := by linarith
          have := mul_left_cancel₀ (show (N : ℤ) ≠ 0 by exact_mod_cast hN.ne') this
          omega)], Int.toNat_natCast,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  · rw [map_zero]
    refine Finset.sum_eq_zero fun b _ ↦ if_neg fun h ↦ ?_
    have : (N : ℤ) * b = N * j := by linarith
    nlinarith

lemma coeff_infSub_lt (N : ℕ) (hN : 0 < N) (P : C[X]) (m : ℤ) (hm : m < -((N : ℤ) * P.natDegree)) :
    (infSub (K := K) N P).coeff m = 0 := by
  rw [infSub_eq_sum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun b hb ↦ ?_
  have hb' := Finset.mem_range.mp hb
  rw [HahnSeries.coeff_single, if_neg]
  intro h
  have : (b : ℤ) ≤ P.natDegree := by exact_mod_cast Nat.lt_succ_iff.mp hb'
  nlinarith

/-- **The residual identity at a segment determines the initial form.** -/
theorem initForm_segment (N : ℕ) (hN : 0 < N) (F : C[X][X]) (l : List (LaurentSeries K))
    (hl0 : ∀ r ∈ l, r ≠ 0) (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (s K0 : ℤ) (hbound : ∀ i ≤ F.natDegree, F.coeff i ≠ 0 →
      ((F.coeff i).natDegree : ℤ) + i * s ≤ K0)
    (Q : C[X]) (hQ : Q = ∑ i ∈ Finset.range (F.natDegree + 1),
      Polynomial.C (coeffZ (F.coeff i) (K0 - i * s)) * X ^ i) (hQ0 : Q ≠ 0) :
    (l.map (initRed ((N : ℤ) * s))).prod = Q.map (algebraMap C K) := by
  classical
  obtain ⟨kk, hLB, hSum⟩ := initForm_coeff N ((N : ℤ) * s) F l hl0 hl
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  -- the leading coefficient of `aᵢ(T^{−N})`
  have hlead : ∀ i, F.coeff i ≠ 0 →
      (infSub (K := K) N (F.coeff i)).coeff (-((N : ℤ) * (F.coeff i).natDegree)) ≠ 0 := by
    intro i hai
    rw [coeff_infSub_negmul N hN, coeffZ, if_pos (by positivity), Int.toNat_natCast]
    exact (_root_.map_ne_zero _).mpr (leadingCoeff_ne_zero.mpr hai)
  -- `kk ≥ N (deg aᵢ + i s)`
  have hge : ∀ i ≤ F.natDegree, F.coeff i ≠ 0 →
      (N : ℤ) * (((F.coeff i).natDegree : ℤ) + i * s) ≤ kk := by
    intro i _ hai
    by_contra hc
    push Not at hc
    apply hlead i hai
    have h1 := hLB i (-((N : ℤ) * (F.coeff i).natDegree) + (kk - i * (N * s))) (by nlinarith)
    rw [coeff_mul_single_one] at h1
    convert h1 using 2
    ring
  -- a non-zero coefficient of the initial form
  have hPne : (l.map (initRed ((N : ℤ) * s))).prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]
    intro h
    obtain ⟨r, hr, h0⟩ := List.mem_map.mp h
    exact initRed_ne_zero _ r (hl0 r hr) h0
  have hle : kk ≤ (N : ℤ) * K0 := by
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
        nlinarith), map_zero, zero_mul]
  have hge' : (N : ℤ) * K0 ≤ kk := by
    by_contra hc
    push Not at hc
    apply hQ0
    rw [hQ]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi' : i ≤ F.natDegree := by have := Finset.mem_range.mp hi; omega
    by_cases hai : F.coeff i = 0
    · rw [hai]; simp [coeffZ]
    · have h1 := hge i hi' hai
      rw [coeffZ]
      split_ifs with h0
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
          have : (F.coeff i).natDegree < K0 - i * s := by nlinarith
          omega), map_zero, zero_mul]
      · rw [map_zero, zero_mul]
  have hkk : kk = (N : ℤ) * K0 := le_antisymm hle hge'
  rw [← hSum, hQ, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hkk,
    show (i : ℤ) * ((N : ℤ) * s) - (N : ℤ) * K0 = -((N : ℤ) * (K0 - i * s)) by ring,
    coeff_infSub_negmul N hN]

/-- **The root data at infinity from the residual polynomials of the segments.** -/
theorem multi_hdata (N : ℕ) (hN : 0 < N) (F : C[X][X]) (hF : F.Monic) (hF0 : F.coeff 0 ≠ 0)
    (l : List (LaurentSeries K)) (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {q : ℕ} (s : Fin (q + 1) → ℤ) (hs : StrictAnti s) (K0 : Fin (q + 1) → ℤ)
    (c : Fin (q + 1) → C) (hc : ∀ k, c k ≠ 0) (lo : Fin (q + 1) → ℕ) (Γ : Fin (q + 1) → List C)
    (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : C) ∉ Γ k)
    (hbound : ∀ k, ∀ i ≤ F.natDegree, F.coeff i ≠ 0 →
      ((F.coeff i).natDegree : ℤ) + i * s k ≤ K0 k)
    (hres : ∀ k, ∑ i ∈ Finset.range (F.natDegree + 1),
      Polynomial.C (coeffZ (F.coeff i) (K0 k - i * s k)) * X ^ i =
        Polynomial.C (c k) * X ^ (lo k) * ((Γ k).map fun γ ↦ X - Polynomial.C γ).prod)
    (htop : lo 0 + (Γ 0).length = F.natDegree)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0) :
    ∀ ρ ∈ l, (N : ℤ) ∣ ρ.order ∧ ρ.coeff ρ.order ∈ Set.range (algebraMap C K) ∧
      ∀ ρ' ∈ l, ρ'.order = ρ.order → ρ'.coeff ρ'.order = ρ.coeff ρ.order → ρ' = ρ := by
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
  set Γ' : Fin (q + 1) → List K := fun k ↦ (Γ k).map ι with hΓ'
  have hR : ∀ k, ∃ cK : K, cK ≠ 0 ∧ (l.map (initRed ((N : ℤ) * s k))).prod =
      Polynomial.C cK * X ^ (lo k) * ((Γ' k).map fun γ ↦ X - Polynomial.C γ).prod := by
    intro k
    have hQ0 : (∑ i ∈ Finset.range (F.natDegree + 1),
        Polynomial.C (coeffZ (F.coeff i) (K0 k - i * s k)) * X ^ i) ≠ 0 := by
      rw [hres k]
      refine mul_ne_zero (mul_ne_zero (by rw [Ne, Polynomial.C_eq_zero]; exact hc k)
        (pow_ne_zero _ X_ne_zero)) ?_
      rw [Ne, List.prod_eq_zero_iff]
      intro h
      obtain ⟨γ, -, h0⟩ := List.mem_map.mp h
      exact X_sub_C_ne_zero γ h0
    refine ⟨ι (c k), (_root_.map_ne_zero _).mpr (hc k), ?_⟩
    rw [initForm_segment N hN F l hl0 hl (s k) (K0 k) (hbound k) _ rfl hQ0, hres k]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_list_prod, List.map_map, hΓ']
    congr 2
    refine List.map_congr_left fun γ _ ↦ ?_
    simp [hι]
  have hσ : StrictAnti fun k ↦ (N : ℤ) * s k := fun a b hab ↦ by
    have := hs hab
    have hNz : (0 : ℤ) < N := by exact_mod_cast hN
    nlinarith
  have hΓK : ∀ k, (Γ' k).Nodup ∧ (0 : K) ∉ Γ' k := fun k ↦
    ⟨(hΓ k).1.map hιi, fun h ↦ by
      obtain ⟨γ, hγ, h0⟩ := List.mem_map.mp h
      exact (hΓ k).2 (by rwa [show γ = 0 from hιi (by rw [h0, map_zero])] at hγ)⟩
  obtain ⟨hord, huniq⟩ := roots_of_segments l hl0 (fun k ↦ (N : ℤ) * s k) hσ lo Γ' hΓK hR
    (by rw [hlen, ← htop, hΓ', List.length_map]) (fun k ↦ by rw [hchain k, hΓ', List.length_map])
    hlast
  intro ρ hρ
  obtain ⟨k, hk, hlc⟩ := hord ρ hρ
  refine ⟨⟨-s k, by rw [hk]; ring⟩, ?_, fun ρ' hρ' ho hc' ↦ huniq ρ' hρ' ρ hρ ho hc'⟩
  obtain ⟨γ, -, hγ⟩ := List.mem_map.mp hlc
  exact ⟨γ, hγ⟩

end Curves
