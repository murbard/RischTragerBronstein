import RischTragerBronstein.Mixed.NKResRam

/-!
# Ramified places at infinity: one residual root per place

For a slope `s/e` (`gcd(s, e) = 1`) at infinity, the expanded inverted curve
`Q(T, Z) = T^{ns} P(T^{−e}, Z T^{−s})` satisfies `Q(wT, w^s Z) = w^{ns} Q(T, Z)` for `wᵉ = 1`, so a
power-series root `Θ` gives the conjugate roots `w^{−s} Θ(wT)` (`fibre_root_conj`). Hence one
residual root `γₖ` per place suffices (the others are `ζ^{−sj} γₖ`), and the residue at `T^e` is
the same along all conjugates (`zero_res_ramConj`): residues can be certified over `Fₘ` even when
the residual roots of a place are not all rational.
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Sym

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K]
  [Differential C] [Differential K]

lemma coeff_reflect_expand_ne (e d : ℕ) (he : 0 < e) (a : C[X]) (ha : a.natDegree * e ≤ d) (m : ℕ)
    (hm : (reflect d (expand C e a)).coeff m ≠ 0) : ∃ k, m + e * k = d := by
  rw [coeff_reflect] at hm
  by_cases hmd : m ≤ d
  · rw [revAt_le hmd, coeff_expand he] at hm
    split_ifs at hm with hdv
    · obtain ⟨k, hk⟩ := hdv; exact ⟨k, by omega⟩
    · exact absurd rfl hm
  · rw [revAt_eq_self_of_lt (by omega), coeff_expand he] at hm
    split_ifs at hm with hdv
    · exfalso; apply hm
      apply coeff_eq_zero_of_natDegree_lt
      obtain ⟨k, hk⟩ := hdv
      rw [hk, Nat.mul_div_cancel_left _ he]
      by_contra h
      push_neg at h
      have h1 : e * k ≤ e * a.natDegree := Nat.mul_le_mul_left _ h
      have h2 : e * a.natDegree = a.natDegree * e := mul_comm _ _
      omega
    · exact absurd rfl hm

lemma rescale_coe_reflect_expand (e d : ℕ) (he : 0 < e) (a : C[X]) (ha : a.natDegree * e ≤ d)
    (w : K) (hw : w ^ e = 1) :
    PowerSeries.rescale w (((reflect d (expand C e a)).map (algebraMap C K) : K[X]) : PowerSeries K) =
      PowerSeries.C (w ^ d) *
        (((reflect d (expand C e a)).map (algebraMap C K) : K[X]) : PowerSeries K) := by
  ext m
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, Polynomial.coeff_coe, Polynomial.coeff_map]
  by_cases h : (reflect d (expand C e a)).coeff m = 0
  · rw [h, map_zero, mul_zero, mul_zero]
  · obtain ⟨k, hk⟩ := coeff_reflect_expand_ne e d he a ha m h
    rw [← hk, pow_add, pow_mul, hw, one_pow, mul_one]

lemma X_pow_dvd_rescale (M : ℕ) (w : K) (f : PowerSeries K)
    (h : (PowerSeries.X : PowerSeries K) ^ M ∣ f) :
    (PowerSeries.X : PowerSeries K) ^ M ∣ PowerSeries.rescale w f := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro d hd
  rw [PowerSeries.coeff_rescale, h d hd, mul_zero]

/-- **Conjugate roots**: if `Θ` is a root of the inverted expanded curve, so is `w^{−s} Θ(wT)`
for every `wᵉ = 1`. -/
theorem fibre_root_conj (P0 : C[X][X]) (n s e : ℕ) (he : 0 < e) (hm : P0.Monic)
    (hn : P0.natDegree = n)
    (hdeg : ∀ i ≤ n, (P0.coeff i).natDegree * e ≤ (n - i) * s) (w : K) (hw : w ^ e = 1)
    (Θ : PowerSeries K)
    (hΘ : (fibrePS (K := K) (invPS n s (P0.map (expand C e : C[X] →+* C[X]))) 0).eval Θ = 0) :
    (fibrePS (K := K) (invPS n s (P0.map (expand C e : C[X] →+* C[X]))) 0).eval
      (PowerSeries.C (w⁻¹ ^ s) * PowerSeries.rescale w Θ) = 0 := by
  classical
  set P := P0.map (expand C e : C[X] →+* C[X]) with hP
  have hw0 : w ≠ 0 := by
    rintro rfl; rw [zero_pow he.ne'] at hw; exact zero_ne_one hw
  have hPm : P.Monic := hm.map _
  have hPn : P.natDegree = n := by rw [hP, hm.natDegree_map, hn]
  obtain ⟨-, hQn⟩ := invPS_monic P n s hPm hPn
  set Q := invPS n s P with hQ
  have hlt : (fibrePS (K := K) Q 0).natDegree < n + 1 := by
    rw [fibrePS]; exact lt_of_le_of_lt (natDegree_map_le) (by omega)
  have hcoef : ∀ i ∈ Finset.range (n + 1), (fibrePS (K := K) Q 0).coeff i =
      (((reflect ((n - i) * s) (expand C e (P0.coeff i))).map (algebraMap C K) : K[X]) :
        PowerSeries K) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [fibrePS, Polynomial.coeff_map, hQ, coeff_invPS, if_pos hi', hP, Polynomial.coeff_map,
      MT.psSub_one_zero]
    rfl
  rw [eval_eq_sum_range' hlt] at hΘ ⊢
  have hr := congrArg (PowerSeries.rescale w) hΘ
  rw [map_zero, map_sum] at hr
  have hstep : ∀ i ∈ Finset.range (n + 1),
      (fibrePS (K := K) Q 0).coeff i * (PowerSeries.C (w⁻¹ ^ s) * PowerSeries.rescale w Θ) ^ i =
        PowerSeries.C (w⁻¹ ^ (n * s)) *
          PowerSeries.rescale w ((fibrePS (K := K) Q 0).coeff i * Θ ^ i) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [map_mul, map_pow (PowerSeries.rescale w), hcoef i hi, rescale_coe_reflect_expand e _ he _ (hdeg i hi') w hw,
      mul_pow]
    have hwk : (w⁻¹ ^ s) ^ i = w⁻¹ ^ (n * s) * w ^ ((n - i) * s) := by
      have e1 : n * s = (n - i) * s + i * s := by rw [← add_mul, Nat.sub_add_cancel hi']
      rw [e1, pow_add, mul_comm, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hw0, one_pow, one_mul,
        ← pow_mul, mul_comm s i]
    have hC : (PowerSeries.C (w⁻¹ ^ s)) ^ i =
        PowerSeries.C (w⁻¹ ^ (n * s)) * PowerSeries.C (w ^ ((n - i) * s)) := by
      rw [← map_pow, ← map_mul, hwk]
    rw [hC]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hr, mul_zero]

end Sym

section Main

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K] [Differential C]
  [Differential K] [IsAlgClosed K]

lemma exists_primitive_K (e : ℕ) (he : 0 < e) : ∃ ζ : K, IsPrimitiveRoot ζ e := by
  have : NeZero (e : K) := ⟨by exact_mod_cast he.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic e K) (degree_cyclotomic_pos e K he).ne'
  exact ⟨z, (isRoot_cyclotomic_iff).mp hz⟩

/-- **Zero residues at ramified places at infinity from one residual root per place.** -/
theorem zero_res_ramConj (P0 : C[X][X]) (hm : P0.Monic) (n np e s M : ℕ) (he : 0 < e)
    (hne : np * e = n) (hcop : Nat.Coprime s e) (hn : P0.natDegree = n)
    (hdeg : ∀ i ≤ n, (P0.coeff i).natDegree * e ≤ (n - i) * s)
    (γ : Fin np → C) (hγ0 : ∀ k, γ k ≠ 0) (hγi : Function.Injective fun k ↦ γ k ^ e)
    (hγ : ∀ k, (fibreAt (K := K) (invPS n s (P0.map (expand C e : C[X] →+* C[X]))) 0).eval
      (algebraMap C K (γ k)) = 0)
    (hγ' : ∀ k, (fibreAt (K := K) (derivative (invPS n s (P0.map (expand C e : C[X] →+* C[X]))))
      0).eval (algebraMap C K (γ k)) ≠ 0)
    (Θt : Fin np → C[X]) (hΘ0 : ∀ k, (Θt k).coeff 0 = γ k)
    (hΘM : ∀ k, (PowerSeries.X : PowerSeries K) ^ M ∣
      (fibrePS (K := K) (invPS n s (P0.map (expand C e : C[X] →+* C[X]))) 0).eval
        (((Θt k).map (algebraMap C K) : K[X]) : PowerSeries K))
    (Q0 : C[X][X])
    (hM : ∀ j ≤ (Q0.map (expand C e : C[X] →+* C[X])).natDegree,
      e + ((Q0.map (expand C e : C[X] →+* C[X])).coeff j).natDegree + s * j < M)
    (z : Fin np → C)
    (hz : ∀ k, (z k)′ = ∑ j ∈ Finset.range ((Q0.map (expand C e : C[X] →+* C[X])).natDegree + 1),
      ∑ i ∈ Finset.range (((Q0.map (expand C e : C[X] →+* C[X])).coeff j).natDegree + 1),
        ((Q0.map (expand C e : C[X] →+* C[X])).coeff j).coeff i * ((Θt k) ^ j).coeff (e + i + s * j))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) :
    ∃ li : List (LaurentSeries K), P0.map (infSub (K := K) e) =
      (li.map fun r ↦ X - Polynomial.C r).prod ∧
      ∀ r ∈ li, ∃ β : K, ((Q0.map (infSub (K := K) e)).eval r).coeff (e : ℤ) = β′ := by
  classical
  set P := P0.map (expand C e : C[X] →+* C[X]) with hP
  set Qf := Q0.map (expand C e : C[X] →+* C[X]) with hQf
  have hPm : P.Monic := hm.map _
  have hPn : P.natDegree = n := by rw [hP, hm.natDegree_map, hn]
  have hdegP : ∀ i ≤ n, (P.coeff i).natDegree ≤ (n - i) * s := by
    intro i hi
    rw [hP, Polynomial.coeff_map]
    change (expand C e (P0.coeff i)).natDegree ≤ _
    rw [natDegree_expand]; exact hdeg i hi
  obtain ⟨ζ, hζ⟩ := exists_primitive_K (K := K) e he
  have hζe : ∀ j : ℕ, (ζ ^ j) ^ e = 1 := fun j ↦ by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero he.ne'
  -- base roots
  choose Θ hΘ using fun k ↦ exists_root_lift (invPS n s P) (invPS_monic P n s hPm hPn).1 (0 : K)
    (algebraMap C K (γ k)) (hγ k) (hγ' k)
  -- conjugate roots
  set η : K := ζ⁻¹ ^ s with hη
  have hηp : IsPrimitiveRoot η e := hζ.inv.pow_of_coprime s hcop
  have hconj : ∀ j : ℕ, (ζ ^ j)⁻¹ ^ s = η ^ j := fun j ↦ by
    rw [hη, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  set Θc : Fin np × Fin e → PowerSeries K := fun p ↦
    PowerSeries.C ((ζ ^ (p.2 : ℕ))⁻¹ ^ s) * PowerSeries.rescale (ζ ^ (p.2 : ℕ)) (Θ p.1) with hΘc
  have hΘcr : ∀ p, (fibrePS (K := K) (invPS n s P) 0).eval (Θc p) = 0 := fun p ↦
    fibre_root_conj P0 n s e he hm hn hdeg _ (hζe _) _ (hΘ p.1).1
  have hΘc0 : ∀ p, PowerSeries.constantCoeff (Θc p) = η ^ (p.2 : ℕ) * algebraMap C K (γ p.1) := by
    intro p
    rw [hΘc, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      (hΘ p.1).2, hconj]
  have hinj : Function.Injective fun p : Fin np × Fin e ↦ η ^ (p.2 : ℕ) * algebraMap C K (γ p.1) := by
    rintro ⟨k, j⟩ ⟨k', j'⟩ h
    simp only at h
    have hpe := congrArg (· ^ e) h
    have he1 : ∀ i : ℕ, (η ^ i) ^ e = 1 := fun i ↦ by
      rw [← pow_mul, mul_comm, pow_mul, hηp.pow_eq_one, one_pow]
    simp only [mul_pow] at hpe
    rw [he1, he1, one_mul, one_mul, ← map_pow, ← map_pow] at hpe
    have hk : k = k' := hγi ((algebraMap C K).injective hpe)
    subst hk
    have hγK : algebraMap C K (γ k) ≠ 0 := fun h0 ↦
      hγ0 k ((map_eq_zero_iff _ (algebraMap C K).injective).mp h0)
    have hj := mul_right_cancel₀ hγK h
    have := hηp.pow_inj j.2 j'.2 hj
    rw [Prod.mk.injEq]
    exact ⟨rfl, Fin.ext this⟩
  set r : Fin np × Fin e → LaurentSeries K := fun p ↦
    ofPowerSeries ℤ K (Θc p) * single (-(s : ℤ)) 1 with hr
  have hrinj : Function.Injective r := by
    intro p q h
    have hs : single (-(s : ℤ)) (1 : K) ≠ 0 := by simp
    have h1 := HahnSeries.ofPowerSeries_injective (mul_right_cancel₀ hs h)
    have h2 := congrArg PowerSeries.constantCoeff h1
    rw [hΘc0, hΘc0] at h2
    exact hinj h2
  set G := P.map (infSub (K := K) 1) with hG
  have hGm : G.Monic := hPm.map _
  have hGd : G.natDegree = n := by rw [hG, hPm.natDegree_map, hPn]
  set l := (Finset.univ : Finset (Fin np × Fin e)).toList.map r with hl
  have hnd : l.Nodup := (Finset.nodup_toList _).map hrinj
  have hlen : l.length = n := by
    rw [hl, List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, hne]
  have hroot : ∀ y ∈ l, G.eval y = 0 := by
    intro y hy
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
    refine inv_root P n s hPn hdegP _ ?_
    have := hΘcr p
    rw [fibrePS] at this
    have e' : (invPS n s P).map (branchSub 1 (0 : K)) =
        ((invPS n s P).map (psSub 1 (0 : K))).map (ofPowerSeries ℤ K) := by
      rw [Polynomial.map_map]; rfl
    rw [e', eval_map, Polynomial.eval₂_hom, this, map_zero]
  have hsplit := EllQuad.split_of_hasRoots hGm.ne_zero hnd (by rw [hGd, hlen]) hroot
  rw [hGm.leadingCoeff, map_one, one_mul] at hsplit
  have hinf := infSub_comp_expand (C := C) (K := K) e
  refine ⟨l, ?_, ?_⟩
  · rw [hinf, ← Polynomial.map_map, ← hP, ← hG, hsplit]
  intro y hy
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
  obtain ⟨k, j⟩ := p
  refine ⟨algebraMap C K (z k), ?_⟩
  rw [hinf, ← Polynomial.map_map, ← hQf]
  set w : K := ζ ^ (j : ℕ) with hw
  have hwe : w ^ e = 1 := hζe _
  set Θk : PowerSeries K := (((Θt k).map (algebraMap C K) : K[X]) : PowerSeries K) with hΘk
  have hagree : (PowerSeries.X : PowerSeries K) ^ M ∣ Θ k - Θk := by
    refine hensel_trunc _ (Θ k) Θk (hΘ k).1 ?_ ?_ M (hΘM k)
    · rw [(hΘ k).2, hΘk, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        Polynomial.coeff_map, hΘ0]
    · rw [derivative_fibrePS, fibrePS_eval_const', hΘk,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, Polynomial.coeff_map,
        hΘ0]
      exact hγ' k
  set Θk' : PowerSeries K := PowerSeries.C (w⁻¹ ^ s) * PowerSeries.rescale w Θk with hΘk'
  have hagree' : (PowerSeries.X : PowerSeries K) ^ M ∣ Θc (k, j) - Θk' := by
    have : Θc (k, j) - Θk' = PowerSeries.C (w⁻¹ ^ s) * PowerSeries.rescale w (Θ k - Θk) := by
      rw [hΘc, hΘk', map_sub, mul_sub]
    rw [this]
    exact Dvd.dvd.mul_left (X_pow_dvd_rescale M w _ hagree) _
  rw [coeff_eval_inf_splitN Qf e s M (Θc (k, j)) Θk' hagree' hM, hK, hz k, map_sum]
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hpow : Θk' ^ j' = PowerSeries.C ((w⁻¹ ^ s) ^ j') * PowerSeries.rescale w (Θk ^ j') := by
    simp only [hΘk', mul_pow, map_pow]
  rw [hpow, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_mul, hΘk, ← Polynomial.coe_pow,
    Polynomial.coeff_coe, ← Polynomial.map_pow, Polynomial.coeff_map]
  rcases eq_or_ne (((Q0.map (expand C e : C[X] →+* C[X])).coeff j').coeff i) 0 with hq | hq
  · rw [Polynomial.coeff_map] at hq
    rw [hq, map_zero, zero_mul, zero_mul]
  · have hdv : e ∣ i := by
      rw [Polynomial.coeff_map] at hq
      change (expand C e (Q0.coeff j')).coeff i ≠ 0 at hq
      rw [coeff_expand he] at hq
      by_contra h
      exact hq (if_neg h)
    obtain ⟨a, rfl⟩ := hdv
    have hw0 : w ≠ 0 := pow_ne_zero _ hζ0
    have h1 : (w⁻¹ ^ s) ^ j' * w ^ (e + e * a + s * j') = 1 := by
      rw [pow_add, pow_add, pow_mul w e a, hwe, one_pow, one_mul, one_mul, ← pow_mul, ← mul_pow,
        inv_mul_cancel₀ hw0, one_pow]
    rw [Polynomial.coeff_map, ← mul_assoc ((w⁻¹ ^ s) ^ j'), h1, one_mul]

end Main

end Curves
