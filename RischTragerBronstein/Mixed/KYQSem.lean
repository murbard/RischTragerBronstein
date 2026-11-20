import RischTragerBronstein.Mixed.KYCodes

/-!
# Arithmetic modulo `M` over `ℚ`, evaluated at a root

For a root `ρ` of `M` in a field `F ⊇ ℚ`: `aeval ρ` turns `NFK.norm M`, `mulQ`, `powQ` into the
field operations (`aeval_normQ`, `aeval_mulQ`, `aeval_powQ`). If `M` stays irreducible over some
field of characteristic zero, no non-zero rational polynomial of degree `< deg M` vanishes at `ρ`
(`hmin_of_irr`), so `1, ρ, …, ρ^{deg M − 1}` are `ℚ`-independent (`pow_indep`) and normal forms
are determined by their values (`normQ_eq_of_aeval`).
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

variable (M : CPoly ℚ) {F : Type*} [Field F] [CharZero F] (ρ : F) (hρ : aeval ρ (toPoly M) = 0)

lemma normQ_dvd (l : CPoly ℚ) : toPoly M ∣ toPoly (NFK.norm M l) - toPoly l := by
  have h := divMod_spec l M
  rw [NFK.norm, toPoly_trim, h]
  exact ⟨-toPoly (divMod l M).1, by ring⟩

lemma normQ_degree (hM0 : toPoly M ≠ 0) (l : CPoly ℚ) :
    (toPoly (NFK.norm M l)).degree < (toPoly M).degree := by
  rw [NFK.norm, toPoly_trim]; exact divMod_degree_lt _ _ hM0

include hρ in
lemma aeval_normQ (l : CPoly ℚ) : aeval ρ (toPoly (NFK.norm M l)) = aeval ρ (toPoly l) := by
  obtain ⟨Q, hQ⟩ := normQ_dvd M l
  have := congrArg (aeval ρ) hQ
  rw [map_sub, map_mul, hρ, zero_mul, sub_eq_zero] at this
  exact this

include hρ in
lemma aeval_mulQ (a b : CPoly ℚ) :
    aeval ρ (toPoly (mulQ M a b)) = aeval ρ (toPoly a) * aeval ρ (toPoly b) := by
  rw [mulQ, aeval_normQ M ρ hρ, toPoly_mul, map_mul]

include hρ in
lemma aeval_powQ (a : CPoly ℚ) : ∀ k, aeval ρ (toPoly (powQ M a k)) = aeval ρ (toPoly a) ^ k
  | 0 => by rw [powQ, aeval_normQ M ρ hρ]; simp
  | k + 1 => by rw [powQ, aeval_mulQ M ρ hρ, aeval_powQ a k, pow_succ]

include hρ in
/-- **No small polynomial vanishes at `ρ`** when `M` stays irreducible over a field `K`. -/
theorem hmin_of_irr {K : Type*} [Field K] [CharZero K]
    (hirr : Irreducible ((toPoly M).map (algebraMap ℚ K))) :
    ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 := by
  intro P hP hdeg h0
  have hM0 : toPoly M ≠ 0 := fun h ↦ hirr.ne_zero (by rw [h, Polynomial.map_zero])
  have hint : IsIntegral ℚ ρ := ⟨_, (monic_mul_leadingCoeff_inv hM0), by
    rw [eval₂_mul, ← aeval_def, hρ, zero_mul]⟩
  set μ := minpoly ℚ ρ with hμ
  have hμM : μ ∣ toPoly M := minpoly.dvd ℚ ρ hρ
  have hμP : μ ∣ P := minpoly.dvd ℚ ρ h0
  have hμpos : 0 < μ.natDegree := minpoly.natDegree_pos hint
  obtain ⟨h, hh⟩ := hμM
  have hdμ : μ.natDegree ≤ P.natDegree := natDegree_le_of_dvd hμP hP
  have hPM : P.natDegree < (toPoly M).natDegree := by
    rwa [degree_eq_natDegree hP, degree_eq_natDegree hM0, Nat.cast_lt] at hdeg
  have hh0 : h ≠ 0 := fun h' ↦ hM0 (by rw [hh, h', mul_zero])
  have hdh : 0 < h.natDegree := by
    have e := congrArg natDegree hh
    rw [natDegree_mul (minpoly.ne_zero hint) hh0] at e
    change _ = μ.natDegree + _ at e
    omega
  rw [hh, Polynomial.map_mul] at hirr
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_map] at this; omega
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_map] at this; omega

variable (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)

include hmin in
/-- **`1, ρ, …` are `ℚ`-independent.** -/
theorem pow_indep (hM0 : toPoly M ≠ 0) (t : ℕ → ℚ)
    (ht : ∑ f ∈ Finset.range (toPoly M).natDegree, (t f : F) * ρ ^ f = 0) :
    ∀ f < (toPoly M).natDegree, t f = 0 := by
  classical
  set d := (toPoly M).natDegree with hd
  set P : ℚ[X] := ∑ f ∈ Finset.range d, Polynomial.C (t f) * X ^ f with hP
  have hPv : aeval ρ P = 0 := by
    rw [hP, map_sum]
    simp only [map_mul, aeval_C, aeval_X_pow, eq_ratCast]
    exact ht
  have hPdeg : P.degree < (toPoly M).degree := by
    rw [degree_eq_natDegree hM0, hP]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro f hf
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast Finset.mem_range.mp hf)
  have hP0 : P = 0 := by
    by_contra h
    exact hmin P h hPdeg hPv
  intro f hf
  have := congrArg (fun Q ↦ Q.coeff f) hP0
  simp only [hP, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rwa [Finset.sum_eq_single f (fun b _ hb ↦ by rw [if_neg (Ne.symm hb)])
    (fun h ↦ absurd (Finset.mem_range.mpr hf) h), if_pos rfl] at this

include hmin in
/-- **Normal forms are determined by their values at `ρ`.** -/
theorem normQ_eq_of_aeval (hM0 : toPoly M ≠ 0) (a b : CPoly ℚ)
    (h : aeval ρ (toPoly (NFK.norm M a)) = aeval ρ (toPoly (NFK.norm M b))) :
    NFK.norm M a = NFK.norm M b := by
  refine RFC.trim_ext (by rw [NFK.norm, trim_trim]) (by rw [NFK.norm, trim_trim]) ?_
  by_contra hne
  have hsub : toPoly (NFK.norm M a) - toPoly (NFK.norm M b) ≠ 0 := sub_ne_zero.mpr hne
  refine hmin _ hsub ((degree_sub_le _ _).trans_lt (max_lt (normQ_degree M hM0 a)
    (normQ_degree M hM0 b))) ?_
  rw [map_sub, h, sub_self]

/-- The value of an element through its coordinates. -/
lemma aeval_coords (hM0 : toPoly M ≠ 0) (hd : 0 < (toPoly M).natDegree) (l : CPoly ℚ) :
    aeval ρ (toPoly (NFK.norm M l)) = ∑ f ∈ Finset.range (toPoly M).natDegree,
      ((NFK.norm M l).getD f 0 : F) * ρ ^ f := by
  rw [aeval_eq_sum_range' (n := (toPoly M).natDegree)]
  · refine Finset.sum_congr rfl fun f _ ↦ ?_
    rw [coeff_toPoly, Algebra.smul_def, eq_ratCast]
  · have := normQ_degree M hM0 l
    rw [degree_eq_natDegree hM0] at this
    by_cases h0 : toPoly (NFK.norm M l) = 0
    · rw [h0, natDegree_zero]; exact hd
    · rw [degree_eq_natDegree h0] at this; exact_mod_cast this

end Curves.MT

namespace Curves.MT

variable (M : CPoly ℚ) {F : Type*} [Field F] [CharZero F] (ρ : F) (hρ : aeval ρ (toPoly M) = 0)
  (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)

lemma powQ_norm (a : CPoly ℚ) : ∀ k, ∃ l, powQ M a k = NFK.norm M l
  | 0 => ⟨[1], rfl⟩
  | _ + 1 => ⟨_, rfl⟩

include hρ hmin in
/-- **The checked root of unity** is a primitive `n`-th root of unity at `ρ`. -/
theorem zeta_prim (hM0 : toPoly M ≠ 0) (n : ℕ) (hn : 0 < n) (zN : CPoly ℚ)
    (h1 : powQ M zN n = NFK.norm M [1])
    (h2 : ∀ k, 0 < k → k < n → powQ M zN k ≠ NFK.norm M [1]) :
    IsPrimitiveRoot (aeval ρ (toPoly zN)) n := by
  have hone : aeval ρ (toPoly (NFK.norm M [1])) = 1 := by
    rw [aeval_normQ M ρ hρ]; simp
  refine IsPrimitiveRoot.mk_of_lt _ hn ?_ fun k hk0 hkn hk ↦ ?_
  · rw [← aeval_powQ M ρ hρ, h1, hone]
  · apply h2 k hk0 hkn
    obtain ⟨l, hl⟩ := powQ_norm M zN k
    rw [hl]
    refine normQ_eq_of_aeval M ρ hmin hM0 _ _ ?_
    rw [← hl, aeval_powQ M ρ hρ, hk, hone]

end Curves.MT
