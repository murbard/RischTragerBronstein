import RischTragerBronstein.Computable.HexpDegenerateDecide

/-!
# The independence certificate for two hyperexponentials is exact over `ℚ`

`hexpHexpIndepAll_complete`: over `ℚ`, if `hexpHexpIndepAll` fails then `z η₁ + c η₂` is a
logarithmic derivative for some integers `c ≠ 0`, `z`: there is `y ≠ 0` with
`y′ + (c η₂ + z η₁) y = 0`. Together with `hexpHexpIndepAll_hom` the certificate therefore decides
exactly whether `t₂′ = η₂ t₂` is a new hyperexponential over `S(x)(t₁)`, `t₁′ = η₁ t₁`
(`hexpHexpIndepAll_iff`).

The certificate fails only when
* both Hermite parts vanish and the degenerate-pair certificate fails (`hexpDegen_complete`), or
* `k η₁ᴴ + η₂ᴴ = 0` and every residue of the reduced `k η₁ + η₂` is rational (`nonRatResidue`
  fails): then `ratResidue_logDeriv` makes `M (k η₁ + η₂)` a logarithmic derivative.
-/

open Polynomial Differential UniqueFactorizationMonoid

namespace CPoly

variable {S K : Type*} [Field S] [CharZero S] [Differential S] [Differential S[X]] [Field K]
variable [CharZero K] [Algebra S[X] K] [Differential K[X]]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

private lemma logDeriv_zpow₃ (u : K) (hu : u ≠ 0) (n : ℤ) :
    logDeriv (u ^ n) = n * logDeriv u := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, logDeriv_pow]; simp
  · rw [zpow_neg, zpow_natCast, ← one_div, logDeriv_div _ _ one_ne_zero (pow_ne_zero _ hu),
      logDeriv_one, logDeriv_pow]
    simp

/-- **Rational residues give a logarithmic derivative**: if `N / s` (`s` squarefree, proper) has
residue polynomial `ρ` that is a rational constant modulo every prime of `s`, then `M N / s` is a
logarithmic derivative for some positive integer `M`. -/
theorem ratResidue_logDeriv (ιQ : ℚ →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (s N ρ : ℚ[X]) (hs0 : s ≠ 0) (hsq : Squarefree s) (hdeg : N.degree < s.degree)
    (hr : s ∣ ρ * derivative s - N)
    (hq : ∀ P ∈ normalizedFactors s, ∃ q : ℚ, P ∣ ρ - C q) :
    ∃ M : ℕ, M ≠ 0 ∧ ∃ w : K, w ≠ 0 ∧
      logDeriv w = (M : K) * (φ (N.map ιQ) / φ (s.map ιQ)) := by
  classical
  set F := (normalizedFactors s).toFinset with hF
  have hmem : ∀ P ∈ F, P ∈ normalizedFactors s := fun P hP ↦ Multiset.mem_toFinset.mp hP
  have hdvd : ∀ P ∈ F, P ∣ s := fun P hP ↦ dvd_of_mem_normalizedFactors (hmem P hP)
  have hirr : ∀ P ∈ F, Irreducible P := fun P hP ↦ irreducible_of_normalized_factor P (hmem P hP)
  let qf : ℚ[X] → ℚ := fun P ↦
    if hP : P ∈ normalizedFactors s then Classical.choose (hq P hP) else 0
  have hqf : ∀ P ∈ normalizedFactors s, P ∣ ρ - C (qf P) := fun P hP ↦ by
    simp only [qf, dif_pos hP]
    exact Classical.choose_spec (hq P hP)
  set M : ℕ := ∏ P ∈ F, (qf P).den with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P _ ↦ (qf P).den_nz
  have hint : ∀ P ∈ F, (((qf P * M).num : ℤ) : ℚ) = qf P * M := fun P hP ↦ by
    have h1 := Kron.den_mul_of_dvd (qf P) M (Finset.dvd_prod_of_mem _ hP)
    have := Rat.num_div_den (qf P * M)
    rwa [h1, Nat.cast_one, div_one] at this
  let n : ℚ[X] → ℤ := fun P ↦ (qf P * M).num
  set G : ℚ[X] := C (M : ℚ) * N with hG
  have hGdeg : G.degree < s.degree :=
    lt_of_le_of_lt (by rw [hG, ← smul_eq_C_mul]; exact degree_smul_le _ _) hdeg
  have hcong : ∀ P ∈ normalizedFactors s, P ∣ G - C (n P : ℚ) * derivative s := by
    intro P hP
    have hPF : P ∈ F := Multiset.mem_toFinset.mpr hP
    have hn : ((n P : ℤ) : ℚ) = qf P * M := hint P hPF
    have e : G - C (n P : ℚ) * derivative s =
        C (M : ℚ) * (-(ρ * derivative s - N)) + C (M : ℚ) * (ρ - C (qf P)) * derivative s := by
      rw [hG, hn, C_mul]; ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ((dvd_neg).mpr ((hdvd P hPF).trans hr)) _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hqf P hP) _) _)
  have hpf := pf_identity s G hs0 hsq n hGdeg hcong
  have hφ0 : ∀ Q : ℚ[X], Q ≠ 0 → φ (Q.map ιQ) ≠ 0 := fun Q hQ ↦
    (map_ne_zero_iff _ (IsFractionRing.injective S[X] K)).mpr
      ((Polynomial.map_ne_zero_iff ιQ.injective).mpr hQ)
  have hderφ : ∀ Q : ℚ[X], (φ (Q.map ιQ))′ = φ ((derivative Q).map ιQ) := fun Q ↦ by
    rw [deriv_algebraMap, hD, derivative_map]
  set w : K := ∏ P ∈ F, (φ (P.map ιQ)) ^ (n P) with hw
  have hw0 : w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P hP ↦
    zpow_ne_zero _ (hφ0 P (hirr P hP).ne_zero)
  refine ⟨M, hM0, w, hw0, ?_⟩
  have hs0K : φ (s.map ιQ) ≠ 0 := hφ0 s hs0
  rw [hw, logDeriv_prod _ _ _ fun P hP ↦ zpow_ne_zero _ (hφ0 P (hirr P hP).ne_zero)]
  have hterm : ∀ P ∈ F, logDeriv ((φ (P.map ιQ)) ^ (n P)) =
      φ ((C (n P : ℚ) * derivative P * (s / P)).map ιQ) / φ (s.map ιQ) := by
    intro P hP
    have hP0 := hφ0 P (hirr P hP).ne_zero
    rw [logDeriv_zpow₃ _ hP0, logDeriv, hderφ]
    have hsP : s = P * (s / P) := (EuclideanDomain.mul_div_cancel' (hirr P hP).ne_zero
      (hdvd P hP)).symm
    have hq0 : s / P ≠ 0 := fun h0 ↦ hs0 (by rw [hsP, h0, mul_zero])
    have hq0K := hφ0 _ hq0
    have hsK : φ (s.map ιQ) = φ (P.map ιQ) * φ ((s / P).map ιQ) := by
      rw [← map_mul, ← Polynomial.map_mul, ← hsP]
    rw [hsK]
    simp only [Polynomial.map_mul, map_C, map_mul, eq_intCast, map_intCast,
      Polynomial.map_intCast]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← map_sum, ← Polynomial.map_sum, ← hpf, hG]
  simp only [Polynomial.map_mul, map_C, map_mul, eq_natCast, map_natCast, Polynomial.map_natCast]
  ring

/-- An irreducible polynomial over `ℚ` does not divide its derivative. -/
lemma not_dvd_derivative_of_irreducible {P : ℚ[X]} (hP : Irreducible P) : ¬P ∣ derivative P :=
  fun hd ↦ hP.not_isUnit ((PerfectField.separable_of_irreducible hP).isUnit_of_dvd' dvd_rfl hd)

/-- **Matching residues**: `N / s = F₁ / F₂` with `s` squarefree and `F₁`, `F₂` coprime; if the
residue polynomial `r` of `F₁ / F₂` is a rational constant modulo the simple primes of `F₂`, then the
residue polynomial `ρ` of `N / s` is a rational constant modulo every prime of `s`. -/
lemma residue_match {s N ρ F₁ F₂ Sp r : ℚ[X]} (hsq : Squarefree s)
    (hρ : s ∣ ρ * derivative s - N) (hF : F₁ * s = N * F₂) (hcop : IsCoprime F₁ F₂)
    (hSimple : ∀ P : ℚ[X], Irreducible P → P ∣ F₂ → ¬P ∣ derivative F₂ → P ∣ Sp)
    (hbez : ∃ t, r * derivative F₂ + t * Sp = F₁)
    (hrat : ∀ P : ℚ[X], Irreducible P → P ∣ Sp → ∃ q : ℚ, P ∣ r - C q)
    (P : ℚ[X]) (hP : Irreducible P) (hPs : P ∣ s) : ∃ q : ℚ, P ∣ ρ - C q := by
  have hpr := hP.prime
  have hsep : IsCoprime s (derivative s) :=
    (PerfectField.separable_iff_squarefree.mpr hsq)
  have hPs' : ¬P ∣ derivative s := fun hd ↦ hP.not_isUnit (hsep.isUnit_of_dvd' hPs hd)
  by_cases hPN : P ∣ N
  · refine ⟨0, ?_⟩
    have h1 : P ∣ ρ * derivative s := by
      have := dvd_add (hPs.trans hρ) hPN
      rwa [sub_add_cancel] at this
    rw [C_0, sub_zero]
    exact (hpr.dvd_or_dvd h1).resolve_right hPs'
  -- `P` is a simple pole of `F₁ / F₂`
  have hPF2 : P ∣ F₂ := by
    have : P ∣ N * F₂ := by rw [← hF]; exact dvd_mul_of_dvd_right hPs _
    exact (hpr.dvd_or_dvd this).resolve_left hPN
  obtain ⟨a, ha⟩ := hPs
  obtain ⟨b, hb⟩ := hPF2
  have hP0 : P ≠ 0 := hP.ne_zero
  have hPa : ¬P ∣ a := fun ⟨a', ha'⟩ ↦ hP.not_isUnit (hsq P ⟨a', by rw [ha, ha']; ring⟩)
  have hPF1 : ¬P ∣ F₁ := fun hd ↦ hP.not_isUnit (hcop.isUnit_of_dvd' hd ⟨b, hb⟩)
  have hPb : ¬P ∣ b := by
    rintro ⟨b', hb'⟩
    have hcopP : IsCoprime (P * P) F₁ := by
      have := (hP.coprime_iff_not_dvd).mpr hPF1
      exact this.mul_left this
    have h2 : P * P ∣ F₁ * s := by rw [hF, hb, hb']; exact ⟨N * b', by ring⟩
    exact hP.not_isUnit (hsq P (hcopP.dvd_of_dvd_mul_left h2))
  have hPd := not_dvd_derivative_of_irreducible hP
  have hPF2' : ¬P ∣ derivative F₂ := by
    intro hd
    rw [hb, derivative_mul] at hd
    have : P ∣ derivative P * b := by
      have := dvd_sub hd (dvd_mul_right P (derivative b))
      rwa [add_sub_cancel_right] at this
    rcases hpr.dvd_or_dvd this with h | h
    · exact hPd h
    · exact hPb h
  obtain ⟨q, hq⟩ := hrat P hP (hSimple P hP ⟨b, hb⟩ hPF2')
  obtain ⟨t, ht⟩ := hbez
  have hSp := hSimple P hP ⟨b, hb⟩ hPF2'
  refine ⟨q, ?_⟩
  -- `N b = F₁ a`
  have hNb : N * b = F₁ * a := by
    have : P * (N * b) = P * (F₁ * a) := by
      calc P * (N * b) = N * (P * b) := by ring
        _ = N * F₂ := by rw [hb]
        _ = F₁ * s := hF.symm
        _ = P * (F₁ * a) := by rw [ha]; ring
    exact mul_left_cancel₀ hP0 this
  have e : (ρ - C q) * (derivative P * a * b) =
      b * (ρ * derivative s - N) - ρ * b * P * derivative a -
        a * ((r * derivative F₂ - F₁) - (r - C q) * derivative F₂) +
          C q * a * P * derivative b + (N * b - F₁ * a) := by
    rw [ha, hb, derivative_mul, derivative_mul]; ring
  have hdiv : P ∣ (ρ - C q) * (derivative P * a * b) := by
    rw [e, hNb, sub_self, add_zero]
    have h1 : P ∣ r * derivative F₂ - F₁ := by
      have : r * derivative F₂ - F₁ = -(t * Sp) := by rw [← ht]; ring
      rw [this]; exact (dvd_neg).mpr (dvd_mul_of_dvd_right hSp _)
    refine dvd_add (dvd_sub (dvd_sub (dvd_mul_of_dvd_right (dvd_trans (Dvd.intro a ha.symm) hρ) _) ?_) ?_) ?_
    · exact ⟨ρ * b * derivative a, by ring⟩
    · exact dvd_mul_of_dvd_right (dvd_sub h1 (dvd_mul_of_dvd_left hq _)) _
    · exact ⟨C q * a * derivative b, by ring⟩
  rcases hpr.dvd_or_dvd hdiv with h | h
  · exact h
  · rcases hpr.dvd_or_dvd h with h | h
    · rcases hpr.dvd_or_dvd h with h | h
      · exact absurd h hPd
      · exact absurd h hPa
    · exact absurd h hPb

set_option maxHeartbeats 3200000 in
/-- **The independence certificate for two hyperexponentials is complete over `ℚ`**: if it fails,
`y′ + (c η₂ + z η₁) y = 0` has a non-zero solution for some integers `c ≠ 0`, `z`. -/
theorem hexpHexpIndepAll_complete (ι : ℚ →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly ℚ} (hHd10 : toPoly Hd₁ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (h : hexpHexpIndepAll Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ = false) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ z : ℤ, ∃ y : K, y ≠ 0 ∧
      y′ + (ev K ι (smul (c : ℚ) Hn₂, Hd₂) +
        (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0 := by
  classical
  suffices hs : ∃ c : ℤ, c ≠ 0 ∧ ∃ z : ℤ, ∃ y : K, y ≠ 0 ∧
      y′ + ((c : K) * (φ ((toPoly Hn₂).map ι) / φ ((toPoly Hd₂).map ι)) +
        (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0 by
    obtain ⟨c, hc, z, y, hy, e⟩ := hs
    refine ⟨c, hc, z, y, hy, ?_⟩
    have hev : ev K ι (smul (c : ℚ) Hn₂, Hd₂) =
        (c : K) * (φ ((toPoly Hn₂).map ι) / φ ((toPoly Hd₂).map ι)) := by
      rw [ev, toPoly_smul, Polynomial.map_mul, map_C, map_mul, map_intCast, mul_div_assoc,
        C_eq_intCast, map_intCast]
    rw [hev]; exact e
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hφ0 : ∀ Q : ℚ[X], Q ≠ 0 → φ (Q.map ι) ≠ 0 := fun Q hQ ↦
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hQ)
  simp only [hexpHexpIndepAll, hexpHexpIndepFull, Bool.or_eq_false_iff] at h
  obtain ⟨⟨-, hcomb⟩, hdegen⟩ := h
  obtain ⟨G₁, -, -, -, hev₁⟩ := hermite_decomp (K := K) ι hD Hn₁ Hd₁ hHd10
  obtain ⟨G₂, -, -, -, hev₂⟩ := hermite_decomp (K := K) ι hD Hn₂ Hd₂ hHd20
  rw [Tower.ηh] at hev₁ hev₂
  unfold hexpHexpComb at hcomb
  split_ifs at hcomb with hz1 hz2
  · -- both Hermite parts vanish: the degenerate pair
    have hz2 : isZero (Tower.hermPartH Hn₂ Hd₂).1 = true := by simpa using hcomb
    have hzero : ∀ {Hn Hd : CPoly ℚ}, isZero (Tower.hermPartH Hn Hd).1 = true →
        ev K ι (Tower.hermPartH Hn Hd) = 0 := fun hz ↦ by
      rw [ev, (isZero_iff _).mp hz]; simp
    rw [hzero hz1] at hev₁
    rw [hzero hz2] at hev₂
    obtain ⟨c, z, hc, y, hy, hy'⟩ :=
      hexpDegen_complete (K := K) ι hD Hn₁ Hd₁ Hn₂ Hd₂ hHd10 hHd20 hdegen
    refine ⟨c, hc, z, y, hy, ?_⟩
    rw [← sub_eq_zero.mp hev₁.symm, ← sub_eq_zero.mp hev₂.symm] at hy'
    exact hy'
  -- both Hermite parts nonzero
  rcases hls : linSolve [mul (Tower.hermPartH Hn₁ Hd₁).1 (Tower.hermPartH Hn₂ Hd₂).2]
      (smul (-1) (mul (Tower.hermPartH Hn₂ Hd₂).1 (Tower.hermPartH Hn₁ Hd₁).2)) with _ | cs
  · simp [hls] at hcomb
  obtain ⟨hlen, hlc⟩ := linSolve_sound _ _ _ hls
  obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hlen
  simp only [hls] at hcomb
  -- the data
  obtain ⟨hsq₁, hdg₁⟩ := integrateRational_facts Hn₁ Hd₁ hHd10
  obtain ⟨hsq₂, hdg₂⟩ := integrateRational_facts Hn₂ Hd₂ hHd20
  set I₁ := integrateRational Hn₁ Hd₁ with hI₁
  set I₂ := integrateRational Hn₂ Hd₂ with hI₂
  simp only [lcomb, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
    add_zero, toPoly_smul, toPoly_mul, Tower.hermPartH, toPoly_sub, map_neg, C_1,
    neg_one_mul] at hlc
  obtain ⟨hd₁, hd₂, hsqs⟩ := lcmSq_spec I₁.s I₂.s hsq₁ hsq₂
  set sC := lcmSq I₁.s I₂.s with hsC
  have hs0 : toPoly sC ≠ 0 := hsqs.ne_zero
  have hs10 : toPoly I₁.s ≠ 0 := hsq₁.ne_zero
  have hs20 : toPoly I₂.s ≠ 0 := hsq₂.ne_zero
  set q₁ := (divMod sC I₁.s).1 with hq₁
  set q₂ := (divMod sC I₂.s).1 with hq₂
  have hsq₁' : toPoly sC = toPoly q₁ * toPoly I₁.s := by
    rw [divMod_spec sC I₁.s, divMod_exact sC I₁.s hs10 hd₁, add_zero]
  have hsq₂' : toPoly sC = toPoly q₂ * toPoly I₂.s := by
    rw [divMod_spec sC I₂.s, divMod_exact sC I₂.s hs20 hd₂, add_zero]
  have hq₁0 : toPoly q₁ ≠ 0 := fun h0 ↦ hs0 (by rw [hsq₁', h0, zero_mul])
  have hq₂0 : toPoly q₂ ≠ 0 := fun h0 ↦ hs0 (by rw [hsq₂', h0, zero_mul])
  set NC : CPoly ℚ := add (smul k (mul I₁.r q₁)) (mul I₂.r q₂) with hNC
  have hNCp : toPoly NC = C k * (toPoly I₁.r * toPoly q₁) + toPoly I₂.r * toPoly q₂ := by
    rw [hNC, toPoly_add, toPoly_smul, toPoly_mul, toPoly_mul]
  have hNdeg : (toPoly NC).degree < (toPoly sC).degree := by
    have hlt : ∀ {r q sᵢ : ℚ[X]}, toPoly sC = q * sᵢ → q ≠ 0 → r.degree < sᵢ.degree →
        (r * q).degree < (toPoly sC).degree := by
      intro r q sᵢ hsqi hq0 hdg
      rw [hsqi, degree_mul, degree_mul, add_comm q.degree sᵢ.degree]
      exact WithBot.add_lt_add_right (by rw [degree_eq_natDegree hq0]; exact WithBot.coe_ne_bot) hdg
    rw [hNCp]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ (hlt hsq₂' hq₂0 hdg₂))
    exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) (hlt hsq₁' hq₁0 hdg₁)
  -- `(k η₁ + η₂) s = N` as polynomials
  have E : (C k * toPoly Hn₁ * toPoly Hd₂ + toPoly Hn₂ * toPoly Hd₁) * toPoly sC =
      toPoly NC * (toPoly Hd₁ * toPoly Hd₂) := by
    have h12 : toPoly I₁.s * toPoly I₂.s ≠ 0 := mul_ne_zero hs10 hs20
    refine mul_right_cancel₀ h12 ?_
    rw [hNCp]
    linear_combination (toPoly sC) * hlc +
      (toPoly Hd₁ * toPoly Hd₂ * C k * toPoly I₁.r * toPoly I₂.s) * hsq₁' +
      (toPoly Hd₁ * toPoly Hd₂ * toPoly I₂.r * toPoly I₁.s) * hsq₂'
  -- the reduced fraction `F = k η₁ + η₂`
  set F := combFrac k Hn₁ Hd₁ Hn₂ Hd₂ with hFd
  have hF20 : toPoly F.2 ≠ 0 := normCoeff_den_ne_zero _
  have hcop : IsCoprime (toPoly F.1) (toPoly F.2) := normCoeff_coprime _
  have hB0 : toPoly Hd₁ * toPoly Hd₂ ≠ 0 := mul_ne_zero hHd10 hHd20
  have hFval : toPoly F.1 * (toPoly Hd₁ * toPoly Hd₂) =
      (C k * toPoly Hn₁ * toPoly Hd₂ + toPoly Hn₂ * toPoly Hd₁) * toPoly F.2 := by
    have hsp : algebraMap ℚ[X] (RatFunc ℚ) (toPoly F.1) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly F.2) =
        algebraMap ℚ[X] (RatFunc ℚ) (toPoly (add (mul (smul k Hn₁) Hd₂) (mul Hn₂ Hd₁))) /
          algebraMap ℚ[X] (RatFunc ℚ) (toPoly (mul Hd₁ Hd₂)) :=
      normCoeff_spec (algebraMap ℚ[X] (RatFunc ℚ)) (IsFractionRing.injective _ _)
        (add (mul (smul k Hn₁) Hd₂) (mul Hn₂ Hd₁), mul Hd₁ Hd₂)
    simp only [toPoly_add, toPoly_mul, toPoly_smul] at hsp
    have hψ0 : ∀ Q : ℚ[X], Q ≠ 0 → algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 := fun Q hQ ↦
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hQ
    rw [div_eq_div_iff (hψ0 _ hF20) (hψ0 _ hB0), ← map_mul, ← map_mul] at hsp
    have := IsFractionRing.injective ℚ[X] (RatFunc ℚ) hsp
    rw [this]
  have hF : toPoly F.1 * toPoly sC = toPoly NC * toPoly F.2 := by
    refine mul_right_cancel₀ hB0 ?_
    linear_combination (toPoly sC) * hFval + (toPoly F.2) * E
  -- the simple part of `F` and its residues
  obtain ⟨S₀, G₁', G, q₁', q₂', σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := simplePart_data F.2 hF20
  obtain ⟨hS0, -, hScop, -, hSimple, -⟩ := Differential.simplePart_props hF20 E1 E2 E3 E4 E5 E6
  have hbez := residuePolyW_bezout F.1 F.2 hS0 hScop.symm
  unfold nonRatResidue at hcomb
  have hz : isZero (divMod (ratShiftProd (residuePolyW F.1 F.2) (HasRatRoots.ratRoots
      (findMu (simplePart F.2) (residuePolyW F.1 F.2)))) (simplePart F.2)).2 = true := by
    simpa using hcomb
  have hSd := dvd_of_rem_zero' hz
  rw [toPoly_ratShiftProd] at hSd
  simp only [Rat.cast_id] at hSd
  have hrat : ∀ P : ℚ[X], Irreducible P → P ∣ toPoly (simplePart F.2) →
      ∃ q : ℚ, P ∣ toPoly (residuePolyW F.1 F.2) - C q := by
    intro P hP hPS
    have : P ∣ ((HasRatRoots.ratRoots (findMu (simplePart F.2) (residuePolyW F.1 F.2))).map
        fun q : ℚ ↦ toPoly (residuePolyW F.1 F.2) - C q).prod :=
      hPS.trans ⟨_, by rw [hSd, mul_comm]⟩
    obtain ⟨a, ha, hPa⟩ := (hP.prime.dvd_prod_iff).mp this
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
    exact ⟨q, by simpa using hPa⟩
  have hρ := resPoly_spec sC NC hsqs
  have hq : ∀ P ∈ normalizedFactors (toPoly sC), ∃ q : ℚ, P ∣ toPoly (resPoly sC NC) - C q :=
    fun P hP ↦ residue_match (s := toPoly sC) (N := toPoly NC) (ρ := toPoly (resPoly sC NC))
      (F₁ := toPoly F.1) (F₂ := toPoly F.2) (Sp := toPoly (simplePart F.2))
      (r := toPoly (residuePolyW F.1 F.2)) hsqs hρ hF hcop hSimple hbez hrat P
      (irreducible_of_normalized_factor P hP) (dvd_of_mem_normalizedFactors hP)
  obtain ⟨M, hM0, w, hw0, hlog⟩ :=
    ratResidue_logDeriv (K := K) ι hD (toPoly sC) (toPoly NC) (toPoly (resPoly sC NC)) hs0 hsqs
      hNdeg hρ hq
  -- the relation
  set dk : ℕ := k.den with hdk
  set W : K := w ^ dk with hW
  have hW0 : W ≠ 0 := pow_ne_zero _ hw0
  refine ⟨(M : ℤ) * dk, by exact_mod_cast Nat.mul_ne_zero hM0 k.den_nz, (M : ℤ) * k.num, W⁻¹,
    inv_ne_zero hW0, ?_⟩
  have hlogW : logDeriv W = (dk : K) * ((M : K) * (φ ((toPoly NC).map ι) / φ ((toPoly sC).map ι))) := by
    rw [hW, logDeriv_pow, hlog]
  have hW' : W′ = (dk : K) * ((M : K) * (φ ((toPoly NC).map ι) / φ ((toPoly sC).map ι))) * W := by
    rw [← hlogW, logDeriv, div_mul_cancel₀ _ hW0]
  -- `k` in `K`
  set κ : K := φ (C (ι k)) with hκ
  have hκd : κ * (dk : K) = (k.num : K) := by
    have := congrArg (fun x : ℚ ↦ φ (C (ι x))) (Rat.mul_den_eq_num k)
    simp only [map_mul, map_natCast, map_intCast, C_mul] at this
    simpa [hκ, hdk, map_natCast] using this
  have EK := congrArg (fun P : ℚ[X] ↦ φ (P.map ι)) E
  simp only [Polynomial.map_mul, Polynomial.map_add, map_C, map_mul, map_add] at EK
  rw [← hκ] at EK
  have h1 := hφ0 _ hHd10
  have h2 := hφ0 _ hHd20
  have hsK := hφ0 _ hs0
  have hsum : (((M : ℤ) * dk : ℤ) : K) * (φ ((toPoly Hn₂).map ι) / φ ((toPoly Hd₂).map ι)) +
      (((M : ℤ) * k.num : ℤ) : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι)) =
      (dk : K) * ((M : K) * (φ ((toPoly NC).map ι) / φ ((toPoly sC).map ι))) := by
    push_cast
    rw [← hκd]
    field_simp
    linear_combination (dk : K) * EK
  rw [Derivation.leibniz_inv, smul_eq_mul, hW', hsum]
  field_simp
  ring

/-- **The certificate decides independence exactly** (over `ℚ`): for well-formed hyperexponential
data, `hexpHexpIndepAll` holds iff `y′ + (c η₂ + z η₁) y = 0` has only the zero solution for all
integers `c ≠ 0`, `z`. -/
theorem hexpHexpIndepAll_iff (ι : ℚ →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly ℚ}
    (hHn10 : toPoly Hn₁ ≠ 0) (hHd10 : toPoly Hd₁ ≠ 0)
    (hcop₁ : IsCoprime (toPoly Hn₁) (toPoly Hd₁)) (hcert₁ : hyperexpMonomialCheck Hn₁ Hd₁ μ₁ = true)
    (hHn20 : toPoly Hn₂ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂)) (hcert₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true) :
    hexpHexpIndepAll Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ = true ↔
      ∀ c : ℤ, c ≠ 0 → ∀ z : ℤ, ∀ y : K,
        y′ + (ev K ι (smul (c : ℚ) Hn₂, Hd₂) +
          (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0 → y = 0 := by
  constructor
  · intro hind c hc z y h
    exact hexpHexpIndepAll_hom ι hD hHn10 hHd10 hcop₁ hcert₁ hHn20 hHd20 hcop₂ hcert₂ hind c hc z y h
  · intro hall
    by_contra hne
    obtain ⟨c, hc, z, y, hy, h⟩ :=
      hexpHexpIndepAll_complete (K := K) ι hD hHd10 hHd20 (Bool.eq_false_iff.mpr hne)
    exact hy (hall c hc z y h)

end CPoly
