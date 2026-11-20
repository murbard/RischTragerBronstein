import RischTragerBronstein.Computable.HexpDegenerateSpec

/-!
# Completeness of the degenerate-pair head certificate

For `ηᵢ = Nᵢ / s` (`s ∈ ℚ[x]` squarefree, `deg Nᵢ < deg s`) with residue polynomials `ρᵢ`
(`s ∣ ρᵢ s′ - Nᵢ`): if the head certificate `Kron.genResCertHead s [ρ₂, ρ₁]` fails, then
`c η₂ + z η₁` is a logarithmic derivative for some integers `c ≠ 0`, `z`. Explicitly
`y = ∏_P P ^ (-n_P)` over the monic irreducible factors `P` of `s` solves
`y′ + (c η₂ + z η₁) y = 0`, in every differential field `K ⊇ S(x)`.

Together with `hexpDegen_hom`, the head certificate therefore decides exactly whether
`t₂′/t₂ = η₂` is independent of `t₁′/t₁ = η₁` modulo logarithmic derivatives.

* `pf_identity`: the partial-fraction identity `G = ∑_P n_P P′ (s / P)` from the congruences
  `G ≡ n_P s′ (mod P)`;
* `degenPair_relation`: the explicit relation.
-/

open Polynomial Differential UniqueFactorizationMonoid

namespace CPoly

section PF

/-- Distinct normalized factors are coprime. -/
lemma isCoprime_of_mem_normalizedFactors {s P Q : ℚ[X]} (hP : P ∈ normalizedFactors s)
    (hQ : Q ∈ normalizedFactors s) (hPQ : P ≠ Q) : IsCoprime P Q := by
  have hPi := irreducible_of_normalized_factor P hP
  have hQi := irreducible_of_normalized_factor Q hQ
  refine (hPi.coprime_iff_not_dvd).mpr fun hd ↦ hPQ ?_
  exact (hPi.associated_of_dvd hQi hd).eq_of_normalized (normalize_normalized_factor P hP)
    (normalize_normalized_factor Q hQ)

/-- **The partial-fraction identity.** -/
lemma pf_identity (s G : ℚ[X]) (hs0 : s ≠ 0) (hsq : Squarefree s) (n : ℚ[X] → ℤ)
    (hdeg : G.degree < s.degree)
    (hcong : ∀ P ∈ normalizedFactors s, P ∣ G - C (n P : ℚ) * derivative s) :
    G = ∑ P ∈ (normalizedFactors s).toFinset, C (n P : ℚ) * derivative P * (s / P) := by
  classical
  set F := (normalizedFactors s).toFinset with hF
  have hmem : ∀ P ∈ F, P ∈ normalizedFactors s := fun P hP ↦ Multiset.mem_toFinset.mp hP
  have hdvd : ∀ P ∈ F, P ∣ s := fun P hP ↦ dvd_of_mem_normalizedFactors (hmem P hP)
  have hirr : ∀ P ∈ F, Irreducible P := fun P hP ↦ irreducible_of_normalized_factor P (hmem P hP)
  have hsP : ∀ P ∈ F, P * (s / P) = s := fun P hP ↦ EuclideanDomain.mul_div_cancel' (hirr P hP).ne_zero
    (hdvd P hP)
  set T := ∑ P ∈ F, C (n P : ℚ) * derivative P * (s / P) with hT
  -- the degree of `T`
  have hTdeg : T.degree < s.degree := by
    have hs : (⊥ : WithBot ℕ) < s.degree := by
      rw [degree_eq_natDegree hs0]; exact WithBot.bot_lt_coe _
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff hs).mpr fun P hP ↦ ?_)
    have hP0 := (hirr P hP).ne_zero
    have hq0 : s / P ≠ 0 := fun h0 ↦ hs0 (by rw [← hsP P hP, h0, mul_zero])
    have hPd : P.natDegree ≠ 0 := fun h0 ↦ (hirr P hP).not_isUnit
      (isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hP0, h0]; rfl))
    calc (C (n P : ℚ) * derivative P * (s / P)).degree
        ≤ (derivative P * (s / P)).degree := by
          rw [mul_assoc, ← smul_eq_C_mul]; exact degree_smul_le _ _
      _ ≤ (derivative P).degree + (s / P).degree := degree_mul_le _ _
      _ < P.degree + (s / P).degree := by
          rw [degree_eq_natDegree hq0]
          exact WithBot.add_lt_add_right (WithBot.coe_ne_bot) (degree_derivative_lt hP0)
      _ = s.degree := by rw [← degree_mul, hsP P hP]
  -- every factor divides `G - T`
  have hY : ∀ P ∈ F, P ∣ G - T := by
    intro P hP
    have hsplit : T = C (n P : ℚ) * derivative P * (s / P) +
        ∑ Q ∈ F.erase P, C (n Q : ℚ) * derivative Q * (s / Q) := by
      rw [hT]; exact (Finset.add_sum_erase F _ hP).symm
    have hrest : P ∣ ∑ Q ∈ F.erase P, C (n Q : ℚ) * derivative Q * (s / Q) := by
      refine Finset.dvd_sum fun Q hQ ↦ dvd_mul_of_dvd_right ?_ _
      have hQP : Q ≠ P := Finset.ne_of_mem_erase hQ
      have hQF : Q ∈ F := Finset.mem_of_mem_erase hQ
      have hcop := isCoprime_of_mem_normalizedFactors (hmem P hP) (hmem Q hQF) hQP.symm
      have : P ∣ Q * (s / Q) := by rw [hsP Q hQF]; exact hdvd P hP
      exact hcop.dvd_of_dvd_mul_left this
    have hs' : derivative s = derivative P * (s / P) + P * derivative (s / P) := by
      conv_lhs => rw [← hsP P hP]
      rw [derivative_mul]
    have e : G - T = (G - C (n P : ℚ) * derivative s) +
        P * (C (n P : ℚ) * derivative (s / P)) -
          ∑ Q ∈ F.erase P, C (n Q : ℚ) * derivative Q * (s / Q) := by
      rw [hsplit, hs']; ring
    rw [e]
    exact dvd_sub (dvd_add (hcong P (hmem P hP)) (dvd_mul_right _ _)) hrest
  -- so does `s`
  have hprod : (∏ P ∈ F, P) ∣ G - T :=
    Finset.prod_dvd_of_coprime (fun P hP Q hQ hPQ ↦
      isCoprime_of_mem_normalizedFactors (hmem P hP) (hmem Q hQ) hPQ) hY
  have hnd : (normalizedFactors s).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hs0).mp hsq
  have hFprod : (∏ P ∈ F, P) = (normalizedFactors s).prod := by
    rw [Finset.prod_eq_multiset_prod, hF, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
  have hsd : s ∣ G - T := by
    rw [hFprod] at hprod
    exact (prod_normalizedFactors hs0).symm.dvd.trans hprod
  have h0 : G - T = 0 := by
    by_contra hne
    exact absurd (degree_le_of_dvd hsd hne)
      (not_le.mpr (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hdeg hTdeg)))
  exact sub_eq_zero.mp h0

end PF

section Relation

variable {S K : Type*} [Field S] [CharZero S] [Differential S] [Differential S[X]] [Field K]
variable [CharZero K] [Algebra S[X] K]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

private lemma logDeriv_zpow'' (u : K) (hu : u ≠ 0) (n : ℤ) :
    logDeriv (u ^ n) = n * logDeriv u := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, logDeriv_pow]; simp
  · rw [zpow_neg, zpow_natCast, ← one_div, logDeriv_div _ _ one_ne_zero (pow_ne_zero _ hu),
      logDeriv_one, logDeriv_pow]
    simp

/-- **A failing head certificate gives an explicit relation**: `y = ∏_P P ^ (-n_P)` solves
`y′ + (c η₂ + z η₁) y = 0` with `c ≠ 0`. -/
theorem degenPair_relation (ιQ : ℚ →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (s N₁ N₂ ρ₁ ρ₂ : CPoly ℚ) (hs0 : toPoly s ≠ 0) (hsq : Squarefree (toPoly s))
    (hd₁ : (toPoly N₁).degree < (toPoly s).degree) (hd₂ : (toPoly N₂).degree < (toPoly s).degree)
    (hr₁ : toPoly s ∣ toPoly ρ₁ * derivative (toPoly s) - toPoly N₁)
    (hr₂ : toPoly s ∣ toPoly ρ₂ * derivative (toPoly s) - toPoly N₂)
    (h : Kron.genResCertHead s [ρ₂, ρ₁] = false) :
    ∃ c z : ℤ, c ≠ 0 ∧ ∃ y : K, y ≠ 0 ∧
      y′ + ((c : K) * (φ ((toPoly N₂).map ιQ) / φ ((toPoly s).map ιQ)) +
        (z : K) * (φ ((toPoly N₁).map ιQ) / φ ((toPoly s).map ιQ))) * y = 0 := by
  classical
  obtain ⟨β, hb0, hrel⟩ := Kron.genResCertHead_complete s [ρ₂, ρ₁] hs0 h
  simp only [Kron.lcomb_two] at hrel
  set b0 := β.getD 0 0 with hb0d
  set b1 := β.getD 1 0 with hb1d
  set sp := toPoly s with hsp
  set F := (normalizedFactors sp).toFinset with hF
  have hmem : ∀ P ∈ F, P ∈ normalizedFactors sp := fun P hP ↦ Multiset.mem_toFinset.mp hP
  have hdvd : ∀ P ∈ F, P ∣ sp := fun P hP ↦ dvd_of_mem_normalizedFactors (hmem P hP)
  have hirr : ∀ P ∈ F, Irreducible P := fun P hP ↦ irreducible_of_normalized_factor P (hmem P hP)
  -- the rational constants
  let qf : ℚ[X] → ℚ := fun P ↦
    if hP : Irreducible P ∧ P ∣ sp then Classical.choose (hrel P hP.1 hP.2) else 0
  have hqf : ∀ P ∈ F, P ∣ C b0 * toPoly ρ₂ + C b1 * toPoly ρ₁ - C (qf P) := fun P hP ↦ by
    have hP' : Irreducible P ∧ P ∣ sp := ⟨hirr P hP, hdvd P hP⟩
    simp only [qf, dif_pos hP']
    exact Classical.choose_spec (hrel P hP'.1 hP'.2)
  -- clearing denominators
  set l : ℚ := b1 / b0 with hl
  let r : ℚ[X] → ℚ := fun P ↦ qf P / b0
  set M : ℕ := l.den * ∏ P ∈ F, (r P).den with hM
  have hM0 : M ≠ 0 := Nat.mul_ne_zero l.den_nz (Finset.prod_ne_zero_iff.mpr fun P _ ↦ (r P).den_nz)
  have hint : ∀ x : ℚ, x.den ∣ M → (((x * M).num : ℤ) : ℚ) = x * M := fun x hx ↦ by
    have h1 := Kron.den_mul_of_dvd x M hx
    have := Rat.num_div_den (x * M)
    rwa [h1, Nat.cast_one, div_one] at this
  have hlM := hint l (Dvd.intro _ rfl)
  have hrM : ∀ P ∈ F, (((r P * M).num : ℤ) : ℚ) = r P * M := fun P hP ↦
    hint _ (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hP) _)
  set c : ℤ := (M : ℤ) with hc
  set z : ℤ := (l * M).num with hz
  let n : ℚ[X] → ℤ := fun P ↦ (r P * M).num
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast hM0
  -- the combined numerator and its congruences
  set G : ℚ[X] := C (c : ℚ) * toPoly N₂ + C (z : ℚ) * toPoly N₁ with hG
  have hGdeg : G.degree < sp.degree := by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) hd₂
    · exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) hd₁
  have hcong : ∀ P ∈ normalizedFactors sp, P ∣ G - C (n P : ℚ) * derivative sp := by
    intro P hP
    have hPF : P ∈ F := Multiset.mem_toFinset.mpr hP
    have hPs := hdvd P hPF
    have e : G - C (n P : ℚ) * derivative sp =
        C (c : ℚ) * (toPoly N₂ - toPoly ρ₂ * derivative sp) +
          C (z : ℚ) * (toPoly N₁ - toPoly ρ₁ * derivative sp) +
          C ((M : ℚ) / b0) * (C b0 * toPoly ρ₂ + C b1 * toPoly ρ₁ - C (qf P)) * derivative sp := by
      have hn : ((n P : ℤ) : ℚ) = qf P / b0 * M := hrM P hPF
      have hzq : ((z : ℤ) : ℚ) = b1 / b0 * M := hlM
      have hcq : ((c : ℤ) : ℚ) = M := by rw [hc]; push_cast; rfl
      have hinv : C b0⁻¹ * C b0 = (1 : ℚ[X]) := by rw [← C_mul, inv_mul_cancel₀ hb0, C_1]
      rw [hG, hn, hzq, hcq]
      simp only [div_eq_mul_inv, C_mul]
      linear_combination (-(C (M : ℚ) * derivative sp * toPoly ρ₂)) * hinv
    rw [e]
    refine dvd_add (dvd_add (dvd_mul_of_dvd_right ?_ _) (dvd_mul_of_dvd_right ?_ _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hqf P hPF) _) _)
    · have := hPs.trans hr₂
      rw [← dvd_neg, neg_sub] at this
      exact this
    · have := hPs.trans hr₁
      rw [← dvd_neg, neg_sub] at this
      exact this
  have hpf := pf_identity sp G hs0 hsq n hGdeg hcong
  -- the solution
  have hφ0 : ∀ Q : ℚ[X], Q ≠ 0 → φ (Q.map ιQ) ≠ 0 := fun Q hQ ↦
    (map_ne_zero_iff _ (IsFractionRing.injective S[X] K)).mpr
      ((Polynomial.map_ne_zero_iff ιQ.injective).mpr hQ)
  have hderφ : ∀ Q : ℚ[X], (φ (Q.map ιQ))′ = φ ((derivative Q).map ιQ) := fun Q ↦ by
    rw [deriv_algebraMap, hD, derivative_map]
  set w : K := ∏ P ∈ F, (φ (P.map ιQ)) ^ (n P) with hw
  have hw0 : w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P hP ↦
    zpow_ne_zero _ (hφ0 P (hirr P hP).ne_zero)
  have hs0K : φ (sp.map ιQ) ≠ 0 := hφ0 sp hs0
  have hlog : logDeriv w = φ (G.map ιQ) / φ (sp.map ιQ) := by
    rw [hw, logDeriv_prod _ _ _ fun P hP ↦ zpow_ne_zero _ (hφ0 P (hirr P hP).ne_zero)]
    have hterm : ∀ P ∈ F, logDeriv ((φ (P.map ιQ)) ^ (n P)) =
        φ ((C (n P : ℚ) * derivative P * (sp / P)).map ιQ) / φ (sp.map ιQ) := by
      intro P hP
      have hP0 := hφ0 P (hirr P hP).ne_zero
      rw [logDeriv_zpow'' _ hP0, logDeriv, hderφ]
      have hsP : sp = P * (sp / P) := (EuclideanDomain.mul_div_cancel' (hirr P hP).ne_zero
        (hdvd P hP)).symm
      have hq0 : sp / P ≠ 0 := fun h0 ↦ hs0 (by rw [hsP, h0, mul_zero])
      have hq0K := hφ0 _ hq0
      have hsK : φ (sp.map ιQ) = φ (P.map ιQ) * φ ((sp / P).map ιQ) := by
        rw [← map_mul, ← Polynomial.map_mul, ← hsP]
      rw [hsK]
      simp only [Polynomial.map_mul, map_C, map_mul, eq_intCast, map_intCast,
        Polynomial.map_intCast]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← map_sum, ← Polynomial.map_sum, ← hpf]
  refine ⟨c, z, hc0, w⁻¹, inv_ne_zero hw0, ?_⟩
  have hGK : φ (G.map ιQ) = (c : K) * φ ((toPoly N₂).map ιQ) + (z : K) * φ ((toPoly N₁).map ιQ) := by
    rw [hG]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_add, map_mul, eq_intCast,
      map_intCast, Polynomial.map_intCast]
  rw [Derivation.leibniz_inv, smul_eq_mul]
  rw [logDeriv, hGK] at hlog
  field_simp
  field_simp at hlog
  linear_combination (-1 : K) * hlog

end Relation

end CPoly
