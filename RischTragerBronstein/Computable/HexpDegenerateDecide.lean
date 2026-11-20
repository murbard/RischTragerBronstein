import RischTragerBronstein.Computable.HexpDegenerateComplete
import RischTragerBronstein.Computable.SquarefreePart

/-!
# The degenerate-pair certificate over `ℚ` is exact

Over `R = ℚ` the untrusted preprocessing of `hexpDegen` always succeeds:

* `lcmSq_spec`: `lcmSq s₁ s₂` is a squarefree common multiple of squarefree `s₁`, `s₂`;
* `resPoly_spec`: `resPoly s N` is a residue polynomial, `s ∣ ρ s′ - N`, for squarefree `s`;
* `toRatL_ratQ`: the rational-coefficient conversion succeeds;
* `squarefreeCheck_complete'`: the squarefreeness check accepts squarefree polynomials.

Hence (`hexpDegen_complete`): if `hexpDegen` fails, the simple-pole parts `rᵢ / sᵢ` of `η₁`, `η₂`
satisfy an explicit relation `y′ + (c r₂/s₂ + z r₁/s₁) y = 0` with `c ≠ 0`, `y ≠ 0`. Together with
`hexpDegen_hom`, `hexpDegen` decides exactly the dependence of `η₂` on `η₁` modulo logarithmic
derivatives when both have only simple poles (so that `ηᵢ = rᵢ / sᵢ`).
-/

open Polynomial Differential

namespace CPoly

section Pre

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- **The squarefreeness check is complete.** -/
theorem squarefreeCheck_complete' {s : CPoly R} (hs : Squarefree (toPoly s)) :
    squarefreeCheck s = true := by
  have hsep : (toPoly s).Separable := PerfectField.separable_iff_squarefree.mpr hs
  have hcop : IsCoprime (toPoly s) (toPoly (deriv s)) := by rw [toPoly_deriv]; exact hsep
  obtain ⟨hga, hgb⟩ := egcd_dvd s (deriv s)
  have hunit : IsUnit (toPoly (egcd s (deriv s)).1) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact isUnit_of_dvd_one (huv ▸ dvd_add (Dvd.dvd.mul_left hga u) (Dvd.dvd.mul_left hgb v))
  have hne : trim (egcd s (deriv s)).1 ≠ [] := fun h ↦
    hunit.ne_zero ((trim_eq_nil_iff _).mp h)
  rw [squarefreeCheck, beq_iff_eq, length_trim hne, natDegree_eq_zero_of_isUnit hunit]

lemma isZero_rem_of_dvd {p d : CPoly R} (hd : toPoly d ≠ 0) (h : toPoly d ∣ toPoly p) :
    isZero (divMod p d).2 = true := (isZero_iff _).mpr (divMod_exact p d hd h)

/-- **`resPoly` computes a residue polynomial.** -/
theorem resPoly_spec (s N : CPoly R) (hs : Squarefree (toPoly s)) :
    toPoly s ∣ toPoly (resPoly s N) * derivative (toPoly s) - toPoly N := by
  have hchk := squarefreeCheck_complete' hs
  rw [squarefreeCheck, beq_iff_eq] at hchk
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp hchk
  obtain ⟨hγ0, hg⟩ := trim_singleton hγ
  have hbez := egcd_spec s (deriv s)
  rw [hg, toPoly_deriv] at hbez
  have hlead : lead (trim (egcd s (deriv s)).1) = γ := by rw [hγ]; rfl
  have hsp := divMod_spec (mul N (smul (lead (trim (egcd s (deriv s)).1))⁻¹ (egcd s (deriv s)).2.2)) s
  rw [hlead] at hsp
  unfold resPoly
  simp only [hlead]
  set e := egcd s (deriv s)
  set Q := (divMod (mul N (smul γ⁻¹ e.2.2)) s).1
  set ρ := (divMod (mul N (smul γ⁻¹ e.2.2)) s).2
  rw [toPoly_mul, toPoly_smul] at hsp
  have hinv : C γ⁻¹ * C γ = (1 : R[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  refine ⟨-(toPoly N * C γ⁻¹ * toPoly e.2.1) - toPoly Q * derivative (toPoly s), ?_⟩
  have hρ : toPoly ρ = toPoly N * (C γ⁻¹ * toPoly e.2.2) - toPoly Q * toPoly s := by
    rw [hsp]; ring
  rw [hρ]
  linear_combination (toPoly N * C γ⁻¹) * hbez + toPoly N * hinv

/-- **`lcmSq` is a squarefree common multiple.** -/
theorem lcmSq_spec (s₁ s₂ : CPoly R) (h₁ : Squarefree (toPoly s₁)) (h₂ : Squarefree (toPoly s₂)) :
    toPoly s₁ ∣ toPoly (lcmSq s₁ s₂) ∧ toPoly s₂ ∣ toPoly (lcmSq s₁ s₂) ∧
      Squarefree (toPoly (lcmSq s₁ s₂)) := by
  set g := (egcd s₁ s₂).1 with hgd
  obtain ⟨hg1, hg2⟩ := egcd_dvd s₁ s₂
  have hs20 : toPoly s₂ ≠ 0 := h₂.ne_zero
  have hg0 : toPoly g ≠ 0 := fun h0 ↦ hs20 (zero_dvd_iff.mp (h0 ▸ hg2))
  set q := (divMod s₂ g).1 with hq
  have hs2 : toPoly s₂ = toPoly q * toPoly g := by
    rw [divMod_spec s₂ g, divMod_exact s₂ g hg0 hg2, add_zero]
  obtain ⟨a, ha⟩ := hg1
  have hl : toPoly (lcmSq s₁ s₂) = toPoly s₁ * toPoly q := by
    rw [lcmSq, toPoly_mul]
  refine ⟨⟨toPoly q, hl⟩, ⟨a, by rw [hl, ha, hs2]; ring⟩, ?_⟩
  rw [hl]
  have hq2 : toPoly q ∣ toPoly s₂ := ⟨toPoly g, hs2⟩
  refine squarefree_mul_iff.mpr ⟨fun p hp1 hpq ↦ ?_, h₁, h₂.squarefree_of_dvd hq2⟩
  -- a common factor of `s₁` and `q` divides `g`, so its square divides `s₂`
  have hpg : p ∣ toPoly g := dvd_egcd s₁ s₂ hp1 (hpq.trans hq2)
  have hpp : p * p ∣ toPoly s₂ := by rw [hs2]; exact mul_dvd_mul hpq hpg
  exact h₂ p hpp

end Pre

/-- **Over `ℚ` the conversion to rational coefficients succeeds.** -/
theorem toRatL_ratQ : ∀ p : CPoly ℚ, ∃ p', toRatL p = some p' ∧ toPoly p' = toPoly p
  | [] => ⟨[], rfl, rfl⟩
  | r :: p => by
    obtain ⟨p', hp', hpp⟩ := toRatL_ratQ p
    have hmem : r ∈ HasRatRoots.ratRoots ([-r, 1] : CPoly ℚ) :=
      HasRatRoots.ratRoots_spec _ r (by
        intro h0
        have := congrArg (fun P : ℚ[X] ↦ P.coeff 1) h0
        simp at this) (by simp [Rat.cast_id])
    obtain ⟨q, hq⟩ : ∃ q, (HasRatRoots.ratRoots ([-r, 1] : CPoly ℚ)).find?
        (fun q : ℚ ↦ ((Rat.cast q : ℚ) == r)) = some q := by
      rcases hf : (HasRatRoots.ratRoots ([-r, 1] : CPoly ℚ)).find?
        (fun q : ℚ ↦ ((Rat.cast q : ℚ) == r)) with _ | q
      · rw [List.find?_eq_none] at hf
        exact absurd (by simp) (hf r hmem)
      · exact ⟨q, rfl⟩
    have hqr : q = r := by
      have := List.find?_some hq
      simpa [Rat.cast_id] using this
    refine ⟨q :: p', ?_, ?_⟩
    · simp only [toRatL, List.mapM_cons] at hp' ⊢
      rw [hq, hp']
      rfl
    · rw [toPoly_cons, toPoly_cons, hpp, hqr]

section Decide

variable {S K : Type*} [Field S] [CharZero S] [Differential S] [Differential S[X]] [Field K]
variable [CharZero K] [Algebra S[X] K] [Differential K[X]]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

lemma integrateRational_facts (Hn Hd : CPoly ℚ) (hHd0 : toPoly Hd ≠ 0) :
    Squarefree (toPoly (integrateRational Hn Hd).s) ∧
      (toPoly (integrateRational Hn Hd).r).degree < (toPoly (integrateRational Hn Hd).s).degree := by
  have hchk := rationalCheck_integrateRational Hn Hd hHd0
  rw [rationalCheck, Bool.and_eq_true, decide_eq_true_eq, hermiteCheck_iff] at hchk
  obtain ⟨⟨-, -, -, -, hsqc⟩, hlen⟩ := hchk
  exact ⟨squarefreeCheck_sound hsqc, degree_lt_of_trim_length_lt hlen⟩

/-- **The degenerate-pair certificate is complete over `ℚ`**: if `hexpDegen` fails, the simple-pole
parts of `η₁`, `η₂` are dependent modulo logarithmic derivatives, with `c ≠ 0`. -/
theorem hexpDegen_complete (ι : ℚ →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (Hn₁ Hd₁ Hn₂ Hd₂ : CPoly ℚ) (hHd10 : toPoly Hd₁ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (h : hexpDegen Hn₁ Hd₁ Hn₂ Hd₂ = false) :
    ∃ c z : ℤ, c ≠ 0 ∧ ∃ y : K, y ≠ 0 ∧
      y′ + ((c : K) * (φ ((toPoly (integrateRational Hn₂ Hd₂).r).map ι) /
          φ ((toPoly (integrateRational Hn₂ Hd₂).s).map ι)) +
        (z : K) * (φ ((toPoly (integrateRational Hn₁ Hd₁).r).map ι) /
          φ ((toPoly (integrateRational Hn₁ Hd₁).s).map ι))) * y = 0 := by
  classical
  obtain ⟨hsq₁, hdg₁⟩ := integrateRational_facts Hn₁ Hd₁ hHd10
  obtain ⟨hsq₂, hdg₂⟩ := integrateRational_facts Hn₂ Hd₂ hHd20
  set I₁ := integrateRational Hn₁ Hd₁ with hI₁
  set I₂ := integrateRational Hn₂ Hd₂ with hI₂
  obtain ⟨hd₁, hd₂, hsq⟩ := lcmSq_spec I₁.s I₂.s hsq₁ hsq₂
  unfold hexpDegen at h
  dsimp only at h
  rw [← hI₁, ← hI₂] at h
  generalize hs : lcmSq I₁.s I₂.s = s at h hd₁ hd₂ hsq
  have hs0 : toPoly s ≠ 0 := hsq.ne_zero
  have hs10 : toPoly I₁.s ≠ 0 := hsq₁.ne_zero
  have hs20 : toPoly I₂.s ≠ 0 := hsq₂.ne_zero
  -- the quotients
  set q₁ := (divMod s I₁.s).1 with hq₁
  set q₂ := (divMod s I₂.s).1 with hq₂
  have hsq₁' : toPoly s = toPoly q₁ * toPoly I₁.s := by
    rw [divMod_spec s I₁.s, divMod_exact s I₁.s hs10 hd₁, add_zero]
  have hsq₂' : toPoly s = toPoly q₂ * toPoly I₂.s := by
    rw [divMod_spec s I₂.s, divMod_exact s I₂.s hs20 hd₂, add_zero]
  have hq₁0 : toPoly q₁ ≠ 0 := fun h0 ↦ hs0 (by rw [hsq₁', h0, zero_mul])
  have hq₂0 : toPoly q₂ ≠ 0 := fun h0 ↦ hs0 (by rw [hsq₂', h0, zero_mul])
  generalize hN₁ : mul I₁.r q₁ = N₁ at h
  generalize hN₂ : mul I₂.r q₂ = N₂ at h
  have hNd : ∀ {r q sᵢ N : CPoly ℚ}, mul r q = N → toPoly s = toPoly q * toPoly sᵢ →
      toPoly q ≠ 0 → (toPoly r).degree < (toPoly sᵢ).degree →
      (toPoly N).degree < (toPoly s).degree := by
    intro r q sᵢ N hN hsqi hq0 hdg
    rw [← hN, toPoly_mul, hsqi, degree_mul, degree_mul,
      add_comm (toPoly q).degree (toPoly sᵢ).degree]
    exact WithBot.add_lt_add_right (by rw [degree_eq_natDegree hq0]; exact WithBot.coe_ne_bot) hdg
  have hNd₁ := hNd hN₁ hsq₁' hq₁0 hdg₁
  have hNd₂ := hNd hN₂ hsq₂' hq₂0 hdg₂
  have hr₁ := resPoly_spec s N₁ hsq
  have hr₂ := resPoly_spec s N₂ hsq
  generalize hρ₁ : resPoly s N₁ = ρ₁ at h hr₁
  generalize hρ₂ : resPoly s N₂ = ρ₂ at h hr₂
  have hchk : ∀ ρ N : CPoly ℚ, toPoly s ∣ toPoly ρ * derivative (toPoly s) - toPoly N →
      isZero (divMod (sub (mul ρ (deriv s)) N) s).2 = true := fun ρ N hρ ↦
    isZero_rem_of_dvd hs0 (by rw [toPoly_sub, toPoly_mul, toPoly_deriv]; exact hρ)
  rw [isZero_rem_of_dvd hs10 hd₁, isZero_rem_of_dvd hs20 hd₂, hchk ρ₁ N₁ hr₁, hchk ρ₂ N₂ hr₂]
    at h
  obtain ⟨sQ, hsQ, hsQp⟩ := toRatL_ratQ s
  obtain ⟨p₁, hp₁, hp₁p⟩ := toRatL_ratQ ρ₁
  obtain ⟨p₂, hp₂, hp₂p⟩ := toRatL_ratQ ρ₂
  simp only [hsQ, hp₁, hp₂, Bool.true_and, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
  have hsqQ : Squarefree (toPoly sQ) := by rw [hsQp]; exact hsq
  have hsQ0 : toPoly sQ ≠ 0 := hsqQ.ne_zero
  have hhead : Kron.genResCertHead sQ [p₂, p₁] = false := by
    rcases h.2 with (h1 | h1) | h1
    · exfalso
      have : isZero sQ = false := by
        cases hz : isZero sQ
        · rfl
        · exact absurd ((isZero_iff _).mp hz) hsQ0
      simp [this] at h1
    · rw [squarefreeCheck_complete' hsqQ] at h1
      exact absurd h1 Bool.noConfusion
    · exact h1
  obtain ⟨c, z, hc0, y, hy0, hy⟩ := degenPair_relation (K := K) ι hD sQ N₁ N₂ p₁ p₂ hsQ0 hsqQ
    (by rw [hsQp]; exact hNd₁) (by rw [hsQp]; exact hNd₂)
    (by rw [hsQp, hp₁p]; exact hr₁) (by rw [hsQp, hp₂p]; exact hr₂) hhead
  refine ⟨c, z, hc0, y, hy0, ?_⟩
  -- `Nᵢ / s = rᵢ / sᵢ`
  have hfrac : ∀ {r q sᵢ N : CPoly ℚ}, mul r q = N → toPoly s = toPoly q * toPoly sᵢ →
      toPoly q ≠ 0 → toPoly sᵢ ≠ 0 →
      φ ((toPoly N).map ι) / φ ((toPoly sQ).map ι) = φ ((toPoly r).map ι) / φ ((toPoly sᵢ).map ι) := by
    intro r q sᵢ N hN hsqi hq0 hsi0
    have hinj := IsFractionRing.injective S[X] K
    have hφ : ∀ P : ℚ[X], P ≠ 0 → φ (P.map ι) ≠ 0 := fun P hP ↦
      (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hP)
    have hq := hφ _ hq0
    have hsi := hφ _ hsi0
    rw [hsQp, hsqi, ← hN, toPoly_mul]
    simp only [Polynomial.map_mul, map_mul]
    field_simp
  rw [hfrac hN₁ hsq₁' hq₁0 hs10, hfrac hN₂ hsq₂' hq₂0 hs20] at hy
  exact hy

end Decide

end CPoly
