import RischTragerBronstein.Computable.HermiteExpF0
import RischTragerBronstein.Computable.Prim2BaseFull

/-!
# Two exponentials, level `0`: every element of `R(x)(exp a₁)` is decided by `integrateExp`

Viewed in `K = R(x)(t₁)(t₂)` (`t₁ = exp a₁`, `t₂ = exp a` independent), an element of `R(x)(t₁)` has
an elementary integral iff the height-two integrator `Tower.integrateExp a₁` says so.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- The Laurent part `Λ / t₁^k` as a sum over coefficient codes. -/
theorem valP_div_pow_eq (x₀ t₁ : F₀) (ht₁0 : t₁ ≠ 0) (Λ : GPoly (GFrac R)) (k : ℕ) :
    Tower.valP x₀ t₁ Λ / t₁ ^ k =
      aeval x₀ (toPoly (Tower.polyA Λ k)) / aeval x₀ (toPoly (Tower.polyD Λ k)) +
        ∑ j ∈ (Finset.range (Λ.length + k + 1)).erase k,
          aeval x₀ (toPoly (Tower.polyA Λ j)) / aeval x₀ (toPoly (Tower.polyD Λ j)) * t₁ ^ j /
            t₁ ^ k := by
  have htk : t₁ ^ k ≠ 0 := pow_ne_zero _ ht₁0
  have hzero : ∀ j, Λ.length ≤ j →
      aeval x₀ (toPoly (Tower.polyA Λ j)) / aeval x₀ (toPoly (Tower.polyD Λ j)) = 0 := fun j hj ↦ by
    unfold Tower.polyA Tower.polyD Tower.normFrac
    rw [List.getD_eq_default _ _ hj]
    simp [toPoly]
  have hsum : Tower.valP x₀ t₁ Λ = ∑ j ∈ Finset.range (Λ.length + k + 1),
      aeval x₀ (toPoly (Tower.polyA Λ j)) / aeval x₀ (toPoly (Tower.polyD Λ j)) * t₁ ^ j := by
    rw [valP_eq_sum_poly]
    refine Finset.sum_subset (Finset.range_subset.mpr fun x hx ↦ Finset.mem_range.mpr (by omega))
      fun j _ hj ↦ ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [hzero j (by omega), zero_mul]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : k < Λ.length + k + 1)),
    add_div, Finset.sum_div, mul_div_assoc, div_self htk, mul_one]

/-- **Level `0` under two exponentials: decided by `integrateExp`.** -/
theorem expExpBaseGen_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (a : CPoly R) (ha : trim (deriv a) ≠ []) (hind : Tower.expIndep a₁ a = true)
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (derivative (toPoly a))) * t)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.isZero (Tower.ops₁g R) Gd = false) :
    HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ (Gn, Gd))) ↔
      Tower.integrateExp a₁ Gn Gd = true := by
  classical
  obtain ⟨hid, hsqc, hXs, hlen, hBn⟩ := Tower.hermite_valG_exp_F₀ hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ Gn Gd
    hGd
  obtain ⟨hadd, hmul, hmono, hne0, hsq0⟩ := Tower.valP_ring_exp hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁
  simp only [Tower.integrateExp]
  generalize GPoly.expSplit (Tower.ops₁g R) Gn Gd = sp at hid hsqc hXs hlen hBn ⊢
  generalize GPoly.hermite (Tower.ops₁g R) (Tower.expW a₁) sp.1 sp.2.2.2 = h
    at hid hsqc hXs hlen hBn ⊢
  generalize GPoly.divMod (Tower.ops₁g R) h.b h.s = qr at hid hlen hBn ⊢
  set k := sp.2.2.1 with hk
  set Λ := GPoly.add (Tower.ops₁g R)
    (GPoly.mul (Tower.ops₁g R) qr.1 (GPoly.monomial (Tower.ops₁g R) k (Tower.ops₁g R).one))
    sp.2.1 with hΛ
  set N := Λ.length + k + 1 with hN
  rw [hid, map_add, ← deriv_algebraMap, hasElementaryIntegral_deriv_add_iff, map_add]
  have hS0 : Tower.valP x₀ t₁ h.s ≠ 0 := hsq0 _ hsqc
  have htk : t₁ ^ k ≠ 0 := pow_ne_zero _ ht₁0
  set Lp : K := algebraMap F₀ K (Tower.valP x₀ t₁ Λ / t₁ ^ k) with hLp
  set Rp : K := algebraMap F₀ K (Tower.valP x₀ t₁ qr.2 / Tower.valP x₀ t₁ h.s) with hRp
  have hBnval : Tower.valP x₀ t₁ (GPoly.add (Tower.ops₁g R) (GPoly.mul (Tower.ops₁g R) Λ h.s)
      (GPoly.mul (Tower.ops₁g R) qr.2 (GPoly.monomial (Tower.ops₁g R) k (Tower.ops₁g R).one))) /
      (Tower.valP x₀ t₁ h.s * t₁ ^ k) =
      Tower.valP x₀ t₁ Λ / t₁ ^ k + Tower.valP x₀ t₁ qr.2 / Tower.valP x₀ t₁ h.s := by
    rw [hadd, hmul, hmul, hmono]
    field_simp
  have hLform : Lp = algebraMap F₀ K (aeval x₀ (toPoly (Tower.polyA Λ k)) /
      aeval x₀ (toPoly (Tower.polyD Λ k)) + ∑ j ∈ (Finset.range N).erase k,
        aeval x₀ (toPoly (Tower.polyA Λ j)) / aeval x₀ (toPoly (Tower.polyD Λ j)) * t₁ ^ j /
          t₁ ^ k) := by
    rw [hLp, valP_div_pow_eq x₀ t₁ ht₁0 Λ k]
  have hIn : GPoly.residueCheck (Tower.ops₁g R) (Tower.expW a₁) qr.2 h.s = true →
      HasElementaryIntegralIn Rp := fun hres ↦
    hasElementaryIntegralIn_expExpBaseResidue (K := K) hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ qr.2 h.s hsqc
      hXs hlen hres
  -- the Laurent part, positively
  have hRK : ∀ r : R, (algebraMap R K r)′ = 0 := fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R F₀ K, deriv_algebraMap, hR, map_zero]
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R K := ⟨fun r ↦ by rw [hRK, h0, map_zero]⟩
  have haevx : ∀ P : R[X], aeval (algebraMap F₀ K x₀) P = algebraMap F₀ K (aeval x₀ P) :=
    fun P ↦ aeval_algebraMap_apply K x₀ P
  have hx' : (algebraMap F₀ K x₀)′ = 1 := by rw [deriv_algebraMap, hx₀, map_one]
  have ht₁' : (algebraMap F₀ K t₁)′ =
      aeval (algebraMap F₀ K x₀) (derivative (toPoly a₁)) * algebraMap F₀ K t₁ := by
    rw [deriv_algebraMap, ht₁, map_mul, haevx]
  have ht₁K : algebraMap F₀ K t₁ ≠ 0 := (_root_.map_ne_zero _).mpr ht₁0
  constructor
  · intro hf
    have hres : GPoly.residueCheck (Tower.ops₁g R) (Tower.expW a₁) qr.2 h.s = true := by
      by_contra hcon
      rw [Bool.not_eq_true] at hcon
      obtain ⟨E, _, _, _, _, hE, g, hg⟩ := hf
      refine not_elementary_expExpBaseResidue hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ a ha hind t ht0
        hgen ht _ qr.2 h.s k hsqc hXs hBn hcon E hE g ?_
      rw [hBnval, map_add]
      exact hg
    have hL : HasElementaryIntegral Lp := by
      have := hf.sub_in (hIn hres)
      rwa [add_sub_cancel_right] at this
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨hres, fun j hj ↦ ?_⟩
    rw [List.mem_range] at hj
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hjk : j = k
    · exact Or.inl hjk
    right
    by_contra hnone
    rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
    obtain ⟨E, _, _, _, _, hE, g, hg⟩ := hL
    rw [hLform] at hg
    exact not_elementary_expExpBaseLaurent hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ a ha hind t ht0 hgen
      ht N k (Tower.polyA Λ) (Tower.polyD Λ) (Tower.polyA Λ k) (Tower.polyD Λ k)
      (fun j _ ↦ Tower.normFrac_den_ne_zero _) j hj hjk hnone E hE g hg
  · intro hall
    rw [Bool.and_eq_true, List.all_eq_true] at hall
    obtain ⟨hres, hall⟩ := hall
    have hsome : ∀ j < N, j ≠ k →
        (rdeRational (expCoeffZ a₁ ((j : ℤ) - k)) (Tower.polyA Λ j) (Tower.polyD Λ j)).isSome =
          true := fun j hj hjk ↦ by
      have := hall j (List.mem_range.mpr hj)
      rw [Bool.or_eq_true, decide_eq_true_eq] at this
      exact this.resolve_left hjk
    have hYG : ∀ j, ∃ Y G : CPoly R, j < N → j ≠ k →
        rdeRational (expCoeffZ a₁ ((j : ℤ) - k)) (Tower.polyA Λ j) (Tower.polyD Λ j) =
          some (Y, G) := fun j ↦ by
      by_cases hc : j < N ∧ j ≠ k
      · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hsome j hc.1 hc.2)
        exact ⟨p.1, p.2, fun _ _ ↦ hp⟩
      · exact ⟨[], [], fun h1 h2 ↦ absurd ⟨h1, h2⟩ hc⟩
    choose Y G hYG using hYG
    have hL := hasElementaryIntegral_expLaurentRat h0 (algebraMap F₀ K x₀) (algebraMap F₀ K t₁)
      hx' ht₁K a₁ ht₁' N k (Tower.polyA Λ) (Tower.polyD Λ) Y G (Tower.polyA Λ k)
      (Tower.polyD Λ k) (Tower.normFrac_den_ne_zero _) (fun j _ ↦ Tower.normFrac_den_ne_zero _)
      hYG
    have hL' : HasElementaryIntegral Lp := by
      rw [hLform]
      simpa only [map_add, map_sum, map_mul, map_pow, map_div₀, haevx] using hL
    exact hL'.add_in (hIn hres)

end CPoly
