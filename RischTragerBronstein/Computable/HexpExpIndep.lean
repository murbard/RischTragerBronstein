import RischTragerBronstein.Computable.RDERationalW
import RischTragerBronstein.Computable.HyperexpWCert
import RischTragerBronstein.Computable.RDEPrimComplete
import RischTragerBronstein.Computable.ExpExpBasics

/-!
# A general hyperexponential and an exponential: the independence certificate

`t₁′ = η t₁` with `η = Hn / Hd ∈ R(x)` arbitrary (certified monomial), `t₂ = exp a` with
`a ∈ R[x]`. `hexpExpIndep Hn Hd μ a` certifies that `t₁^m t₂^n ∉ R(x)` for `(m, n) ≠ 0`:
`a′ ≠ 0`, and either the proper part of `η` is not a rational multiple of a logarithmic derivative
(`hexpProperCert`: a repeated factor of `Hd`, or a non-rational residue), or `a′` is not an
`R`-multiple of the polynomial part of `η`.

The consequence used by the Risch differential equation over `R(x)(t₁)` (`RDEHexp.lean`):
`y′ + (k a′ + z η) y = 0` has only the zero solution in `S(x)`, for every `k ∈ R ∖ 0`, every
integer `z` and every constant extension `S ⊇ R` (`hexp_hom_of_polyPart`, `hexpExpIndep_hom`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasRatRoots R]

/-- The polynomial part of `Gn / Gd`. -/
def polyPart (Gn Gd : CPoly R) : CPoly R := (divMod Gn Gd).1

/-- The proper part of `Gn / Gd` is not a rational multiple of a logarithmic derivative: `Gd` has
a repeated factor, or a residue at a simple pole is not rational. -/
def hexpProperCert (Gn Gd μ : CPoly R) : Bool :=
  !squarefreeCheck Gd ||
    !isZero (divMod (ratShiftProd (residuePolyW Gn Gd) (HasRatRoots.ratRoots μ)) (simplePart Gd)).2

/-- **The independence certificate** for `t₁′ = (Hn / Hd) t₁` and `t₂ = exp a`. -/
def hexpExpIndep (Hn Hd μ a : CPoly R) : Bool :=
  !isZero (deriv a) &&
    (hexpProperCert Hn Hd μ || (linSolve [polyPart Hn Hd] (deriv a)).isNone)

end Defs

section Spec

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [HasRatRoots R]

/-- The residue polynomial of `(g Gd + Gn) / Gd` is `r` modulo `S`. -/
lemma residuePolyW_add_mul (g Gn Gd : CPoly R) (hGd0 : toPoly Gd ≠ 0) :
    toPoly (simplePart Gd) ∣
      toPoly (residuePolyW (add (mul g Gd) Gn) Gd) - toPoly (residuePolyW Gn Gd) := by
  obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := simplePart_data Gd hGd0
  obtain ⟨hS0, hSd, hcop, -, -, -⟩ := simplePart_props hGd0 E1 E2 E3 E4 E5 E6
  obtain ⟨t, ht⟩ := residuePolyW_bezout Gn Gd hS0 hcop.symm
  obtain ⟨t', ht'⟩ := residuePolyW_bezout (add (mul g Gd) Gn) Gd hS0 hcop.symm
  rw [toPoly_add, toPoly_mul] at ht'
  obtain ⟨G', hG'⟩ := hSd
  refine hcop.dvd_of_dvd_mul_right ⟨toPoly g * G' + t - t', ?_⟩
  linear_combination ht' - ht + toPoly g * hG'

/-- `S ∣ r' - r` implies `S ∣ μ(r') - μ(r)`. -/
lemma dvd_comp_sub_comp {S r r' μ : R[X]} (h : S ∣ r' - r) : S ∣ μ.comp r' - μ.comp r := by
  have := sub_dvd_eval_sub r' r (μ.map C)
  rw [eval_map, eval_map] at this
  exact h.trans this

/-- Euclidean division is unique. -/
lemma div_unique_of_degree_lt {q q' d r : R[X]} (h : q * d + r = q' * d)
    (hr : degree r < degree d) : q = q' := by
  by_contra hne
  have hqq : q - q' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (q - q') * d = -r := by linear_combination h
  have h2 : degree ((q - q') * d) = degree (q - q') + degree d := degree_mul
  rw [h1, degree_neg] at h2
  have h3 : degree d ≤ degree (q - q') + degree d := by
    rw [← h2, h2]; exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hqq)
  exact absurd (lt_of_lt_of_le hr h3) (by rw [← h2]; exact lt_irrefl _)

variable {S K : Type*} [Field S] [CharZero S] [Differential S] [Differential S[X]] [Field K]
variable [CharZero K] [Algebra S[X] K] [Differential K[X]]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

/-- A non-rational residue: the third alternative of `rde_homogeneous_W`, over `S`. -/
lemma nonrational_residue_alt (ι : R →+* S) {Gn Gd μ : CPoly R} (hGd0 : toPoly Gd ≠ 0)
    (hμ0 : toPoly μ ≠ 0)
    (hres : isZero (divMod (ratShiftProd (residuePolyW Gn Gd) (HasRatRoots.ratRoots μ))
      (simplePart Gd)).2 = false) :
    ∃ p : S[X], Irreducible p ∧ p ∣ (toPoly (simplePart Gd)).map ι ∧
      ∀ q : ℚ, ((toPoly μ).map ι).eval (q : S) = 0 →
        ¬p ∣ (toPoly (residuePolyW Gn Gd)).map ι - C (q : S) := by
  have hιinj : Function.Injective ι := ι.injective
  obtain ⟨⟨hS0, -⟩, -, -, -, -, -, hsqS⟩ := simplePart_props_map ι Gd hGd0
  generalize hP : ratShiftProd (residuePolyW Gn Gd) (HasRatRoots.ratRoots μ) = P at hres
  have hPpoly : toPoly P = ((HasRatRoots.ratRoots μ).map fun (q : ℚ) ↦
      toPoly (residuePolyW Gn Gd) - C ((q : ℚ) : R)).prod := by
    rw [← hP, toPoly_ratShiftProd]
  generalize hSp : simplePart Gd = Sp at hS0 hsqS hres ⊢
  generalize hr : residuePolyW Gn Gd = r at hPpoly ⊢
  obtain ⟨Qd, Rm, hdm⟩ : ∃ Qd Rm, divMod P Sp = (Qd, Rm) := ⟨_, _, rfl⟩
  have hspec := divMod_spec P Sp
  have hlt := divMod_degree_lt P Sp hS0
  rw [hdm] at hspec hlt hres
  have hrem : toPoly Rm ≠ 0 := fun h0 ↦ by
    have := (isZero_iff _).mpr h0
    simp [this] at hres
  have hndvd : ¬(toPoly Sp).map ι ∣ (toPoly P).map ι := by
    intro hdvd
    have hremS : (toPoly Sp).map ι ∣ (toPoly Rm).map ι := by
      have : (toPoly Rm).map ι = (toPoly P).map ι - (toPoly Qd).map ι * (toPoly Sp).map ι := by
        rw [← Polynomial.map_mul, ← Polynomial.map_sub]
        exact congrArg (Polynomial.map ι) (by rw [hspec]; ring)
      rw [this]
      exact dvd_sub hdvd (dvd_mul_left _ _)
    have h0 := eq_zero_of_dvd_of_degree_lt hremS (by rw [degree_map, degree_map]; exact hlt)
    exact hrem ((Polynomial.map_eq_zero_iff hιinj).mp h0)
  by_contra hall
  push Not at hall
  refine hndvd (dvd_of_squarefree_of_irreducible_dvd hsqS fun p hp hpS ↦ ?_)
  obtain ⟨q', hq', hpq'⟩ := hall p hp hpS
  rw [hPpoly, Polynomial.map_list_prod, List.map_map]
  have hqR : (toPoly μ).eval ((q' : ℚ) : R) = 0 := by
    rw [← map_ratCast ι, eval_map, eval₂_at_apply] at hq'
    exact hιinj (by rw [hq', map_zero])
  have hmem := HasRatRoots.ratRoots_spec μ q' hμ0 hqR
  refine hpq'.trans (List.dvd_prod ?_)
  refine List.mem_map.mpr ⟨q', hmem, ?_⟩
  simp only [Function.comp_apply, Polynomial.map_sub, map_C, map_ratCast]

/-- **The homogeneous equation `y′ + (g + z η) y = 0` has only the zero solution** in `S(x)`,
for `g ∈ R[x] ∖ 0` and every integer `z`, when either the proper part of `η` is not a rational
multiple of a logarithmic derivative or `g + z · polyPart η ≠ 0`. -/
theorem hexp_hom_of_polyPart (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn Hd μ g : CPoly R} (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : hyperexpMonomialCheck Hn Hd μ = true)
    (hg0 : toPoly g ≠ 0) (z : ℤ)
    (hg : hexpProperCert Hn Hd μ = true ∨ toPoly (add g (smul (z : R) (polyPart Hn Hd))) ≠ 0)
    (y : K) (h : y′ + (φ ((toPoly g).map ι) +
      (z : K) * (φ ((toPoly Hn).map ι) / φ ((toPoly Hd).map ι))) * y = 0) : y = 0 := by
  have hιinj : Function.Injective ι := ι.injective
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  by_cases hz : z = 0
  · subst hz
    simp only [Int.cast_zero, zero_mul, add_zero] at h
    exact Tower.rde_unique_K₁ ι hD g hg0 y 0 0 h (by simp)
  -- `z ≠ 0`: the coefficient is `-z · Gn' / Hd` with `Gn' = z⁻¹ g Hd + Hn`
  have hzR : (z : R) ≠ 0 := Int.cast_ne_zero.mpr hz
  have hzS : (z : S) ≠ 0 := Int.cast_ne_zero.mpr hz
  obtain ⟨Gn', hGn'⟩ : ∃ G : CPoly R, G = add (mul (smul ((z : R)⁻¹) g) Hd) Hn := ⟨_, rfl⟩
  have hGn'poly : toPoly Gn' = C ((z : R)⁻¹) * toPoly g * toPoly Hd + toPoly Hn := by
    rw [hGn', toPoly_add, toPoly_mul, toPoly_smul]
  have hcop' : IsCoprime (toPoly Gn') (toPoly Hd) := by
    rw [hGn'poly, add_comm]; exact hcop.add_mul_right_left _
  -- `Gn' ≠ 0` and the certificate for `Gn' / Hd`
  obtain ⟨⟨hS0, hcopR⟩, hS0', hSd', hcop'', hScop', hS', hsqS⟩ :=
    simplePart_props_map ι Hd hHd0
  simp only [hyperexpMonomialCheck, Bool.and_eq_true] at hcert
  obtain ⟨hμ, -⟩ := hcert
  obtain ⟨hμ0, q, hq⟩ := muCheck_spec hμ
  have hpp := divMod_spec Hn Hd
  have hpplt := divMod_degree_lt Hn Hd hHd0
  have hHdS : (toPoly Hd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hHd0
  have hφHd : φ ((toPoly Hd).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hHdS
  have hGn'0_cert : toPoly Gn' ≠ 0 ∧
      ((∃ p : S[X], Irreducible p ∧ p ^ 2 ∣ (toPoly Hd).map ι) ∨
        ((toPoly Hd).map ι).natDegree ≤ ((toPoly Gn').map ι).natDegree ∨
        ∃ p : S[X], Irreducible p ∧ p ∣ (toPoly (simplePart Hd)).map ι ∧
          ∀ q : ℚ, ((toPoly μ).map ι).eval (q : S) = 0 →
            ¬p ∣ (toPoly (residuePolyW Gn' Hd)).map ι - C (q : S)) := by
    rcases hg with hprop | hne
    · -- the proper part of `η` is not a rational multiple of a logarithmic derivative
      have hGn'0 : toPoly Gn' ≠ 0 := by
        intro h0
        have hdvd : toPoly Hd ∣ toPoly Hn := ⟨-(C ((z : R)⁻¹) * toPoly g), by
          linear_combination h0 - hGn'poly⟩
        have hunit : IsUnit (toPoly Hd) := hcop.isUnit_of_dvd' hdvd dvd_rfl
        have hdeg0 : (toPoly Hd).natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
        simp only [hexpProperCert, Bool.or_eq_true, Bool.not_eq_true'] at hprop
        rcases hprop with hsq | hres
        · obtain ⟨p, hp1, hp2⟩ := exists_sq_dvd_of_squarefreeCheck hHd0 hsq
          have := natDegree_le_of_dvd hp2 hHd0
          rw [natDegree_pow, hdeg0] at this
          omega
        · obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ :=
            simplePart_data Hd hHd0
          obtain ⟨-, hSd, -, -, -, -⟩ := simplePart_props hHd0 E1 E2 E3 E4 E5 E6
          have hSdeg : (toPoly (simplePart Hd)).natDegree = 0 := by
            have := natDegree_le_of_dvd hSd hHd0
            omega
          have hlt := divMod_degree_lt
            (ratShiftProd (residuePolyW Hn Hd) (HasRatRoots.ratRoots μ)) (simplePart Hd) hS0
          generalize (divMod (ratShiftProd (residuePolyW Hn Hd) (HasRatRoots.ratRoots μ))
            (simplePart Hd)).2 = Rm at hlt hres
          rw [degree_eq_natDegree hS0, hSdeg] at hlt
          have h0 : toPoly Rm = 0 := by
            by_contra hne
            rw [degree_eq_natDegree hne] at hlt
            exact absurd (WithBot.coe_lt_coe.mp hlt) (Nat.not_lt_zero _)
          rw [(isZero_iff _).mpr h0] at hres
          exact Bool.noConfusion hres
      refine ⟨hGn'0, ?_⟩
      simp only [hexpProperCert, Bool.or_eq_true, Bool.not_eq_true'] at hprop
      rcases hprop with hsq | hres
      · left
        obtain ⟨p, hp1, hp2⟩ := exists_sq_dvd_of_squarefreeCheck hHd0 hsq
        have hpS : (p.map ι) ^ 2 ∣ (toPoly Hd).map ι := by
          rw [← Polynomial.map_pow]; exact Polynomial.map_dvd ι hp2
        have hpS0 : p.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr (fun h0 ↦ by
          rw [h0, natDegree_zero] at hp1; omega)
        obtain ⟨p', hp', hp'p⟩ := WfDvdMonoid.exists_irreducible_factor
          (fun hu ↦ by
            have := natDegree_eq_zero_of_isUnit hu
            rw [natDegree_map] at this; omega) hpS0
        exact ⟨p', hp', (pow_dvd_pow_of_dvd hp'p 2).trans hpS⟩
      · right; right
        obtain ⟨p, hp, hpS, hall⟩ := nonrational_residue_alt ι hHd0 hμ0 hres
        refine ⟨p, hp, hpS, fun q hq hdvd ↦ hall q hq ?_⟩
        have hrr : (toPoly (simplePart Hd)).map ι ∣
            (toPoly (residuePolyW Gn' Hd)).map ι - (toPoly (residuePolyW Hn Hd)).map ι := by
          rw [← Polynomial.map_sub, hGn']
          exact Polynomial.map_dvd ι (residuePolyW_add_mul (smul ((z : R)⁻¹) g) Hn Hd hHd0)
        have := dvd_sub hdvd (hpS.trans hrr)
        rwa [sub_sub_sub_cancel_left] at this
    · -- `g + z · polyPart ≠ 0`: the polynomial part of `Gn' / Hd` is nonzero
      rw [toPoly_add, toPoly_smul] at hne
      have hq0 : C ((z : R)⁻¹) * (toPoly g + C (z : R) * toPoly (polyPart Hn Hd)) ≠ 0 :=
        mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hzR)) hne
      have hGn'eq : toPoly Gn' = C ((z : R)⁻¹) * (toPoly g + C (z : R) * toPoly (polyPart Hn Hd)) *
          toPoly Hd + toPoly (divMod Hn Hd).2 := by
        rw [hGn'poly, polyPart]
        have hzz : C ((z : R)⁻¹) * C (z : R) = (1 : R[X]) := by
          rw [← C_mul, inv_mul_cancel₀ hzR, C_1]
        linear_combination hpp - toPoly (divMod Hn Hd).1 * toPoly Hd * hzz
      have hdegq : degree (toPoly (divMod Hn Hd).2) <
          degree (C ((z : R)⁻¹) * (toPoly g + C (z : R) * toPoly (polyPart Hn Hd)) * toPoly Hd) := by
        rw [degree_mul]
        exact lt_of_lt_of_le hpplt (le_add_of_nonneg_left (zero_le_degree_iff.mpr hq0))
      have hdeg : degree (toPoly Gn') =
          degree (C ((z : R)⁻¹) * (toPoly g + C (z : R) * toPoly (polyPart Hn Hd)) * toPoly Hd) := by
        rw [hGn'eq]; exact degree_add_eq_left_of_degree_lt hdegq
      have hGn'0 : toPoly Gn' ≠ 0 := by
        intro h0
        rw [h0, degree_zero] at hdeg
        exact mul_ne_zero hq0 hHd0 (degree_eq_bot.mp hdeg.symm)
      refine ⟨hGn'0, Or.inr (Or.inl ?_)⟩
      rw [natDegree_map, natDegree_map]
      refine natDegree_le_natDegree ?_
      rw [hdeg, degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hq0)
  obtain ⟨hGn'0, hcert'⟩ := hGn'0_cert
  have hGn'S : (toPoly Gn').map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hGn'0
  -- the residue data of `Gn' / Hd`
  obtain ⟨t, ht⟩ := residuePolyW_bezout Gn' Hd hS0 hcopR.symm
  have hrS : (toPoly (simplePart Hd)).map ι ∣
      (toPoly (residuePolyW Gn' Hd)).map ι * derivative ((toPoly Hd).map ι) - (toPoly Gn').map ι := by
    refine ⟨-(t.map ι), ?_⟩
    have := congrArg (Polynomial.map ι) ht
    simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map] at this
    rw [← this]; ring
  have hμS : (toPoly (simplePart Hd)).map ι ∣
      ((toPoly μ).map ι).comp ((toPoly (residuePolyW Gn' Hd)).map ι) := by
    have h1 : toPoly (simplePart Hd) ∣ (toPoly μ).comp (toPoly (residuePolyW Gn' Hd)) := by
      have h2 := dvd_comp_sub_comp (μ := toPoly μ)
        (residuePolyW_add_mul (smul ((z : R)⁻¹) g) Hn Hd hHd0)
      rw [← hGn'] at h2
      have h3 : toPoly (simplePart Hd) ∣ (toPoly μ).comp (toPoly (residuePolyW Hn Hd)) :=
        ⟨q, hq⟩
      have := dvd_add h2 h3
      rwa [sub_add_cancel] at this
    rw [← Polynomial.map_comp]
    exact Polynomial.map_dvd ι h1
  -- the equation in the form of `rde_homogeneous_W`
  refine rde_homogeneous_W hD _ _ _ _ _ hGn'S hHdS (hcop'.map (mapRingHom ι)) hSd' hScop' hrS hμS
    hcert' (-z) (neg_ne_zero.mpr hz) y ?_
  have hev : φ ((toPoly Gn').map ι) = φ (C (ι ((z : R)⁻¹))) * φ ((toPoly g).map ι) *
      φ ((toPoly Hd).map ι) + φ ((toPoly Hn).map ι) := by
    rw [hGn'poly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_add,
      map_mul, map_mul]
  have hzK : (z : K) ≠ 0 := Int.cast_ne_zero.mpr hz
  have hzφ : ((z : ℤ) : K) = φ (C (z : S)) := by rw [map_intCast, map_intCast]
  have hzinv : φ (C (ι ((z : R)⁻¹))) = ((z : K))⁻¹ := by
    rw [map_inv₀, map_intCast]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hzφ, ← map_mul, ← C_mul, inv_mul_cancel₀ hzS, C_1, map_one]
  rw [hev, hzinv, Int.cast_neg, C_neg, map_neg, ← hzφ]
  have e : -(z : K) * (((z : K)⁻¹ * φ ((toPoly g).map ι) * φ ((toPoly Hd).map ι) +
      φ ((toPoly Hn).map ι)) / φ ((toPoly Hd).map ι)) =
      -(φ ((toPoly g).map ι) + (z : K) * (φ ((toPoly Hn).map ι) / φ ((toPoly Hd).map ι))) := by
    field_simp
  rw [e]
  linear_combination h

/-- **The independence certificate gives uniqueness** for the coefficients `k a′ + z η`. -/
theorem hexpExpIndep_hom (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn Hd μ a : CPoly R} (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : hyperexpMonomialCheck Hn Hd μ = true)
    (hind : hexpExpIndep Hn Hd μ a = true) (k : R) (hk : k ≠ 0) (z : ℤ) (y : K)
    (h : y′ + (φ ((toPoly (smul k (deriv a))).map ι) +
      (z : K) * (φ ((toPoly Hn).map ι) / φ ((toPoly Hd).map ι))) * y = 0) : y = 0 := by
  simp only [hexpExpIndep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hind
  obtain ⟨ha, hdisj⟩ := hind
  have ha0 : toPoly (deriv a) ≠ 0 := fun h0 ↦ by
    rw [(isZero_iff _).mpr h0] at ha; exact absurd ha (by decide)
  have hg0 : toPoly (smul k (deriv a)) ≠ 0 := by
    rw [toPoly_smul]; exact mul_ne_zero (C_ne_zero.mpr hk) ha0
  refine hexp_hom_of_polyPart ι hD hHn0 hHd0 hcop hcert hg0 z ?_ y h
  rcases hdisj with hprop | hnone
  · exact Or.inl hprop
  · right
    intro h0
    rw [toPoly_add, toPoly_smul, toPoly_smul] at h0
    refine linSolve_complete_map (RingHom.id R) [polyPart Hn Hd] (deriv a) [-(z : R) / k] rfl
      ?_ hnone
    simp only [lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
      List.sum_nil, add_zero, Polynomial.map_id]
    have hCk : (C k : R[X]) ≠ 0 := C_ne_zero.mpr hk
    apply mul_left_cancel₀ hCk
    rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hk, C_neg]
    linear_combination -h0

end Spec

end CPoly
