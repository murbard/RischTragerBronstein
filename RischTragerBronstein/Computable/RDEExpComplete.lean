import RischTragerBronstein.Computable.RDEExp

/-!
# Completeness of `rdeExp`
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P) (a : CPoly R)

lemma rdePolyExpAux_isSome_of_zero (g : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) (fuel : ℕ)
    (Ap acc : GPoly (GFrac R)) (hz : GPoly.isZero (ops₁g R) Ap = true) :
    (rdePolyExpAux a g m D P₀ fuel Ap acc).isSome = true := by
  cases fuel <;> simp [rdePolyExpAux, hz]

include h0 hD in
set_option maxHeartbeats 1600000 in
/-- **Completeness of the recursion.** -/
theorem rdePolyExpAux_complete
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (g : CPoly R) (m : ℕ) (hcomb : ∀ z : ℤ, CPoly.toPoly (CPoly.add g
      (CPoly.smul (z : R) (CPoly.deriv a))) ≠ 0) (D P₀ : GPoly (GFrac R))
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D ≠ 0)
    (hP₀ : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) P₀ =
      C (φ ((CPoly.toPoly g).map ι) - m * ηa ι a) * GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D -
        (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D)′)
    (fuel : ℕ) (Ap acc : GPoly (GFrac R)) (Y : K₁[X])
    (hY : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D * Y′ +
      GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) P₀ * Y = GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Ap)
    (hfuel : Y.natDegree < fuel) :
    (rdePolyExpAux a g m D P₀ fuel Ap acc).isSome = true := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  set gK : K₁ := φ ((CPoly.toPoly g).map ι) with hgK
  have hgd : ∀ δ d : ℕ, φ ((CPoly.toPoly (expGd a g m δ d)).map ι) =
      gK - m * ηa ι a + ((d : K₁) - δ) * ηa ι a := fun δ d ↦ by
    rw [expGd, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_add,
      Polynomial.map_mul, map_C, map_add, map_mul, ← derivative_map]
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast, hgK, ηa, derivative_map]
    ring
  have hgnl : ∀ δ d : ℕ, ∀ e : K₁, e ≠ 0 →
      e′ + (gK - m * ηa ι a + ((d : K₁) - δ) * ηa ι a) * e ≠ 0 := fun δ d e he h ↦
    he (rde_unique_K₁ ι hD (expGd a g m δ d) (hcomb _) e 0 0 (by rw [hgd]; exact h) (by simp))
  induction fuel generalizing Ap acc Y with
  | zero => omega
  | succ fuel ih =>
    simp only [rdePolyExpAux]
    by_cases hz : GPoly.isZero (ops₁g R) Ap = true
    · rw [if_pos hz]; rfl
    rw [if_neg hz]
    have hAp0 : GPoly.toPoly M₁ Ap ≠ 0 := fun h ↦ hz ((GPoly.isZero_iff M₁ Ap).mpr h)
    have hY0 : Y ≠ 0 := fun h ↦ hAp0 (by rw [← hY, h]; simp)
    rw [hP₀] at hY
    obtain ⟨hdeg, hcoeff, -⟩ := rde_poly_top_exp (ηa ι a) (gK - m * ηa ι a) hD₂
      (GPoly.toPoly M₁ D) Y hD0 hY0 (hgnl _ _)
    rw [hY] at hdeg hcoeff
    have hAne : GPoly.trim (ops₁g R) Ap ≠ [] := fun h ↦ hAp0 ((GPoly.trim_eq_nil_iff M₁ Ap).mp h)
    have hDne : GPoly.trim (ops₁g R) D ≠ [] := fun h ↦ hD0 ((GPoly.trim_eq_nil_iff M₁ D).mp h)
    obtain ⟨hdA, hlA, -⟩ := GPoly.natDegree_toPoly_of_trim_ne_nil M₁ hAne
    obtain ⟨hd₁, hlD, -⟩ := GPoly.natDegree_toPoly_of_trim_ne_nil M₁ hDne
    have hlt : ¬((GPoly.trim (ops₁g R) Ap).length - 1 < (GPoly.trim (ops₁g R) D).length - 1) := by
      rw [← hdA, ← hd₁, hdeg]; omega
    rw [if_neg hlt]
    -- the top coefficient
    obtain ⟨L, hL⟩ : ∃ L, L = M₁.sem (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D)) := ⟨_, rfl⟩
    obtain ⟨top, htop⟩ : ∃ t, t = M₁.sem (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) :=
      ⟨_, rfl⟩
    have hLlc : (GPoly.toPoly M₁ D).leadingCoeff = L := by
      rw [leadingCoeff, hd₁, hlD, hL]
    have htoplc : top = L ^ 2 * ((Y.leadingCoeff / L)′ +
        (gK - m * ηa ι a + ((Y.natDegree : K₁) - (GPoly.toPoly M₁ D).natDegree) * ηa ι a) *
          (Y.leadingCoeff / L)) := by
      rw [htop, ← hlA, ← hLlc, ← hcoeff, ← hdeg, hdA]
    set gd : K₁ := gK - m * ηa ι a +
      ((Y.natDegree : K₁) - (GPoly.toPoly M₁ D).natDegree) * ηa ι a with hgd'
    have hgdc : φ ((CPoly.toPoly (expGd a g m ((GPoly.trim (ops₁g R) D).length - 1)
        ((GPoly.trim (ops₁g R) Ap).length - 1 - ((GPoly.trim (ops₁g R) D).length - 1)))).map ι)
        = gd := by
      rw [hgd, hgd', ← hd₁, ← hdA, hdeg, Nat.add_sub_cancel_left]
    have hL0 : L ≠ 0 := by rw [← hLlc]; exact leadingCoeff_ne_zero.mpr hD0
    obtain ⟨z, hz'⟩ : ∃ z, z = Y.leadingCoeff / L := ⟨_, rfl⟩
    rw [← hz'] at htoplc
    have hzsol : z′ + gd * z = top / L ^ 2 := by rw [htoplc]; field_simp
    -- `rdeTopCoeff` succeeds and returns `L z`
    obtain ⟨Lc, hLc⟩ : ∃ c, c = GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D) := ⟨_, rfl⟩
    obtain ⟨tc, htc⟩ : ∃ c, c = GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap) := ⟨_, rfl⟩
    rw [← hLc] at hL
    rw [← htc] at htop
    rw [← hLc, ← htc]
    have hev : ∀ q : GFrac R, M₁.sem q = φ ((CPoly.toPoly q.1).map ι) / φ ((CPoly.toPoly q.2).map ι) :=
      fun q ↦ by rw [hM₁, sem_M₁In]; rfl
    have hφ : ∀ {P : CPoly R}, CPoly.toPoly P ≠ 0 → φ ((CPoly.toPoly P).map ι) ≠ 0 := fun hP ↦
      CPoly.map_toPoly_ne_zero ι hP
    have hne' : ∀ {P : CPoly R}, φ ((CPoly.toPoly P).map ι) ≠ 0 → CPoly.toPoly P ≠ 0 :=
      fun h hP ↦ h (by rw [hP]; simp)
    have hL1 : CPoly.toPoly Lc.1 ≠ 0 := hne' fun h ↦ hL0 (by rw [hL, hev, h, zero_div])
    have hL2 : CPoly.toPoly Lc.2 ≠ 0 := hne' fun h ↦ hL0 (by rw [hL, hev, h, div_zero])
    have htop0 : top ≠ 0 := by
      rw [htoplc]; exact mul_ne_zero (pow_ne_zero 2 hL0) (hgnl _ _ z (by
        rw [hz']; exact div_ne_zero (leadingCoeff_ne_zero.mpr hY0) hL0))
    have ht2 : CPoly.toPoly tc.2 ≠ 0 := hne' fun h ↦ htop0 (by rw [htop, hev, h, div_zero])
    have hden : CPoly.toPoly (CPoly.mul (CPoly.mul tc.2 Lc.1) Lc.1) ≠ 0 := by
      simp only [CPoly.toPoly_mul]; exact mul_ne_zero (mul_ne_zero ht2 hL1) hL1
    obtain ⟨gc, hgc⟩ : ∃ c, c = expGd a g m ((GPoly.trim (ops₁g R) D).length - 1)
      ((GPoly.trim (ops₁g R) Ap).length - 1 - ((GPoly.trim (ops₁g R) D).length - 1)) := ⟨_, rfl⟩
    have hgc0 : CPoly.toPoly gc ≠ 0 := by rw [hgc]; exact hcomb _
    rw [← hgc] at hgdc
    rw [← hgc]
    have hrde : CPoly.rdeRational gc (CPoly.mul (CPoly.mul tc.1 Lc.2) Lc.2)
        (CPoly.mul (CPoly.mul tc.2 Lc.1) Lc.1) ≠ none := fun hnone ↦
      CPoly.rdeRational_complete (K := K₁) ι hD hden hgc0 hnone z (by
        rw [hgdc, hzsol, htop, hL, hev, hev]
        simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul]
        have := hφ hL1; have := hφ hL2; have := hφ ht2
        field_simp)
    obtain ⟨⟨Yz, Gz⟩, hsome⟩ := Option.ne_none_iff_exists'.mp hrde
    have htc : rdeTopCoeff gc Lc tc = some ((ops₁g R).mul Lc (Yz, Gz)) := by
      simp only [rdeTopCoeff, hsome, Option.map_some]
    rw [htc]
    simp only
    -- the returned coefficient is `L z`
    have hsol := CPoly.rdeRational_sound (K := K₁) ι hD hden hsome
    have hz'' : φ ((CPoly.toPoly Yz).map ι) / φ ((CPoly.toPoly Gz).map ι) = z := by
      refine rde_unique_K₁ ι hD gc hgc0 _ _ (top / L ^ 2) ?_ (by rw [hgdc]; exact hzsol)
      rw [hsol, htop, hL, hev, hev]
      simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul]
      have := hφ hL1; have := hφ hL2; have := hφ ht2
      field_simp
    have hyd : M₁.sem ((ops₁g R).mul Lc (Yz, Gz)) = Y.leadingCoeff := by
      rw [M₁.sem_mul, ← hL, hev (Yz, Gz)]
      have : φ ((CPoly.toPoly (Yz, Gz).1).map ι) / φ ((CPoly.toPoly (Yz, Gz).2).map ι) = z := hz''
      rw [this, hz']
      exact mul_div_cancel₀ _ hL0
    -- recurse with `Y - lc Y * X ^ d`
    obtain ⟨d, hd⟩ : ∃ d, d = (GPoly.trim (ops₁g R) Ap).length - 1 -
      ((GPoly.trim (ops₁g R) D).length - 1) := ⟨_, rfl⟩
    rw [← hd]
    have hdY : d = Y.natDegree := by rw [hd, ← hdA, ← hd₁, hdeg]; omega
    have hYd : GPoly.toPoly M₁ (GPoly.monomial (ops₁g R) d ((ops₁g R).mul Lc (Yz, Gz))) =
        C Y.leadingCoeff * X ^ Y.natDegree := by
      rw [GPoly.toPoly_monomial, hyd, hdY]
    have hY'sol : GPoly.toPoly M₁ D * (Y.eraseLead)′ +
        (C (gK - m * ηa ι a) * GPoly.toPoly M₁ D - (GPoly.toPoly M₁ D)′) * Y.eraseLead =
        GPoly.toPoly M₁ (GPoly.sub (ops₁g R) Ap (GPoly.add (ops₁g R)
          (GPoly.mul (ops₁g R) D (GPoly.derivT (ops₁g R) (expW a)
            (GPoly.monomial (ops₁g R) d ((ops₁g R).mul Lc (Yz, Gz)))))
          (GPoly.mul (ops₁g R) P₀ (GPoly.monomial (ops₁g R) d ((ops₁g R).mul Lc (Yz, Gz)))))) := by
      simp only [GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul]
      rw [toPoly_derivT_expW ι h0 hD a hD₂, hYd, ← hY, hP₀, ← Y.self_sub_C_mul_X_pow, map_sub]
      ring
    rcases Y.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt' | hz'
    · exact ih _ _ Y.eraseLead (by omega) (by rw [hP₀]; exact hY'sol)
    · rw [hz'] at hY'sol
      simp only [map_zero, mul_zero, add_zero] at hY'sol
      apply rdePolyExpAux_isSome_of_zero
      exact (GPoly.isZero_iff M₁ _).mpr hY'sol.symm

include h0 hD in
/-- **Completeness of `rdeExp`.** -/
theorem rdeExp_complete (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (g : CPoly R)
    (hcomb : ∀ z : ℤ, CPoly.toPoly (CPoly.add g (CPoly.smul (z : R) (CPoly.deriv a))) ≠ 0)
    (A D₁ : GPoly (GFrac R)) (m : ℕ)
    (hD₁ : ¬X ∣ GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁) (y : K₂)
    (hy : y′ + φ₂ (C (φ ((CPoly.toPoly g).map ι))) * y =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁))) :
    (rdeExp a g A D₁ m).isSome = true := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  set gK : K₁ := φ ((CPoly.toPoly g).map ι) with hgK
  have hD0 : GPoly.toPoly M₁ D₁ ≠ 0 := fun h ↦ hD₁ (h ▸ dvd_zero X)
  have hnorm : ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ :=
    fun p hm hp hpX hdvd ↦ hpX (by
      have hXp := dvd_X_of_irreducible_special (ηa ι a) hD₂ hconst hp hdvd
      exact eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp))
  have hg : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ + (gK - r * ηa ι a) * e ≠ 0 :=
    fun r _ e he h ↦ by
    have hcr := hcomb (-(r : ℤ))
    refine he (rde_unique_K₁ ι hD _ hcr e 0 0 ?_ (by simp))
    rw [CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_add,
      Polynomial.map_mul, map_C, map_add, map_mul, ← derivative_map]
    simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_natCast, derivative_map]
    linear_combination h
  obtain ⟨Y, hY, hpoly⟩ := rde_denominator_exp (K := K₂) (ηa ι a) hD₂ hnorm gK hg
    (GPoly.toPoly M₁ A) (GPoly.toPoly M₁ D₁) m hD₁ y hy
  have hP₀ : GPoly.toPoly M₁ (rdeP₀E a g m D₁) =
      C (gK - m * ηa ι a) * GPoly.toPoly M₁ D₁ - (GPoly.toPoly M₁ D₁)′ := by
    rw [rdeP₀E, GPoly.toPoly_sub, GPoly.toPoly_smul, toPoly_derivT_expW ι h0 hD a hD₂, hM₁,
      sem_M₁In]
    congr 3
    rw [CPoly.ev, CPoly.toPoly_sub, CPoly.toPoly_smul, CPoly.toPoly_deriv]
    simp [CPoly.toPoly, hgK, ηa, map_natCast]
  refine rdePolyExpAux_complete ι h0 hD a hD₂ g m hcomb D₁ _ hD0 hP₀ _ _ [] Y (by
    rw [hP₀, GPoly.toPoly_mul]; exact hpoly) ?_
  -- the degree bound
  by_cases hY0 : Y = 0
  · rw [hY0, natDegree_zero]; omega
  have hgnl : ∀ e : K₁, e ≠ 0 →
      e′ + (gK - m * ηa ι a + ((Y.natDegree : K₁) - (GPoly.toPoly M₁ D₁).natDegree) * ηa ι a) * e
        ≠ 0 := fun e he h ↦ by
    have hcz := hcomb ((Y.natDegree : ℤ) - m - (GPoly.toPoly M₁ D₁).natDegree)
    refine he (rde_unique_K₁ ι hD _ hcz e 0 0 ?_ (by simp))
    rw [CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_add,
      Polynomial.map_mul, map_C, map_add, map_mul, ← derivative_map]
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast, derivative_map]
    linear_combination h
  obtain ⟨hdeg, -, -⟩ := rde_poly_top_exp (ηa ι a) (gK - m * ηa ι a) hD₂ (GPoly.toPoly M₁ D₁) Y
    hD0 hY0 hgnl
  rw [hpoly, ← GPoly.toPoly_mul] at hdeg
  have hne : GPoly.trim (ops₁g R) (GPoly.mul (ops₁g R) A D₁) ≠ [] := fun h ↦ by
    have := (GPoly.trim_eq_nil_iff M₁ _).mp h
    rw [this, natDegree_zero] at hdeg
    have h2 := hpoly
    rw [← GPoly.toPoly_mul, (GPoly.trim_eq_nil_iff M₁ _).mp h] at h2
    have := rde_poly_top_exp (ηa ι a) (gK - m * ηa ι a) hD₂ (GPoly.toPoly M₁ D₁) Y hD0 hY0 hgnl
    exact absurd h2 this.2.2
  have h1 := GPoly.length_trim M₁ hne
  have hlen := GPoly.length_trim_le (O := ops₁g R) (GPoly.mul (ops₁g R) A D₁)
  omega

end Tower
