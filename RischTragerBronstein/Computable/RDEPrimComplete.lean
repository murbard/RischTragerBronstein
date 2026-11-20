import RischTragerBronstein.Computable.RDEPrimTop

/-!
# Completeness of `rdePrim`

If `y′ + g y = A / D` has a solution in any model `K₂` of `S(x)(t₁)` (`S ⊇ R` an extension of
the constants), then `rdePrim` returns one.
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

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
  {En₁ Ed₁ : CPoly R}

include hD in
/-- Uniqueness of solutions of `z′ + g z = f` in `K₁ = S(x)` for a non-zero polynomial `g`. -/
theorem rde_unique_K₁ (g : CPoly R) (hg : CPoly.toPoly g ≠ 0) (z₁ z₂ f : K₁)
    (h₁ : z₁′ + φ ((CPoly.toPoly g).map ι) * z₁ = f)
    (h₂ : z₂′ + φ ((CPoly.toPoly g).map ι) * z₂ = f) : z₁ = z₂ := by
  have hnorm : ∀ p : S[X], Irreducible p → ¬p ∣ p′ := fun p hp hdvd ↦ by
    rw [hD] at hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0' ↦ hpos (derivative_eq_zero.mp h0')
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  set gS := (CPoly.toPoly g).map ι with hgS
  have hgS0 : gS ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hg
  have hhom : (z₁ - z₂)′ + φ gS * (z₁ - z₂) = 0 := by
    rw [map_sub]; linear_combination h₁ - h₂
  obtain ⟨Y, hY⟩ := rde_denominator_regular (K := K₁) hnorm (φ gS)
    (fun p hp ↦ algebraMap_mem_regularAt hp.prime _) 0 1 one_ne_zero (z₁ - z₂)
    (by rw [hhom, map_zero, zero_div])
  rw [map_one, mul_one] at hY
  have hpoly := rde_poly_of_rde (K := K₁) gS 0 1 Y one_ne_zero (z₁ - z₂)
    (by rw [map_one, mul_one, hY]) (by rw [hhom, map_zero, zero_div])
  rw [hD, hD, derivative_one] at hpoly
  simp only [one_mul, mul_one, sub_zero, zero_mul] at hpoly
  have hY0 : Y = 0 := by
    by_contra hne
    have hdeg : (gS * Y).natDegree = gS.natDegree + Y.natDegree := natDegree_mul hgS0 hne
    have h1 : derivative Y = -(gS * Y) := by linear_combination hpoly
    have h2 : (derivative Y).natDegree < Y.natDegree ∨ derivative Y = 0 := by
      by_cases hY' : derivative Y = 0
      · exact Or.inr hY'
      · exact Or.inl (natDegree_derivative_lt fun h0' ↦ hY' (by
          rw [eq_C_of_natDegree_eq_zero h0']; simp))
    rcases h2 with h2 | h2
    · rw [h1, natDegree_neg, hdeg] at h2; omega
    · rw [h2] at h1
      exact mul_ne_zero hgS0 hne (neg_eq_zero.mp h1.symm)
  rw [hY0, map_zero] at hY
  exact sub_eq_zero.mp hY

lemma rdePolyPrimAux_isSome_of_zero (g : CPoly R) (D P₀ : GPoly (GFrac R)) (fuel : ℕ)
    (Ap acc : GPoly (GFrac R)) (hz : GPoly.isZero (ops₁g R) Ap = true) :
    (rdePolyPrimAux En₁ Ed₁ g D P₀ fuel Ap acc).isSome = true := by
  cases fuel <;> simp [rdePolyPrimAux, hz]

include h0 hD in
set_option maxHeartbeats 1600000 in
/-- **Completeness of the recursion.** -/
theorem rdePolyPrimAux_complete
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (g : CPoly R) (hg : CPoly.toPoly g ≠ 0) (D P₀ : GPoly (GFrac R))
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D ≠ 0)
    (hP₀ : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) P₀ =
      C (φ ((CPoly.toPoly g).map ι)) * GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D -
        (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D)′)
    (fuel : ℕ) (Ap acc : GPoly (GFrac R)) (Y : K₁[X])
    (hY : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D * Y′ +
      GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) P₀ * Y = GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Ap)
    (hfuel : Y.natDegree < fuel) :
    (rdePolyPrimAux En₁ Ed₁ g D P₀ fuel Ap acc).isSome = true := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  set gK : K₁ := φ ((CPoly.toPoly g).map ι) with hgK
  have hgnl : ∀ e : K₁, e ≠ 0 → e′ + gK * e ≠ 0 := fun e he h ↦
    he (rde_unique_K₁ ι hD g hg e 0 0 h (by simp))
  induction fuel generalizing Ap acc Y with
  | zero => omega
  | succ fuel ih =>
    simp only [rdePolyPrimAux]
    by_cases hz : GPoly.isZero (ops₁g R) Ap = true
    · rw [if_pos hz]; rfl
    rw [if_neg hz]
    have hAp0 : GPoly.toPoly M₁ Ap ≠ 0 := fun h ↦ hz ((GPoly.isZero_iff M₁ Ap).mpr h)
    have hY0 : Y ≠ 0 := fun h ↦ hAp0 (by rw [← hY, h]; simp)
    rw [hP₀] at hY
    obtain ⟨hdeg, hcoeff, -⟩ := rde_poly_top (CPoly.ev K₁ ι (En₁, Ed₁)) gK hD₂ hgnl
      (GPoly.toPoly M₁ D) Y hD0 hY0
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
    have htoplc : top = L ^ 2 * ((Y.leadingCoeff / L)′ + gK * (Y.leadingCoeff / L)) := by
      rw [htop, ← hlA, ← hLlc, ← hcoeff, ← hdeg, hdA]
    have hL0 : L ≠ 0 := by rw [← hLlc]; exact leadingCoeff_ne_zero.mpr hD0
    obtain ⟨z, hz'⟩ : ∃ z, z = Y.leadingCoeff / L := ⟨_, rfl⟩
    rw [← hz'] at htoplc
    have hzsol : z′ + gK * z = top / L ^ 2 := by rw [htoplc]; field_simp
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
      rw [htoplc]; exact mul_ne_zero (pow_ne_zero 2 hL0) (hgnl z (by
        rw [hz']; exact div_ne_zero (leadingCoeff_ne_zero.mpr hY0) hL0))
    have ht2 : CPoly.toPoly tc.2 ≠ 0 := hne' fun h ↦ htop0 (by rw [htop, hev, h, div_zero])
    have hden : CPoly.toPoly (CPoly.mul (CPoly.mul tc.2 Lc.1) Lc.1) ≠ 0 := by
      simp only [CPoly.toPoly_mul]; exact mul_ne_zero (mul_ne_zero ht2 hL1) hL1
    have hrde : CPoly.rdeRational g (CPoly.mul (CPoly.mul tc.1 Lc.2) Lc.2)
        (CPoly.mul (CPoly.mul tc.2 Lc.1) Lc.1) ≠ none := fun hnone ↦
      CPoly.rdeRational_complete (K := K₁) ι hD hden hg hnone z (by
        rw [hzsol, htop, hL, hev, hev]
        simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul]
        have := hφ hL1; have := hφ hL2; have := hφ ht2
        field_simp)
    obtain ⟨⟨Yz, Gz⟩, hsome⟩ := Option.ne_none_iff_exists'.mp hrde
    have htc : rdeTopCoeff g Lc tc = some ((ops₁g R).mul Lc (Yz, Gz)) := by
      simp only [rdeTopCoeff, hsome, Option.map_some]
    rw [htc]
    simp only
    -- the returned coefficient is `L z`
    have hsol := CPoly.rdeRational_sound (K := K₁) ι hD hden hsome
    have hz'' : φ ((CPoly.toPoly Yz).map ι) / φ ((CPoly.toPoly Gz).map ι) = z := by
      refine rde_unique_K₁ ι hD g hg _ _ (top / L ^ 2) ?_ hzsol
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
        (C gK * GPoly.toPoly M₁ D - (GPoly.toPoly M₁ D)′) * Y.eraseLead =
        GPoly.toPoly M₁ (GPoly.sub (ops₁g R) Ap (GPoly.add (ops₁g R)
          (GPoly.mul (ops₁g R) D (GPoly.derivT (ops₁g R) [(En₁, Ed₁)]
            (GPoly.monomial (ops₁g R) d ((ops₁g R).mul Lc (Yz, Gz)))))
          (GPoly.mul (ops₁g R) P₀ (GPoly.monomial (ops₁g R) d ((ops₁g R).mul Lc (Yz, Gz)))))) := by
      simp only [GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul]
      rw [toPoly_derivT_η ι h0 hD hD₂, hYd, ← hY, hP₀, ← Y.self_sub_C_mul_X_pow, map_sub]
      ring
    rcases Y.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt' | hz'
    · exact ih _ _ Y.eraseLead (by omega) (by rw [hP₀]; exact hY'sol)
    · rw [hz'] at hY'sol
      simp only [map_zero, mul_zero, add_zero] at hY'sol
      apply rdePolyPrimAux_isSome_of_zero
      exact (GPoly.isZero_iff M₁ _).mpr hY'sol.symm

include h0 hD in
/-- **Completeness of `rdePrim`**: if `y′ + g y = A / D` has a solution in `K₂`, the solver finds
one. -/
theorem rdePrim_complete (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e)
    (g : CPoly R) (hg : CPoly.toPoly g ≠ 0) (A D : GPoly (GFrac R))
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D ≠ 0) (y : K₂)
    (hy : y′ + φ₂ (C (φ ((CPoly.toPoly g).map ι))) * y =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D)) :
    (rdePrim En₁ Ed₁ g A D).isSome = true := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive (CPoly.ev K₁ ι (En₁, Ed₁)) hD₂ hconst₂ hp
  obtain ⟨Y, hY⟩ := rde_denominator_regular (K := K₂) hnorm (φ₂ (C (φ ((CPoly.toPoly g).map ι))))
    (fun p hp ↦ algebraMap_mem_regularAt hp.prime _) _ _ hD0 y hy
  have hpoly := rde_poly_of_rde (K := K₂) (C (φ ((CPoly.toPoly g).map ι))) _ _ Y hD0 y hY hy
  have hP₀ : GPoly.toPoly M₁ (rdeP₀ En₁ Ed₁ g D) =
      C (φ ((CPoly.toPoly g).map ι)) * GPoly.toPoly M₁ D - (GPoly.toPoly M₁ D)′ := by
    rw [rdeP₀, GPoly.toPoly_sub, GPoly.toPoly_smul, toPoly_derivT_η ι h0 hD hD₂, hM₁, sem_M₁In]
    simp [CPoly.ev, CPoly.toPoly]
  refine rdePolyPrimAux_complete ι h0 hD hD₂ g hg D _ hD0 hP₀ _ _ [] Y (by
    rw [hP₀, GPoly.toPoly_mul]; exact hpoly) ?_
  -- the degree bound
  by_cases hY0 : Y = 0
  · rw [hY0, natDegree_zero]; omega
  have hgnl : ∀ e : K₁, e ≠ 0 → e′ + φ ((CPoly.toPoly g).map ι) * e ≠ 0 := fun e he h ↦
    he (rde_unique_K₁ ι hD g hg e 0 0 h (by simp))
  obtain ⟨hdeg, -, -⟩ := rde_poly_top (CPoly.ev K₁ ι (En₁, Ed₁)) _ hD₂ hgnl (GPoly.toPoly M₁ D) Y
    hD0 hY0
  rw [hpoly, ← GPoly.toPoly_mul] at hdeg
  have hne : GPoly.trim (ops₁g R) (GPoly.mul (ops₁g R) A D) ≠ [] := fun h ↦ by
    have := (GPoly.trim_eq_nil_iff M₁ _).mp h
    rw [this, natDegree_zero] at hdeg
    exact hY0 (by
      have : Y.natDegree = 0 := by omega
      have h2 := hpoly
      rw [← GPoly.toPoly_mul, (GPoly.trim_eq_nil_iff M₁ _).mp h] at h2
      have := rde_poly_top (CPoly.ev K₁ ι (En₁, Ed₁)) _ hD₂ hgnl (GPoly.toPoly M₁ D) Y hD0 hY0
      exact absurd h2 this.2.2)
  have h1 := GPoly.length_trim M₁ hne
  have hlen := GPoly.length_trim_le (O := ops₁g R) (GPoly.mul (ops₁g R) A D)
  omega

end Tower
