import RischTragerBronstein.Computable.RDEHexp2
import RischTragerBronstein.Computable.RDEHexpComplete
import RischTragerBronstein.Computable.RDEExpComplete
import RischTragerBronstein.Computable.RDEPrimWComplete

/-!
# Completeness of `rdeHexp₂` (rational coefficient)

If `y′ + g y = A / (t₁^m D₁)` (`g = Gn / Gd ∈ R(x)`) has a solution in `K₂ = S(x)(t₁)`
(`t₁′ = η t₁`), then `rdeHexp₂` returns one. The hypothesis `hhom`: for every integer `z`, `e′ + (g + z η) e = 0` has only the
zero solution in `S(x)` (from the independence certificate, `hexpExpIndep_hom`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [CPoly.HasRatRoots R] [HasNatTest R]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
  (Hn Hd : CPoly R)

lemma rdePolyHexpAux₂_isSome_of_zero (Gn Gd : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) (fuel : ℕ)
    (Ap acc : GPoly (GFrac R)) (hz : GPoly.isZero (ops₁g R) Ap = true) :
    (rdePolyHexpAux₂ Hn Hd Gn Gd m D P₀ fuel Ap acc).isSome = true := by
  cases fuel <;> simp [rdePolyHexpAux₂, hz]

include h0 hD in
set_option maxHeartbeats 1600000 in
/-- **Completeness of the recursion.** -/
theorem rdePolyHexpAux₂_complete
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hHd0 : CPoly.toPoly Hd ≠ 0) (hcop : IsCoprime (CPoly.toPoly Hn) (CPoly.toPoly Hd))
    (Gn Gd : CPoly R) (hGd0 : CPoly.toPoly Gd ≠ 0)
    (hcopG : IsCoprime (CPoly.toPoly Gn) (CPoly.toPoly Gd))
    (m : ℕ)
    (hhom : ∀ z : ℤ, ∀ e : K₁,
      e′ + (CPoly.ev K₁ ι (Gn, Gd) + (z : K₁) * ηh ι Hn Hd) * e = 0 → e = 0)
    (D P₀ : GPoly (GFrac R))
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D ≠ 0)
    (hP₀ : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) P₀ =
      C (CPoly.ev K₁ ι (Gn, Gd) - m * ηh ι Hn Hd) * GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D -
        (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D)′)
    (fuel : ℕ) (Ap acc : GPoly (GFrac R)) (Y : K₁[X])
    (hY : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D * Y′ +
      GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) P₀ * Y = GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Ap)
    (hfuel : Y.natDegree < fuel) :
    (rdePolyHexpAux₂ Hn Hd Gn Gd m D P₀ fuel Ap acc).isSome = true := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  set gK : K₁ := CPoly.ev K₁ ι (Gn, Gd) with hgK
  have hgd : ∀ dA d₁ : ℕ, CPoly.ev K₁ ι (hexpGq₂ Hn Hd Gn Gd (hexpZ dA d₁ m)) =
      gK - m * ηh ι Hn Hd + (((dA - d₁ : ℕ) : K₁) - d₁) * ηh ι Hn Hd := fun dA d₁ ↦ by
    rw [ev_hexpGq₂ ι Hn Hd Gn Gd hHd0 hGd0, hexpZ]
    simp only [Int.cast_sub, Int.cast_natCast, hgK]
    ring
  have hgnl : ∀ dA d₁ : ℕ, ∀ e : K₁, e ≠ 0 →
      e′ + (gK - m * ηh ι Hn Hd + (((dA - d₁ : ℕ) : K₁) - d₁) * ηh ι Hn Hd) * e ≠ 0 :=
    fun dA d₁ e he h ↦ he (hhom (hexpZ dA d₁ m) e (by
      rw [hexpZ]; simp only [Int.cast_sub, Int.cast_natCast]; linear_combination h))
  induction fuel generalizing Ap acc Y with
  | zero => omega
  | succ fuel ih =>
    simp only [rdePolyHexpAux₂]
    by_cases hz : GPoly.isZero (ops₁g R) Ap = true
    · rw [if_pos hz]; rfl
    rw [if_neg hz]
    have hAp0 : GPoly.toPoly M₁ Ap ≠ 0 := fun h ↦ hz ((GPoly.isZero_iff M₁ Ap).mpr h)
    have hY0 : Y ≠ 0 := fun h ↦ hAp0 (by rw [← hY, h]; simp)
    rw [hP₀] at hY
    obtain ⟨hdeg, hcoeff, -⟩ := rde_poly_top_exp (ηh ι Hn Hd) (gK - m * ηh ι Hn Hd) hD₂
      (GPoly.toPoly M₁ D) Y hD0 hY0 (fun e he h ↦ by
        refine hgnl (Y.natDegree + (GPoly.toPoly M₁ D).natDegree) (GPoly.toPoly M₁ D).natDegree
          e he ?_
        rw [Nat.add_sub_cancel]; exact h)
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
        (gK - m * ηh ι Hn Hd + ((Y.natDegree : K₁) - (GPoly.toPoly M₁ D).natDegree) * ηh ι Hn Hd) *
          (Y.leadingCoeff / L)) := by
      rw [htop, ← hlA, ← hLlc, ← hcoeff, ← hdeg, hdA]
    set gd : K₁ := gK - m * ηh ι Hn Hd +
      ((Y.natDegree : K₁) - (GPoly.toPoly M₁ D).natDegree) * ηh ι Hn Hd with hgd'
    obtain ⟨dA, hdA'⟩ : ∃ d, d = (GPoly.trim (ops₁g R) Ap).length - 1 := ⟨_, rfl⟩
    obtain ⟨d₁, hd₁'⟩ : ∃ d, d = (GPoly.trim (ops₁g R) D).length - 1 := ⟨_, rfl⟩
    have hdAY : dA - d₁ = Y.natDegree := by rw [hdA', hd₁', ← hdA, ← hd₁, hdeg]; omega
    have hd₁D : d₁ = (GPoly.toPoly M₁ D).natDegree := by rw [hd₁', hd₁]
    have hgdc : CPoly.ev K₁ ι (hexpGq₂ Hn Hd Gn Gd (hexpZ dA d₁ m)) = gd := by
      rw [hgd, hgd', hdAY, hd₁D]
    have hgnl' : ∀ e : K₁, e ≠ 0 → e′ + gd * e ≠ 0 := fun e he h ↦
      hgnl dA d₁ e he (by rw [hdAY, hd₁D]; exact h)
    have hL0 : L ≠ 0 := by rw [← hLlc]; exact leadingCoeff_ne_zero.mpr hD0
    obtain ⟨z, hz'⟩ : ∃ z, z = Y.leadingCoeff / L := ⟨_, rfl⟩
    rw [← hz'] at htoplc
    have hzsol : z′ + gd * z = top / L ^ 2 := by rw [htoplc]; field_simp
    -- `rdeTopCoeffW` succeeds and returns `L z`
    obtain ⟨Lc, hLc⟩ : ∃ c, c = GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D) := ⟨_, rfl⟩
    obtain ⟨tc, htc⟩ : ∃ c, c = GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap) := ⟨_, rfl⟩
    rw [← hLc] at hL
    rw [← htc] at htop
    rw [← hLc, ← htc, ← hdA', ← hd₁']
    have hev : ∀ q : GFrac R, M₁.sem q = φ ((CPoly.toPoly q.1).map ι) / φ ((CPoly.toPoly q.2).map ι) :=
      fun q ↦ by rw [hM₁, sem_M₁In]; rfl
    have hφ : ∀ {P : CPoly R}, CPoly.toPoly P ≠ 0 → φ ((CPoly.toPoly P).map ι) ≠ 0 := fun hP ↦
      CPoly.map_toPoly_ne_zero ι hP
    have hne' : ∀ {P : CPoly R}, φ ((CPoly.toPoly P).map ι) ≠ 0 → CPoly.toPoly P ≠ 0 :=
      fun h hP ↦ h (by rw [hP]; simp)
    have hL1 : CPoly.toPoly Lc.1 ≠ 0 := hne' fun h ↦ hL0 (by rw [hL, hev, h, zero_div])
    have hL2 : CPoly.toPoly Lc.2 ≠ 0 := hne' fun h ↦ hL0 (by rw [hL, hev, h, div_zero])
    have htop0 : top ≠ 0 := by
      rw [htoplc]; exact mul_ne_zero (pow_ne_zero 2 hL0) (hgnl' z (by
        rw [hz']; exact div_ne_zero (leadingCoeff_ne_zero.mpr hY0) hL0))
    have ht2 : CPoly.toPoly tc.2 ≠ 0 := hne' fun h ↦ htop0 (by rw [htop, hev, h, div_zero])
    have hden : CPoly.toPoly (CPoly.mul (CPoly.mul tc.2 Lc.1) Lc.1) ≠ 0 := by
      simp only [CPoly.toPoly_mul]; exact mul_ne_zero (mul_ne_zero ht2 hL1) hL1
    obtain ⟨gc, hgc⟩ : ∃ c, c = hexpGq₂ Hn Hd Gn Gd (hexpZ dA d₁ m) := ⟨_, rfl⟩
    obtain ⟨μc, hμc⟩ : ∃ c, c = hexpMu₂ Hn Hd Gn Gd (hexpZ dA d₁ m) := ⟨_, rfl⟩
    have hgcev : CPoly.ev K₁ ι gc = gd := by rw [hgc]; exact hgdc
    have hgc2 : CPoly.toPoly gc.2 ≠ 0 := by
      rw [hgc]; exact hexpGq₂_den_ne_zero Hn Hd Gn Gd _
    have hgc1 : CPoly.toPoly gc.1 ≠ 0 := by
      rw [hgc]
      refine hexpGq₂_num_ne_zero (K₁ := K₁) ι Hn Hd Gn Gd hHd0 hGd0 _ fun e he ↦ ?_
      exact hhom _ e he
    have hgccop : IsCoprime (CPoly.toPoly gc.1) (CPoly.toPoly gc.2) := by
      rw [hgc]; exact hexpGq₂_coprime Hn Hd Gn Gd _
    obtain ⟨hμc0, hμcq⟩ : CPoly.toPoly μc ≠ 0 ∧ ∃ q : R[X],
        (CPoly.toPoly μc).comp (CPoly.toPoly (CPoly.residuePolyW gc.1 gc.2)) =
          CPoly.toPoly (CPoly.simplePart gc.2) * q := by
      rw [hμc, hgc]; exact hexpMu₂_spec Hn Hd Gn Gd hHd0 hGd0 _
    have hhomc : ∀ y : K₁, y′ + φ ((CPoly.toPoly gc.1).map ι) / φ ((CPoly.toPoly gc.2).map ι) * y = 0 →
        y = 0 := fun y hy ↦ by
      by_contra hy0
      exact hgnl' y hy0 (by rw [← hgcev]; exact hy)
    rw [← hgc, ← hμc]
    have hrde : CPoly.rdeRationalW μc gc.1 gc.2 (CPoly.mul (CPoly.mul tc.1 Lc.2) Lc.2)
        (CPoly.mul (CPoly.mul tc.2 Lc.1) Lc.1) ≠ none := fun hnone ↦
      CPoly.rdeRationalW_complete (K := K₁) ι hD hden hgc1 hgc2 hgccop hμc0 hμcq hhomc hnone z (by
        have : φ ((CPoly.toPoly gc.1).map ι) / φ ((CPoly.toPoly gc.2).map ι) = gd := hgcev
        rw [this, hzsol, htop, hL, hev, hev]
        simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul]
        have := hφ hL1; have := hφ hL2; have := hφ ht2
        field_simp)
    obtain ⟨⟨Yz, Gz⟩, hsome⟩ := Option.ne_none_iff_exists'.mp hrde
    have htc' : rdeTopCoeffW gc μc Lc tc = some ((ops₁g R).mul Lc (Yz, Gz)) := by
      simp only [rdeTopCoeffW, hsome, Option.map_some]
    rw [htc']
    simp only
    -- the returned coefficient is `L z`
    have hsol := CPoly.rdeRationalW_sound (K := K₁) ι hD hden hgc2 hsome
    have hz'' : φ ((CPoly.toPoly Yz).map ι) / φ ((CPoly.toPoly Gz).map ι) = z := by
      refine rde_unique_of_hom hgnl' _ _ (top / L ^ 2) ?_ hzsol
      rw [← hgcev, CPoly.ev, hsol, htop, hL, hev, hev]
      simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul]
      have := hφ hL1; have := hφ hL2; have := hφ ht2
      field_simp
    have hyd : M₁.sem ((ops₁g R).mul Lc (Yz, Gz)) = Y.leadingCoeff := by
      rw [M₁.sem_mul, ← hL, hev (Yz, Gz)]
      have : φ ((CPoly.toPoly (Yz, Gz).1).map ι) / φ ((CPoly.toPoly (Yz, Gz).2).map ι) = z := hz''
      rw [this, hz']
      exact mul_div_cancel₀ _ hL0
    -- recurse with `Y - lc Y * X ^ d`
    have hYd : GPoly.toPoly M₁ (GPoly.monomial (ops₁g R) (dA - d₁) ((ops₁g R).mul Lc (Yz, Gz))) =
        C Y.leadingCoeff * X ^ Y.natDegree := by
      rw [GPoly.toPoly_monomial, hyd, hdAY]
    have hY'sol : GPoly.toPoly M₁ D * (Y.eraseLead)′ +
        (C (gK - m * ηh ι Hn Hd) * GPoly.toPoly M₁ D - (GPoly.toPoly M₁ D)′) * Y.eraseLead =
        GPoly.toPoly M₁ (GPoly.sub (ops₁g R) Ap (GPoly.add (ops₁g R)
          (GPoly.mul (ops₁g R) D (GPoly.derivT (ops₁g R) (hexpW Hn Hd)
            (GPoly.monomial (ops₁g R) (dA - d₁) ((ops₁g R).mul Lc (Yz, Gz)))))
          (GPoly.mul (ops₁g R) P₀ (GPoly.monomial (ops₁g R) (dA - d₁) ((ops₁g R).mul Lc (Yz, Gz)))))) := by
      simp only [GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul]
      rw [toPoly_derivT_hexpW ι h0 hD Hn Hd hD₂, hYd, ← hY, hP₀, ← Y.self_sub_C_mul_X_pow, map_sub]
      ring
    rcases Y.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt' | hz'
    · exact ih _ _ Y.eraseLead (by omega) (by rw [hP₀]; exact hY'sol)
    · rw [hz'] at hY'sol
      simp only [map_zero, mul_zero, add_zero] at hY'sol
      apply rdePolyHexpAux₂_isSome_of_zero
      exact (GPoly.isZero_iff M₁ _).mpr hY'sol.symm

include h0 hD in
/-- **Completeness of `rdeHexp`.** -/
theorem rdeHexp₂_complete (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (hHd0 : CPoly.toPoly Hd ≠ 0) (hcop : IsCoprime (CPoly.toPoly Hn) (CPoly.toPoly Hd))
    (Gn Gd : CPoly R) (hGd0 : CPoly.toPoly Gd ≠ 0)
    (hcopG : IsCoprime (CPoly.toPoly Gn) (CPoly.toPoly Gd))
    (hhom : ∀ z : ℤ, ∀ e : K₁,
      e′ + (CPoly.ev K₁ ι (Gn, Gd) + (z : K₁) * ηh ι Hn Hd) * e = 0 → e = 0)
    (A D₁ : GPoly (GFrac R)) (m : ℕ)
    (hD₁ : ¬X ∣ GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁) (y : K₂)
    (hy : y′ + φ₂ (C (CPoly.ev K₁ ι (Gn, Gd))) * y =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁))) :
    (rdeHexp₂ Hn Hd Gn Gd A D₁ m).isSome = true := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  set gK : K₁ := CPoly.ev K₁ ι (Gn, Gd) with hgK
  have hD0 : GPoly.toPoly M₁ D₁ ≠ 0 := fun h ↦ hD₁ (h ▸ dvd_zero X)
  have hnorm : ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ :=
    fun p hm hp hpX hdvd ↦ hpX (by
      have hXp := dvd_X_of_irreducible_special (ηh ι Hn Hd) hD₂ hconst hp hdvd
      exact eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp))
  have hg : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ + (gK - r * ηh ι Hn Hd) * e ≠ 0 :=
    fun r _ e he h ↦ he (hhom (-(r : ℤ)) e (by
      simp only [Int.cast_neg, Int.cast_natCast]; linear_combination h))
  obtain ⟨Y, hY, hpoly⟩ := rde_denominator_exp (K := K₂) (ηh ι Hn Hd) hD₂ hnorm gK hg
    (GPoly.toPoly M₁ A) (GPoly.toPoly M₁ D₁) m hD₁ y hy
  have hP₀ : GPoly.toPoly M₁ (rdeP₀H₂ Hn Hd Gn Gd m D₁) =
      C (gK - m * ηh ι Hn Hd) * GPoly.toPoly M₁ D₁ - (GPoly.toPoly M₁ D₁)′ := by
    rw [rdeP₀H₂, GPoly.toPoly_sub, GPoly.toPoly_smul, toPoly_derivT_hexpW ι h0 hD Hn Hd hD₂, hM₁,
      sem_M₁In, ev_hexpGq₂ ι Hn Hd Gn Gd hHd0 hGd0]
    congr 3
    rw [Int.cast_neg, Int.cast_natCast, hgK]
    ring
  refine rdePolyHexpAux₂_complete ι h0 hD Hn Hd hD₂ hHd0 hcop Gn Gd hGd0 hcopG m hhom D₁ _
    hD0 hP₀ _ _ [] Y
    (by rw [hP₀, GPoly.toPoly_mul]; exact hpoly) ?_
  -- the degree bound
  by_cases hY0 : Y = 0
  · rw [hY0, natDegree_zero]; omega
  have hgnl : ∀ e : K₁, e ≠ 0 →
      e′ + (gK - m * ηh ι Hn Hd + ((Y.natDegree : K₁) - (GPoly.toPoly M₁ D₁).natDegree) *
        ηh ι Hn Hd) * e ≠ 0 := fun e he h ↦
    he (hhom ((Y.natDegree : ℤ) - m - (GPoly.toPoly M₁ D₁).natDegree) e (by
      simp only [Int.cast_sub, Int.cast_natCast]; linear_combination h))
  obtain ⟨hdeg, -, -⟩ := rde_poly_top_exp (ηh ι Hn Hd) (gK - m * ηh ι Hn Hd) hD₂
    (GPoly.toPoly M₁ D₁) Y hD0 hY0 hgnl
  rw [hpoly, ← GPoly.toPoly_mul] at hdeg
  have hne : GPoly.trim (ops₁g R) (GPoly.mul (ops₁g R) A D₁) ≠ [] := fun h ↦ by
    have := (GPoly.trim_eq_nil_iff M₁ _).mp h
    rw [this, natDegree_zero] at hdeg
    have h2 := hpoly
    rw [← GPoly.toPoly_mul, (GPoly.trim_eq_nil_iff M₁ _).mp h] at h2
    have := rde_poly_top_exp (ηh ι Hn Hd) (gK - m * ηh ι Hn Hd) hD₂ (GPoly.toPoly M₁ D₁) Y hD0
      hY0 hgnl
    exact absurd h2 this.2.2
  have h1 := GPoly.length_trim M₁ hne
  have hlen := GPoly.length_trim_le (O := ops₁g R) (GPoly.mul (ops₁g R) A D₁)
  omega

end Tower
