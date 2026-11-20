import RischTragerBronstein.Computable.PRDERational
import RischTragerBronstein.Computable.RDERationalW

/-!
# The parametric Risch differential equation over `R(x)`, weakly normalised

`y′ + (Gn / Gd) y = A₀ / D - c A₁ / D`, one unknown constant `c`, `Gn / Gd` arbitrary: the same
denominator bound `D E` and pivot bound as `rdeRationalW`, then the parametric polynomial solver
`prdeSolveFull`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [HasRatRoots R] [HasNatTest R]

/-- Solve `y′ + (Gn / Gd) y = A₀ / D - c A₁ / D`; the solution is `(c, Y / (D E))`. -/
def prdeRationalW (μ Gn Gd A₀ A₁ D : CPoly R) : Option (R × CPoly R) :=
  let E := extraDenW μ Gn Gd
  let D' := mul D E
  prdeSolveFull (mul Gd D') (sub (mul Gn D') (mul Gd (deriv D'))) (mul (mul (mul A₀ E) D') Gd)
    (mul (mul (mul A₁ E) D') Gd) (pivBoundW Gn Gd D')

/-- The denominator returned with a solution of `prdeRationalW`. -/
def prdeDenW (μ Gn Gd D : CPoly R) : CPoly R := mul D (extraDenW μ Gn Gd)

variable {S K : Type*} [Field S] [DecidableEq S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

theorem prdeRationalW_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {μ Gn Gd A₀ A₁ D : CPoly R} (hD0 : toPoly D ≠ 0) (hGd0 : toPoly Gd ≠ 0) {c : R}
    {Y : CPoly R} (h : prdeRationalW μ Gn Gd A₀ A₁ D = some (c, Y)) :
    (φ ((toPoly Y).map ι) / φ ((toPoly (prdeDenW μ Gn Gd D)).map ι))′ +
        φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) *
          (φ ((toPoly Y).map ι) / φ ((toPoly (prdeDenW μ Gn Gd D)).map ι)) =
      φ ((toPoly A₀).map ι) / φ ((toPoly D).map ι) -
        φ (C (ι c)) * (φ ((toPoly A₁).map ι) / φ ((toPoly D).map ι)) := by
  have hs := prdeSolveFull_sound h
  simp only [toPoly_mul, toPoly_sub, toPoly_deriv] at hs
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hE0 : toPoly (extraDenW μ Gn Gd) ≠ 0 :=
    extraDen_ne_zero _ _ ((simplePart_props_map ι Gd hGd0).1.1) _
  have hφD : φ ((toPoly D).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hD0)
  have hφE : φ ((toPoly (extraDenW μ Gn Gd)).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hE0)
  have hφGd : φ ((toPoly Gd).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hGd0)
  have := congrArg (fun P : R[X] ↦ φ (P.map ι)) hs
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, map_add, map_mul,
    map_sub, ← derivative_map, map_C] at this
  rw [prdeDenW, toPoly_mul, Polynomial.map_mul, map_mul]
  rw [Derivation.leibniz_div, Derivation.leibniz, deriv_algebraMap, deriv_algebraMap,
    deriv_algebraMap, hD, hD, hD]
  simp only [smul_eq_mul, derivative_mul, map_add, map_mul] at this ⊢
  field_simp
  linear_combination this

/-- **Completeness**, over every extension of the constants. -/
theorem prdeRationalW_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {μ Gn Gd A₀ A₁ D : CPoly R} (hD0 : toPoly D ≠ 0) (hGn0 : toPoly Gn ≠ 0)
    (hGd0 : toPoly Gd ≠ 0) (hcop : IsCoprime (toPoly Gn) (toPoly Gd)) (hμ0 : toPoly μ ≠ 0)
    (hμ : ∃ q : R[X], (toPoly μ).comp (toPoly (residuePolyW Gn Gd)) = toPoly (simplePart Gd) * q)
    (hhom : ∀ y : K, y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y = 0 → y = 0)
    (h : prdeRationalW μ Gn Gd A₀ A₁ D = none) (c : S) (y : K)
    (hy : y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y =
      φ ((toPoly A₀).map ι) / φ ((toPoly D).map ι) -
        φ (C c) * (φ ((toPoly A₁).map ι) / φ ((toPoly D).map ι))) : False := by
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hιinj : Function.Injective ι := ι.injective
  obtain ⟨⟨hS0, hcopR⟩, hS0', hSd', hcop', hScop', hS', -⟩ := simplePart_props_map ι Gd hGd0
  obtain ⟨t, ht⟩ := residuePolyW_bezout Gn Gd hS0 hcopR.symm
  obtain ⟨q, hq⟩ := hμ
  have hE0 : toPoly (extraDenW μ Gn Gd) ≠ 0 := extraDen_ne_zero _ _ hS0 _
  -- the extra denominator
  have hES' : ∀ k : ℕ, k ≠ 0 → ((toPoly μ).map ι).eval (k : S) = 0 →
      ∀ p : S[X], Irreducible p → p ∣ (toPoly (simplePart Gd)).map ι →
      p ∣ (toPoly (residuePolyW Gn Gd)).map ι - C (k : S) →
      p ^ k ∣ (toPoly (extraDenW μ Gn Gd)).map ι := by
    intro k hk hev p hp hpS hpr
    have hevR : (toPoly μ).eval ((k : ℚ) : R) = 0 := by
      rw [← map_natCast ι, eval_map, eval₂_at_apply] at hev
      rw [Rat.cast_natCast]
      exact hιinj (by rw [hev, map_zero])
    have hmem : k ∈ natCands (HasRatRoots.ratRoots μ) :=
      mem_natCands hk (HasRatRoots.ratRoots_spec _ _ hμ0 hevR)
    have hTk : (toPoly (gcd (simplePart Gd) (sub (residuePolyW Gn Gd) [(k : R)]))).map ι ^ k ∣
        (toPoly (extraDenW μ Gn Gd)).map ι := by
      rw [← Polynomial.map_pow]
      exact Polynomial.map_dvd ι (pow_gcd_dvd_extraDen _ _ hmem)
    refine (pow_dvd_pow_of_dvd ?_ k).trans hTk
    have hb := egcd_spec (simplePart Gd) (sub (residuePolyW Gn Gd) [(k : R)])
    rw [← toPoly_gcd] at hb
    have := congrArg (Polynomial.map ι) hb
    simp only [Polynomial.map_add, Polynomial.map_mul, toPoly_sub, Polynomial.map_sub,
      toPoly_cons, toPoly_nil, mul_zero, add_zero, Polynomial.map_natCast, map_natCast] at this
    rw [← this]
    have hpr' : p ∣ (toPoly (residuePolyW Gn Gd)).map ι - (k : S[X]) := by
      rwa [← C_eq_natCast]
    exact dvd_add (Dvd.dvd.mul_left hpS _) (Dvd.dvd.mul_left hpr' _)
  simp only [prdeRationalW] at h
  -- make the data opaque
  generalize hE : extraDenW μ Gn Gd = E at h hE0 hES'
  generalize hr : residuePolyW Gn Gd = r at ht hq hES'
  generalize hSp : simplePart Gd = Sp at hS0 hcopR hS0' hSd' hcop' hScop' hS' ht hq hES'
  generalize hD' : mul D E = D' at h
  have hD'0 : toPoly D' ≠ 0 := by rw [← hD', toPoly_mul]; exact mul_ne_zero hD0 hE0
  have hDS : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hD0
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hGd0
  have hES : (toPoly E).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hE0
  have hφD : φ ((toPoly D).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDS
  have hφGd : φ ((toPoly Gd).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hGdS
  have hφE : φ ((toPoly E).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hES
  -- the residue polynomial and the annihilator, over `S`
  have hrS : (toPoly Sp).map ι ∣ (toPoly r).map ι * derivative ((toPoly Gd).map ι) -
      (toPoly Gn).map ι := by
    refine ⟨-(t.map ι), ?_⟩
    have := congrArg (Polynomial.map ι) ht
    simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map] at this
    rw [← this]; ring
  have hμS : (toPoly Sp).map ι ∣ ((toPoly μ).map ι).comp ((toPoly r).map ι) :=
    ⟨q.map ι, by rw [← Polynomial.map_comp, hq, Polynomial.map_mul]⟩
  -- the denominator bound
  have hy' : y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y =
      φ ((toPoly A₀).map ι - C c * (toPoly A₁).map ι) / φ ((toPoly D).map ι) := by
    rw [hy, map_sub, map_mul, sub_div, mul_div_assoc]
  obtain ⟨Ys, hYs⟩ := rde_denominator_rational_W (K := K) hD _ _ _ _ _ _ _ _ hDS hGdS
    (hcop.map (mapRingHom ι)) hS' hrS hμS hES' y hy'
  have hD'S : (toPoly D').map ι = (toPoly D).map ι * (toPoly E).map ι := by
    rw [← hD', toPoly_mul, Polynomial.map_mul]
  have hφD' : φ ((toPoly D').map ι) ≠ 0 := by
    rw [hD'S, map_mul]; exact mul_ne_zero hφD hφE
  have hyY : y = φ Ys / φ ((toPoly D').map ι) := by
    rw [hD'S, ← hYs]; field_simp
  -- the polynomial ODE, in the form of the solver
  generalize hP₁ : mul Gd D' = P₁ at h
  generalize hP₀ : sub (mul Gn D') (mul Gd (deriv D')) = P₀ at h
  have hP₁poly : toPoly P₁ = toPoly Gd * toPoly D' := by rw [← hP₁, toPoly_mul]
  have hP₀poly : toPoly P₀ = toPoly Gn * toPoly D' - toPoly Gd * derivative (toPoly D') := by
    rw [← hP₀, toPoly_sub, toPoly_mul, toPoly_mul, toPoly_deriv]
  have hder : ∀ Y : S[X], (φ Y / φ ((toPoly D').map ι))′ =
      (φ (derivative Y) * φ ((toPoly D').map ι) - φ Y * φ (derivative ((toPoly D').map ι))) /
        φ ((toPoly D').map ι) ^ 2 := fun Y ↦ by
    rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
    simp only [smul_eq_mul]
    ring
  -- `P₀ ≠ 0`: otherwise `1 / D'` solves the homogeneous equation
  have hP₀ne : toPoly P₀ ≠ 0 := by
    intro h0
    rw [hP₀poly] at h0
    have h0S := congrArg (Polynomial.map ι) h0
    simp only [Polynomial.map_sub, Polynomial.map_mul, ← derivative_map, Polynomial.map_zero] at h0S
    have h0K := congrArg φ h0S
    simp only [map_sub, map_mul, map_zero] at h0K
    have := hhom (1 / φ ((toPoly D').map ι)) (by
      rw [← map_one φ, hder, derivative_one, map_zero, map_one]
      field_simp
      linear_combination h0K)
    exact one_ne_zero (by rwa [div_eq_zero_iff, or_iff_left hφD'] at this)
  have htP₀ : trim P₀ ≠ [] := fun h0 ↦ hP₀ne ((trim_eq_nil_iff _).mp h0)
  have hP₁ne : toPoly P₁ ≠ 0 := by rw [hP₁poly]; exact mul_ne_zero hGd0 hD'0
  have htP₁ : trim P₁ ≠ [] := fun h0 ↦ hP₁ne ((trim_eq_nil_iff _).mp h0)
  have hd₀ := (natDegree_toPoly_of_trim_ne_nil htP₀).1
  have hd₁ := (natDegree_toPoly_of_trim_ne_nil htP₁).1
  have hdgeq : odeDg P₁ P₀ = max ((toPoly P₁).natDegree - 1) (toPoly P₀).natDegree := by
    rw [odeDg, hd₀, hd₁]
    congr 1
  -- the pivot bound
  have htD' : trim D' ≠ [] := fun h0 ↦ hD'0 ((trim_eq_nil_iff _).mp h0)
  obtain ⟨hdD', -, -⟩ := natDegree_toPoly_of_trim_ne_nil htD'
  have hkb : ∀ k, odePiv P₁ P₀ k = 0 → k ≤ pivBoundW Gn Gd D' := fun k hk ↦ by
    rw [odePiv, ← coeff_toPoly, ← coeff_toPoly, hdgeq, hP₁poly, hP₀poly] at hk
    unfold pivBoundW
    rcases rde_pivot_W (toPoly Gn) (toPoly Gd) (toPoly D') hGn0 hGd0 hD'0
      (hP₀poly ▸ hP₀ne) k hk with hle | ⟨hdeg, hkeq⟩
    · exact (hle.trans hdD'.le).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have htGn : trim Gn ≠ [] := fun h0 ↦ hGn0 ((trim_eq_nil_iff _).mp h0)
      have htGd : trim Gd ≠ [] := fun h0 ↦ hGd0 ((trim_eq_nil_iff _).mp h0)
      obtain ⟨hdGn, hlGn, -⟩ := natDegree_toPoly_of_trim_ne_nil htGn
      obtain ⟨hdGd, hlGd, -⟩ := natDegree_toPoly_of_trim_ne_nil htGd
      have hlen : (trim Gn).length + 1 = (trim Gd).length := by
        have := List.length_pos_of_ne_nil htGn
        have := List.length_pos_of_ne_nil htGd
        omega
      rw [ite_eq_left hlen]
      have hkeq' : ((trim D').length - 1 : ℕ) - lead (trim Gn) / lead (trim Gd) = (k : R) := by
        rw [hkeq, ← hdD', ← hlGn, ← hlGd, ← hdGn, ← hdGd, coeff_natDegree, coeff_natDegree]
      rw [(HasNatTest.natTest_spec _ k).mpr hkeq']
      exact le_rfl
  -- the solver would have found `(c, Ys)`
  refine prdeSolveFull_complete_map ι htP₀ hkb h ⟨c, Ys, ?_⟩
  rw [hP₁poly, hP₀poly]
  simp only [Polynomial.map_mul, Polynomial.map_sub, toPoly_mul, ← derivative_map]
  apply hinj
  simp only [map_add, map_mul, map_sub]
  have hy'' := hy'
  rw [hyY, hder] at hy''
  have hφD'2 : φ ((toPoly D').map ι) ^ 2 ≠ 0 := pow_ne_zero _ hφD'
  rw [hD'S, map_mul] at hy'' hφD' hφD'2 ⊢
  simp only [map_sub, map_mul] at hy''
  field_simp at hy''
  field_simp
  linear_combination hy''

end CPoly
