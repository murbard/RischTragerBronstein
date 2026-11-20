import RischTragerBronstein.Computable.HexpReduce
import RischTragerBronstein.Computable.DerivHexp
import RischTragerBronstein.Computable.PRDERationalW
import RischTragerBronstein.Computable.LimitedExpW
import RischTragerBronstein.Computable.ConstQuot
import RischTragerBronstein.Computable.PRDERational
import RischTragerBronstein.RDE.ExponentialTwoProper

/-!
# Limited integration inside `R(x)(t)`, `t′ = η t` with `η ∈ R(x)` arbitrary

`limitedHexpW Hn Hd μ Gn Gd Wn Wd`: the constant `c` with `G - c W` a derivative in `R(x)(t)`
(`W` not a derivative), the analogue of `limitedExpW` for a general hyperexponential
`t′ = (Hn / Hd) t`; the Risch equations over `R(x)` are solved by `rdeRationalW` /
`prdeRationalW`. `limitedHexpW_complete`: complete over every extension of the constants.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- The candidate constant from the Laurent position `j` of `W` (`none` if the position is free). -/
def limitedHexpWAt (Hn Hd μ : CPoly R) (eG eW : ExpRed R) (j : ℕ) : Option R :=
  let B := (polyA eW.Λ j, polyD eW.Λ j)
  let A := laurentCoeffZ eG.Λ eG.k ((j : ℤ) - eW.k)
  if j = eW.k then
    let IA := CPoly.integrateRational A.1 A.2
    let IB := CPoly.integrateRational B.1 B.2
    if CPoly.isZero IB.r then none else CPoly.limitedCrit IA.r IA.s IB.r IB.s
  else
    let c : R := (((j : ℤ) - eW.k : ℤ) : R)
    if (CPoly.rdeRationalW (CPoly.scaleMu c μ) (CPoly.smul c Hn) Hd B.1 B.2).isSome then none
    else (CPoly.prdeRationalW (CPoly.scaleMu c μ) (CPoly.smul c Hn) Hd (CPoly.mul A.1 B.2)
      (CPoly.mul B.1 A.2) (CPoly.mul A.2 B.2)).map Prod.fst

/-- The constant `c` with `G - c W` a derivative in `R(x)(exp a)`, if `W` is not a derivative. -/
def limitedHexpW (Hn Hd μ : CPoly R) (Gn Gd Wn Wd : GPoly (GFrac R)) : Option R :=
  let eG := hexpReduce Hn Hd Gn Gd
  let eW := hexpReduce Hn Hd Wn Wd
  if GPoly.isZero (ops₁g R) eW.r then
    (List.range (eW.Λ.length + eW.k + 1)).findSome? (limitedHexpWAt Hn Hd μ eG eW)
  else constQuot (GPoly.mul (ops₁g R) eG.r eW.s) (GPoly.mul (ops₁g R) eW.r eG.s)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [DecidableEq S]
variable [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [CPoly.HasRatRoots R] [HasNatTest R]
variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
local notation "𝓜₁" => M₁In (K₁ := K₁) ι h0 hD

set_option maxHeartbeats 3200000 in
/-- **Completeness.** -/
theorem limitedHexpW_complete (Hn Hd μ : CPoly R)
    (hHn0 : CPoly.toPoly Hn ≠ 0) (hHd0 : CPoly.toPoly Hd ≠ 0)
    (hcop : IsCoprime (CPoly.toPoly Hn) (CPoly.toPoly Hd))
    (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (Gn Gd Wn Wd : GPoly (GFrac R)) (hGd : GPoly.toPoly (𝓜₁) Gd ≠ 0)
    (hWd : GPoly.toPoly (𝓜₁) Wd ≠ 0)
    (hW : isDerivHexp Hn Hd μ Wn Wd = false) (c : S) (y : K₂)
    (hy : y′ = φ₂ (GPoly.toPoly (𝓜₁) Gn) /
        φ₂ (GPoly.toPoly (𝓜₁) Gd) -
      φ₂ (C (φ (C c))) * (φ₂ (GPoly.toPoly (𝓜₁) Wn) /
        φ₂ (GPoly.toPoly (𝓜₁) Wd))) :
    ∃ c' : R, limitedHexpW Hn Hd μ Gn Gd Wn Wd = some c' ∧ ι c' = c := by
  have hinj₁ : Function.Injective φ := IsFractionRing.injective S[X] K₁
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hnorm' := normal_of_hconst (ηh ι Hn Hd) hD₂ hconst
  have hη := hexp_pow_not_in_base (K₁ := K₁) ι hD Hn Hd hHn0 hHd0 hcop hcert
  obtain ⟨hμ0, hμq⟩ := CPoly.muCheck_spec (CPoly.hyperexpMonomialCheck_mu hcert)
  obtain ⟨hGid, hsG, hXG, hdG⟩ := hexpReduce_spec (K₂ := K₂) ι h0 hD Hn Hd hD₂ hconst Gn Gd hGd
  obtain ⟨hWid, hsW, hXW, hdW⟩ := hexpReduce_spec (K₂ := K₂) ι h0 hD Hn Hd hD₂ hconst Wn Wd hWd
  rw [isDerivHexp_eq] at hW
  simp only [limitedHexpW]
  generalize hexpReduce Hn Hd Gn Gd = eG at hGid hsG hXG hdG ⊢
  generalize hexpReduce Hn Hd Wn Wd = eW at hWid hsW hXW hdW hW ⊢
  -- the constant
  set c' : K₁ := φ (C c) with hc'
  have hc'0 : c'′ = 0 := by rw [hc', deriv_algebraMap, hD, derivative_C, map_zero]
  have hC0 : (φ₂ (C c'))′ = 0 := by
    rw [deriv_algebraMap, hD₂, implicitDeriv_C, hc'0, C_0, map_zero]
  -- the derivative of `z = y - (g_G - c g_W)`
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
  have hφsG : φ₂ (GPoly.toPoly 𝓜₁ eG.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hsG.ne_zero
  have hφsW : φ₂ (GPoly.toPoly 𝓜₁ eW.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hsW.ne_zero
  set Λ : K₁[X] := GPoly.toPoly 𝓜₁ eG.Λ * X ^ eW.k - C c' * (GPoly.toPoly 𝓜₁ eW.Λ * X ^ eG.k)
    with hΛ
  set z : K₂ := y - (φ₂ (GPoly.toPoly 𝓜₁ eG.gn) / φ₂ (GPoly.toPoly 𝓜₁ eG.gd) -
    φ₂ (C c') * (φ₂ (GPoly.toPoly 𝓜₁ eW.gn) / φ₂ (GPoly.toPoly 𝓜₁ eW.gd))) with hz
  have hz' : z′ = φ₂ Λ / φ₂ X ^ (eG.k + eW.k) + φ₂ (GPoly.toPoly 𝓜₁ eG.r) / φ₂ (GPoly.toPoly 𝓜₁ eG.s) +
      φ₂ (-(C c' * GPoly.toPoly 𝓜₁ eW.r)) / φ₂ (GPoly.toPoly 𝓜₁ eW.s) := by
    rw [hz, map_sub, map_sub, Derivation.leibniz, hC0, hy, hGid, hWid]
    simp only [smul_eq_mul, hΛ, map_sub, map_mul, map_neg, map_pow]
    field_simp
    ring
  by_cases hrW : GPoly.isZero (ops₁g R) eW.r = true
  · -- the proper part of `W` vanishes: look at the Laurent coefficients
    rw [if_pos hrW]
    have hrW0 : GPoly.toPoly 𝓜₁ eW.r = 0 := (GPoly.isZero_iff 𝓜₁ _).mp hrW
    rw [hrW0, mul_zero, neg_zero, map_zero, zero_div, add_zero] at hz'
    obtain ⟨hrG0, P, hP, hcoef⟩ := laurent_coeff_eqs_exp (K₂ := K₂) (ηh ι Hn Hd) hD₂ hnorm' hη
      Λ _ _ (eG.k + eW.k) hsG hXG hdG z hz'
    rw [hrW, Bool.true_and, List.all_eq_false] at hW
    obtain ⟨j₀, hj₀, hj₀f⟩ := hW
    -- the coefficient equation at position `j` of `W`
    have heq : ∀ j : ℕ, (P.coeff (j + eG.k))′ + ((j : K₁) - eW.k) * ηh ι Hn Hd * P.coeff (j + eG.k) =
        CPoly.ev K₁ ι (laurentCoeffZ eG.Λ eG.k ((j : ℤ) - eW.k)) -
          c' * CPoly.ev K₁ ι (polyA eW.Λ j, polyD eW.Λ j) := by
      intro j
      have h1 := hcoef (j + eG.k)
      rw [hΛ, coeff_sub, coeff_C_mul, coeff_mul_X_pow' (GPoly.toPoly 𝓜₁ eW.Λ) eG.k,
        if_pos (by omega : eG.k ≤ j + eG.k), Nat.add_sub_cancel] at h1
      rw [ev_laurentCoeffZ ι h0 hD, ← coeff_toPoly_polyA ι h0 hD eW.Λ j, ← h1]
      push_cast
      ring
    -- every candidate is the constant
    have hsound : ∀ j ∈ List.range (eW.Λ.length + eW.k + 1), ∀ v : R,
        limitedHexpWAt Hn Hd μ eG eW j = some v → ι v = c := by
      intro j _ v hv
      have hB2 : CPoly.toPoly (polyD eW.Λ j) ≠ 0 := normFrac_den_ne_zero _
      have hA2 : CPoly.toPoly (laurentCoeffZ eG.Λ eG.k ((j : ℤ) - eW.k)).2 ≠ 0 :=
        laurentCoeffZ_den_ne_zero _ _ _
      simp only [limitedHexpWAt] at hv
      split_ifs at hv with hjk hzB hsomeB
      · -- position `k`: rational limited integration
        subst hjk
        simp only [sub_self] at hA2 hv
        have hcA := CPoly.rationalCheck_integrateRational (laurentCoeffZ eG.Λ eG.k 0).1 _ hA2
        have hcB := CPoly.rationalCheck_integrateRational (polyA eW.Λ eW.k) _ hB2
        obtain ⟨hdecA, hsqA, hdegA⟩ := CPoly.rationalCheck_sound_map (K := K₁) ι hD _ _ _ hcA
        obtain ⟨hdecB, hsqB, hdegB⟩ := CPoly.rationalCheck_sound_map (K := K₁) ι hD _ _ _ hcB
        have h1 := heq eW.k
        simp only [sub_self, zero_mul, add_zero, CPoly.ev] at h1
        rw [hdecA, hdecB] at h1
        have hid := (limited_integral_iff (K := K₁) hD _ _ _ _ _ _ hsqA hsqB hdegA hdegB c).mp
          ⟨_, h1⟩
        have hv' := CPoly.limitedCrit_sound hv
        have hv'' := congrArg (Polynomial.map ι) hv'
        simp only [Polynomial.map_mul, map_C] at hv''
        have hne : (CPoly.toPoly (CPoly.integrateRational (polyA eW.Λ eW.k) (polyD eW.Λ eW.k)).r).map ι *
            (CPoly.toPoly (CPoly.integrateRational (laurentCoeffZ eG.Λ eG.k 0).1
              (laurentCoeffZ eG.Λ eG.k 0).2).s).map ι ≠ 0 := by
          refine mul_ne_zero ?_ hsqA.ne_zero
          rw [Ne, Polynomial.map_eq_zero_iff ι.injective, ← CPoly.isZero_iff]
          exact fun h ↦ hzB (by rw [h])
        have : C c * ((CPoly.toPoly (CPoly.integrateRational (polyA eW.Λ eW.k) (polyD eW.Λ eW.k)).r).map ι *
            (CPoly.toPoly (CPoly.integrateRational (laurentCoeffZ eG.Λ eG.k 0).1
              (laurentCoeffZ eG.Λ eG.k 0).2).s).map ι) =
            C (ι v) * ((CPoly.toPoly (CPoly.integrateRational (polyA eW.Λ eW.k) (polyD eW.Λ eW.k)).r).map ι *
            (CPoly.toPoly (CPoly.integrateRational (laurentCoeffZ eG.Λ eG.k 0).1
              (laurentCoeffZ eG.Λ eG.k 0).2).s).map ι) := by
          linear_combination hv'' - hid
        exact (C_inj.mp (mul_right_cancel₀ hne this)).symm
      · -- position `j ≠ k`: the parametric Risch equation
        rw [Option.map_eq_some_iff] at hv
        obtain ⟨⟨v', Y⟩, hsol, hv1⟩ := hv
        simp only at hv1
        rw [← hv1]
        rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hsomeB
        have hD0 : CPoly.toPoly (CPoly.mul (laurentCoeffZ eG.Λ eG.k ((j : ℤ) - eW.k)).2
            (polyD eW.Λ j)) ≠ 0 := by
          rw [CPoly.toPoly_mul]; exact mul_ne_zero hA2 hB2
        have hs := CPoly.prdeRationalW_sound (K := K₁) ι hD hD0 hHd0 hsol
        have hφA2 : φ ((CPoly.toPoly (laurentCoeffZ eG.Λ eG.k ((j : ℤ) - eW.k)).2).map ι) ≠ 0 :=
          (map_ne_zero_iff _ hinj₁).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hA2)
        have hφB2 : φ ((CPoly.toPoly (polyD eW.Λ j)).map ι) ≠ 0 :=
          (map_ne_zero_iff _ hinj₁).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hB2)
        have hcast : φ (C (ι ((((j : ℤ) - eW.k : ℤ)) : R))) = (j : K₁) - eW.k := by
          simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
        set Ysol : K₁ := φ ((CPoly.toPoly Y).map ι) / φ ((CPoly.toPoly (CPoly.prdeDenW
          (CPoly.scaleMu ((((j : ℤ) - eW.k : ℤ)) : R) μ) (CPoly.smul ((((j : ℤ) - eW.k : ℤ)) : R) Hn)
          Hd (CPoly.mul (laurentCoeffZ eG.Λ eG.k ((j : ℤ) - eW.k)).2 (polyD eW.Λ j)))).map ι)
          with hYsol
        rw [ev_hexpCoeff, hcast] at hs
        simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul] at hs
        have hs' : Ysol′ + ((j : K₁) - eW.k) * ηh ι Hn Hd * Ysol =
            CPoly.ev K₁ ι (laurentCoeffZ eG.Λ eG.k ((j : ℤ) - eW.k)) -
              φ (C (ι v')) * CPoly.ev K₁ ι (polyA eW.Λ j, polyD eW.Λ j) := by
          rw [hs]
          simp only [CPoly.ev]
          field_simp
        have h1 := heq j
        by_contra hne
        have hd0 : c' - φ (C (ι v')) ≠ 0 := by
          rw [sub_ne_zero, hc']
          intro h
          exact hne (C_inj.mp (hinj₁ h)).symm
        have hd' : (c' - φ (C (ι v')))′ = 0 := by
          rw [map_sub, hc'0, deriv_algebraMap, hD, derivative_C, map_zero, sub_zero]
        set u : K₁ := (Ysol - P.coeff (j + eG.k)) / (c' - φ (C (ι v'))) with hu
        have hu' : u′ = (Ysol′ - (P.coeff (j + eG.k))′) / (c' - φ (C (ι v'))) := by
          rw [hu, Derivation.leibniz_div, hd', map_sub]
          simp only [smul_eq_mul, mul_zero, sub_zero]
          field_simp
        have hz : ((((j : ℤ) - eW.k : ℤ)) : R) ≠ 0 :=
          Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjk))
        have hu1 : IsUnit (C ((((j : ℤ) - eW.k : ℤ)) : R) : R[X]) := isUnit_C.mpr hz.isUnit
        have hhom : ∀ y : K₁, y′ + φ ((CPoly.toPoly (CPoly.smul ((((j : ℤ) - eW.k : ℤ)) : R) Hn)).map ι) /
            φ ((CPoly.toPoly Hd).map ι) * y = 0 → y = 0 := fun y hy ↦
          CPoly.hyperexpW_homogeneous (K := K₁) ι hD hHn0 hHd0 hcop hcert (-((j : ℤ) - eW.k))
            (neg_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjk))) y (by
              rw [ev_hexpCoeff, hcast] at hy
              rw [Int.cast_neg, C_neg, map_neg]
              simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
              linear_combination hy)
        refine CPoly.rdeRationalW_complete (K := K₁) ι hD hB2
          (by rw [CPoly.toPoly_smul]; exact mul_ne_zero (C_ne_zero.mpr hz) hHn0) hHd0
          (by rw [CPoly.toPoly_smul]; exact (isCoprime_mul_unit_left_left hu1 _ _).mpr hcop)
          (CPoly.scaleMu_ne_zero hz hμ0)
          (CPoly.dvd_scaleMu_comp hμq (CPoly.residuePolyW_smul Hn Hd hHd0 _)) hhom hsomeB u ?_
        rw [hu', ev_hexpCoeff, hcast, hu]
        simp only [CPoly.ev] at h1 hs'
        rw [← mul_div_assoc, ← add_div, div_eq_iff hd0]
        linear_combination hs' - h1
    -- the failing position of `W` yields a candidate
    have hex : limitedHexpWAt Hn Hd μ eG eW j₀ ≠ none := by
      have hB2 : CPoly.toPoly (polyD eW.Λ j₀) ≠ 0 := normFrac_den_ne_zero _
      have hA2 : CPoly.toPoly (laurentCoeffZ eG.Λ eG.k ((j₀ : ℤ) - eW.k)).2 ≠ 0 :=
        laurentCoeffZ_den_ne_zero _ _ _
      simp only [limitedHexpWAt]
      split_ifs with hjk hzB hsomeB
      · exact absurd (by rw [if_pos hjk, hzB]) hj₀f
      · -- `W_k` has a non-zero residue part: `limitedCrit` succeeds
        subst hjk
        simp only [sub_self] at hA2 ⊢
        have hcA := CPoly.rationalCheck_integrateRational (laurentCoeffZ eG.Λ eG.k 0).1 _ hA2
        have hcB := CPoly.rationalCheck_integrateRational (polyA eW.Λ eW.k) _ hB2
        obtain ⟨hdecA, hsqA, hdegA⟩ := CPoly.rationalCheck_sound_map (K := K₁) ι hD _ _ _ hcA
        obtain ⟨hdecB, hsqB, hdegB⟩ := CPoly.rationalCheck_sound_map (K := K₁) ι hD _ _ _ hcB
        have h1 := heq eW.k
        simp only [sub_self, zero_mul, add_zero, CPoly.ev] at h1
        rw [hdecA, hdecB] at h1
        have hid := (limited_integral_iff (K := K₁) hD _ _ _ _ _ _ hsqA hsqB hdegA hdegB c).mp
          ⟨_, h1⟩
        obtain ⟨c₀, hc₀⟩ := CPoly.limited_descent ι hid
        intro hnone
        exact CPoly.limitedCrit_complete hnone ⟨c₀, hc₀⟩
      · exact absurd (by rw [if_neg hjk, hsomeB]) hj₀f
      · -- the parametric equation is solvable: the solver succeeds
        rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hsomeB
        rw [Ne, Option.map_eq_none_iff]
        intro hnone
        have hD0 : CPoly.toPoly (CPoly.mul (laurentCoeffZ eG.Λ eG.k ((j₀ : ℤ) - eW.k)).2
            (polyD eW.Λ j₀)) ≠ 0 := by
          rw [CPoly.toPoly_mul]; exact mul_ne_zero hA2 hB2
        have hz : ((((j₀ : ℤ) - eW.k : ℤ)) : R) ≠ 0 :=
          Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjk))
        have hu1 : IsUnit (C ((((j₀ : ℤ) - eW.k : ℤ)) : R) : R[X]) := isUnit_C.mpr hz.isUnit
        have hcast : φ (C (ι ((((j₀ : ℤ) - eW.k : ℤ)) : R))) = (j₀ : K₁) - eW.k := by
          simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
        have hφA2 : φ ((CPoly.toPoly (laurentCoeffZ eG.Λ eG.k ((j₀ : ℤ) - eW.k)).2).map ι) ≠ 0 :=
          (map_ne_zero_iff _ hinj₁).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hA2)
        have hφB2 : φ ((CPoly.toPoly (polyD eW.Λ j₀)).map ι) ≠ 0 :=
          (map_ne_zero_iff _ hinj₁).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hB2)
        have hhom : ∀ y : K₁, y′ + φ ((CPoly.toPoly (CPoly.smul ((((j₀ : ℤ) - eW.k : ℤ)) : R) Hn)).map ι) /
            φ ((CPoly.toPoly Hd).map ι) * y = 0 → y = 0 := fun y hy ↦
          CPoly.hyperexpW_homogeneous (K := K₁) ι hD hHn0 hHd0 hcop hcert (-((j₀ : ℤ) - eW.k))
            (neg_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjk))) y (by
              rw [ev_hexpCoeff, hcast] at hy
              rw [Int.cast_neg, C_neg, map_neg]
              simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
              linear_combination hy)
        refine CPoly.prdeRationalW_complete (K := K₁) ι hD hD0
          (by rw [CPoly.toPoly_smul]; exact mul_ne_zero (C_ne_zero.mpr hz) hHn0) hHd0
          (by rw [CPoly.toPoly_smul]; exact (isCoprime_mul_unit_left_left hu1 _ _).mpr hcop)
          (CPoly.scaleMu_ne_zero hz hμ0)
          (CPoly.dvd_scaleMu_comp hμq (CPoly.residuePolyW_smul Hn Hd hHd0 _)) hhom
          hnone c (P.coeff (j₀ + eG.k)) ?_
        have h1 := heq j₀
        rw [ev_hexpCoeff, hcast]
        simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul]
        simp only [CPoly.ev] at h1
        rw [← hc']
        field_simp
        field_simp at h1
        linear_combination h1
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hex
    cases hfs : (List.range (eW.Λ.length + eW.k + 1)).findSome? (limitedHexpWAt Hn Hd μ eG eW) with
    | none => exact absurd (List.findSome?_eq_none_iff.mp hfs j₀ hj₀) hex
    | some v' =>
      obtain ⟨j, hj, hjv⟩ := List.exists_of_findSome?_eq_some hfs
      exact ⟨v', rfl, hsound j hj v' hjv⟩
  · -- the proper part of `W` is non-zero: the two proper parts must cancel
    rw [if_neg hrW]
    have hrW0 : GPoly.toPoly 𝓜₁ eW.r ≠ 0 := fun h ↦ hrW ((GPoly.isZero_iff 𝓜₁ _).mpr h)
    have hd₂ : (-(C c' * GPoly.toPoly 𝓜₁ eW.r)).degree < (GPoly.toPoly 𝓜₁ eW.s).degree := by
      rw [degree_neg]
      refine lt_of_le_of_lt ((degree_mul_le _ _).trans ?_) hdW
      calc (C c').degree + (GPoly.toPoly 𝓜₁ eW.r).degree
          ≤ 0 + (GPoly.toPoly 𝓜₁ eW.r).degree := add_le_add degree_C_le le_rfl
        _ = (GPoly.toPoly 𝓜₁ eW.r).degree := zero_add _
    obtain ⟨hb, -⟩ := deriv_eq_laurent_add_two_proper_exp (K := K₂) (ηh ι Hn Hd) hD₂ hnorm' hη
      Λ _ _ _ _ (eG.k + eW.k) hsG hsW hXG hXW hdG hd₂ z hz'
    have hmul : GPoly.toPoly 𝓜₁ (GPoly.mul (ops₁g R) eG.r eW.s) =
        C c' * GPoly.toPoly 𝓜₁ (GPoly.mul (ops₁g R) eW.r eG.s) := by
      rw [GPoly.toPoly_mul, GPoly.toPoly_mul]
      linear_combination hb
    exact constQuot_complete (K₁ := K₁) ι h0 hD _ _ c
      (by rw [GPoly.toPoly_mul]; exact mul_ne_zero hrW0 hsG.ne_zero) hmul

end Tower
