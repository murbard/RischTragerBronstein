import RischTragerBronstein.Computable.DerivExpSol
import RischTragerBronstein.Computable.DerivHexp

/-!
# The antiderivative of a derivative in `R(x)(t)`, `t′ = η t` with `η ∈ R(x)` arbitrary

`Tower.derivHexpSol Hn Hd μ Gn Gd`: the analogue of `derivExpSol` for a general hyperexponential,
with the Laurent-coefficient Risch equations solved by `rdeRationalW`.

* `derivHexpSol_isSome`: `derivHexpSol` succeeds exactly when `isDerivHexp` accepts;
* `derivHexpSol_sound`: the returned code is an antiderivative, in every model.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- The antiderivative code of the Laurent coefficient `j` (position `j - k`). -/
def derivHexpCoeff (Hn Hd μ : CPoly R) (e : ExpRed R) (j : ℕ) : Option (GFrac R) :=
  if j = e.k then
    let I := CPoly.integrateRational (polyA e.Λ j) (polyD e.Λ j)
    if CPoly.isZero I.r then some ((ops₁g R).add (I.gn, I.gd) (I.Q, [1])) else none
  else CPoly.rdeRationalW (CPoly.scaleMu ((((j : ℤ) - e.k : ℤ)) : R) μ)
    (CPoly.smul ((((j : ℤ) - e.k : ℤ)) : R) Hn) Hd (polyA e.Λ j) (polyD e.Λ j)

/-- The antiderivative of `Gn / Gd` in `R(x)(exp a)`, if there is one. -/
def derivHexpSol (Hn Hd μ : CPoly R) (Gn Gd : GPoly (GFrac R)) : Option (GFrac (GFrac R)) :=
  let e := hexpReduce Hn Hd Gn Gd
  let ys := (List.range (e.Λ.length + e.k + 1)).map (derivHexpCoeff Hn Hd μ e)
  if GPoly.isZero (ops₁g R) e.r && ys.all Option.isSome then
    some ((ops₂h Hn Hd).add (e.gn, e.gd)
      (ys.map (fun o ↦ o.getD (ops₁g R).zero), GPoly.monomial (ops₁g R) e.k (ops₁g R).one))
  else none

lemma derivHexpCoeff_isSome (Hn Hd μ : CPoly R) (e : ExpRed R) (j : ℕ) :
    (derivHexpCoeff Hn Hd μ e j).isSome =
      (if j = e.k then
        CPoly.isZero (CPoly.integrateRational (polyA e.Λ j) (polyD e.Λ j)).r
      else
        (CPoly.rdeRationalW (CPoly.scaleMu ((((j : ℤ) - e.k : ℤ)) : R) μ)
          (CPoly.smul ((((j : ℤ) - e.k : ℤ)) : R) Hn) Hd (polyA e.Λ j) (polyD e.Λ j)).isSome) := by
  unfold derivHexpCoeff
  by_cases hjk : j = e.k
  · rw [if_pos hjk, if_pos hjk]
    dsimp only
    split_ifs <;> simp_all
  · rw [if_neg hjk, if_neg hjk]

/-- `derivHexpSol` succeeds exactly when `isDerivHexp` accepts. -/
theorem derivHexpSol_isSome (Hn Hd μ : CPoly R) (Gn Gd : GPoly (GFrac R)) :
    (derivHexpSol Hn Hd μ Gn Gd).isSome = isDerivHexp Hn Hd μ Gn Gd := by
  rw [isDerivHexp_eq]
  simp only [derivHexpSol, List.all_map]
  have hf : (Option.isSome ∘ derivHexpCoeff Hn Hd μ (hexpReduce Hn Hd Gn Gd)) = fun j ↦
      if j = (hexpReduce Hn Hd Gn Gd).k then
        CPoly.isZero (CPoly.integrateRational (polyA (hexpReduce Hn Hd Gn Gd).Λ j)
          (polyD (hexpReduce Hn Hd Gn Gd).Λ j)).r
      else
        (CPoly.rdeRationalW
          (CPoly.scaleMu ((((j : ℤ) - (hexpReduce Hn Hd Gn Gd).k : ℤ)) : R) μ)
          (CPoly.smul ((((j : ℤ) - (hexpReduce Hn Hd Gn Gd).k : ℤ)) : R) Hn) Hd
          (polyA (hexpReduce Hn Hd Gn Gd).Λ j) (polyD (hexpReduce Hn Hd Gn Gd).Λ j)).isSome :=
    funext fun j ↦ derivHexpCoeff_isSome Hn Hd μ _ j
  rw [hf]
  split_ifs with h
  · rw [h]; rfl
  · rw [Option.isSome_none, Bool.eq_false_iff.mpr h]

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

include h0 hD

set_option maxHeartbeats 1600000 in
/-- **Soundness.** -/
theorem derivHexpSol_sound (Hn Hd μ : CPoly R) (hHd0 : CPoly.toPoly Hd ≠ 0)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.toPoly 𝓜₁ Gd ≠ 0) {y : GFrac (GFrac R)}
    (h : derivHexpSol Hn Hd μ Gn Gd = some y) :
    ((M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem y)′ = φ₂ (GPoly.toPoly 𝓜₁ Gn) / φ₂ (GPoly.toPoly 𝓜₁ Gd) := by
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  obtain ⟨hid, -, -, -⟩ := hexpReduce_spec (K₂ := K₂) ι h0 hD Hn Hd hD₂ hconst Gn Gd hGd
  simp only [derivHexpSol] at h
  generalize hexpReduce Hn Hd Gn Gd = e at hid h
  split_ifs at h with hc
  · rw [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hr0, hall⟩ := hc
    have hr0' : GPoly.toPoly 𝓜₁ e.r = 0 := (GPoly.isZero_iff 𝓜₁ _).mp hr0
    rw [hr0', map_zero, zero_div, add_zero] at hid
    rw [← Option.some.inj h, CField.sem_add, hid, sem_M₂H, sem_M₂H, toPoly_monomial_one, map_pow,
      map_add]
    dsimp only
    congr 1
    -- the Laurent part
    set n := e.Λ.length + e.k + 1 with hn
    set P : GPoly (GFrac R) := ((List.range n).map (derivHexpCoeff Hn Hd μ e)).map
      (fun o ↦ o.getD (ops₁g R).zero) with hP
    have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
    have hXk : φ₂ (X : K₁[X]) ^ e.k ≠ 0 := pow_ne_zero _ hX0
    have hXk' : (φ₂ (X : K₁[X]) ^ e.k)′ = φ₂ (C ((e.k : K₁) * ηh ι Hn Hd)) * φ₂ X ^ e.k := by
      rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
    have hpoly : (GPoly.toPoly 𝓜₁ P)′ - C ((e.k : K₁) * ηh ι Hn Hd) * GPoly.toPoly 𝓜₁ P =
        GPoly.toPoly 𝓜₁ e.Λ := by
      ext j
      rw [coeff_sub, coeff_C_mul, hD₂, coeff_implicitDeriv_C_mul_X, GPoly.coeff_toPoly,
        coeff_toPoly_polyA ι h0 hD]
      by_cases hj : j < n
      · have hmem : derivHexpCoeff Hn Hd μ e j ∈ (List.range n).map (derivHexpCoeff Hn Hd μ e) :=
          List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hall _ hmem)
        have hPj : (P.map (CField.sem 𝓜₁)).getD j 0 = CField.sem 𝓜₁ v := by
          rw [hP, List.map_map, List.map_map, List.getD_eq_getElem _ _ (by simpa using hj),
            List.getElem_map, List.getElem_range]
          simp [hv]
        rw [hPj, sem_M₁In]
        unfold derivHexpCoeff at hv
        dsimp only at hv
        split_ifs at hv with hjk hz
        · -- `j = k`: the rational integral
          subst hjk
          rw [Option.some.inj hv.symm]
          have hD0 : CPoly.toPoly (polyD e.Λ e.k) ≠ 0 := normFrac_den_ne_zero _
          have hcA := CPoly.rationalCheck_integrateRational (polyA e.Λ e.k) _ hD0
          obtain ⟨hdec, -, -⟩ := CPoly.rationalCheck_sound_map (K := K₁) ι hD _ _ _ hcA
          have hz' : (CPoly.toPoly (CPoly.integrateRational (polyA e.Λ e.k)
              (polyD e.Λ e.k)).r).map ι = 0 := by
            rw [(CPoly.isZero_iff _).mp hz, Polynomial.map_zero]
          rw [hz', map_zero, zero_div, add_zero] at hdec
          rw [← sem_M₁In (K₁ := K₁) ι h0 hD, CField.sem_add, sem_M₁In, sem_M₁In]
          simp only [CPoly.ev] at hdec ⊢
          have h1 : φ ((CPoly.toPoly ([1] : CPoly R)).map ι) = 1 := by simp [CPoly.toPoly]
          rw [h1, div_one, hdec]
          ring
        · -- `j ≠ k`: the Risch differential equation
          have hD0 : CPoly.toPoly (polyD e.Λ j) ≠ 0 := normFrac_den_ne_zero _
          obtain ⟨Y, G⟩ := v
          have hs := CPoly.rdeRationalW_sound (K := K₁) ι hD hD0 hHd0 hv
          have hcast : φ (C (ι ((((j : ℤ) - e.k : ℤ)) : R))) = (j : K₁) - e.k := by
            simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
          rw [ev_hexpCoeff, hcast] at hs
          simp only [CPoly.ev]
          rw [← hs]
          ring
      · have hPj : (P.map (CField.sem 𝓜₁)).getD j 0 = 0 := by
          rw [List.getD_eq_default]
          simp only [hP, List.length_map, List.length_range]
          omega
        have hΛj : CPoly.ev K₁ ι (polyA e.Λ j, polyD e.Λ j) = 0 := by
          rw [← coeff_toPoly_polyA ι h0 hD, GPoly.coeff_toPoly,
            List.getD_eq_default _ _ (by rw [List.length_map]; omega)]
        rw [hPj, hΛj, map_zero]
        ring
    rw [Derivation.leibniz_div, hXk', deriv_algebraMap, hD₂]
    simp only [smul_eq_mul]
    rw [← hpoly, map_sub, map_mul, hD₂]
    field_simp
    simp only [map_mul]
    ring

end Tower
