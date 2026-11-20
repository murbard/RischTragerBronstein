import RischTragerBronstein.Computable.ExpReduce
import RischTragerBronstein.Computable.IntegrateExpExp

/-!
# The antiderivative of a derivative in `R(x)(exp a)`

`Tower.derivExpSol a Gn Gd`: the executable antiderivative of `Gn / Gd ∈ R(x)(exp a)` when one
exists in the field: `gn / gd + (∑ⱼ yⱼ tʲ) / t^k` with `yⱼ` from the Risch differential
equations of the Laurent coefficients (`rdeRational`) and `y_k` the rational integral.

* `derivExpSol_isSome`: `derivExpSol` succeeds exactly when `isDerivExp` accepts;
* `derivExpSol_sound`: the returned code is an antiderivative, in every model.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The antiderivative code of the Laurent coefficient `j` (position `j - k`). -/
def derivExpCoeff (a : CPoly R) (e : ExpRed R) (j : ℕ) : Option (GFrac R) :=
  if j = e.k then
    let I := CPoly.integrateRational (polyA e.Λ j) (polyD e.Λ j)
    if CPoly.isZero I.r then some ((ops₁g R).add (I.gn, I.gd) (I.Q, [1])) else none
  else CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - e.k)) (polyA e.Λ j) (polyD e.Λ j)

/-- The antiderivative of `Gn / Gd` in `R(x)(exp a)`, if there is one. -/
def derivExpSol (a : CPoly R) (Gn Gd : GPoly (GFrac R)) : Option (GFrac (GFrac R)) :=
  let e := expReduce a Gn Gd
  let ys := (List.range (e.Λ.length + e.k + 1)).map (derivExpCoeff a e)
  if GPoly.isZero (ops₁g R) e.r && ys.all Option.isSome then
    some ((ops₂e a).add (e.gn, e.gd)
      (ys.map (fun o ↦ o.getD (ops₁g R).zero), GPoly.monomial (ops₁g R) e.k (ops₁g R).one))
  else none

lemma derivExpCoeff_isSome (a : CPoly R) (e : ExpRed R) (j : ℕ) :
    (derivExpCoeff a e j).isSome =
      (if j = e.k then
        CPoly.isZero (CPoly.integrateRational (polyA e.Λ j) (polyD e.Λ j)).r
      else
        (CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - e.k)) (polyA e.Λ j)
          (polyD e.Λ j)).isSome) := by
  unfold derivExpCoeff
  by_cases hjk : j = e.k
  · rw [if_pos hjk, if_pos hjk]
    dsimp only
    split_ifs <;> simp_all
  · rw [if_neg hjk, if_neg hjk]

/-- `derivExpSol` succeeds exactly when `isDerivExp` accepts. -/
theorem derivExpSol_isSome (a : CPoly R) (Gn Gd : GPoly (GFrac R)) :
    (derivExpSol a Gn Gd).isSome = isDerivExp a Gn Gd := by
  rw [isDerivExp_eq]
  simp only [derivExpSol, List.all_map]
  have hf : (Option.isSome ∘ derivExpCoeff a (expReduce a Gn Gd)) = fun j ↦
      if j = (expReduce a Gn Gd).k then
        CPoly.isZero (CPoly.integrateRational (polyA (expReduce a Gn Gd).Λ j)
          (polyD (expReduce a Gn Gd).Λ j)).r
      else
        (CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - (expReduce a Gn Gd).k))
          (polyA (expReduce a Gn Gd).Λ j) (polyD (expReduce a Gn Gd).Λ j)).isSome :=
    funext fun j ↦ derivExpCoeff_isSome a _ j
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
variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
local notation "𝓜₁" => M₁In (K₁ := K₁) ι h0 hD

include h0 hD

/-- The model of `R(x)(exp a)` in `K₂`, from the one-level hypotheses. -/
noncomputable def M₂E {a : CPoly R}
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P) :
    CField (GFrac (GFrac R)) K₂ (ops₂e a) :=
  CField.monomialIn 𝓜₁ (expW a) K₂ fun P ↦ by
    rw [toPoly_expW_In]; exact hD₂ P

lemma sem_M₂E {a : CPoly R} (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (q : GFrac (GFrac R)) :
    (M₂E (K₂ := K₂) ι h0 hD hD₂).sem q =
      φ₂ (GPoly.toPoly 𝓜₁ q.1) / φ₂ (GPoly.toPoly 𝓜₁ q.2) := rfl

lemma toPoly_monomial_one (k : ℕ) :
    GPoly.toPoly 𝓜₁ (GPoly.monomial (ops₁g R) k (ops₁g R).one) = X ^ k := by
  rw [GPoly.toPoly_monomial, CField.sem_one, C_1, one_mul]

set_option maxHeartbeats 1600000 in
/-- **Soundness.** -/
theorem derivExpSol_sound (a : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.toPoly 𝓜₁ Gd ≠ 0) {y : GFrac (GFrac R)}
    (h : derivExpSol a Gn Gd = some y) :
    ((M₂E (K₂ := K₂) ι h0 hD hD₂).sem y)′ = φ₂ (GPoly.toPoly 𝓜₁ Gn) / φ₂ (GPoly.toPoly 𝓜₁ Gd) := by
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  obtain ⟨hid, -, -, -⟩ := expReduce_spec (K₂ := K₂) ι h0 hD a hD₂ hconst Gn Gd hGd
  simp only [derivExpSol] at h
  generalize expReduce a Gn Gd = e at hid h
  split_ifs at h with hc
  · rw [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hr0, hall⟩ := hc
    have hr0' : GPoly.toPoly 𝓜₁ e.r = 0 := (GPoly.isZero_iff 𝓜₁ _).mp hr0
    rw [hr0', map_zero, zero_div, add_zero] at hid
    rw [← Option.some.inj h, CField.sem_add, hid, sem_M₂E, sem_M₂E, toPoly_monomial_one, map_pow,
      map_add]
    dsimp only
    congr 1
    -- the Laurent part
    set n := e.Λ.length + e.k + 1 with hn
    set P : GPoly (GFrac R) := ((List.range n).map (derivExpCoeff a e)).map
      (fun o ↦ o.getD (ops₁g R).zero) with hP
    have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
    have hXk : φ₂ (X : K₁[X]) ^ e.k ≠ 0 := pow_ne_zero _ hX0
    have hXk' : (φ₂ (X : K₁[X]) ^ e.k)′ = φ₂ (C ((e.k : K₁) * ηa ι a)) * φ₂ X ^ e.k := by
      rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
    have hpoly : (GPoly.toPoly 𝓜₁ P)′ - C ((e.k : K₁) * ηa ι a) * GPoly.toPoly 𝓜₁ P =
        GPoly.toPoly 𝓜₁ e.Λ := by
      ext j
      rw [coeff_sub, coeff_C_mul, hD₂, coeff_implicitDeriv_C_mul_X, GPoly.coeff_toPoly,
        coeff_toPoly_polyA ι h0 hD]
      by_cases hj : j < n
      · have hmem : derivExpCoeff a e j ∈ (List.range n).map (derivExpCoeff a e) :=
          List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hall _ hmem)
        have hPj : (P.map (CField.sem 𝓜₁)).getD j 0 = CField.sem 𝓜₁ v := by
          rw [hP, List.map_map, List.map_map, List.getD_eq_getElem _ _ (by simpa using hj),
            List.getElem_map, List.getElem_range]
          simp [hv]
        rw [hPj, sem_M₁In]
        unfold derivExpCoeff at hv
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
          have hs := CPoly.rdeRational_sound (K := K₁) ι hD hD0 hv
          rw [ev_expCoeffZ] at hs
          simp only [CPoly.ev]
          rw [← hs]
          push_cast
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
