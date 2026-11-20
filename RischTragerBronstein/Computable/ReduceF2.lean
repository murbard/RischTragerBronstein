import RischTragerBronstein.Computable.GBezout
import RischTragerBronstein.Computable.Prim2StepGen

/-!
# Reduction of a code of `R(x)(t₁)` by the gcd of numerator and denominator

`reduceF₂ q` divides both components of `q : GFrac (GFrac R)` by their gcd (as polynomials in
`t₁` over `R(x)`), and returns `0 / 1` when the denominator is zero. Semantics are preserved
(`reduceF₂_spec`); the point is to keep the codes produced by the limited-integration loops small
(an unreduced representation of `0` with a large denominator otherwise blows up the later
Hermite reductions).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Divide numerator and denominator of a fraction of `R(x)` by their gcd. -/
def normCoeff (q : GFrac R) : GFrac R :=
  if CPoly.isZero q.2 then ([], [1])
  else
    let g := (CPoly.egcd q.1 q.2).1
    let d := CPoly.trim (CPoly.divMod q.2 g).1
    let c := (CPoly.lead d)⁻¹
    (CPoly.smul c (CPoly.divMod q.1 g).1, CPoly.smul c d)

/-- Normalise every coefficient of numerator and denominator, and return `0 / 1` when the
numerator (or the denominator) is zero. (A gcd of numerator and denominator as polynomials in
`t₁` is *not* taken: the Euclidean algorithm over unreduced fractions of `R(x)` blows up.) -/
def reduceF₂ (q : GFrac (GFrac R)) : GFrac (GFrac R) :=
  if GPoly.isZero (ops₁g R) q.2 then ([], [(ops₁g R).one])
  else
    let n := q.1.map normCoeff
    if GPoly.isZero (ops₁g R) n then ([], [(ops₁g R).one]) else (n, q.2.map normCoeff)

end Defs

section Coeff

variable {R S K₁ : Type*} [Field R] [DecidableEq R] [Field S] [Differential S] [Differential S[X]]
variable [Field K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁] [Differential K₁]
variable [DifferentialAlgebra S[X] K₁]

/-- `normCoeff` preserves the value. -/
lemma ev_normCoeff (ι : R →+* S) (q : GFrac R) :
    CPoly.ev K₁ ι (normCoeff q) = CPoly.ev K₁ ι q := by
  have hinj : Function.Injective (algebraMap S[X] K₁) := IsFractionRing.injective S[X] K₁
  unfold normCoeff
  split_ifs with hz
  · have hz' := (CPoly.isZero_iff _).mp hz
    simp only [CPoly.ev, hz']
    simp [CPoly.toPoly]
  · have hq2 : CPoly.toPoly q.2 ≠ 0 := fun h ↦ hz ((CPoly.isZero_iff _).mpr h)
    simp only
    obtain ⟨hg1, hg2⟩ := CPoly.egcd_dvd q.1 q.2
    have hg0 : CPoly.toPoly (CPoly.egcd q.1 q.2).1 ≠ 0 := fun h ↦ by
      rw [h] at hg2; exact hq2 (zero_dvd_iff.mp hg2)
    have exact : ∀ p : CPoly R, CPoly.toPoly (CPoly.egcd q.1 q.2).1 ∣ CPoly.toPoly p →
        CPoly.toPoly p = CPoly.toPoly (CPoly.divMod p (CPoly.egcd q.1 q.2).1).1 *
          CPoly.toPoly (CPoly.egcd q.1 q.2).1 := fun p hp ↦ by
      have hspec := CPoly.divMod_spec p (CPoly.egcd q.1 q.2).1
      have hrem : CPoly.toPoly (CPoly.egcd q.1 q.2).1 ∣
          CPoly.toPoly (CPoly.divMod p (CPoly.egcd q.1 q.2).1).2 := by
        have : CPoly.toPoly (CPoly.divMod p (CPoly.egcd q.1 q.2).1).2 = CPoly.toPoly p -
            CPoly.toPoly (CPoly.divMod p (CPoly.egcd q.1 q.2).1).1 *
              CPoly.toPoly (CPoly.egcd q.1 q.2).1 := by rw [hspec]; ring
        rw [this]
        exact dvd_sub hp (Dvd.intro_left _ rfl)
      have h0 := eq_zero_of_dvd_of_degree_lt hrem (CPoly.divMod_degree_lt p _ hg0)
      rwa [h0, add_zero] at hspec
    have e1 := exact q.1 hg1
    have e2 := exact q.2 hg2
    have hφg : algebraMap S[X] K₁ ((CPoly.toPoly (CPoly.egcd q.1 q.2).1).map ι) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hg0)
    -- the quotient of the denominator is nonzero, so its leading coefficient is a unit
    have hd0 : CPoly.toPoly (CPoly.divMod q.2 (CPoly.egcd q.1 q.2).1).1 ≠ 0 := fun h ↦
      hq2 (by rw [e2, h, zero_mul])
    have hdne : CPoly.trim (CPoly.divMod q.2 (CPoly.egcd q.1 q.2).1).1 ≠ [] := fun h ↦
      hd0 ((CPoly.trim_eq_nil_iff _).mp h)
    obtain ⟨-, -, hlc0⟩ := CPoly.natDegree_toPoly_of_trim_ne_nil hdne
    have hc0 : (CPoly.lead (CPoly.trim (CPoly.divMod q.2 (CPoly.egcd q.1 q.2).1).1))⁻¹ ≠ 0 :=
      inv_ne_zero hlc0
    have hφc : algebraMap S[X] K₁ (C (ι (CPoly.lead (CPoly.trim
        (CPoly.divMod q.2 (CPoly.egcd q.1 q.2).1).1))⁻¹)) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (C_ne_zero.mpr ((map_ne_zero_iff _ ι.injective).mpr hc0))
    simp only [CPoly.ev, CPoly.toPoly_smul, CPoly.toPoly_trim, Polynomial.map_mul, map_C, map_mul]
    rw [mul_div_mul_left _ _ hφc, e1, e2, Polynomial.map_mul, Polynomial.map_mul, map_mul, map_mul,
      mul_div_mul_right _ _ hφg]

end Coeff

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Algebra K₁[X] K₂] [IsFractionRing K₁[X] K₂]

local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

/-- Coefficient normalisation preserves the polynomial. -/
lemma toPoly_map_normCoeff (p : GPoly (GFrac R)) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (p.map normCoeff) =
      GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) p := by
  rw [GPoly.toPoly_eq_sum_range _ (p.map normCoeff) ([], [1]),
    GPoly.toPoly_eq_sum_range _ p ([], [1]), List.length_map]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j < p.length := Finset.mem_range.mp hj
  rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ hj',
    List.getElem_map, sem_M₁In, sem_M₁In, ev_normCoeff]

/-- **`reduceF₂` preserves the value and has a nonzero denominator.** -/
theorem reduceF₂_spec (q : GFrac (GFrac R)) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (reduceF₂ q).2 ≠ 0 ∧
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (reduceF₂ q).1) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (reduceF₂ q).2) =
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) q.1) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) q.2) := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  unfold reduceF₂
  split_ifs with hz
  · have hz' := (GPoly.isZero_iff M₁ _).mp hz
    refine ⟨by simp [CField.sem_one], ?_⟩
    rw [hz']
    simp [CField.sem_one]
  · have hq2 : GPoly.toPoly M₁ q.2 ≠ 0 := fun h ↦ hz ((GPoly.isZero_iff M₁ _).mpr h)
    simp only
    split_ifs with hn
    · have hn' := (GPoly.isZero_iff M₁ _).mp hn
      rw [toPoly_map_normCoeff] at hn'
      refine ⟨by simp [CField.sem_one], ?_⟩
      rw [hn']
      simp [CField.sem_one]
    · rw [toPoly_map_normCoeff, toPoly_map_normCoeff]
      exact ⟨hq2, rfl⟩

end Tower
