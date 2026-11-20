import RischTragerBronstein.Liouville.PrimitivePoly
import RischTragerBronstein.Liouville.Transcendence
import Mathlib.FieldTheory.Differential.Basic

/-!
# The polynomial part of a Liouville identity in a primitive extension

Let `K = F(t)` with `t′ = η ∈ F` (the derivation of `F[t]` is `implicitDeriv (C η)`). Every
element of `K` is a polynomial plus a *proper* fraction (`deg num < deg den`), uniquely; proper
fractions are closed under sums, `F`-multiples and the derivation; and the logarithmic
derivative of any `u ≠ 0` is `(lc u)′ / lc u` plus a proper fraction.

**Theorem** (`poly_part_liouville`). If `P + z = ∑ cᵢ uᵢ′ / uᵢ + v′` with `P ∈ F[t]`, `z` proper,
`cᵢ ∈ F`, then comparing polynomial parts, `P - ∑ cᵢ eᵢ′ / eᵢ = D(Pv)` for some `eᵢ ∈ F ∖ {0}` and
`Pv ∈ F[t]` (the polynomial part of `v`). No hypothesis on constants or normality is needed.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

variable (F) in
/-- `z` is a proper fraction: `a / b` with `deg a < deg b`. -/
def IsProperFrac (z : K) : Prop := ∃ a b : F[X], b ≠ 0 ∧ a.degree < b.degree ∧ z = φ a / φ b

omit [Differential F[X]] [Differential K] [DifferentialAlgebra F[X] K] in
lemma degree_mul_lt_of_lt {a b d : F[X]} (h : a.degree < b.degree) (hd : d ≠ 0) :
    (a * d).degree < (b * d).degree := by
  rw [degree_mul, degree_mul]
  exact WithBot.add_lt_add_right (degree_ne_bot.mpr hd) h

lemma isProperFrac_zero : IsProperFrac F (0 : K) :=
  ⟨0, 1, one_ne_zero, by simp, by simp⟩

lemma isProperFrac_add {z w : K} (hz : IsProperFrac F z) (hw : IsProperFrac F w) :
    IsProperFrac F (z + w) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, b, hb, hab, rfl⟩ := hz
  obtain ⟨c, d, hd, hcd, rfl⟩ := hw
  refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_, ?_⟩
  · refine (degree_add_le _ _).trans_lt (max_lt (degree_mul_lt_of_lt hab hd) ?_)
    rw [mul_comm b d]
    exact degree_mul_lt_of_lt hcd hb
  · have h1 : φ b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
    have h2 : φ d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd
    rw [map_add, map_mul, map_mul, map_mul]
    field_simp

lemma isProperFrac_neg {z : K} (hz : IsProperFrac F z) : IsProperFrac F (-z) := by
  obtain ⟨a, b, hb, hab, rfl⟩ := hz
  exact ⟨-a, b, hb, by rwa [degree_neg], by rw [map_neg, neg_div]⟩

lemma isProperFrac_sub {z w : K} (hz : IsProperFrac F z) (hw : IsProperFrac F w) :
    IsProperFrac F (z - w) := by
  rw [sub_eq_add_neg]
  exact isProperFrac_add hz (isProperFrac_neg hw)

lemma isProperFrac_C_mul (e : F) {z : K} (hz : IsProperFrac F z) : IsProperFrac F (φ (C e) * z) := by
  obtain ⟨a, b, hb, hab, rfl⟩ := hz
  refine ⟨C e * a, b, hb, ?_, by rw [map_mul, mul_div_assoc]⟩
  rw [← smul_eq_C_mul]
  exact (degree_smul_le _ _).trans_lt hab

lemma isProperFrac_sum {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsProperFrac F (f i)) :
    IsProperFrac F (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isProperFrac_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isProperFrac_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

omit [IsFractionRing F[X] K] [Differential F[X]] [Differential K] [DifferentialAlgebra F[X] K] in
lemma eq_zero_of_isProperFrac_poly {P : F[X]} (h : IsProperFrac F (φ P)) (hinj : Function.Injective φ) :
    P = 0 := by
  obtain ⟨a, b, hb, hab, h⟩ := h
  have h1 : φ b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
  have hPb : P * b = a := hinj (by rw [map_mul, h, div_mul_cancel₀ _ h1])
  by_contra hP
  rw [← hPb, degree_mul] at hab
  have : b.degree ≤ P.degree + b.degree := by
    rw [degree_eq_natDegree hP, degree_eq_natDegree hb]
    exact_mod_cast Nat.le_add_left _ _
  exact absurd hab (not_lt.mpr this)

lemma exists_poly_add_proper (z : K) : ∃ P : F[X], IsProperFrac F (z - φ P) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := F[X]) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have h1 : φ b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  refine ⟨a / b, a % b, b, hb0, degree_mod_lt a hb0, ?_⟩
  have hab : φ a = φ b * φ (a / b) + φ (a % b) := by
    rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
  rw [hab]
  field_simp
  ring

section Exponential

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
include hDe

/-- For `t′ = b t`: `u′ / u = (lc u)′ / lc u + (deg u) b + proper`, `u` a nonzero polynomial. -/
lemma logDeriv_poly_sub_isProperFrac_exp (a : F[X]) (ha : a ≠ 0) :
    IsProperFrac F (logDeriv (φ a) -
      φ (C (logDeriv a.leadingCoeff + (a.natDegree : F) * b))) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hla : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha
  have h1 : φ a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have h2 : φ (C a.leadingCoeff) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (C_ne_zero.mpr hla)
  refine ⟨implicitDeriv (C b * X) a * C a.leadingCoeff -
    C (a.leadingCoeff′ + (a.natDegree : F) * b * a.leadingCoeff) * a,
    a * C a.leadingCoeff, mul_ne_zero ha (C_ne_zero.mpr hla), ?_, ?_⟩
  · rw [degree_mul, degree_C hla, add_zero, degree_eq_natDegree ha, degree_lt_iff_coeff_zero]
    intro k hk
    have hk' : a.natDegree ≤ k := by exact_mod_cast hk
    rw [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_implicitDeriv_C_mul_X]
    rcases hk'.eq_or_lt with h | h
    · rw [← h, coeff_natDegree]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt h]
      simp
  · unfold logDeriv
    rw [deriv_algebraMap, hDe]
    have hdiv : φ (C (a.leadingCoeff′ / a.leadingCoeff + (a.natDegree : F) * b)) =
        φ (C (a.leadingCoeff′ + (a.natDegree : F) * b * a.leadingCoeff)) /
          φ (C a.leadingCoeff) := by
      have e : a.leadingCoeff′ / a.leadingCoeff + (a.natDegree : F) * b =
          (a.leadingCoeff′ + (a.natDegree : F) * b * a.leadingCoeff) / a.leadingCoeff := by
        field_simp
      rw [e]
      exact map_div₀ ((algebraMap F[X] K).comp C) _ _
    rw [hdiv]
    simp only [map_sub, map_mul]
    field_simp

/-- For `t′ = b t`: `u′ / u = e′ / e + n b + proper` for some `e ∈ F ∖ {0}`, `n ∈ ℤ`. -/
lemma logDeriv_sub_isProperFrac_exp (u : K) (hu : u ≠ 0) :
    ∃ (e : F) (n : ℤ), e ≠ 0 ∧ IsProperFrac F (logDeriv u - φ (C (logDeriv e + (n : F) * b))) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := F[X]) u
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have ha0 : a ≠ 0 := by rintro rfl; simp at hu
  have h1 : φ a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have h2 : φ d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
  have hla : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha0
  have hld : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd0
  refine ⟨a.leadingCoeff / d.leadingCoeff, (a.natDegree : ℤ) - d.natDegree,
    div_ne_zero hla hld, ?_⟩
  rw [logDeriv_div _ _ h1 h2, logDeriv_div _ _ hla hld]
  have := isProperFrac_sub (logDeriv_poly_sub_isProperFrac_exp (K := K) hDe a ha0)
    (logDeriv_poly_sub_isProperFrac_exp (K := K) hDe d hd0)
  have e : logDeriv (φ a) - logDeriv (φ d) - φ (C (logDeriv a.leadingCoeff -
      logDeriv d.leadingCoeff + (((a.natDegree : ℤ) - d.natDegree : ℤ) : F) * b)) =
      logDeriv (φ a) - φ (C (logDeriv a.leadingCoeff + (a.natDegree : F) * b)) -
        (logDeriv (φ d) - φ (C (logDeriv d.leadingCoeff + (d.natDegree : F) * b))) := by
    simp only [map_add, map_sub, map_mul, Int.cast_sub, Int.cast_natCast]
    ring
  rw [e]
  exact this

end Exponential

variable {η : F}

lemma degree_implicitDeriv_le (P : F[X]) : (implicitDeriv (C η) P).degree ≤ P.degree := by
  by_cases hP : P = 0
  · simp [hP]
  rw [degree_eq_natDegree hP]
  refine degree_le_of_natDegree_le ?_
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hk),
    coeff_eq_zero_of_natDegree_lt (by have : P.natDegree < k := by exact_mod_cast hk
                                      omega)]
  simp

variable (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
include hD

lemma deriv_phi (P : F[X]) : (φ P)′ = φ (implicitDeriv (C η) P) := by
  rw [deriv_algebraMap, hD]

lemma isProperFrac_deriv {z : K} (hz : IsProperFrac F z) : IsProperFrac F z′ := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, b, hb, hab, rfl⟩ := hz
  have h1 : φ b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
  refine ⟨implicitDeriv (C η) a * b - a * implicitDeriv (C η) b, b * b, mul_ne_zero hb hb, ?_, ?_⟩
  · refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · refine lt_of_le_of_lt ?_ (degree_mul_lt_of_lt hab hb)
      rw [degree_mul, degree_mul]
      gcongr
      exact degree_implicitDeriv_le a
    · refine lt_of_le_of_lt ?_ (degree_mul_lt_of_lt hab hb)
      rw [degree_mul, degree_mul]
      gcongr
      exact degree_implicitDeriv_le b
  · rw [Derivation.leibniz_div, deriv_phi hD, deriv_phi hD]
    simp only [smul_eq_mul, map_sub, map_mul]
    field_simp

/-- `u′ / u = (lc u)′ / lc u + proper`, for a nonzero polynomial `u`. -/
lemma logDeriv_poly_sub_isProperFrac (a : F[X]) (ha : a ≠ 0) :
    IsProperFrac F (logDeriv (φ a) - φ (C (logDeriv a.leadingCoeff))) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hla : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha
  have h1 : φ a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have h2 : φ (C a.leadingCoeff) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (C_ne_zero.mpr hla)
  refine ⟨implicitDeriv (C η) a * C a.leadingCoeff - C (a.leadingCoeff′) * a,
    a * C a.leadingCoeff, mul_ne_zero ha (C_ne_zero.mpr hla), ?_, ?_⟩
  · rw [degree_mul, degree_C hla, add_zero, degree_eq_natDegree ha, degree_lt_iff_coeff_zero]
    intro k hk
    have hk' : a.natDegree ≤ k := by exact_mod_cast hk
    rw [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_implicitDeriv_C,
      coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < k + 1)]
    rcases hk'.eq_or_lt with h | h
    · rw [← h, coeff_natDegree]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt h]
      simp
  · unfold logDeriv
    rw [deriv_phi hD]
    have hdiv : φ (C (a.leadingCoeff′ / a.leadingCoeff)) =
        φ (C a.leadingCoeff′) / φ (C a.leadingCoeff) :=
      map_div₀ ((algebraMap F[X] K).comp C) _ _
    rw [hdiv]
    simp only [map_sub, map_mul]
    field_simp

/-- `u′ / u = e′ / e + proper` for some `e ∈ F ∖ {0}`, for every `u ≠ 0` in `K`. -/
lemma logDeriv_sub_isProperFrac (u : K) (hu : u ≠ 0) :
    ∃ e : F, e ≠ 0 ∧ IsProperFrac F (logDeriv u - φ (C (logDeriv e))) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := F[X]) u
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hu
  have h1 : φ a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have h2 : φ b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  have hla : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha0
  have hlb : b.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hb0
  refine ⟨a.leadingCoeff / b.leadingCoeff, div_ne_zero hla hlb, ?_⟩
  rw [logDeriv_div _ _ h1 h2, logDeriv_div _ _ hla hlb, C_sub, map_sub]
  have := isProperFrac_sub (logDeriv_poly_sub_isProperFrac (K := K) hD a ha0)
    (logDeriv_poly_sub_isProperFrac (K := K) hD b hb0)
  convert this using 1
  ring

/-- **The polynomial part of a Liouville identity** in a primitive extension. -/
theorem poly_part_liouville {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K)
    (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (P : F[X]) (z : K) (hz : IsProperFrac F z)
    (h : φ P + z = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (Pv : F[X]), (∀ i ∈ s, e i ≠ 0) ∧
      implicitDeriv (C η) Pv = P - C (∑ i ∈ s, c i * logDeriv (e i)) := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have he : ∀ i, ∃ e : F,
      (u i ≠ 0 → e ≠ 0 ∧ IsProperFrac F (logDeriv (u i) - φ (C (logDeriv e)))) := fun i ↦ by
    by_cases hi : u i = 0
    · exact ⟨1, fun h ↦ absurd hi h⟩
    · obtain ⟨e, he0, hp⟩ := logDeriv_sub_isProperFrac hD (u i) hi
      exact ⟨e, fun _ ↦ ⟨he0, hp⟩⟩
  choose e he using he
  obtain ⟨Pv, hPv⟩ := exists_poly_add_proper (F := F) v
  refine ⟨e, Pv, fun i hi ↦ (he i (hu i hi)).1, ?_⟩
  have hsum := isProperFrac_sum s
    (fun i ↦ φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i)))))
    (fun i hi ↦ isProperFrac_C_mul (c i) (he i (hu i hi)).2)
  have hv := isProperFrac_deriv hD hPv
  have hC : φ (C (∑ i ∈ s, c i * logDeriv (e i))) =
      ∑ i ∈ s, φ (C (c i)) * φ (C (logDeriv (e i))) := by
    simp only [map_sum, map_mul]
  have key : φ (P - C (∑ i ∈ s, c i * logDeriv (e i)) - implicitDeriv (C η) Pv) =
      (∑ i ∈ s, φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i))))) + (v - φ Pv)′ - z := by
    rw [map_sub, map_sub, hC, ← deriv_phi hD, map_sub]
    simp only [mul_sub, Finset.sum_sub_distrib]
    linear_combination h
  have h0 := eq_zero_of_isProperFrac_poly
    (by rw [key]; exact isProperFrac_sub (isProperFrac_add hsum hv) hz) hinj
  exact (sub_eq_zero.mp h0).symm

end Differential
