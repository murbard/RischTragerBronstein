import RischTragerBronstein.Liouville.PrimitivePolyPart
import RischTragerBronstein.Liouville.ExponentialPoly

/-!
# The Laurent part of a Liouville identity in an exponential extension

Let `K = F(t)` with `t′ = b t` (the derivation of `F[t]` is `implicitDeriv (C b * X)`). Every
element of `K` is a Laurent polynomial `P / tᵏ` plus a *normal proper* fraction (`a / s`,
`t ∤ s`, `deg a < deg s`), uniquely; normal proper fractions are closed under sums,
`F`-multiples and the derivation; and `u′ / u = e′ / e + n b + (normal proper)` for `u ≠ 0`.

**Theorem** (`laurent_part_liouville`). If `P / tᵏ + z = ∑ cᵢ uᵢ′ / uᵢ + v′` with `z` normal
proper, then with `V / t^kv` the Laurent part of `v`,
`P / tᵏ = ∑ cᵢ (eᵢ′ / eᵢ + nᵢ b) + (V / t^kv)′`, stated cleared of denominators.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

variable (F) in
/-- `z` is a normal proper fraction: `a / s` with `t ∤ s` and `deg a < deg s`. -/
def IsNProperFrac (z : K) : Prop :=
  ∃ a s : F[X], s ≠ 0 ∧ ¬X ∣ s ∧ a.degree < s.degree ∧ z = φ a / φ s

lemma not_X_dvd_mul {s d : F[X]} (hs : ¬X ∣ s) (hd : ¬X ∣ d) : ¬X ∣ s * d := fun h ↦
  (prime_X.dvd_or_dvd h).elim hs hd

lemma isNProperFrac_zero : IsNProperFrac F (0 : K) :=
  ⟨0, 1, one_ne_zero, fun h ↦ absurd (degree_le_of_dvd h one_ne_zero) (by simp), by simp, by simp⟩

lemma isNProperFrac_add {z w : K} (hz : IsNProperFrac F z) (hw : IsNProperFrac F w) :
    IsNProperFrac F (z + w) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, b, hb, hbX, hab, rfl⟩ := hz
  obtain ⟨c, d, hd, hdX, hcd, rfl⟩ := hw
  refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, not_X_dvd_mul hbX hdX, ?_, ?_⟩
  · refine (degree_add_le _ _).trans_lt (max_lt (degree_mul_lt_of_lt hab hd) ?_)
    rw [mul_comm b d]
    exact degree_mul_lt_of_lt hcd hb
  · have h1 : φ b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
    have h2 : φ d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd
    rw [map_add, map_mul, map_mul, map_mul]
    field_simp

lemma isNProperFrac_neg {z : K} (hz : IsNProperFrac F z) : IsNProperFrac F (-z) := by
  obtain ⟨a, b, hb, hbX, hab, rfl⟩ := hz
  exact ⟨-a, b, hb, hbX, by rwa [degree_neg], by rw [map_neg, neg_div]⟩

lemma isNProperFrac_sub {z w : K} (hz : IsNProperFrac F z) (hw : IsNProperFrac F w) :
    IsNProperFrac F (z - w) := by
  rw [sub_eq_add_neg]
  exact isNProperFrac_add hz (isNProperFrac_neg hw)

lemma isNProperFrac_C_mul (e : F) {z : K} (hz : IsNProperFrac F z) :
    IsNProperFrac F (φ (C e) * z) := by
  obtain ⟨a, b, hb, hbX, hab, rfl⟩ := hz
  refine ⟨C e * a, b, hb, hbX, ?_, by rw [map_mul, mul_div_assoc]⟩
  rw [← smul_eq_C_mul]
  exact (degree_smul_le _ _).trans_lt hab

lemma isNProperFrac_sum {ι : Type*} (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, IsNProperFrac F (f i)) : IsNProperFrac F (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isNProperFrac_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isNProperFrac_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

omit [Differential F[X]] [Differential K] [DifferentialAlgebra F[X] K] in
/-- **Uniqueness**: a Laurent polynomial which is a normal proper fraction is zero. -/
lemma eq_zero_of_isNProperFrac_laurent {Q : F[X]} {N : ℕ}
    (h : IsNProperFrac F (φ Q / φ (X ^ N))) : Q = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, s, hs, hsX, has, h⟩ := h
  have h1 : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs
  have h2 : φ (X ^ N : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hQs : Q * s = a * X ^ N := hinj (by
    rw [map_mul, map_mul]
    field_simp at h
    linear_combination h)
  have hcop : IsCoprime (X ^ N : F[X]) s :=
    IsCoprime.pow_left ((irreducible_X.coprime_iff_not_dvd).mpr hsX)
  obtain ⟨R, hR⟩ : (X ^ N : F[X]) ∣ Q := hcop.dvd_of_dvd_mul_right ⟨a, by rw [hQs, mul_comm]⟩
  have hRs : R * s = a := by
    have : X ^ N * (R * s) = X ^ N * a := by rw [← mul_assoc, ← hR, hQs, mul_comm]
    exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) this
  by_contra hQ
  have hR0 : R ≠ 0 := by rintro rfl; simp at hR; exact hQ hR
  rw [← hRs, degree_mul] at has
  have : s.degree ≤ R.degree + s.degree := by
    rw [degree_eq_natDegree hR0, degree_eq_natDegree hs]
    exact_mod_cast Nat.le_add_left _ _
  exact absurd has (not_lt.mpr this)

omit [Differential F[X]] [Differential K] [DifferentialAlgebra F[X] K] in
/-- Every element is a Laurent polynomial plus a normal proper fraction. -/
lemma exists_laurent_add_nproper (z : K) :
    ∃ (P : F[X]) (k : ℕ), IsNProperFrac F (z - φ P / φ (X ^ k)) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := F[X]) z
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨d₁, hdd, hd₁X⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd0 0
  simp only [map_zero, sub_zero] at hdd hd₁X
  set k := d.rootMultiplicity 0
  have hd₁0 : d₁ ≠ 0 := by rintro rfl; simp at hd₁X
  have hcop : IsCoprime (X ^ k : F[X]) d₁ :=
    IsCoprime.pow_left ((irreducible_X.coprime_iff_not_dvd).mpr hd₁X)
  obtain ⟨α, β, hαβ⟩ := hcop
  refine ⟨a * β + (a * α / d₁) * X ^ k, k, (a * α) % d₁, d₁, hd₁0, hd₁X,
    degree_mod_lt _ hd₁0, ?_⟩
  have h1 : φ d₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd₁0
  have h2 : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hdiv : φ (a * α) = φ d₁ * φ (a * α / d₁) + φ ((a * α) % d₁) := by
    rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
  have ha : φ a = φ a * (φ α * φ (X ^ k) + φ β * φ d₁) := by
    rw [← map_mul, ← map_mul, ← map_add, hαβ, map_one, mul_one]
  rw [hdd]
  simp only [map_mul, map_add] at hdiv ⊢
  field_simp
  linear_combination ha + φ (X ^ k : F[X]) * hdiv

variable {b : F}

lemma degree_implicitDeriv_exp_le (P : F[X]) : (implicitDeriv (C b * X) P).degree ≤ P.degree := by
  by_cases hP : P = 0
  · simp [hP]
  rw [degree_eq_natDegree hP]
  refine degree_le_of_natDegree_le ?_
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_implicitDeriv_C_mul_X, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hk)]
  simp

variable (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
include hDe

lemma deriv_phi_exp (P : F[X]) : (φ P)′ = φ (implicitDeriv (C b * X) P) := by
  rw [deriv_algebraMap, hDe]

lemma isNProperFrac_deriv {z : K} (hz : IsNProperFrac F z) : IsNProperFrac F z′ := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, s, hs, hsX, has, rfl⟩ := hz
  have h1 : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs
  refine ⟨implicitDeriv (C b * X) a * s - a * implicitDeriv (C b * X) s, s * s,
    mul_ne_zero hs hs, not_X_dvd_mul hsX hsX, ?_, ?_⟩
  · refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · refine lt_of_le_of_lt ?_ (degree_mul_lt_of_lt has hs)
      rw [degree_mul, degree_mul]
      gcongr
      exact degree_implicitDeriv_exp_le a
    · refine lt_of_le_of_lt ?_ (degree_mul_lt_of_lt has hs)
      rw [degree_mul, degree_mul]
      gcongr
      exact degree_implicitDeriv_exp_le s
  · rw [Derivation.leibniz_div, deriv_phi_exp hDe, deriv_phi_exp hDe]
    simp only [smul_eq_mul, map_sub, map_mul]
    field_simp

/-- For `t ∤ a`: `a′ / a = (lc a)′ / lc a + (deg a) b + (normal proper)`. -/
lemma logDeriv_poly_sub_isNProperFrac (a : F[X]) (ha : a ≠ 0) (haX : ¬X ∣ a) :
    IsNProperFrac F (logDeriv (φ a) -
      φ (C (logDeriv a.leadingCoeff + (a.natDegree : F) * b))) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hla : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha
  have h1 : φ a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have h2 : φ (C a.leadingCoeff) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (C_ne_zero.mpr hla)
  have hCX : ¬X ∣ C a.leadingCoeff := fun h ↦ by
    have := degree_le_of_dvd h (C_ne_zero.mpr hla)
    rw [degree_X, degree_C hla] at this
    exact absurd this (by decide)
  refine ⟨implicitDeriv (C b * X) a * C a.leadingCoeff -
    C (a.leadingCoeff′ + (a.natDegree : F) * b * a.leadingCoeff) * a,
    a * C a.leadingCoeff, mul_ne_zero ha (C_ne_zero.mpr hla), not_X_dvd_mul haX hCX, ?_, ?_⟩
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

/-- For a nonzero polynomial: `a′ / a = e′ / e + n b + (normal proper)`. -/
lemma logDeriv_poly_sub_isNProperFrac' (a : F[X]) (ha : a ≠ 0) :
    ∃ (e : F) (n : ℕ), e ≠ 0 ∧
      IsNProperFrac F (logDeriv (φ a) - φ (C (logDeriv e + (n : F) * b))) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a₁, haa, ha₁X⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha 0
  simp only [map_zero, sub_zero] at haa ha₁X
  set j := a.rootMultiplicity 0
  have ha₁0 : a₁ ≠ 0 := by rintro rfl; simp at ha₁X
  have hla : a₁.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha₁0
  refine ⟨a₁.leadingCoeff, j + a₁.natDegree, hla, ?_⟩
  have hX : φ (X : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have h1 : φ a₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha₁0
  have hlX : logDeriv (φ (X : F[X])) = φ (C b) := by
    unfold logDeriv
    rw [deriv_phi_exp hDe, implicitDeriv_X, map_mul]
    field_simp
  have hsplit : logDeriv (φ a) = (j : K) * φ (C b) + logDeriv (φ a₁) := by
    rw [haa, map_mul, map_pow, logDeriv_mul _ _ (pow_ne_zero _ hX) h1, logDeriv_pow, hlX]
  rw [hsplit]
  have := logDeriv_poly_sub_isNProperFrac (K := K) hDe a₁ ha₁0 ha₁X
  have e : (j : K) * φ (C b) + logDeriv (φ a₁) -
      φ (C (logDeriv a₁.leadingCoeff + ((j + a₁.natDegree : ℕ) : F) * b)) =
      logDeriv (φ a₁) - φ (C (logDeriv a₁.leadingCoeff + (a₁.natDegree : F) * b)) := by
    simp only [map_add, map_mul, map_natCast, Nat.cast_add]
    ring
  rw [e]
  exact this

/-- `u′ / u = e′ / e + n b + (normal proper)` for every `u ≠ 0`. -/
lemma logDeriv_sub_isNProperFrac (u : K) (hu : u ≠ 0) :
    ∃ e : F, e ≠ 0 ∧ ∃ n : ℤ,
      IsNProperFrac F (logDeriv u - φ (C (logDeriv e + (n : F) * b))) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := F[X]) u
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have ha0 : a ≠ 0 := by rintro rfl; simp at hu
  have h1 : φ a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have h2 : φ d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
  obtain ⟨ea, na, hea, hpa⟩ := logDeriv_poly_sub_isNProperFrac' (K := K) hDe a ha0
  obtain ⟨ed, nd, hed, hpd⟩ := logDeriv_poly_sub_isNProperFrac' (K := K) hDe d hd0
  refine ⟨ea / ed, div_ne_zero hea hed, (na : ℤ) - nd, ?_⟩
  rw [logDeriv_div _ _ h1 h2, logDeriv_div _ _ hea hed]
  have e : logDeriv (φ a) - logDeriv (φ d) - φ (C (logDeriv ea - logDeriv ed +
      (((na : ℤ) - nd : ℤ) : F) * b)) =
      logDeriv (φ a) - φ (C (logDeriv ea + (na : F) * b)) -
        (logDeriv (φ d) - φ (C (logDeriv ed + (nd : F) * b))) := by
    simp only [map_add, map_sub, map_mul, Int.cast_sub, Int.cast_natCast]
    ring
  rw [e]
  exact isNProperFrac_sub hpa hpd

/-- `(V / tᵏ)′ = (V′ - k b V) / tᵏ`. -/
lemma deriv_laurent (V : F[X]) (k : ℕ) :
    (φ V / φ (X ^ k))′ =
      φ (implicitDeriv (C b * X) V - C ((k : F) * b) * V) / φ (X ^ k) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have h2 : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  rw [Derivation.leibniz_div, deriv_phi_exp hDe, deriv_phi_exp hDe, deriv_X_pow]
  simp only [smul_eq_mul, map_sub, map_mul]
  field_simp

/-- **The Laurent part of a Liouville identity** in an exponential extension `t′ = b t`:
`P / tᵏ = ∑ cᵢ (eᵢ′ / eᵢ + nᵢ b) + (V / t^kv)′`, cleared of denominators. -/
theorem laurent_part_liouville {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K)
    (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (P : F[X]) (k : ℕ) (z : K) (hz : IsNProperFrac F z)
    (h : φ P / φ (X ^ k) + z = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (n : ι → ℤ) (V : F[X]) (kv : ℕ), (∀ i ∈ s, e i ≠ 0) ∧
      P * X ^ kv = (C (∑ i ∈ s, c i * (logDeriv (e i) + (n i : F) * b)) * X ^ kv +
        (implicitDeriv (C b * X) V - C ((kv : F) * b) * V)) * X ^ k := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have he : ∀ i, ∃ e : F, ∃ n : ℤ, (u i ≠ 0 → e ≠ 0 ∧
      IsNProperFrac F (logDeriv (u i) - φ (C (logDeriv e + (n : F) * b)))) := fun i ↦ by
    by_cases hi : u i = 0
    · exact ⟨1, 0, fun h ↦ absurd hi h⟩
    · obtain ⟨e, he0, n, hp⟩ := logDeriv_sub_isNProperFrac hDe (u i) hi
      exact ⟨e, n, fun _ ↦ ⟨he0, hp⟩⟩
  choose e n he using he
  obtain ⟨V, kv, hV⟩ := exists_laurent_add_nproper (F := F) v
  refine ⟨e, n, V, kv, fun i hi ↦ (he i (hu i hi)).1, ?_⟩
  set S := ∑ i ∈ s, c i * (logDeriv (e i) + (n i : F) * b) with hS
  have hsum := isNProperFrac_sum s
    (fun i ↦ φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i) + (n i : F) * b))))
    (fun i hi ↦ isNProperFrac_C_mul (c i) (he i (hu i hi)).2)
  have hv := isNProperFrac_deriv hDe hV
  have hC : φ (C S) = ∑ i ∈ s, φ (C (c i)) * φ (C (logDeriv (e i) + (n i : F) * b)) := by
    simp only [hS, map_sum, map_mul]
  have hX1 : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hX2 : φ (X ^ kv : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  set Q := P * X ^ kv - (C S * X ^ kv +
    (implicitDeriv (C b * X) V - C ((kv : F) * b) * V)) * X ^ k with hQ
  have key : φ Q / φ (X ^ (k + kv)) =
      (∑ i ∈ s, φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i) + (n i : F) * b)))) +
        (v - φ V / φ (X ^ kv))′ - z := by
    have hQv : φ Q = φ P * φ (X ^ kv) - (φ (C S) * φ (X ^ kv) +
        φ (implicitDeriv (C b * X) V - C ((kv : F) * b) * V)) * φ (X ^ k) := by
      rw [hQ]; simp only [map_sub, map_mul, map_add]
    have hd : (v - φ V / φ (X ^ kv))′ =
        v′ - φ (implicitDeriv (C b * X) V - C ((kv : F) * b) * V) / φ (X ^ kv) := by
      rw [map_sub, deriv_laurent hDe V kv]
    have hP : φ P = (∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′ - z) * φ (X ^ k) := by
      rw [← h]; field_simp; ring
    rw [hQv, hd, pow_add, map_mul, hP]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hC]
    field_simp
    rw [map_mul φ (X ^ k) (X ^ kv)]
    ring
  have h0 := eq_zero_of_isNProperFrac_laurent (K := K)
    (by rw [key]; exact isNProperFrac_sub (isNProperFrac_add hsum hv) hz)
  exact sub_eq_zero.mp h0

end Differential
