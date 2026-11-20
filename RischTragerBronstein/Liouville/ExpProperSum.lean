import RischTragerBronstein.Liouville.ExponentialLaurentPart
import RischTragerBronstein.Liouville.ProperFractionSum

/-!
# Sums of normal proper fractions are not derivatives (exponential case)

In `K = F(t)`, `t′ = b t`, every prime other than `t` normal: if
`z′ = A / tᵏ + ∑ rᵢ / sᵢ` with each `sᵢ` squarefree, `t ∤ sᵢ` and `deg rᵢ < deg sᵢ`, then
`∑ rᵢ / sᵢ = 0` and `z` is a Laurent polynomial `V / t^kv`. This is what parametric limited
integration over an exponential needs.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

lemma isNProperFrac_list_sum (l : List (F[X] × F[X])) (hs : ∀ p ∈ l, p.2 ≠ 0)
    (hX : ∀ p ∈ l, ¬X ∣ p.2) (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) :
    IsNProperFrac F ((l.map fun p ↦ φ p.1 / φ p.2).sum : K) := by
  induction l with
  | nil => simpa using isNProperFrac_zero
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons]
    exact isNProperFrac_add ⟨p.1, p.2, hs p List.mem_cons_self, hX p List.mem_cons_self,
      hdeg p List.mem_cons_self, rfl⟩ (ih (fun q hq ↦ hs q (List.mem_cons_of_mem _ hq))
        (fun q hq ↦ hX q (List.mem_cons_of_mem _ hq)) (fun q hq ↦ hdeg q (List.mem_cons_of_mem _ hq)))

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)

include hDe in
/-- **Antiderivatives over an exponential, several fractions**: the normal simple parts cancel
and the antiderivative is a Laurent polynomial. -/
theorem deriv_eq_laurent_add_sum_proper
    (hnorm : ∀ p : F[X], Irreducible p → ¬X ∣ p → ¬p ∣ p′)
    (A : F[X]) (k : ℕ) (l : List (F[X] × F[X])) (hsq : ∀ p ∈ l, Squarefree p.2)
    (hX : ∀ p ∈ l, ¬X ∣ p.2) (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) (z : K)
    (h : z′ = φ A / φ (X ^ k) + (l.map fun p ↦ φ p.1 / φ p.2).sum) :
    (l.map fun p ↦ φ p.1 / φ p.2).sum = 0 ∧ ∃ (V : F[X]) (kv : ℕ), z = φ V / φ (X ^ kv) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨V, kv, hz1⟩ := exists_laurent_add_nproper (F := F) z
  obtain ⟨z1, hz1d⟩ : ∃ z1, z1 = z - φ V / φ (X ^ kv) := ⟨_, rfl⟩
  rw [← hz1d] at hz1
  obtain ⟨S, hS⟩ : ∃ S, S = (l.map fun p ↦ φ p.1 / φ p.2).sum := ⟨_, rfl⟩
  rw [← hS] at h ⊢
  have hSn : IsNProperFrac F S := hS ▸ isNProperFrac_list_sum l (fun p hp ↦ (hsq p hp).ne_zero) hX hdeg
  have hd1 := isNProperFrac_deriv hDe hz1
  have hXk : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hXkv : φ (X ^ kv : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hlau : z1′ - S = φ (A * X ^ kv - (implicitDeriv (C b * X) V - C ((kv : F) * b) * V) * X ^ k) /
      φ (X ^ (k + kv)) := by
    have hzd : z1′ = z′ - φ (implicitDeriv (C b * X) V - C ((kv : F) * b) * V) / φ (X ^ kv) := by
      rw [hz1d, map_sub, deriv_laurent hDe V kv]
    rw [hzd, h, pow_add]
    simp only [map_sub, map_mul]
    field_simp
    ring
  have hQ := eq_zero_of_isNProperFrac_laurent (hlau ▸ isNProperFrac_sub hd1 hSn)
  have hz1S : z1′ = S := by rw [← sub_eq_zero, hlau, hQ, map_zero, zero_div]
  obtain ⟨P, hP⟩ : ∃ P : F[X], z1 = φ P := exists_polynomial_of_regularAt z1 fun p _ hp ↦ by
    by_cases hXp : X ∣ p
    · obtain ⟨a, s, hs, hsX, -, hz⟩ := hz1
      refine ⟨a, s, fun hps ↦ hsX (hXp.trans hps), ?_⟩
      rw [hz]; exact div_mul_cancel₀ _ ((map_ne_zero_iff _ hinj).mpr hs)
    · refine mem_regularAt_of_deriv_simple_pole hp.prime (hnorm p hp hXp)
        (not_dvd_natCast_polynomial hp.prime) ?_
      rw [hz1S, hS, ← List.sum_map_mul_right]
      refine Subring.list_sum_mem _ fun y hy ↦ ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      exact simple_pole_mem_regularAt (hsq q hq) hp
  have hP0 : P = 0 := eq_zero_of_isNProperFrac_laurent (N := 0) (K := K)
    (by rw [pow_zero, map_one, div_one, ← hP]; exact hz1)
  have hz10 : z1 = 0 := by rw [hP, hP0, map_zero]
  refine ⟨by rw [← hz1S, hz10, Derivation.map_zero], V, kv, ?_⟩
  rw [hz1d, sub_eq_zero] at hz10
  exact hz10

include hDe in
/-- **Normalising a Laurent antiderivative**: if `(V / t^kv)′ = P / tˢ` and no `e′ + j b e = 0`
(`j ≠ 0`) has a non-zero solution, then `V / t^kv = Y / tˢ` for a polynomial `Y` with
`Y′ - S b Y = P`. -/
theorem laurent_normalize (hhom : ∀ j : ℤ, j ≠ 0 → ∀ e : F, e ≠ 0 → e′ + (j : F) * b * e ≠ 0)
    (V P : F[X]) (kv S : ℕ) (h : (φ V / φ (X ^ kv))′ = φ P / φ (X ^ S)) :
    ∃ Y : F[X], φ V / φ (X ^ kv) = φ Y / φ (X ^ S) ∧
      implicitDeriv (C b * X) Y - C ((S : F) * b) * Y = P := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hXp : ∀ n : ℕ, φ (X ^ n : F[X]) ≠ 0 := fun n ↦
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  rw [deriv_laurent hDe V kv] at h
  have hx : (implicitDeriv (C b * X) V - C ((kv : F) * b) * V) * X ^ S = P * X ^ kv := hinj (by
    have := hXp kv; have := hXp S
    field_simp at h
    simp only [map_mul] at h ⊢
    linear_combination h)
  have hDXd : ∀ (d : ℕ) (Y : F[X]), implicitDeriv (C b * X) (X ^ d * Y) =
      X ^ d * (implicitDeriv (C b * X) Y + C ((d : F) * b) * Y) := fun d Y ↦ by
    rw [Derivation.leibniz, deriv_X_pow]
    simp only [smul_eq_mul]
    ring
  rcases le_or_gt kv S with hle | hlt
  · obtain ⟨d, rfl⟩ : ∃ d, S = kv + d := ⟨S - kv, by omega⟩
    refine ⟨X ^ d * V, ?_, ?_⟩
    · rw [pow_add, map_mul, map_mul]
      have := hXp kv; have := hXp d
      field_simp
    · rw [hDXd]
      have hx' : X ^ kv * (X ^ d * (implicitDeriv (C b * X) V - C ((kv : F) * b) * V)) =
          X ^ kv * P := by rw [pow_add] at hx; linear_combination hx
      have := mul_left_cancel₀ (pow_ne_zero kv X_ne_zero) hx'
      push_cast
      rw [← this, C_mul, C_mul, C_add, C_mul]
      ring
  · obtain ⟨d, rfl⟩ : ∃ d, kv = S + d := ⟨kv - S, by omega⟩
    have hx' : implicitDeriv (C b * X) V - C (((S + d : ℕ) : F) * b) * V = X ^ d * P := by
      have : X ^ S * (implicitDeriv (C b * X) V - C (((S + d : ℕ) : F) * b) * V) =
          X ^ S * (X ^ d * P) := by rw [pow_add] at hx; linear_combination hx
      exact mul_left_cancel₀ (pow_ne_zero S X_ne_zero) this
    -- the low coefficients of `V` vanish
    have hdvd : X ^ d ∣ V := by
      rw [X_pow_dvd_iff]
      intro i hi
      have hc := congrArg (fun Q : F[X] ↦ Q.coeff i) hx'
      simp only [coeff_sub, coeff_C_mul, coeff_implicitDeriv_C_mul_X, coeff_X_pow_mul'] at hc
      rw [if_neg (by omega)] at hc
      by_contra hV
      refine hhom ((i : ℤ) - (S + d : ℕ)) (by omega) (V.coeff i) hV ?_
      push_cast at hc ⊢
      linear_combination hc
    obtain ⟨Y, rfl⟩ := hdvd
    refine ⟨Y, ?_, ?_⟩
    · rw [pow_add, map_mul, map_mul]
      have := hXp S; have := hXp d
      field_simp
    · rw [hDXd] at hx'
      have hx'' : X ^ d * (implicitDeriv (C b * X) Y - C ((S : F) * b) * Y) = X ^ d * P := by
        rw [← hx']; push_cast; simp only [C_mul, C_add]; ring
      exact mul_left_cancel₀ (pow_ne_zero d X_ne_zero) hx''

omit [CharZero F] [Differential F[X]] [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]
  [Differential K] [DifferentialAlgebra F[X] K] in
/-- **The coefficients of a cleared Laurent identity**
`P tᵏᵛ = (σ tᵏᵛ + (V′ - kv b V)) tˢ`: every coefficient `j ≠ S` of `P` is `y′ + (j - S) b y`, and
`P_S = σ + (V_kv)′`. -/
lemma laurent_coeff_eqs (b : F) (P V : F[X]) (σ : F) (kv S : ℕ)
    (h : P * X ^ kv = (C σ * X ^ kv + (implicitDeriv (C b * X) V - C ((kv : F) * b) * V)) * X ^ S) :
    (∀ j, j ≠ S → ∃ y : F, y′ + (((j : ℤ) - S : ℤ) : F) * b * y = P.coeff j) ∧
      P.coeff S = σ + (V.coeff kv)′ := by
  have hc : ∀ j, P.coeff j = if S ≤ j + kv then
      (C σ * X ^ kv + (implicitDeriv (C b * X) V - C ((kv : F) * b) * V)).coeff (j + kv - S)
      else 0 := fun j ↦ by
    have := congrArg (fun Q : F[X] ↦ Q.coeff (j + kv)) h
    simp only [coeff_mul_X_pow] at this
    rw [this, coeff_mul_X_pow']
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [hc j]
    split_ifs with hle
    · refine ⟨V.coeff (j + kv - S), ?_⟩
      rw [coeff_add, coeff_C_mul_X_pow, if_neg (by omega), coeff_sub, coeff_C_mul,
        coeff_implicitDeriv_C_mul_X]
      have : ((j + kv - S : ℕ) : F) = (j : F) + kv - S := by
        rw [Nat.cast_sub hle]; push_cast; ring
      rw [this]
      push_cast
      ring
    · exact ⟨0, by simp⟩
  · rw [hc S, if_pos (by omega), Nat.add_sub_cancel_left, coeff_add, coeff_C_mul_X_pow, if_pos rfl,
      coeff_sub, coeff_C_mul, coeff_implicitDeriv_C_mul_X]
    ring

end Differential
