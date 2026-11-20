import RischTragerBronstein.Liouville.SimplePoles
import RischTragerBronstein.Rational.SquarefreePart

/-!
# A resultant-free test for constant residues

Let `s ∈ F[t]` be squarefree with all prime factors normal, and let `r ∈ F[t]` be the **residue
polynomial** of `b / s`: `r s′ ≡ b (mod s)`. The residue of `b / s` at a root `α` of `s` is `r(α)`,
and it is a constant iff `(D r)(α) = 0` for the unique extension of the derivation of `F` to
`F(α)`, i.e. iff `s` divides

  `T = r^κ · ∂ₜ s - ∂ₜ r · s^κ`

(`^κ`: differentiate the coefficients; `∂ₜ = d/dt`). This test needs neither resultants nor
factorisation, and it is invariant under extension of the constants.

* `dvd_residueTest_of_residue`: a constant residue at a normal prime `p ∣ s` forces `p ∣ T`.
* `dvd_residueTest`: if `b / s` (+ anything regular) has an integral of Liouville form, `s ∣ T`.
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F] [Differential F]

/-- The residue test polynomial `T = r^κ · ∂ₜ s - ∂ₜ r · s^κ`. -/
noncomputable def residueTest (r s : F[X]) : F[X] :=
  mapCoeffs r * derivative s - derivative r * mapCoeffs s

section Map

variable {F' : Type*} [Field F'] [Differential F'] (j : F →+* F') (hj : ∀ a : F, j a′ = (j a)′)

include hj in
/-- Differentiating coefficients commutes with a morphism of differential fields. -/
lemma mapCoeffs_map (P : F[X]) : (mapCoeffs P).map j = mapCoeffs (P.map j) := by
  ext n
  rw [coeff_map, coeff_mapCoeffs, coeff_mapCoeffs, coeff_map, hj]

include hj in
/-- The residue test polynomial commutes with a morphism of differential fields. -/
lemma residueTest_map (r s : F[X]) :
    (residueTest r s).map j = residueTest (r.map j) (s.map j) := by
  rw [residueTest, residueTest, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
    mapCoeffs_map j hj, mapCoeffs_map j hj, derivative_map, derivative_map]

end Map

variable [Differential F[X]]

/-- A constant residue `N` at a normal prime factor `p` of `s = p s₁` forces `p ∣ T`. -/
theorem dvd_residueTest_of_residue {p s₁ b r : F[X]} {N : F} (hp : Prime p) (hnorm : ¬p ∣ p′)
    (hs₁ : ¬p ∣ s₁) (hN : N′ = 0) (hres : p ∣ b - C N * (p * s₁)′)
    (hr : p * s₁ ∣ r * (p * s₁)′ - b) : p ∣ residueTest r (p * s₁) := by
  -- `p ∣ r - N`
  have h1 : p ∣ (r - C N) * (p * s₁)′ := by
    have : (r - C N) * (p * s₁)′ = (r * (p * s₁)′ - b) + (b - C N * (p * s₁)′) := by ring
    rw [this]
    exact dvd_add ((dvd_mul_right p s₁).trans hr) hres
  have h2 : ¬p ∣ (p * s₁)′ := fun hdvd ↦ by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hdvd
    have : p ∣ s₁ * p′ := (dvd_add_right (dvd_mul_right p _)).mp hdvd
    rcases hp.dvd_or_dvd this with h | h
    · exact hs₁ h
    · exact hnorm h
  obtain ⟨q, hq⟩ := (hp.dvd_or_dvd h1).resolve_right h2
  have hrq : r = C N + p * q := by rw [← hq]; ring
  have hκN : mapCoeffs (C N) = (0 : F[X]) := by rw [mapCoeffs_C, hN, C_0]
  refine ⟨mapCoeffs q * (derivative p * s₁ + p * derivative s₁) +
    mapCoeffs p * q * derivative s₁ - derivative q * (mapCoeffs p * s₁ + p * mapCoeffs s₁) -
    derivative p * q * mapCoeffs s₁, ?_⟩
  rw [residueTest, hrq, map_add, hκN, Derivation.leibniz, Derivation.leibniz, derivative_add,
    derivative_C, derivative_mul, derivative_mul]
  simp only [smul_eq_mul]
  ring

/-- A squarefree polynomial whose irreducible factors are all normal is coprime to its
derivative. -/
theorem isCoprime_deriv_of_squarefree {s : F[X]} (hs : Squarefree s)
    (hnorm : ∀ p : F[X], Irreducible p → p ∣ s → ¬p ∣ p′) : IsCoprime s′ s := by
  refine isCoprime_of_irreducible_dvd (fun h ↦ hs.ne_zero h.2) fun p hp hps' hps ↦ ?_
  obtain ⟨s₁, rfl⟩ := hps
  have hs₁ : ¬p ∣ s₁ := fun ⟨q, hq⟩ ↦ by
    have : p * p ∣ p * s₁ := ⟨q, by rw [hq]; ring⟩
    exact hp.not_isUnit (hs p this)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hps'
  have : p ∣ s₁ * p′ := (dvd_add_right (dvd_mul_right p _)).mp hps'
  rcases hp.prime.dvd_or_dvd this with h | h
  · exact hs₁ h
  · exact hnorm p hp (dvd_mul_right p s₁) h

section Global

variable [CharZero F] {K : Type*} [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]
variable [Differential K] [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- **Necessity of the residue test.** If `b / s` — `s` squarefree with normal prime factors, `b`
arbitrary (so a polynomial part is allowed) — has an integral of Liouville form with constant
coefficients, then `s ∣ T` for any residue polynomial `r`. -/
theorem dvd_residueTest {s b r : F[X]} (hs : Squarefree s)
    (hnorm : ∀ p : F[X], Irreducible p → p ∣ s → ¬p ∣ p′) (hr : s ∣ r * s′ - b)
    {ι : Type*} (S : Finset ι) (c : ι → F) (hc : ∀ i ∈ S, (c i)′ = 0) (u : ι → K)
    (hu : ∀ i ∈ S, u i ≠ 0) (v : K)
    (h : φ b / φ s = ∑ i ∈ S, φ (C (c i)) * logDeriv (u i) + v′) :
    s ∣ residueTest r s := by
  refine dvd_of_squarefree_of_irreducible_dvd hs fun p hp hps ↦ ?_
  obtain ⟨s₁, rfl⟩ := hps
  have hs₁ : ¬p ∣ s₁ := fun ⟨q, hq⟩ ↦ by
    have : p * p ∣ p * s₁ := ⟨q, by rw [hq]; ring⟩
    exact hp.not_isUnit (hs p this)
  obtain ⟨N, hN, hres⟩ := residue_criterion (K := K) hp.prime
    (hnorm p hp (dvd_mul_right p s₁)) b s₁ hs₁ S c hc u hu v h
  exact dvd_residueTest_of_residue hp.prime (hnorm p hp (dvd_mul_right p s₁)) hs₁ hN hres hr

/-- **Necessity of the residue test, with a cofactor.** The same for an integrand `B / (s m)`,
where no prime factor of `s` divides `m` (e.g. `m = t ^ k` in an exponential extension) and
`B ≡ b m (mod s)`. -/
theorem dvd_residueTest_mul {s m B b r : F[X]} (hs : Squarefree s)
    (hnorm : ∀ p : F[X], Irreducible p → p ∣ s → ¬p ∣ p′)
    (hm : ∀ p : F[X], Irreducible p → p ∣ s → ¬p ∣ m) (hB : s ∣ B - b * m)
    (hr : s ∣ r * s′ - b)
    {ι : Type*} (S : Finset ι) (c : ι → F) (hc : ∀ i ∈ S, (c i)′ = 0) (u : ι → K)
    (hu : ∀ i ∈ S, u i ≠ 0) (v : K)
    (h : φ B / φ (s * m) = ∑ i ∈ S, φ (C (c i)) * logDeriv (u i) + v′) :
    s ∣ residueTest r s := by
  refine dvd_of_squarefree_of_irreducible_dvd hs fun p hp hps ↦ ?_
  have hpm := hm p hp hps
  have hpn := hnorm p hp hps
  obtain ⟨s₁, rfl⟩ := hps
  have hs₁ : ¬p ∣ s₁ := fun ⟨q, hq⟩ ↦ by
    have : p * p ∣ p * s₁ := ⟨q, by rw [hq]; ring⟩
    exact hp.not_isUnit (hs p this)
  have hs₁m : ¬p ∣ s₁ * m := fun hd ↦ (hp.prime.dvd_or_dvd hd).elim hs₁ hpm
  obtain ⟨N, hN, hres⟩ := residue_criterion (K := K) hp.prime hpn B (s₁ * m) hs₁m S c hc u hu v
    (by rw [← mul_assoc]; exact h)
  -- `p ∣ m (b - N s′)`, hence `p ∣ b - N s′`
  have h1 : p ∣ m * (b - C N * (p * s₁)′) := by
    have hexp : m * (b - C N * (p * s₁)′) =
        (B - C N * (p * (s₁ * m))′) - (B - b * m) + C N * (p * s₁) * m′ := by
      have hl : (p * s₁ * m)′ = p * s₁ * m′ + m * (p * s₁)′ := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
      rw [show p * (s₁ * m) = p * s₁ * m by ring, hl]
      ring
    rw [hexp]
    exact dvd_add (dvd_sub hres ((dvd_mul_right p s₁).trans hB))
      (Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_right p s₁) _) _)
  have h2 : p ∣ b - C N * (p * s₁)′ := (hp.prime.dvd_or_dvd h1).resolve_left hpm
  exact dvd_residueTest_of_residue hp.prime hpn hs₁ hN h2 hr

end Global

end Differential
