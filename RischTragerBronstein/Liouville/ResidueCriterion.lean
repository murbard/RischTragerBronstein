import RischTragerBronstein.Liouville.Residue

/-!
# The residue criterion, locally

Let `A` be a differential domain with fraction field `K`, `p ∈ A` a **normal** prime, and
`s = p * s₁` with `p ∤ s₁` (as when `s` is squarefree and `p ∣ s`). Suppose

  `b / s = ∑ γᵢ uᵢ′ / uᵢ + v′`   in `K`,  with `γᵢ ∈ A` and `uᵢ = p ^ mᵢ * gᵢ`, `gᵢ ∈ O_p^×`.

Then (`residue_criterion_local`)

  `p ∣ b - (∑ γᵢ mᵢ) * s′`.

In words: the residue of `b / s` at `p`, namely `b / s′ mod p`, equals `∑ γᵢ ord_p(uᵢ)` — an
integer combination of the coefficients `γᵢ`. In `F[t]` with constant `γᵢ`, the residues of an
elementary-integrable `b / s` are therefore constants: they are the roots of the Rothstein–Trager
resultant `res_t (b - z s′, s)`, which is how the algorithm decides (Bronstein, Theorem 5.6.1); a
non-constant root is a proof of non-elementarity.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Differential

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [Differential A] [Differential K] [DifferentialAlgebra A K]
variable {p : A} (hp : Prime p)

local notation "φ" => algebraMap A K

include hp in
theorem residue_criterion_local (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    (b s₁ : A) (hs₁ : ¬p ∣ s₁)
    {ι : Type*} (S : Finset ι) (γ : ι → A) (u g : ι → K) (m : ι → ℤ) (v : K)
    (hg : ∀ i ∈ S, IsUnitAt K p (g i)) (hu : ∀ i ∈ S, u i = φ p ^ m i * g i)
    (h : φ b / φ (p * s₁) = ∑ i ∈ S, φ (γ i) * logDeriv (u i) + v′) :
    p ∣ b - (∑ i ∈ S, γ i * (m i : A)) * (p * s₁)′ := by
  have hinj : Function.Injective φ := IsFractionRing.injective A K
  have hp0 : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  have hs₁0 : φ s₁ ≠ 0 := map_ne_zero_of_not_dvd hp hs₁
  have hg0 : ∀ i ∈ S, g i ≠ 0 := fun i hi h0 ↦ by
    obtain ⟨a, b', ha, -, hab⟩ := hg i hi
    rw [h0, zero_mul] at hab
    exact map_ne_zero_of_not_dvd (K := K) hp ha hab.symm
  have hu0 : ∀ i ∈ S, u i ≠ 0 := fun i hi ↦ by
    rw [hu i hi]; exact mul_ne_zero (zpow_ne_zero _ hp0) (hg0 i hi)
  -- `b / s` has at most a simple pole at `p`
  have hα : φ p * (φ b / φ (p * s₁)) ∈ regularAt K p hp :=
    ⟨b, s₁, hs₁, by rw [map_mul]; field_simp⟩
  -- so `v` and `v′` are regular at `p`
  have hv : v ∈ regularAt K p hp :=
    mem_regularAt_of_liouville_eq' hp hnorm hnat S (fun i ↦ φ (γ i)) u v _
      (fun i _ ↦ algebraMap_mem_regularAt hp _) hu0 hα h
  have hv' := deriv_mem_regularAt hp hv
  -- split the logarithmic derivatives
  set N := ∑ i ∈ S, γ i * (m i : A) with hN
  have hsplit : ∑ i ∈ S, φ (γ i) * logDeriv (u i) =
      φ N * (φ p′ / φ p) + ∑ i ∈ S, φ (γ i) * logDeriv (g i) := by
    rw [hN, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hu i hi, logDeriv_mul _ _ (zpow_ne_zero _ hp0) (hg0 i hi), logDeriv_algebraMap_zpow hp,
      map_mul, map_intCast]
    ring
  have hreg : ∑ i ∈ S, φ (γ i) * logDeriv (g i) ∈ regularAt K p hp :=
    sum_mem fun i hi ↦ mul_mem (algebraMap_mem_regularAt hp _)
      ((hg i hi).logDeriv_mem_regularAt hp)
  -- `b - N p′ s₁ = p * (regular)`
  have h1 : p ∣ b - N * (p′ * s₁) := by
    refine dvd_of_algebraMap_eq_mul hp (r := φ s₁ * (v′ + ∑ i ∈ S, φ (γ i) * logDeriv (g i)))
      (mul_mem (algebraMap_mem_regularAt hp _) (add_mem hv' hreg)) ?_
    have h2 : v′ + ∑ i ∈ S, φ (γ i) * logDeriv (g i) =
        φ b / φ (p * s₁) - φ N * (φ p′ / φ p) := by rw [h, hsplit]; ring
    rw [h2, map_sub, map_mul, map_mul, map_mul]
    field_simp
  -- `s′ = p′ s₁ + p s₁′`
  have hs' : (p * s₁)′ = p′ * s₁ + p * s₁′ := by
    rw [Derivation.leibniz]; simp only [smul_eq_mul]; ring
  rw [hs']
  have : b - N * (p′ * s₁ + p * s₁′) = (b - N * (p′ * s₁)) - p * (N * s₁′) := by ring
  rw [this]
  exact dvd_sub h1 (dvd_mul_right p _)

end Differential

namespace Differential

open Polynomial Finset

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

/-- **The residue criterion in `F(t)`.** Let `p ∈ F[t]` be a normal prime, `s = p s₁` with
`p ∤ s₁`. If `b / s = ∑ cᵢ uᵢ′ / uᵢ + v′` in `F(t)` with **constant** `cᵢ ∈ F`, then there is a
constant `N ∈ F` with `p ∣ b - N s′`: the residue of `b / s` at `p` is a constant. -/
theorem residue_criterion {p : F[X]} (hp : Prime p)
    (hnorm : ¬p ∣ p′) (b s₁ : F[X]) (hs₁ : ¬p ∣ s₁)
    {ι : Type*} (S : Finset ι) (c : ι → F) (hc : ∀ i ∈ S, (c i)′ = 0) (u : ι → K)
    (hu : ∀ i ∈ S, u i ≠ 0) (v : K)
    (h : algebraMap F[X] K b / algebraMap F[X] K (p * s₁) =
      ∑ i ∈ S, algebraMap F[X] K (C (c i)) * logDeriv (u i) + v′) :
    ∃ N : F, N′ = 0 ∧ p ∣ b - C N * (p * s₁)′ := by
  classical
  have hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : F[X]) := fun k hk hdvd ↦
    hp.not_isUnit (isUnit_of_dvd_unit hdvd (by
      rw [← C_eq_natCast, isUnit_C, isUnit_iff_ne_zero]; exact Nat.cast_ne_zero.mpr hk))
  -- orders of the `u i` at `p`
  have hdec : ∀ i, ∃ (m : ℤ) (g : K), i ∈ S → IsUnitAt K p g ∧
      u i = algebraMap F[X] K p ^ m * g := fun i ↦ by
    by_cases hi : i ∈ S
    · obtain ⟨m, g, hg, hug⟩ := exists_zpow_mul_isUnitAt hp (hu i hi)
      exact ⟨m, g, fun _ ↦ ⟨hg, hug⟩⟩
    · exact ⟨0, 0, fun h' ↦ absurd h' hi⟩
  choose m g hmg using hdec
  refine ⟨∑ i ∈ S, c i * (m i : F), ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Derivation.leibniz, hc i hi, Derivation.map_intCast]
    simp
  · have := residue_criterion_local hp hnorm hnat b s₁ hs₁ S (fun i ↦ C (c i)) u g m v
      (fun i hi ↦ (hmg i hi).1) (fun i hi ↦ (hmg i hi).2) h
    convert this using 3
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_intCast]

end Differential
