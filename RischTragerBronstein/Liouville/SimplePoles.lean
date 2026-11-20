import RischTragerBronstein.Liouville.ResidueCriterion
import RischTragerBronstein.Liouville.LogPart

/-!
# Simple poles: constant residues are necessary and sufficient

Let `s = ∏_{j ∈ J} pⱼ` be a product of pairwise coprime **normal** primes of `F[t]`, `K = F(t)`.

* `residues_of_liouville` (necessity): if `b / s = ∑ cᵢ uᵢ′ / uᵢ + v′` with constant `cᵢ ∈ F`, then
  every `pⱼ` has a constant residue `Nⱼ ∈ F`: `pⱼ ∣ b - Nⱼ (pⱼ′ ∏_{i ≠ j} pᵢ)`.
* `sum_logDeriv_of_residues` (sufficiency, `LogPart.lean`): conversely such residues give
  `b / s = ∑ Nⱼ pⱼ′ / pⱼ`.

Together (`simple_poles_liouville_iff_residues`, under the degree hypotheses of the second): `b / s`
is a constant combination of logarithmic derivatives of elements of `F(t)`, up to a derivative, **iff**
all its residues are constants — the theorem behind the Rothstein–Trager algorithm.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

theorem residues_of_liouville {ι' : Type*} [DecidableEq ι'] (J : Finset ι') (p : ι' → F[X])
    (hprime : ∀ j ∈ J, Prime (p j)) (hnorm : ∀ j ∈ J, ¬p j ∣ (p j)′)
    (hcop : (J : Set ι').Pairwise fun i j ↦ IsCoprime (p i) (p j)) (b : F[X])
    {ι : Type*} (S : Finset ι) (c : ι → F) (hc : ∀ i ∈ S, (c i)′ = 0) (u : ι → K)
    (hu : ∀ i ∈ S, u i ≠ 0) (v : K)
    (h : φ b / φ (∏ j ∈ J, p j) = ∑ i ∈ S, φ (C (c i)) * logDeriv (u i) + v′) :
    ∀ j ∈ J, ∃ N : F, N′ = 0 ∧ p j ∣ b - C N * ((p j)′ * ∏ i ∈ J.erase j, p i) := by
  intro j hj
  have hsplit : ∏ i ∈ J, p i = p j * ∏ i ∈ J.erase j, p i := (Finset.mul_prod_erase J p hj).symm
  -- `p j` does not divide the cofactor
  have hndvd : ¬p j ∣ ∏ i ∈ J.erase j, p i := fun hdvd ↦ by
    have hcopP : IsCoprime (p j) (∏ i ∈ J.erase j, p i) :=
      IsCoprime.prod_right fun i hi ↦
        hcop hj (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi).symm
    exact (hprime j hj).not_isUnit (hcopP.isUnit_of_dvd' dvd_rfl hdvd)
  rw [hsplit] at h
  obtain ⟨N, hN, hdvd⟩ := residue_criterion (K := K) (hprime j hj) (hnorm j hj) b _ hndvd S c hc u
    hu v h
  refine ⟨N, hN, ?_⟩
  have hder : (p j * ∏ i ∈ J.erase j, p i)′ =
      (p j)′ * ∏ i ∈ J.erase j, p i + p j * (∏ i ∈ J.erase j, p i)′ := by
    rw [Derivation.leibniz]; simp only [smul_eq_mul]; ring
  rw [hder] at hdvd
  have : b - C N * ((p j)′ * ∏ i ∈ J.erase j, p i) =
      (b - C N * ((p j)′ * ∏ i ∈ J.erase j, p i + p j * (∏ i ∈ J.erase j, p i)′)) +
        p j * (C N * (∏ i ∈ J.erase j, p i)′) := by ring
  rw [this]
  exact dvd_add hdvd (dvd_mul_right _ _)

/-- **Simple poles**: a Liouville form with constant coefficients exists iff all residues are
constants. -/
theorem simple_poles_liouville_iff_residues {ι' : Type*} [DecidableEq ι'] (J : Finset ι')
    (p : ι' → F[X]) (hprime : ∀ j ∈ J, Prime (p j)) (hnorm : ∀ j ∈ J, ¬p j ∣ (p j)′)
    (hcop : (J : Set ι').Pairwise fun i j ↦ IsCoprime (p i) (p j))
    (hdegp : ∀ j ∈ J, ((p j)′).degree < (p j).degree) (b : F[X])
    (hdeg : b.degree < (∏ j ∈ J, p j).degree) :
    (∃ (S : Finset ι') (c : ι' → F) (u : ι' → K) (v : K), (∀ i ∈ S, (c i)′ = 0 ∧ u i ≠ 0) ∧
        φ b / φ (∏ j ∈ J, p j) = ∑ i ∈ S, φ (C (c i)) * logDeriv (u i) + v′) ↔
      ∀ j ∈ J, ∃ N : F, N′ = 0 ∧ p j ∣ b - C N * ((p j)′ * ∏ i ∈ J.erase j, p i) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  constructor
  · rintro ⟨S, c, u, v, hdata, h⟩
    exact residues_of_liouville J p hprime hnorm hcop b S c (fun i hi ↦ (hdata i hi).1) u
      (fun i hi ↦ (hdata i hi).2) v h
  · intro hres
    choose! N hN using hres
    refine ⟨J, N, fun j ↦ φ (p j), 0, fun j hj ↦ ⟨(hN j hj).1,
      (map_ne_zero_iff _ hinj).mpr (hprime j hj).ne_zero⟩, ?_⟩
    rw [map_zero, add_zero]
    exact sum_logDeriv_of_residues hinj J p N b (fun j hj ↦ (hprime j hj).ne_zero) hcop hdegp hdeg
      fun j hj ↦ (hN j hj).2

end Differential
