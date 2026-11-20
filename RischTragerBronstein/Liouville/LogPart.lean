import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Field

/-!
# The logarithmic part: constant residues suffice

Let `s = ∏_{j ∈ J} pⱼ` with the `pⱼ ∈ F[t]` pairwise coprime and `deg pⱼ′ < deg pⱼ`, and let
`deg b < deg s`. If every `pⱼ` has a residue `cⱼ ∈ F`, in the sense

  `pⱼ ∣ b - cⱼ * (pⱼ′ * ∏_{i ≠ j} pᵢ)`,

then (`sum_logDeriv_of_residues`)

  `b / s = ∑ⱼ cⱼ * pⱼ′ / pⱼ`,

so that `∫ b / s = ∑ cⱼ log pⱼ` when the `cⱼ` are constants. This is the converse of the residue
criterion (`residue_criterion`): for simple-pole integrands, constant residues are necessary *and
sufficient* for a logarithmic antiderivative (Rothstein–Trager; Bronstein, Theorem 5.6.1).
-/

open Polynomial Finset

namespace Differential

variable {F K : Type*} [Field F] [Differential F[X]] [Field K] [Algebra F[X] K]
variable [Differential K] [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

theorem sum_logDeriv_of_residues (hinj : Function.Injective φ) {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (p : ι → F[X]) (c : ι → F) (b : F[X])
    (hp0 : ∀ j ∈ J, p j ≠ 0)
    (hcop : (J : Set ι).Pairwise fun i j ↦ IsCoprime (p i) (p j))
    (hdegp : ∀ j ∈ J, ((p j)′).degree < (p j).degree)
    (hdeg : b.degree < (∏ j ∈ J, p j).degree)
    (hres : ∀ j ∈ J, p j ∣ b - C (c j) * ((p j)′ * ∏ i ∈ J.erase j, p i)) :
    φ b / φ (∏ j ∈ J, p j) = ∑ j ∈ J, φ (C (c j)) * logDeriv (φ (p j)) := by
  set s := ∏ j ∈ J, p j with hs
  have hs0 : s ≠ 0 := Finset.prod_ne_zero_iff.mpr hp0
  have hsplit : ∀ j ∈ J, s = p j * ∏ i ∈ J.erase j, p i := fun j hj ↦
    (Finset.mul_prod_erase J p hj).symm
  -- the numerator of the difference
  set n := b - ∑ j ∈ J, C (c j) * ((p j)′ * ∏ i ∈ J.erase j, p i) with hn
  -- every `p k` divides `n`
  have hdvd : ∀ k ∈ J, p k ∣ n := fun k hk ↦ by
    have : n = (b - C (c k) * ((p k)′ * ∏ i ∈ J.erase k, p i)) -
        ∑ j ∈ J.erase k, C (c j) * ((p j)′ * ∏ i ∈ J.erase j, p i) := by
      rw [hn, ← Finset.add_sum_erase J _ hk]; ring
    rw [this]
    refine dvd_sub (hres k hk) (Finset.dvd_sum fun j hj ↦ ?_)
    have hkj : k ∈ J.erase j :=
      Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hj).symm, hk⟩
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem p hkj) _) _
  have hsn : s ∣ n := Finset.prod_dvd_of_coprime hcop hdvd
  -- but `deg n < deg s`
  have hdegn : n.degree < s.degree := by
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt hdeg ?_)
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hs0))]
    intro j hj
    have hP0 : ∏ i ∈ J.erase j, p i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi ↦ hp0 i (Finset.mem_of_mem_erase hi)
    calc (C (c j) * ((p j)′ * ∏ i ∈ J.erase j, p i)).degree
        ≤ ((p j)′ * ∏ i ∈ J.erase j, p i).degree := by
          by_cases hc : c j = 0
          · simp [hc]
          · rw [degree_C_mul hc]
      _ = ((p j)′).degree + (∏ i ∈ J.erase j, p i).degree := degree_mul
      _ < (p j).degree + (∏ i ∈ J.erase j, p i).degree :=
          WithBot.add_lt_add_right (degree_ne_bot.mpr hP0) (hdegp j hj)
      _ = s.degree := by rw [hsplit j hj, degree_mul]
  have hn0 : n = 0 := eq_zero_of_dvd_of_degree_lt hsn hdegn
  have hb : b = ∑ j ∈ J, C (c j) * ((p j)′ * ∏ i ∈ J.erase j, p i) := sub_eq_zero.mp hn0
  -- the identity in `K`
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  rw [div_eq_iff hφs, Finset.sum_mul]
  conv_lhs => rw [hb]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hφp : φ (p j) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hp0 j hj)
  rw [logDeriv, deriv_algebraMap]
  conv_rhs => rw [hsplit j hj]
  simp only [map_mul]
  field_simp

end Differential
