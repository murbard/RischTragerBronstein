import RischTragerBronstein.Liouville.ProperFraction
import RischTragerBronstein.Liouville.HermitePrimitive
import RischTragerBronstein.Liouville.PrimitivePoly

/-!
# Integration inside a primitive extension: the coefficient equations

`K = F(t)`, `t′ = η ∈ F` primitive without new constants. If a Hermite-reduced element
`A + b / s` (`s` squarefree, `deg b < deg s`) is the derivative of some `z ∈ K`, then `b = 0`, and
`z = ∑ pⱼ t ^ j` with

  `pⱼ′ + (j + 1) η pⱼ₊₁ = Aⱼ` for **all** `j ≥ 0`,

`p_{d+1}` constant and `p_{d+2} = 0` for `d ≥ deg A`. (Compare `exists_coeffs_of_liouville_primitive`,
where new logarithms are allowed and the equation at `j = 0` is lost.) This is the recursion behind
limited integration inside `F(t)`, the ingredient of towers of height ≥ 3.
-/

open Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

theorem coeffs_of_deriv_in_primitive (η : F) (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hconst : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e)
    (A b s : F[X]) (hs : Squarefree s) (hdeg : b.degree < s.degree) (z : K)
    (h : z′ = φ A + φ b / φ s) :
    b = 0 ∧ ∃ p : ℕ → F, (∀ j, (p j)′ + ((j + 1 : ℕ) : F) * η * p (j + 1) = A.coeff j) ∧
      ∀ d, A.natDegree ≤ d → (p (d + 1))′ = 0 ∧ p (d + 2) = 0 := by
  have hconst' : ∀ P : F[X], implicitDeriv (C η) P = 0 → ∃ e : F, P = C e :=
    fun P hP ↦ hconst P (by rw [hD, hP])
  obtain ⟨hb, P, -, hP⟩ := deriv_eq_poly_add_proper
    (fun p hp ↦ not_dvd_deriv_of_irreducible_primitive η hD hconst hp) A b s hs hdeg z h
  rw [hD] at hP
  have hcoeff : ∀ j, (P.coeff j)′ + ((j + 1 : ℕ) : F) * η * P.coeff (j + 1) = A.coeff j :=
    fun j ↦ by
      have hj := congrArg (fun Q : F[X] ↦ Q.coeff j) hP
      simp only [coeff_implicitDeriv_C] at hj
      rw [← hj]
      push_cast
      ring
  refine ⟨hb, P.coeff, hcoeff, fun d hd ↦ ?_⟩
  have hdegP := natDegree_le_succ_of_natDegree_deriv_le η hconst'
    (by rw [hP] : (implicitDeriv (C η) P).natDegree ≤ A.natDegree)
  have h2 : P.coeff (d + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨?_, h2⟩
  have h1 := hcoeff (d + 1)
  rw [h2, mul_zero, add_zero] at h1
  rw [h1]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

end Differential
