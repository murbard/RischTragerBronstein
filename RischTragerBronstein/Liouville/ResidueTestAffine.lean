import RischTragerBronstein.Liouville.ResidueTest

/-!
# The residue test is affine in a constant parameter

For the parametric integrand `ρ - c W` (`c` a constant), written over the denominator `s · m` with
`s = s_W` squarefree and `m` prime to `s`:

  `(q s m + B₁ - c r_W m) / (s m) = ∑ cᵢ uᵢ′ / uᵢ + v′`  ⟹  `s ∣ T(r₁, s) - c T(r_W*, s)`,

where `r₁ (s′ m) ≡ B₁` and `r_W* s′ ≡ r_W` modulo `s`. When `s ∤ T(r_W*, s)` (the residues of `W`
are not constants) this determines `c`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

lemma mapCoeffs_C_mul_of_const {c : F} (hc : c′ = 0) (P : F[X]) :
    mapCoeffs (C c * P) = C c * mapCoeffs P := by
  ext n
  rw [coeff_mapCoeffs, coeff_C_mul, coeff_C_mul, coeff_mapCoeffs, Derivation.leibniz, hc]
  simp

lemma residueTest_sub_C_mul {c : F} (hc : c′ = 0) (r₁ r₂ s : F[X]) :
    residueTest (r₁ - C c * r₂) s = residueTest r₁ s - C c * residueTest r₂ s := by
  rw [residueTest, residueTest, residueTest, map_sub, mapCoeffs_C_mul_of_const hc, derivative_sub,
    derivative_mul, derivative_C]
  ring

theorem dvd_residueTest_affine {s m q B₁ rW r₁ rWs : F[X]} {c : F} (hc : c′ = 0)
    (hs : Squarefree s) (hnorm : ∀ p : F[X], Irreducible p → p ∣ s → ¬p ∣ p′)
    (hm : ∀ p : F[X], Irreducible p → p ∣ s → ¬p ∣ m)
    (hr₁ : s ∣ r₁ * (s′ * m) - B₁) (hrW : s ∣ rWs * s′ - rW)
    {ι : Type*} (S : Finset ι) (cs : ι → F) (hcs : ∀ i ∈ S, (cs i)′ = 0) (u : ι → K)
    (hu : ∀ i ∈ S, u i ≠ 0) (v : K)
    (h : φ (q * (s * m) + (B₁ - C c * rW * m)) / φ (s * m) =
      ∑ i ∈ S, φ (C (cs i)) * logDeriv (u i) + v′) :
    s ∣ residueTest r₁ s - C c * residueTest rWs s := by
  rw [← residueTest_sub_C_mul hc]
  refine dvd_residueTest_mul (b := r₁ * s′ - C c * rW) hs hnorm hm ?_ ?_ S cs hcs u hu v h
  · have : q * (s * m) + (B₁ - C c * rW * m) - (r₁ * s′ - C c * rW) * m =
        s * (q * m) - (r₁ * (s′ * m) - B₁) := by ring
    rw [this]
    exact dvd_sub (dvd_mul_right _ _) hr₁
  · have : (r₁ - C c * rWs) * s′ - (r₁ * s′ - C c * rW) = -(C c * (rWs * s′ - rW)) := by ring
    rw [this]
    exact (dvd_neg).mpr (hrW.mul_left _)

end Differential
