import RischTragerBronstein.Liouville.StepExponentialLaurent
import RischTragerBronstein.Liouville.HermiteExponential
import RischTragerBronstein.Liouville.ResidueTest

/-!
# The residue test inside an ambient field: exponential case

If `B(t) / (s(t) t ^ k)` (`t` exponential and transcendental over `F`, no new constants in `F⟮t⟯`,
`s` squarefree with `t ∤ s`, `B ≡ b t ^ k mod s`) has an integral of Liouville form inside
`F⟮t⟯ ⊆ E` with constant coefficients in `F`, the residue test passes: `s ∣ T(r, s)`.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

theorem residueTest_step_exponential (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η * t)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (hc : ∀ i ∈ s, (c i)′ = 0) (v : E) (hv : v ∈ F⟮t⟯) (B b sd r : F[X]) (k : ℕ)
    (hsd : Squarefree sd) (hX : ¬X ∣ sd) (hB : sd ∣ B - b * X ^ k)
    (hr : sd ∣ r * (mapCoeffs sd + C η * X * derivative sd) - b)
    (h : aeval t B / (aeval t sd * t ^ k) =
      ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    sd ∣ residueTest r sd := by
  classical
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η * X)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  have hinjφ : Function.Injective (algebraMap F[X] F⟮t⟯) := IsFractionRing.injective _ _
  -- no new constants, at the level of polynomials
  have hconstE : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n := by
    intro P n hP
    have hXn : algebraMap F[X] F⟮t⟯ (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ hinjφ).mpr (pow_ne_zero _ X_ne_zero)
    have h0 : (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n))′ = 0 := by
      rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap]
      simp only [smul_eq_mul, ← map_mul, ← map_sub]
      rw [show X ^ n * P′ - P * (X ^ n)′ = 0 by rw [← hP]; ring, map_zero, mul_zero]
    have h1 : ((algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n) : F⟮t⟯) : E)′ = 0 := by
      exact congrArg Subtype.val h0
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n)).2 h1
    refine ⟨e, hinjt ?_⟩
    have hXnE : aeval t (X ^ n : F[X]) ≠ 0 := by
      rw [← algebraMap_adjoinSimple]
      exact fun h' ↦ hXn (Subtype.ext h')
    rw [map_mul, aeval_C, he, IntermediateField.coe_div, algebraMap_adjoinSimple,
      algebraMap_adjoinSimple]
    field_simp
  -- lift the data to `F⟮t⟯`
  let u' : ι → F⟮t⟯ := fun i ↦ if hi : i ∈ s then ⟨u i, (hu i hi).1⟩ else 1
  let v' : F⟮t⟯ := ⟨v, hv⟩
  have hu' : ∀ i ∈ s, u' i ≠ 0 := fun i hi h0 ↦ by
    simp only [u', dif_pos hi] at h0
    exact (hu i hi).2 (congrArg Subtype.val h0)
  have hcoeC : ∀ a : F, ((algebraMap F[X] F⟮t⟯ (C a) : F⟮t⟯) : E) = algebraMap F E a := fun a ↦ by
    rw [algebraMap_adjoinSimple, aeval_C]
  have hlog : ∀ i ∈ s, ((logDeriv (u' i) : F⟮t⟯) : E) = logDeriv (u i) := fun i hi ↦ by
    simp only [u', dif_pos hi, logDeriv, IntermediateField.coe_div]
    rfl
  have h' : algebraMap F[X] F⟮t⟯ B / algebraMap F[X] F⟮t⟯ (sd * X ^ k) =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [IntermediateField.coe_div, algebraMap_adjoinSimple, algebraMap_adjoinSimple, map_mul,
      map_pow, aeval_X, h, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  have hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P := fun _ ↦ rfl
  have hXp : ∀ p : F[X], Irreducible p → p ∣ sd → ¬X ∣ p := fun p _ hps hXp ↦
    hX (hXp.trans hps)
  refine dvd_residueTest_mul (K := F⟮t⟯) hsd
    (fun p hp hps hsp ↦ hXp p hp hps (dvd_X_of_irreducible_special η hD hconstE hp hsp))
    (fun p hp hps hpk ↦ hXp p hp hps ?_) hB ?_ s c hc u' hu' v' h'
  · have hpX : p ∣ X := hp.prime.dvd_of_dvd_pow hpk
    exact (hp.associated_of_dvd irreducible_X hpX).symm.dvd
  · have hsd' : sd′ = mapCoeffs sd + C η * X * derivative sd := by
      change implicitDeriv (C η * X) sd = _
      simp [implicitDeriv]
    rw [hsd']
    exact hr

end Differential
