import RischTragerBronstein.Liouville.StepPrimitive
import RischTragerBronstein.Liouville.HermitePrimitive
import RischTragerBronstein.Liouville.ResidueTest

/-!
# The residue test inside an ambient field: primitive case

If `b(t) / s(t)` (`t` primitive and transcendental over `F`, no new constants in `F⟮t⟯`, `s`
squarefree, `b` arbitrary) has an integral of Liouville form inside `F⟮t⟯ ⊆ E` with constant
coefficients in `F`, the residue test passes: `s ∣ T(r, s)`.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

theorem residueTest_step_primitive (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (hc : ∀ i ∈ s, (c i)′ = 0) (v : E) (hv : v ∈ F⟮t⟯) (b sd r : F[X]) (hsd : Squarefree sd)
    (hr : sd ∣ r * (mapCoeffs sd + C η * derivative sd) - b)
    (h : aeval t b / aeval t sd = ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    sd ∣ residueTest r sd := by
  classical
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t (C η) hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t (C η) hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  -- no new constants, at the level of polynomials
  have hconstP : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e := fun P hP ↦ by
    have h1 : ((algebraMap F[X] F⟮t⟯ P : F⟮t⟯) : E)′ = 0 := by
      have := congrArg (fun y : F⟮t⟯ ↦ (y : E)) (deriv_algebraMap (A := F[X]) (B := F⟮t⟯) P)
      simp only [hP, map_zero, ZeroMemClass.coe_zero] at this
      exact this
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P).2 h1
    refine ⟨e, hinjt ?_⟩
    rw [aeval_C, he, algebraMap_adjoinSimple]
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
  have h' : algebraMap F[X] F⟮t⟯ b / algebraMap F[X] F⟮t⟯ sd =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [IntermediateField.coe_div, algebraMap_adjoinSimple, algebraMap_adjoinSimple, h,
      IntermediateField.coe_add,
      AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  have hD : ∀ P : F[X], P′ = implicitDeriv (C η) P := fun _ ↦ rfl
  refine dvd_residueTest (K := F⟮t⟯) hsd
    (fun p hp _ ↦ not_dvd_deriv_of_irreducible_primitive η hD hconstP hp) ?_ s c hc
    u' hu' v' h'
  have hsd' : sd′ = mapCoeffs sd + C η * derivative sd := by
    change implicitDeriv (C η) sd = _
    simp [implicitDeriv]
  rw [hsd']
  exact hr

end Differential
