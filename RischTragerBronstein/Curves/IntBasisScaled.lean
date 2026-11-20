import RischTragerBronstein.Curves.IntBasisMain

/-!
# Logarithmic integral bases for a rescaled derivation

**`exists_logBasis_scaled`**: for a curve over `ℚ` inside a differential field `L` whose
derivation `D` kills `ℚ` and has `D x = e ≠ 0` (e.g. `x = t` a primitive over a differential field,
`e = η`), the conclusion of `exists_logBasis` holds for `D` with the factor `e`:
`S₀ D(wᵢ) = e ∑ⱼ Pᵢⱼ wⱼ`. (Apply `exists_logBasis` to the derivation `e⁻¹ D`, for which `x′ = 1`.)
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Scaled

variable {L : Type*} [Field L] [CharZero L]

lemma derivation_ratCast (D : Derivation ℤ L L) (q : ℚ) : D (q : L) = 0 := by
  have hb : ((q.den : ℤ) : L) * (q : L) = (q.num : L) := by
    rw [Rat.cast_def]
    have : ((q.den : ℤ) : L) ≠ 0 := by exact_mod_cast q.den_nz
    field_simp
    push_cast; ring
  have := congrArg D hb
  rw [Derivation.leibniz, Derivation.map_intCast, Derivation.map_intCast, smul_zero, add_zero,
    smul_eq_mul] at this
  have hd : ((q.den : ℤ) : L) ≠ 0 := by exact_mod_cast q.den_nz
  exact (mul_eq_zero.mp this).resolve_left hd

variable [Differential L]

namespace CurveData

/-- **Logarithmic integral bases for `D` with `D x = e`.** -/
theorem exists_logBasis_scaled (S : CurveData ℚ L) (e : L) (he : e ≠ 0) (hx : S.x′ = e) :
    ∃ (w : Fin S.F.natDegree → ℚ⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : ℚ[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → ℚ[X]),
      (∀ c : Fin S.F.natDegree → ℚ⟮S.x⟯,
        ∑ j, algebraMap ℚ⟮S.x⟯ (ℚ⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, ((w i : L))′ * aeval S.x S0 = e * ∑ j, aeval S.x (P i j) * (w j : L)) ∧
      ∀ i j, (X ^ (r j + 1) * P i j -
        (if i = j then Polynomial.C (r i : ℚ) * X ^ r i * S0 else 0)).natDegree ≤
          r i + S0.natDegree := by
  let D0 : Derivation ℤ L L := Differential.deriv
  letI dQ : Differential ℚ := ⟨0⟩
  letI dL : Differential L := ⟨e⁻¹ • D0⟩
  haveI : DifferentialAlgebra ℚ L := ⟨fun q ↦ by
    show (e⁻¹ • D0) (algebraMap ℚ L q) = algebraMap ℚ L 0
    rw [Derivation.smul_apply, map_zero, eq_ratCast, derivation_ratCast, smul_zero]⟩
  have hC : ∀ c : ℚ, c′ = 0 := fun c ↦ rfl
  have hx0 : D0 S.x = e := hx
  have hx' : S.x′ = 1 := by
    show (e⁻¹ • D0) S.x = 1
    rw [Derivation.smul_apply, smul_eq_mul, hx0, inv_mul_cancel₀ he]
  obtain ⟨w, r, S0, P, hind, hS0, hsq, hder, hdeg⟩ := S.exists_logBasis hC hx'
  refine ⟨w, r, S0, P, hind, hS0, hsq, fun i ↦ ?_, hdeg⟩
  have h := congrArg (fun z : ℚ⟮S.x⟯⟮S.y⟯ ↦ (z : L)) (hder i)
  simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum] at h
  change (e⁻¹ • D0) (w i : L) * aeval S.x S0 = ∑ j, aeval S.x (P i j) * (w j : L) at h
  show D0 (w i : L) * aeval S.x S0 = e * ∑ j, aeval S.x (P i j) * (w j : L)
  rw [← h, Derivation.smul_apply, smul_eq_mul]
  field_simp

/-- **Logarithmic integral bases for `D` with `D x = e`, with their residue matrices.** -/
theorem exists_logBasis_scaledA (S : CurveData ℚ L) (e : L) (he : e ≠ 0) (hx : S.x′ = e) :
    ∃ (w : Fin S.F.natDegree → ℚ⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : ℚ[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → ℚ[X]),
      (∀ c : Fin S.F.natDegree → ℚ⟮S.x⟯,
        ∑ j, algebraMap ℚ⟮S.x⟯ (ℚ⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, ((w i : L))′ * aeval S.x S0 = e * ∑ j, aeval S.x (P i j) * (w j : L)) ∧
      (∀ i j, (X ^ (r j + 1) * P i j -
        (if i = j then Polynomial.C (r i : ℚ) * X ^ r i * S0 else 0)).natDegree ≤
          r i + S0.natDegree) ∧
      (∀ S1 : ℚ[X], S0 = X * S1 →
        ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
          S1.eval 0 * (k : ℚ) / S.F.natDegree.factorial).foldr
        (fun μ M ↦ M * (Matrix.of (fun i j ↦ (P i j).eval 0) - μ • 1)) 1 = 0) ∧
      ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
          -((k : ℚ) / S.F.natDegree.factorial)).foldr
        (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1 = 0 := by
  let D0 : Derivation ℤ L L := Differential.deriv
  letI dQ : Differential ℚ := ⟨0⟩
  letI dL : Differential L := ⟨e⁻¹ • D0⟩
  haveI : DifferentialAlgebra ℚ L := ⟨fun q ↦ by
    show (e⁻¹ • D0) (algebraMap ℚ L q) = algebraMap ℚ L 0
    rw [Derivation.smul_apply, map_zero, eq_ratCast, derivation_ratCast, smul_zero]⟩
  have hC : ∀ c : ℚ, c′ = 0 := fun c ↦ rfl
  have hx0 : D0 S.x = e := hx
  have hx' : S.x′ = 1 := by
    show (e⁻¹ • D0) S.x = 1
    rw [Derivation.smul_apply, smul_eq_mul, hx0, inv_mul_cancel₀ he]
  obtain ⟨w, r, S0, P, hind, hS0, hsq, hder, hdeg, h0, hinf⟩ := S.exists_logBasisA hC hx'
  refine ⟨w, r, S0, P, hind, hS0, hsq, fun i ↦ ?_, hdeg, h0, hinf⟩
  have h := congrArg (fun z : ℚ⟮S.x⟯⟮S.y⟯ ↦ (z : L)) (hder i)
  simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum] at h
  change (e⁻¹ • D0) (w i : L) * aeval S.x S0 = ∑ j, aeval S.x (P i j) * (w j : L) at h
  show D0 (w i : L) * aeval S.x S0 = e * ∑ j, aeval S.x (P i j) * (w j : L)
  rw [← h, Derivation.smul_apply, smul_eq_mul]
  field_simp

end CurveData

end Scaled

end Curves
