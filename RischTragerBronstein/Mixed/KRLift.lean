import RischTragerBronstein.Mixed.KQMMain

/-!
# Adjoining a constant `ⁿ√κ` and a primitive `n`-th root of unity

`root_zeta_ext`: a finite (hence elementary) extension containing a constant `s` with `sⁿ = κ` and a
primitive `n`-th root of unity `ζ` (constant). `kr_lift`: the Liouville data of an elementary
integral of `f θʲ` in such an extension, for the lifted realization of the tower.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

universe v

/-- **Adjoining `ⁿ√κ` and `ζₙ`**: a finite, hence elementary, extension. -/
theorem root_zeta_ext (E : Type v) [Field E] [Differential E] [CharZero E] (n : ℕ) (hn : 0 < n)
    (κ : ℚ) (hκ : κ ≠ 0) :
    ∃ (E₂ : Type v) (_ : Field E₂) (_ : Differential E₂) (_ : Algebra E E₂)
      (_ : DifferentialAlgebra E E₂), IsElementaryExtension E E₂ ∧ Algebra.IsAlgebraic E E₂ ∧
        ∃ s ζ : E₂, s ^ n = κ ∧ s′ = 0 ∧ IsPrimitiveRoot ζ n ∧ ζ′ = 0 := by
  classical
  set q : E[X] := (X ^ n - Polynomial.C ((κ : ℚ) : E)) * cyclotomic n E
  letI : Differential (SplittingField q) := differentialFiniteDimensional E (SplittingField q)
  haveI : DifferentialAlgebra E (SplittingField q) := differentialAlgebraFiniteDimensional
  haveI : CharZero (SplittingField q) :=
    charZero_of_injective_algebraMap (algebraMap E (SplittingField q)).injective
  set F := SplittingField q
  have hf0 : X ^ n - Polynomial.C ((κ : ℚ) : E) ≠ 0 := X_pow_sub_C_ne_zero hn _
  have hc0 : cyclotomic n E ≠ 0 := cyclotomic_ne_zero n E
  have hq0 : q.map (algebraMap E F) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap E _).injective]; exact mul_ne_zero hf0 hc0
  have hs1 := (SplittingField.splits q).of_dvd hq0
    (Polynomial.map_dvd (algebraMap E F) (dvd_mul_right (X ^ n - Polynomial.C ((κ : ℚ) : E)) _))
  have hs2 := (SplittingField.splits q).of_dvd hq0
    (Polynomial.map_dvd (algebraMap E F) (dvd_mul_left (cyclotomic n E) _))
  obtain ⟨s, hs⟩ := hs1.exists_eval_eq_zero (by
    rw [degree_map, degree_X_pow_sub_C hn]; exact_mod_cast hn.ne')
  obtain ⟨ζ, hζ⟩ := hs2.exists_eval_eq_zero (by
    rw [degree_map, degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hn).ne')
  have hsn : s ^ n = (κ : F) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      eval_sub, eval_pow, eval_X, eval_C, map_ratCast] at hs
    linear_combination hs
  haveI : NeZero (n : F) := ⟨by exact_mod_cast hn.ne'⟩
  have hζp : IsPrimitiveRoot ζ n := by
    rw [map_cyclotomic] at hζ
    exact (isRoot_cyclotomic_iff).mp hζ
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance,
    isElementaryExtension_of_finiteDimensional, Algebra.IsAlgebraic.of_finite _ _, s, ζ, hsn, ?_,
    hζp, LaurentSeries.deriv_root_of_unity hn hζp.pow_eq_one⟩
  have hs0 : s ≠ 0 := fun h ↦ by
    rw [h, zero_pow hn.ne'] at hsn; exact hκ (by exact_mod_cast hsn.symm)
  have hd := congrArg (fun w ↦ w′) hsn
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
  rw [Tower.NestP.deriv_ratCastK (K := F) κ] at hd
  have hn' : ((n : ℕ) : F) * s ^ (n - 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ hs0)
  have : ((n : ℕ) : F) * s ^ (n - 1) * s′ = 0 := by rw [← hd]; ring
  exact (mul_eq_zero.mp this).resolve_left hn'

end Differential

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Lifting an elementary integral**: the Liouville data of `f θʲ` in an elementary extension
containing a constant `ⁿ√κ` and a primitive `n`-th root of unity, for the lifted realization. -/
theorem kr_lift (m : ℕ) (hn : T.n = m + 1) (n : ℕ) (hn0 : 0 < n) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ n = T.evP m A) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (k l j : ℕ)
    (hf : HasElementaryIntegral (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j))
    (κ : ℚ) (hκ : κ ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Differential E) (_ : CharZero E)
      (TE : MTower Fc ks (constants E) E) (θE s ζ : E) (ι : Type) (sI : Finset ι) (c u : ι → E)
      (v : E), TE.n = m + 1 ∧ θE ^ n = TE.evP m A ∧ s ^ n = κ ∧ s′ = 0 ∧
      IsPrimitiveRoot ζ n ∧ ζ′ = 0 ∧
      (∀ i ∈ sI, (c i)′ = 0) ∧
      (∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE}) ∧
      v ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} ∧
      TE.evP m B / (TE.ts m ^ k * TE.evP m A ^ l) * θE ^ j = v′ + ∑ i ∈ sI, c i * logDeriv (u i) := by
  classical
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨E₂, _, _, _, _, hE₁₂, -, s, ζ, hsn, hs', hζ, hζ'⟩ := root_zeta_ext E₁ n hn0 κ hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap E₁ E₂).injective
  letI : Algebra L E₂ := ((algebraMap E₁ E₂).comp (algebraMap L E₁)).toAlgebra
  haveI : IsScalarTower L E₁ E₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI hDA₂ : DifferentialAlgebra L E₂ :=
    ⟨fun z ↦ by
      change (algebraMap E₁ E₂ (algebraMap L E₁ z))′ = algebraMap E₁ E₂ (algebraMap L E₁ z′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hE₂ : IsElementaryExtension L E₂ := hE₁.trans hE₁₂
  have hg₂ : (algebraMap E₁ E₂ g)′ =
      algebraMap L E₂ (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j) := by
    rw [deriv_algebraMap, hg]; rfl
  obtain ⟨ι, sI, c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₂ _ _ hg₂
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₂
  set ψ := algebraMap L E₂ with hψ
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    induction P with
    | nil => simp [evP, evPL]
    | cons a P ih =>
      simp only [evP, evPL, List.foldr_cons] at ih ⊢
      rw [ih, map_add, map_mul, hTEts m, ← hTEev m a]
  set θE := ψ θ
  have hT1 : ∀ w ∈ TE.F (m + 1), w ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} :=
    fun w hw ↦ IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : TE.F (m + 1))
  have hLT : ∀ z : L, ψ z ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hT1 _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₂, w ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := TE.hconst w hw
      rw [← hc0]
      exact hT1 _ (TE.const_mem (m + 1) c0)
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  refine ⟨E₂, inferInstance, inferInstance, inferInstance, TE, θE, s, ζ, ι, sI, c, u, v,
    by rw [hTEn, hn], by rw [hPE, ← map_pow, hθ], hsn, hs', hζ, hζ', fun i hi ↦ (hdata i hi).1,
    fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩, hCT _ hv, ?_⟩
  rw [hPE, hPE, hTEts m, add_comm, ← heqL]
  simp only [map_mul, map_div₀, map_pow]
  rfl

end MTower

end Curves.MT
