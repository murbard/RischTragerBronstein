import RischTragerBronstein.Computable.PrimHexpFullDecision
import RischTragerBronstein.Computable.IntegratePrimExp
import RischTragerBronstein.Computable.IntegrateNestedLog

/-!
# The integrator for a logarithm over a general hyperexponential `R(x)(t₁)(t₂)`, `t₂ = log U`

`t₁′ = η t₁` with `η = Hn / Hd ∈ R(x)` arbitrary (certified monomial by `hyperexpMonomialCheck`),
e.g. `ℚ(x, exp (arctan x), log (exp (arctan x) + x))`. `Tower.integratePrimHexp`: Hermite reduction at
`t₂` over the computable field `R(x)(t₁)`, the residue test, and the polynomial part
`integratePrimHexpPoly`. `Tower.integratePrimHexp_decides`: every element, both directions.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- **The integrator for `R(x)(exp a₁)(log U)`**, as a decision procedure. -/
def integratePrimHexp (Hn Hd μ : CPoly R) (W : GFrac (GFrac R))
    (A D : GPoly (GFrac (GFrac R))) : Bool :=
  let h := GPoly.hermite (ops₂h Hn Hd) [W] A D
  let qr := GPoly.divMod (ops₂h Hn Hd) h.b h.s
  GPoly.residueCheck (ops₂h Hn Hd) [W] qr.2 h.s &&
    integratePrimHexpPoly Hn Hd μ W (fun k ↦ qr.1.getD k ([], [(ops₁g R).one])) qr.1.length

end Defs

universe u

variable {R K₁ K₂ : Type*} {K₃ : Type u} [Field R] [DecidableEq R] [CharZero R]
variable [Differential R] [Differential R[X]] [Field K₁] [CharZero K₁] [Algebra R[X] K₁]
variable [IsFractionRing R[X] K₁] [Differential K₁] [DifferentialAlgebra R[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]
variable [Differential K₂[X]] [Field K₃] [Differential K₃] [Algebra K₂[X] K₃]
variable [IsFractionRing K₂[X] K₃] [DifferentialAlgebra K₂[X] K₃]
variable [Algebra K₂ K₃] [IsScalarTower K₂ K₂[X] K₃] [DifferentialAlgebra K₂ K₃]
variable [CPoly.HasRatRoots R] [HasNatTest R]

set_option maxHeartbeats 1600000 in
/-- **Logarithms over `R(x)(exp a₁)` are decided**: every element, both directions, no
assumption on constants. -/
theorem integratePrimHexp_decides (h0 : ∀ r : R, r′ = 0) {Hn Hd μ : CPoly R}
    (M : ModelHW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) Hn Hd μ) (W U : GFrac (GFrac R))
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C ((M.cf (RingHom.id R) h0).sem W)) P)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivHexp Hn Hd μ W.1 W.2 = false)
    (hU0 : (ops₂h Hn Hd).isZero U = false)
    (hlog : (ops₂h Hn Hd).isZero ((ops₂h Hn Hd).add ((ops₂h Hn Hd).mul W U)
      ((ops₂h Hn Hd).neg ((ops₂h Hn Hd).deriv U))) = true)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    HasElementaryIntegral
        (algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) A) /
          algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) D)) ↔
      integratePrimHexp Hn Hd μ W A D = true := by
  classical
  set φ₁ := algebraMap R[X] K₁ with hφ₁
  set φ₂ := algebraMap K₁[X] K₂ with hφ₂
  set φ₃ := algebraMap K₂[X] K₃ with hφ₃
  have hchar2 : CharZero K₂ := charZero_of_injective_algebraMap (algebraMap K₁ K₂).injective
  have hchar3 : CharZero K₃ := charZero_of_injective_algebraMap (algebraMap K₂ K₃).injective
  -- `R`-algebra structures
  let ψ : R[X] →+* K₂ := (algebraMap K₁ K₂).comp φ₁
  let _ : Algebra R K₂ := (ψ.comp C).toAlgebra
  let _ : Algebra R K₃ := ((algebraMap K₂ K₃).comp (ψ.comp C)).toAlgebra
  have hST : IsScalarTower R K₂ K₃ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hCφ₂ : ∀ e : K₁, φ₂ (C e) = algebraMap K₁ K₂ e := fun e ↦ by
    rw [IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, Polynomial.algebraMap_eq]
  have hCφ₃ : ∀ e : K₂, φ₃ (C e) = algebraMap K₂ K₃ e := fun e ↦ by
    rw [IsScalarTower.algebraMap_apply K₂ K₂[X] K₃, Polynomial.algebraMap_eq]
  set x₀ : K₂ := ψ X with hx₀d
  set t₁ : K₂ := φ₂ X with ht₁d
  set t : K₃ := φ₃ X with htd
  have haev : ∀ P : R[X], aeval x₀ P = ψ P := fun P ↦ by
    rw [aeval_def]
    conv_rhs => rw [← eval₂_C_X (p := P)]
    rw [hom_eval₂]
    rfl
  have hev : ∀ q : CPoly R × CPoly R, algebraMap K₁ K₂ (ev K₁ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    rw [haev, haev, ev, Polynomial.map_id, Polynomial.map_id, map_div₀]
    rfl
  have hR : ∀ r : R, (algebraMap R K₂ r)′ = 0 := fun r ↦ by
    change (algebraMap K₁ K₂ (φ₁ (C r)))′ = 0
    rw [deriv_algebraMap, deriv_algebraMap, M.hD, derivative_C, map_zero, map_zero]
  have hx₀ : x₀′ = 1 := by
    change (algebraMap K₁ K₂ (φ₁ X))′ = 1
    rw [deriv_algebraMap, deriv_algebraMap, M.hD, derivative_X, map_one, map_one]
  have ht₁0 : t₁ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K₁[X] K₂)).mpr X_ne_zero
  have ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁ := by
    rw [haev, haev, ht₁d, deriv_algebraMap, M.hD₂, implicitDeriv_X, map_mul, hCφ₂]
    congr 1
    rw [ηh, Polynomial.map_id, Polynomial.map_id, map_div₀]
    rfl
  -- generation
  have hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R K₂) := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    refine mem_subfield_of_isFractionRing (F := K₁) (adjoin R {x₀, t₁}).toSubfield (fun a ↦ ?_)
      (subset_adjoin R _ (Or.inr rfl)) y
    rw [hCφ₂]
    refine mem_subfield_of_isFractionRing (F := R)
      ((adjoin R {x₀, t₁}).toSubfield.comap (algebraMap K₁ K₂)) (fun r ↦ ?_) ?_ a
    · exact (adjoin R {x₀, t₁}).algebraMap_mem r
    · exact subset_adjoin R _ (Or.inl rfl)
  have hgen : adjoin K₂ {t} = (⊤ : IntermediateField K₂ K₃) := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    refine mem_subfield_of_isFractionRing (F := K₂) (adjoin K₂ {t}).toSubfield (fun a ↦ ?_)
      (mem_adjoin_simple_self K₂ t) y
    rw [hCφ₃]
    exact (adjoin K₂ {t}).algebraMap_mem a
  -- the model of `R(x)(t₁)` and its values
  set M₁ := M₁In (K₁ := K₁) (RingHom.id R) h0 M.hD with hM₁
  set M₂ := M.cf (RingHom.id R) h0 with hM₂
  have hvalP : ∀ q : GPoly (GFrac R), valP x₀ t₁ q = φ₂ (GPoly.toPoly M₁ q) := fun q ↦ by
    rw [GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, hCφ₂, hM₁, sem_M₁In, hev]
    rfl
  have hvalG : ∀ q : GFrac (GFrac R), valG x₀ t₁ q = M₂.sem q := fun q ↦ by
    rw [hM₂, ModelHW.cf, sem_M₂H, valG, hvalP, hvalP]
  set η₂ : K₂ := M₂.sem W with hη₂
  have hη₂eq : valG x₀ t₁ W = η₂ := hvalG W
  have ht : t′ = algebraMap K₂ K₃ (valG x₀ t₁ W) := by
    rw [hη₂eq, htd, deriv_algebraMap, hD₃, ← hCφ₃]
    simp [implicitDeriv]
    rfl
  have hW : GPoly.toPoly M₂ [W] = C η₂ := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
  have hD₃' : ∀ P : K₂[X], P′ = implicitDeriv (GPoly.toPoly M₂ [W]) P :=
    fun P ↦ by rw [hW]; exact hD₃ P
  have hW0' : GPoly.toPoly M₁ W.2 ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₁ W.2).mpr hz] at hW0
    exact Bool.noConfusion hW0
  -- normality at the top level
  have hη₂nd : ∀ y : K₂, y′ ≠ η₂ := fun y hy ↦ by
    have := isDerivHexp_complete (K₁ := K₁) (K₂ := K₂) (RingHom.id R) h0 M.hD Hn Hd μ M.hHn0 M.hHd0
      M.hcop M.hcert M.hD₂
      M.hconst W.1 W.2 hW0' y (by rw [hy, hη₂, hM₂, ModelHW.cf, sem_M₂H])
    rw [hWnd] at this
    exact Bool.noConfusion this
  have hconst₃ : ∀ P : K₂[X], P′ = 0 → ∃ e : K₂, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero η₂ hη₂nd (by rw [← hD₃, hP])
  have hnormal : ∀ p : K₂[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive η₂ hD₃ hconst₃ hp
  have hDne : GPoly.toPoly M₂ D ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₂ D).mpr hz] at hD0
    exact Bool.noConfusion hD0
  -- Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M₂ [W] A D
    (fun p hp _ ↦ by rw [← hD₃']; exact hnormal p hp) hDne
  simp only [integratePrimHexp]
  generalize GPoly.hermite (ops₂h Hn Hd) [W] A D = h at hchk ⊢
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₃) M₂ [W] A D h hD₃' hchk
  set S := GPoly.toPoly M₂ h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hdm := GPoly.divMod_spec M₂ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₂ h.b h.s hS0
  generalize GPoly.divMod (ops₂h Hn Hd) h.b h.s = qr at hdm hdeglt ⊢
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M₂ [W]) S) S := by
    rw [← hD₃']
    exact isCoprime_deriv_of_squarefree hsq fun p hp _ ↦ hnormal p hp
  have hr := GPoly.residuePoly_spec M₂ [W] qr.2 h.s hS0 hcop
  have hidd : implicitDeriv (GPoly.toPoly M₂ [W]) S =
      mapCoeffs S + C (valG x₀ t₁ W) * derivative S := by
    rw [hW, hη₂eq]
    simp [implicitDeriv]
  rw [hidd] at hr
  have haev₃ : ∀ P : K₂[X], aeval t P = φ₃ P := fun P ↦ by
    rw [htd, aeval_algebraMap_apply, aeval_X_left_apply]
  have hst : aeval t S ≠ 0 := by
    rw [haev₃]
    exact (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr hS0
  -- the polynomial part, coefficientwise
  have hdflt : M₂.sem (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by
    rw [hM₂, ModelHW.cf, sem_M₂H]
    simp
  have hsum : ∑ k ∈ Finset.range (qr.1.length + 1),
      algebraMap K₂ K₃ (valG x₀ t₁ (qr.1.getD k ([], [(ops₁g R).one]))) * t ^ k =
      φ₃ (GPoly.toPoly M₂ qr.1) := by
    rw [Finset.sum_range_succ, List.getD_eq_default _ _ le_rfl, hvalG, hdflt, map_zero, zero_mul,
      add_zero, GPoly.toPoly_eq_sum_range _ qr.1 ([], [(ops₁g R).one]), map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, hCφ₃, hvalG]
  have key := primHexpFull_decides (K := K₃) hR x₀ t₁ hx₀ Hn Hd μ M.hHn0 M.hHd0 M.hcop M.hcert ht₁0 ht₁ hgen₀
    W U t hgen ht
    hW0 hWnd hU0 hlog
    (φ₃ (GPoly.toPoly M₂ h.gn) / φ₃ (GPoly.toPoly M₂ h.gd)) qr.1.length
    (fun k ↦ qr.1.getD k ([], [(ops₁g R).one])) (GPoly.toPoly M₂ qr.2) S _ hsq hdeglt hst hr
  have hφS : φ₃ S ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr hS0
  have hform : φ₃ (GPoly.toPoly M₂ A) / φ₃ (GPoly.toPoly M₂ D) =
      (φ₃ (GPoly.toPoly M₂ h.gn) / φ₃ (GPoly.toPoly M₂ h.gd))′ +
        ∑ k ∈ Finset.range (qr.1.length + 1),
          algebraMap K₂ K₃ (valG x₀ t₁ (qr.1.getD k ([], [(ops₁g R).one]))) * t ^ k +
        aeval t (GPoly.toPoly M₂ qr.2) / aeval t S := by
    rw [hid, hsum, haev₃, haev₃, hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφS,
      mul_one]
    ring
  rw [hform, key, Bool.and_eq_true, GPoly.residueCheck_iff M₂ [W] qr.2 h.s hS0]

end Tower
