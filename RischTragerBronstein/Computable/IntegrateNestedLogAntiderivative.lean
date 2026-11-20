import RischTragerBronstein.Computable.IntegrateNestedLog
import RischTragerBronstein.Computable.IntegratePrim2Antiderivative

/-!
# The nested-primitive integrator returns an antiderivative

With `t₂′ = W ∈ R(x)(t₁)` (any nested primitive handled by the loop `prim2LoopW`): when the loop
succeeds on the polynomial part,

  `A / D = (gn / gd + W_poly)′ + ρ + rem / s`

with `gn / gd` the Hermite part, `W_poly = prim2WVal …` the closed-form polynomial part,
`ρ = A₀ - W Q₁ ∈ R(x)(t₁)` the level-0 remainder and `rem / s` the part with simple poles.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

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

set_option maxHeartbeats 1600000 in
/-- **The result is an antiderivative** (nested primitive `t₂′ = W`). -/
theorem integrateNestedLog_antiderivative (h0 : ∀ r : R, r′ = 0) {En₁ Ed₁ : CPoly R}
    (M : ModelW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) En₁ Ed₁) (W : GFrac (GFrac R))
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C ((M.cf (RingHom.id R) h0).sem W)) P)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 = false)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false)
    {L : List (R × GFrac (GFrac R))}
    (hL : prim2LoopW En₁ Ed₁ Iη₁ W
      (fun k ↦ (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).b (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).s).1.getD k ([], [(ops₁g R).one]))
      (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).b (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).s).1.length ([], [(ops₁g R).one]) = some L) :
    algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) A) / algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) D) =
      (algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).gn) /
          algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).gd) +
        prim2WVal (M.cf (RingHom.id R) h0).sem
          (fun r ↦ algebraMap K₁ K₂ (algebraMap R[X] K₁ (C r))) (algebraMap K₂[X] K₃ X)
          ((GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).b (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).s).1.length + 1) ([], [(ops₁g R).one]) L)′ +
      algebraMap K₂ K₃ ((M.cf (RingHom.id R) h0).sem (gCodeW En₁ Ed₁ W 0
          ((GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).b (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).s).1.getD 0 ([], [(ops₁g R).one])) (lastGen ([], [(ops₁g R).one]) L))) +
      algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).b (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).s).2) /
        algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.hermite (ops₂p En₁ Ed₁) [W] A D).s) := by
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
  have ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁) := by
    rw [← hev (En₁, Ed₁), ht₁d, deriv_algebraMap, M.hD₂, ← hCφ₂]
    simp [implicitDeriv]
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
    rw [hM₂, sem_M₂W, valG, hvalP, hvalP]
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
  have hEd₁ : toPoly Ed₁ ≠ 0 := by
    have hc := hcη₁
    rw [rationalCheck, Bool.and_eq_true] at hc
    exact ((hermiteCheck_iff _ _ _).mp hc.1).1
  have hW0' : GPoly.toPoly M₁ W.2 ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₁ W.2).mpr hz] at hW0
    exact Bool.noConfusion hW0
  -- normality at the top level
  have hη₂nd : ∀ y : K₂, y′ ≠ η₂ := fun y hy ↦ by
    have := isDerivPrim_complete (K₁ := K₁) (K₂ := K₂) (RingHom.id R) h0 M.hD M.hKconst hcη₁
      hEd₁ hη₁0 M.hD₂ M.hconst₂ W.1 W.2 hW0' y (by rw [hy, hη₂, hM₂, sem_M₂W])
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
  generalize GPoly.hermite (ops₂p En₁ Ed₁) [W] A D = h at hchk hL ⊢
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₃) M₂ [W] A D h hD₃' hchk
  set S := GPoly.toPoly M₂ h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hdm := GPoly.divMod_spec M₂ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₂ h.b h.s hS0
  generalize GPoly.divMod (ops₂p En₁ Ed₁) h.b h.s = qr at hdm hdeglt hL ⊢
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
    rw [hM₂, sem_M₂W]
    simp
  have hsum : ∑ k ∈ Finset.range (qr.1.length + 1),
      algebraMap K₂ K₃ (valG x₀ t₁ (qr.1.getD k ([], [(ops₁g R).one]))) * t ^ k =
      φ₃ (GPoly.toPoly M₂ qr.1) := by
    rw [Finset.sum_range_succ, List.getD_eq_default _ _ le_rfl, hvalG, hdflt, map_zero, zero_mul,
      add_zero, GPoly.toPoly_eq_sum_range _ qr.1 ([], [(ops₁g R).one]), map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, hCφ₃, hvalG]
  have hφS : φ₃ S ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr hS0
  have hanti := prim2LoopW_antiderivative (K := K₃) hR x₀ t₁ hx₀ ht₁ W t ht hcη₁ hη₁0
    _ qr.1.length _ hL
  have hQ0 : valG x₀ t₁ (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by rw [hvalG, hdflt]
  rw [hQ0, map_zero, map_zero, zero_mul, zero_add] at hanti
  obtain ⟨-, hval⟩ := valG_gCodeW_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 W 0
    (qr.1.getD 0 ([], [(ops₁g R).one])) (lastGen ([], [(ops₁g R).one]) L)
  have hWeq : ∀ (m : ℕ) (Q : GFrac (GFrac R)) (L : List (R × GFrac (GFrac R))),
      prim2WGen x₀ t₁ t m Q L = prim2WVal M₂.sem
        (fun r ↦ algebraMap K₁ K₂ (algebraMap R[X] K₁ (C r))) t m Q L := fun m Q L ↦ by
    induction L generalizing m Q with
    | nil => rw [prim2WGen, prim2WVal, hvalG]
    | cons cQ L ih =>
      rw [prim2WGen, prim2WVal, hvalG, ih]
      rfl
  rw [hid, hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one, ← hsum, hanti,
    ← hvalG, hval, ← hWeq, map_add]
  simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]
  ring

end Tower
