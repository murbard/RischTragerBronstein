import RischTragerBronstein.Computable.IntegrateExpPrim
import RischTragerBronstein.Computable.IntegratePrim2Antiderivative

/-!
# The mixed-tower integrator returns an antiderivative

`t₂ = exp a` over `R(x)(t₁)`: when the Risch differential equations are solvable (`Yⱼ`),

  `A / D = (gn / gd + ∑_{j ≠ k} (Yⱼ / Dⱼ) t₂^j / t₂^k)′ + A_k + rem / s`

with `A_k ∈ R(x)(t₁)` the level-0 coefficient (handled by the height-two integrator).
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

set_option maxHeartbeats 3200000 in
/-- **The result is an antiderivative** (exponential over a primitive tower). -/
theorem integrateExpPrim_antiderivative (h0 : ∀ r : R, r′ = 0) {En₁ Ed₁ : CPoly R}
    (M : ModelW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) En₁ Ed₁) (a : CPoly R)
    (ha : trim (deriv a) ≠ [])
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (algebraMap K₁ K₂ (algebraMap R[X] K₁
      (derivative (toPoly a)))) * X) P)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false)
    (Y : ℕ → GPoly (GFrac R))
    (hY : ∀ j < (GPoly.add (ops₂p En₁ Ed₁) (GPoly.mul (ops₂p En₁ Ed₁) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).b (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s).1 (GPoly.monomial (ops₂p En₁ Ed₁) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 (ops₂p En₁ Ed₁).one)) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.1).length + (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 + 1, j ≠ (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 →
      rdePrim En₁ Ed₁ (expCoeffZ a ((j : ℤ) - (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1)) (normF₂ ((GPoly.add (ops₂p En₁ Ed₁) (GPoly.mul (ops₂p En₁ Ed₁) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).b (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s).1 (GPoly.monomial (ops₂p En₁ Ed₁) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 (ops₂p En₁ Ed₁).one)) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.1).getD j ([], [(ops₁g R).one]))).1 (normF₂ ((GPoly.add (ops₂p En₁ Ed₁) (GPoly.mul (ops₂p En₁ Ed₁) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).b (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s).1 (GPoly.monomial (ops₂p En₁ Ed₁) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 (ops₂p En₁ Ed₁).one)) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.1).getD j ([], [(ops₁g R).one]))).2 = some (Y j)) :
    algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) A) / algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) D) =
      (algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).gn) /
          algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).gd) +
        ∑ j ∈ (Finset.range ((GPoly.add (ops₂p En₁ Ed₁) (GPoly.mul (ops₂p En₁ Ed₁) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).b (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s).1 (GPoly.monomial (ops₂p En₁ Ed₁) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 (ops₂p En₁ Ed₁).one)) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.1).length + (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 + 1)).erase (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1,
          algebraMap K₂ K₃ (algebraMap K₁[X] K₂
              (GPoly.toPoly (M₁In (K₁ := K₁) (RingHom.id R) h0 M.hD) (Y j)) / algebraMap K₁[X] K₂
              (GPoly.toPoly (M₁In (K₁ := K₁) (RingHom.id R) h0 M.hD) (normF₂ ((GPoly.add (ops₂p En₁ Ed₁) (GPoly.mul (ops₂p En₁ Ed₁) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).b (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s).1 (GPoly.monomial (ops₂p En₁ Ed₁) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 (ops₂p En₁ Ed₁).one)) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.1).getD j ([], [(ops₁g R).one]))).2)) *
            algebraMap K₂[X] K₃ X ^ j / algebraMap K₂[X] K₃ X ^ (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1)′ +
      algebraMap K₂ K₃ ((M.cf (RingHom.id R) h0).sem (normF₂ ((GPoly.add (ops₂p En₁ Ed₁) (GPoly.mul (ops₂p En₁ Ed₁) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).b (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s).1 (GPoly.monomial (ops₂p En₁ Ed₁) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 (ops₂p En₁ Ed₁).one)) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.1).getD (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.1 ([], [(ops₁g R).one])))) +
      algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.divMod (ops₂p En₁ Ed₁) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).b (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s).2) /
        algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) (GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) (GPoly.expSplit (ops₂p En₁ Ed₁) A D).1 (GPoly.expSplit (ops₂p En₁ Ed₁) A D).2.2.2).s) := by
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
  set η₂ : K₂ := algebraMap K₁ K₂ (algebraMap R[X] K₁ (derivative (toPoly a))) with hη₂
  have hη₂eq : aeval x₀ (derivative (toPoly a)) = η₂ := by rw [haev]; rfl
  have hsemη : M₂.sem (expEta a) = η₂ := by
    rw [hM₂, sem_M₂W, expEta, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
      GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1, map_one,
      div_one, sem_M₁In, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K₁ K₁[X] K₂]
    congr 1
    rw [CPoly.ev, CPoly.toPoly_deriv]
    simp [CPoly.toPoly]
  have hW : GPoly.toPoly M₂ (expWPrim En₁ Ed₁ a) = C η₂ * X := by
    rw [expWPrim, GPoly.toPoly_cons, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
      CField.sem_zero, C_0, zero_add, hsemη, mul_comm]
  have ht : t′ = algebraMap K₂ K₃ (aeval x₀ (derivative (toPoly a))) * t := by
    rw [hη₂eq, htd, deriv_algebraMap, hD₃, ← hCφ₃]
    simp [implicitDeriv]
    rfl
  have ht0 : t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr X_ne_zero
  have hD₃' : ∀ P : K₂[X], P′ = implicitDeriv (GPoly.toPoly M₂ (expWPrim En₁ Ed₁ a)) P :=
    fun P ↦ by rw [hW]; exact hD₃ P
  have hconst := exp_no_new_constants_prim (K₁ := K₁) (K₂ := K₂) h0 M a ha hD₃
  have hDne : GPoly.toPoly M₂ D ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₂ D).mpr hz] at hD0
    exact Bool.noConfusion hD0
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M₂ A D hDne
  generalize GPoly.expSplit (ops₂p En₁ Ed₁) A D = sp at hsp1 hsp2 hsp3 hY ⊢
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly M₂ sp.2.2.2 ≠ 0 := fun h ↦ hDne (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : K₂[X], Irreducible p → p ∣ GPoly.toPoly M₂ sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₂ (expWPrim En₁ Ed₁ a)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η₂ hD₃ hconst hp (by rw [hD₃']; exact hsp')).trans hpd)
  -- (2) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M₂ (expWPrim En₁ Ed₁ a) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₃) M₂ (expWPrim En₁ Ed₁ a) sp.1 sp.2.2.2
    _ hD₃' hchk
  have hsdvd := GPoly.hermite_s_dvd M₂ (expWPrim En₁ Ed₁ a) sp.1 sp.2.2.2 hd₁0
  generalize GPoly.hermite (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) sp.1 sp.2.2.2 = h
    at hchk hid hsq hsdvd hY ⊢
  set S := GPoly.toPoly M₂ h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ S := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) polynomial part and proper part
  have hdm := GPoly.divMod_spec M₂ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₂ h.b h.s hS0
  generalize GPoly.divMod (ops₂p En₁ Ed₁) h.b h.s = qr at hdm hdeglt hY ⊢
  set Λ := GPoly.add (ops₂p En₁ Ed₁)
    (GPoly.mul (ops₂p En₁ Ed₁) qr.1 (GPoly.monomial (ops₂p En₁ Ed₁) k (ops₂p En₁ Ed₁).one))
    sp.2.1 with hΛ
  have hΛpoly : GPoly.toPoly M₂ Λ = GPoly.toPoly M₂ qr.1 * X ^ k + GPoly.toPoly M₂ sp.2.1 := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M₂.sem_one, C_1, one_mul]
  -- (4) the residue polynomial
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M₂ (expWPrim En₁ Ed₁ a)) S) S := by
    rw [← hD₃']
    exact isCoprime_deriv_of_squarefree (s := S) hsq fun p hp hpS ↦ by
      rw [hD₃']; exact hnormal p hp (hpS.trans hsdvd)
  have hr := GPoly.residuePoly_spec M₂ (expWPrim En₁ Ed₁ a) qr.2 h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly M₂ (GPoly.residuePoly (ops₂p En₁ Ed₁) (expWPrim En₁ Ed₁ a) qr.2 h.s) *
      (mapCoeffs S + C (aeval x₀ (derivative (toPoly a))) * X * derivative S) -
      GPoly.toPoly M₂ qr.2 := by
    have hidd : implicitDeriv (GPoly.toPoly M₂ (expWPrim En₁ Ed₁ a)) S =
        mapCoeffs S + C (aeval x₀ (derivative (toPoly a))) * X * derivative S := by
      rw [hW, hη₂eq]
      simp [implicitDeriv]
    rwa [hidd] at hr
  have haev₃ : ∀ P : K₂[X], aeval t P = φ₃ P := fun P ↦ by
    rw [htd, aeval_algebraMap_apply, aeval_X_left_apply]
  have hst : aeval t S ≠ 0 := by
    rw [haev₃]
    exact (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr hS0
  -- (5) the Laurent part, coefficientwise
  set N := Λ.length + k + 1 with hN
  have hnf : ∀ j, M₂.sem (normF₂ (Λ.getD j ([], [(ops₁g R).one]))) =
      M₂.sem (Λ.getD j ([], [(ops₁g R).one])) := fun j ↦ by
    unfold normF₂
    split_ifs with hz
    · have hz' := (GPoly.isZero_iff M₁ _).mp hz
      rw [hM₂, sem_M₂W, sem_M₂W, hz']
      simp
    · rfl
  have hnf0 : ∀ j, GPoly.isZero (ops₁g R) (normF₂ (Λ.getD j ([], [(ops₁g R).one]))).2 = false :=
    fun j ↦ by
      unfold normF₂
      split_ifs with hz
      · exact Bool.eq_false_iff.mpr fun h' ↦ by
          have := (GPoly.isZero_iff M₁ _).mp h'
          simp [CField.sem_one] at this
      · exact Bool.eq_false_iff.mpr fun h' ↦ hz (by simpa using h')
  have hΛsum : GPoly.toPoly M₂ Λ = ∑ j ∈ Finset.range N,
      C (M₂.sem (Λ.getD j ([], [(ops₁g R).one]))) * X ^ j := by
    rw [GPoly.toPoly_eq_sum_range _ Λ ([], [(ops₁g R).one])]
    refine (Finset.sum_subset (Finset.range_subset.mpr fun x hx ↦ Finset.mem_range.mpr
      (by omega)) fun j hj hj' ↦ ?_)
    rw [Finset.mem_range, not_lt] at hj'
    have hjΛ : Λ.length ≤ j := by omega
    rw [List.getD_eq_default _ _ hjΛ]
    rw [hM₂, sem_M₂W]
    simp
  have hφX : φ₃ X = t := rfl
  have hW' := expPrimLaurent_antiderivative (K := K₃) hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 a t ht0 ht N k
    (fun j ↦ normF₂ (Λ.getD j ([], [(ops₁g R).one]))) Y (fun j _ ↦ hnf0 j) hY
  have hform : φ₃ (GPoly.toPoly M₂ A) / φ₃ (GPoly.toPoly M₂ D) =
      (φ₃ (GPoly.toPoly M₂ h.gn) / φ₃ (GPoly.toPoly M₂ h.gd))′ +
      (algebraMap K₂ K₃ (valG x₀ t₁ (normF₂ (Λ.getD k ([], [(ops₁g R).one])))) +
        ∑ j ∈ (Finset.range N).erase k,
          algebraMap K₂ K₃ (valG x₀ t₁ (normF₂ (Λ.getD j ([], [(ops₁g R).one])))) * t ^ j / t ^ k) +
      aeval t (GPoly.toPoly M₂ qr.2) / aeval t S := by
    have hφS : φ₃ S ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr hS0
    have hφd₁ : φ₃ (GPoly.toPoly M₂ sp.2.2.2) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr hd₁0
    have hXk : t ^ k ≠ 0 := pow_ne_zero _ ht0
    have hterm : ∀ j, algebraMap K₂ K₃ (valG x₀ t₁ (normF₂ (Λ.getD j ([], [(ops₁g R).one])))) =
        φ₃ (C (M₂.sem (Λ.getD j ([], [(ops₁g R).one])))) := fun j ↦ by
      rw [hvalG, hnf, hCφ₃]
    have hLaurent : algebraMap K₂ K₃ (valG x₀ t₁ (normF₂ (Λ.getD k ([], [(ops₁g R).one])))) +
        ∑ j ∈ (Finset.range N).erase k,
          algebraMap K₂ K₃ (valG x₀ t₁ (normF₂ (Λ.getD j ([], [(ops₁g R).one])))) * t ^ j / t ^ k =
        φ₃ (GPoly.toPoly M₂ Λ) / t ^ k := by
      rw [hΛsum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : k < N)),
        add_div, Finset.sum_div]
      congr 1
      · rw [map_mul, map_pow, hφX, hterm, mul_div_assoc, div_self hXk, mul_one]
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_mul, map_pow, hφX, hterm]
    have hAD : φ₃ (GPoly.toPoly M₂ A) / φ₃ (GPoly.toPoly M₂ D) =
        φ₃ (GPoly.toPoly M₂ sp.1) / φ₃ (GPoly.toPoly M₂ sp.2.2.2) +
          φ₃ (GPoly.toPoly M₂ sp.2.1) / t ^ k := by
      rw [← hsp1, hsp2, map_add, map_mul, map_mul, map_mul, map_pow, hφX]
      field_simp
    have hbS : φ₃ (GPoly.toPoly M₂ h.b) / φ₃ S =
        φ₃ (GPoly.toPoly M₂ qr.1) + φ₃ (GPoly.toPoly M₂ qr.2) / φ₃ S := by
      rw [hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one]
    have hΛk : φ₃ (GPoly.toPoly M₂ Λ) / t ^ k =
        φ₃ (GPoly.toPoly M₂ qr.1) + φ₃ (GPoly.toPoly M₂ sp.2.1) / t ^ k := by
      rw [hΛpoly, map_add, map_mul, map_pow, hφX, add_div, mul_div_assoc, div_self hXk, mul_one]
    rw [hLaurent, hAD, hid, haev₃, haev₃, hbS, hΛk]
    ring
  rw [hform, ← hW', haev₃, haev₃, map_add, hvalG, hnf]
  simp only [hvalP, hφX]
  ring

end Tower
