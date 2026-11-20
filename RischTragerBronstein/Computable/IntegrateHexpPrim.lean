import RischTragerBronstein.Computable.HexpPrimFullDecision
import RischTragerBronstein.Computable.IntegrateExpPrim
import RischTragerBronstein.Computable.IntegrateNestedLog
import RischTragerBronstein.Computable.IntegrateExp

/-!
# The integrator for a hyperexponential over `R(x)(t₁)`: `R(x)(t₁)(t₂)`, `t₂′ = η t₂`

`t₁′ = η₁ ∈ R(x)` a primitive, `t₂′ = η t₂` with `η = Gn / Gd ∈ R(x)` **arbitrary** (certified
monomial by `CPoly.hyperexpMonomialCheck Gn Gd μ`), e.g. `ℚ(x, log x, exp (arctan x))`.
`Tower.integrateHexpPrim En₁ Ed₁ Iη₁ Gn Gd μ A D : Bool` decides whether `A / D ∈ R(x)(t₁)(t₂)` has an
elementary integral: the pipeline of `integrateExpPrim` with the Risch differential equations
`y′ + (j - k) η y = Λⱼ` over `R(x)(t₁)` solved by `rdePrimW`.

`Tower.integrateHexpPrim_decides`: for **every** element the answer is `true` iff an elementary
integral exists, in every model of the tower.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The code of `η = Gn / Gd ∈ R(x)` inside `R(x)(t₁)`. -/
def hexpEta (Gn Gd : CPoly R) : GFrac (GFrac R) := ([(Gn, Gd)], [(ops₁g R).one])

/-- The code of `t₂′ = η t₂` as a polynomial in `t₂`. -/
def hexpWPrim (En₁ Ed₁ Gn Gd : CPoly R) : GPoly (GFrac (GFrac R)) :=
  [(ops₂p En₁ Ed₁).zero, hexpEta Gn Gd]

variable [HasRatRoots R] [HasNatTest R]

/-- **The integrator for `R(x)(t₁)(t₂)`, `t₂′ = η t₂`**, as a decision procedure. -/
def integrateHexpPrim (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (Gn Gd μ : CPoly R)
    (A D : GPoly (GFrac (GFrac R))) : Bool :=
  let sp := GPoly.expSplit (ops₂p En₁ Ed₁) A D
  let h := GPoly.hermite (ops₂p En₁ Ed₁) (hexpWPrim En₁ Ed₁ Gn Gd) sp.1 sp.2.2.2
  let qr := GPoly.divMod (ops₂p En₁ Ed₁) h.b h.s
  let Λ := GPoly.add (ops₂p En₁ Ed₁)
    (GPoly.mul (ops₂p En₁ Ed₁) qr.1 (GPoly.monomial (ops₂p En₁ Ed₁) sp.2.2.1 (ops₂p En₁ Ed₁).one))
    sp.2.1
  GPoly.residueCheck (ops₂p En₁ Ed₁) (hexpWPrim En₁ Ed₁ Gn Gd) qr.2 h.s &&
    (List.range (Λ.length + sp.2.2.1 + 1)).all (fun j ↦
      decide (j = sp.2.2.1) ||
        (rdePrimW En₁ Ed₁ (smul ((((j : ℤ) - sp.2.2.1 : ℤ)) : R) Gn, Gd)
          (scaleMu ((((j : ℤ) - sp.2.2.1 : ℤ)) : R) μ)
          (normF₂ (Λ.getD j ([], [(ops₁g R).one]))).1
          (normF₂ (Λ.getD j ([], [(ops₁g R).one]))).2).isSome) &&
    integratePrim En₁ Ed₁ Iη₁ (normF₂ (Λ.getD sp.2.2.1 ([], [(ops₁g R).one]))).1
      (normF₂ (Λ.getD sp.2.2.1 ([], [(ops₁g R).one]))).2

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
variable [HasRatRoots R] [HasNatTest R]

/-- No new constants when adjoining a hyperexponential `t₂′ = η t₂` to `S(x)(t₁)`. -/
theorem hexp_no_new_constants_prim (h0 : ∀ r : R, r′ = 0) {En₁ Ed₁ : CPoly R}
    (M : ModelW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) En₁ Ed₁) (Gn Gd μ : CPoly R)
    (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0) (hcop : IsCoprime (toPoly Gn) (toPoly Gd))
    (hcert : hyperexpMonomialCheck Gn Gd μ = true)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (algebraMap K₁ K₂ (algebraMap R[X] K₁ (toPoly Gn) /
      algebraMap R[X] K₁ (toPoly Gd))) * X) P)
    (P : K₂[X]) (n : ℕ) (h : P′ * X ^ n = P * (X ^ n)′) :
    ∃ e : K₂, P = C e * X ^ n := by
  set η₁ : K₁ := algebraMap R[X] K₁ (toPoly Gn) / algebraMap R[X] K₁ (toPoly Gd) with hη₁
  set η := algebraMap K₁ K₂ η₁ with hη
  refine ⟨P.coeff n, ?_⟩
  have hP : implicitDeriv (C η * X) P = C (n * η) * P := by
    rw [hD₃, hD₃, deriv_X_pow] at h
    have hX : (X : K₂[X]) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_right_cancel₀ hX
    rw [h]; ring
  have hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive (CPoly.ev K₁ (RingHom.id R) (En₁, Ed₁)) M.hD₂
      M.hconst₂ hp
  ext j
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hjn
  · rw [hjn, mul_one]
  rw [mul_zero]
  have hc := congrArg (fun Q : K₂[X] ↦ Q.coeff j) hP
  simp only [coeff_implicitDeriv_C_mul_X, coeff_C_mul] at hc
  set g₀ : K₁ := ((j : K₁) - n) * η₁ with hg₀
  have hgnl : ∀ e : K₁, e ≠ 0 → e′ + g₀ * e ≠ 0 := fun e he h' ↦
    he (hyperexpW_homogeneous (K := K₁) (RingHom.id R) M.hD hGn0 hGd0 hcop hcert (-((j : ℤ) - n))
      (neg_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjn))) e (by
        rw [C_eq_intCast, map_intCast, Polynomial.map_id, Polynomial.map_id, ← hη₁]
        simp only [Int.cast_neg, Int.cast_sub, Int.cast_natCast]
        rw [hg₀] at h'
        linear_combination h'))
  refine eq_zero_of_rde_homogeneous (K := K₂) hnorm (CPoly.ev K₁ (RingHom.id R) (En₁, Ed₁)) g₀
    M.hD₂ hgnl (P.coeff j) ?_
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, hg₀, map_mul,
    ← hη, map_sub, map_natCast, map_natCast]
  linear_combination hc

set_option maxHeartbeats 3200000 in
/-- **Exponentials over `R(x)(t₁)` are decided**: every element, both directions. -/
theorem integrateHexpPrim_decides (h0 : ∀ r : R, r′ = 0) {En₁ Ed₁ : CPoly R}
    (M : ModelW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) En₁ Ed₁) (Gn Gd μ : CPoly R)
    (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0) (hcopη : IsCoprime (toPoly Gn) (toPoly Gd))
    (hcert : hyperexpMonomialCheck Gn Gd μ = true)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (algebraMap K₁ K₂ (algebraMap R[X] K₁ (toPoly Gn) /
      algebraMap R[X] K₁ (toPoly Gd))) * X) P)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false) :
    HasElementaryIntegral
        (algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) A) /
          algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf (RingHom.id R) h0) D)) ↔
      integrateHexpPrim En₁ Ed₁ Iη₁ Gn Gd μ A D = true := by
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
  set η₂ : K₂ := algebraMap K₁ K₂ (algebraMap R[X] K₁ (toPoly Gn) / algebraMap R[X] K₁ (toPoly Gd))
    with hη₂
  have hη₂eq : aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd) = η₂ := by
    rw [haev, haev, hη₂, map_div₀]
    rfl
  have hsemη : M₂.sem (hexpEta Gn Gd) = η₂ := by
    rw [hM₂, sem_M₂W, hexpEta, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
      GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1, map_one,
      div_one, sem_M₁In, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K₁ K₁[X] K₂]
    congr 1
    simp [CPoly.ev]
  have hW : GPoly.toPoly M₂ (hexpWPrim En₁ Ed₁ Gn Gd) = C η₂ * X := by
    rw [hexpWPrim, GPoly.toPoly_cons, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
      CField.sem_zero, C_0, zero_add, hsemη, mul_comm]
  have ht : t′ = algebraMap K₂ K₃ (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * t := by
    rw [hη₂eq, htd, deriv_algebraMap, hD₃, ← hCφ₃]
    simp [implicitDeriv]
    rfl
  have ht0 : t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr X_ne_zero
  have hD₃' : ∀ P : K₂[X], P′ = implicitDeriv (GPoly.toPoly M₂ (hexpWPrim En₁ Ed₁ Gn Gd)) P :=
    fun P ↦ by rw [hW]; exact hD₃ P
  have hconst := hexp_no_new_constants_prim (K₁ := K₁) (K₂ := K₂) h0 M Gn Gd μ hGn0 hGd0 hcopη
    hcert hD₃
  have hDne : GPoly.toPoly M₂ D ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₂ D).mpr hz] at hD0
    exact Bool.noConfusion hD0
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M₂ A D hDne
  simp only [integrateHexpPrim]
  generalize GPoly.expSplit (ops₂p En₁ Ed₁) A D = sp at hsp1 hsp2 hsp3 ⊢
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly M₂ sp.2.2.2 ≠ 0 := fun h ↦ hDne (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : K₂[X], Irreducible p → p ∣ GPoly.toPoly M₂ sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₂ (hexpWPrim En₁ Ed₁ Gn Gd)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η₂ hD₃ hconst hp (by rw [hD₃']; exact hsp')).trans hpd)
  -- (2) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M₂ (hexpWPrim En₁ Ed₁ Gn Gd) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₃) M₂ (hexpWPrim En₁ Ed₁ Gn Gd) sp.1 sp.2.2.2
    _ hD₃' hchk
  have hsdvd := GPoly.hermite_s_dvd M₂ (hexpWPrim En₁ Ed₁ Gn Gd) sp.1 sp.2.2.2 hd₁0
  generalize GPoly.hermite (ops₂p En₁ Ed₁) (hexpWPrim En₁ Ed₁ Gn Gd) sp.1 sp.2.2.2 = h
    at hchk hid hsq hsdvd ⊢
  set S := GPoly.toPoly M₂ h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ S := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) polynomial part and proper part
  have hdm := GPoly.divMod_spec M₂ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₂ h.b h.s hS0
  generalize GPoly.divMod (ops₂p En₁ Ed₁) h.b h.s = qr at hdm hdeglt ⊢
  set Λ := GPoly.add (ops₂p En₁ Ed₁)
    (GPoly.mul (ops₂p En₁ Ed₁) qr.1 (GPoly.monomial (ops₂p En₁ Ed₁) k (ops₂p En₁ Ed₁).one))
    sp.2.1 with hΛ
  have hΛpoly : GPoly.toPoly M₂ Λ = GPoly.toPoly M₂ qr.1 * X ^ k + GPoly.toPoly M₂ sp.2.1 := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M₂.sem_one, C_1, one_mul]
  -- (4) the residue polynomial
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M₂ (hexpWPrim En₁ Ed₁ Gn Gd)) S) S := by
    rw [← hD₃']
    exact isCoprime_deriv_of_squarefree (s := S) hsq fun p hp hpS ↦ by
      rw [hD₃']; exact hnormal p hp (hpS.trans hsdvd)
  have hr := GPoly.residuePoly_spec M₂ (hexpWPrim En₁ Ed₁ Gn Gd) qr.2 h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly M₂ (GPoly.residuePoly (ops₂p En₁ Ed₁) (hexpWPrim En₁ Ed₁ Gn Gd) qr.2 h.s) *
      (mapCoeffs S + C (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * X * derivative S) -
      GPoly.toPoly M₂ qr.2 := by
    have hidd : implicitDeriv (GPoly.toPoly M₂ (hexpWPrim En₁ Ed₁ Gn Gd)) S =
        mapCoeffs S + C (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * X * derivative S := by
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
  have key := hexpPrimFull_decides (K := K₃) hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ Gn Gd μ hGn0 hGd0
    hcopη hcert t ht0 hgen ht
    Iη₁ hcη₁ hη₁0 (φ₃ (GPoly.toPoly M₂ h.gn) / φ₃ (GPoly.toPoly M₂ h.gd)) N k
    (fun j ↦ normF₂ (Λ.getD j ([], [(ops₁g R).one]))) (fun j _ ↦ hnf0 j)
    (normF₂ (Λ.getD k ([], [(ops₁g R).one]))) (hnf0 k) (GPoly.toPoly M₂ qr.2) S _ hsq hXS hdeglt
    hst hr'
  have hφX : φ₃ X = t := rfl
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
  rw [hform, key, Bool.and_eq_true, Bool.and_eq_true,
    GPoly.residueCheck_iff M₂ (hexpWPrim En₁ Ed₁ Gn Gd) qr.2 h.s hS0, List.all_eq_true, and_assoc]
  refine and_congr Iff.rfl (and_congr ⟨fun hall j hj ↦ ?_, fun hall j hj hjk ↦ ?_⟩ Iff.rfl)
  · rw [List.mem_range] at hj
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hjk : j = k
    · exact Or.inl hjk
    · exact Or.inr (hall j hj hjk)
  · have := hall j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.resolve_left hjk

end Tower
