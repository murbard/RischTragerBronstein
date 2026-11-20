import RischTragerBronstein.Computable.ExpArgExpFullDecision
import RischTragerBronstein.Computable.IntegrateExpExp
import RischTragerBronstein.Computable.IntegrateExpPrim

/-!
# The integrator for `R(x)(exp a₁)(exp a)`, `a ∈ R(x)[exp a₁]` with `a′` of positive degree

`e^{eˣ}`, `exp (x eˣ)`, … . `Tower.integrateExpArgExp`:
`expSplit`, Hermite reduction at `t₂` over the computable field `R(x)(exp a₁)`, the residue test,
one non-cancellation Risch equation (`rdeNCExp`) per power of `t₂`, and `integrateExp a₁` for the
coefficient of `t₂⁰`. `Tower.integrateExpArgExp_decides`: for **every** element `A / D` of `K₃`,
`true` iff `A / D` has an elementary integral.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasNatTest R]

/-- The code of `a′ ∈ R(x)[t₁]` inside `R(x)(exp a₁)`. -/
def expEtaE (a₁ : CPoly R) (a : GPoly (GFrac R)) : GFrac (GFrac R) :=
  (GPoly.derivT (ops₁g R) (expW a₁) a, [(ops₁g R).one])

/-- The code of `t₂′ = a′ t₂` as a polynomial in `t₂` over `R(x)(exp a₁)`. -/
def expWArgE (a₁ : CPoly R) (a : GPoly (GFrac R)) : GPoly (GFrac (GFrac R)) :=
  [(ops₂e a₁).zero, expEtaE a₁ a]

/-- **The integrator for `R(x)(exp a₁)(exp a)`, `a ∈ R(x)[exp a₁]`**, as a decision procedure. -/
def integrateExpArgExp (a₁ : CPoly R) (a : GPoly (GFrac R)) (A D : GPoly (GFrac (GFrac R))) :
    Bool :=
  let sp := GPoly.expSplit (ops₂e a₁) A D
  let h := GPoly.hermite (ops₂e a₁) (expWArgE a₁ a) sp.1 sp.2.2.2
  let qr := GPoly.divMod (ops₂e a₁) h.b h.s
  let Λ := GPoly.add (ops₂e a₁)
    (GPoly.mul (ops₂e a₁) qr.1 (GPoly.monomial (ops₂e a₁) sp.2.2.1 (ops₂e a₁).one)) sp.2.1
  GPoly.residueCheck (ops₂e a₁) (expWArgE a₁ a) qr.2 h.s &&
    (List.range (Λ.length + sp.2.2.1 + 1)).all (fun j ↦
      decide (j = sp.2.2.1) ||
        (rdeNCExpB a₁ (GPoly.smul (ops₁g R) (constZ ((j : ℤ) - sp.2.2.1)) (GPoly.derivT (ops₁g R) (expW a₁) a))
          (normF₂ (Λ.getD j ([], [(ops₁g R).one]))).1
          (normF₂ (Λ.getD j ([], [(ops₁g R).one]))).2).isSome) &&
    integrateExp a₁ (normF₂ (Λ.getD sp.2.2.1 ([], [(ops₁g R).one]))).1
      (normF₂ (Λ.getD sp.2.2.1 ([], [(ops₁g R).one]))).2

end Defs

universe u

variable {R K₁ K₂ : Type*} {K₃ : Type u} [Field R] [DecidableEq R] [CharZero R] [HasNatTest R]
variable [Differential R] [Differential R[X]] [Field K₁] [CharZero K₁] [Algebra R[X] K₁]
variable [IsFractionRing R[X] K₁] [Differential K₁] [DifferentialAlgebra R[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]
variable [Differential K₂[X]] [Field K₃] [Differential K₃] [Algebra K₂[X] K₃]
variable [IsFractionRing K₂[X] K₃] [DifferentialAlgebra K₂[X] K₃]
variable [Algebra K₂ K₃] [IsScalarTower K₂ K₂[X] K₃] [DifferentialAlgebra K₂ K₃]

variable (h0 : ∀ r : R, r′ = 0) {a₁ : CPoly R} (M : ModelE (K₁ := K₁) a₁)

set_option maxHeartbeats 3200000 in
/-- **Exponentials with argument in `R(x)[exp a₁]` are decided**: every element, both directions. -/
theorem integrateExpArgExp_decides (a : GPoly (GFrac R))
    (hηc : 2 ≤ (GPoly.trim (ops₁g R) (GPoly.derivT (ops₁g R) (expW a₁) a)).length)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C ((M.cf h0).sem (expEtaE a₁ a)) * X) P)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂e a₁) D = false) :
    HasElementaryIntegral
        (algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf h0) A) /
          algebraMap K₂[X] K₃ (GPoly.toPoly (M.cf h0) D)) ↔
      integrateExpArgExp a₁ a A D = true := by
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
  have ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁ := by
    rw [haev, ht₁d, deriv_algebraMap, M.hD₂, implicitDeriv_X, map_mul, hCφ₂]
    congr 1
    rw [ηa, Polynomial.map_id]
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
  set M₂ := M.cf (K₂ := K₂) h0 with hM₂
  have hvalP : ∀ q : GPoly (GFrac R), valP x₀ t₁ q = φ₂ (GPoly.toPoly M₁ q) := fun q ↦ by
    rw [GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, hCφ₂, hM₁, sem_M₁In, hev]
    rfl
  have hvalG : ∀ q : GFrac (GFrac R), valG x₀ t₁ q = M₂.sem q := fun q ↦ by
    rw [hM₂, sem_ModelE_cf, valG, hvalP, hvalP]
  set ηc : GPoly (GFrac R) := GPoly.derivT (ops₁g R) (expW a₁) a with hηcdef
  set η₂ : K₂ := M₂.sem (expEtaE a₁ a) with hη₂
  have hsemη : M₂.sem (expEtaE a₁ a) = η₂ := rfl
  have hη₂poly : η₂ = φ₂ (GPoly.toPoly M₁ ηc) := by
    rw [hη₂, hM₂, sem_ModelE_cf, expEtaE, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
      CField.sem_one, C_1, map_one, div_one]
  have hη₂eq : valP x₀ t₁ ηc = η₂ := by rw [hvalP, hη₂poly]
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ (expW a₁)) P := fun P ↦ by
    rw [hM₁, toPoly_expW_In]; exact M.hD₂ P
  have hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree := fun P ↦ by
    rw [M.hD₂]; exact natDegree_implicitDeriv_C_mul_X_le _ P
  have htηc : GPoly.trim (ops₁g R) ηc ≠ [] := fun h0' ↦ by rw [h0'] at hηc; simp at hηc
  have hgdeg : 1 ≤ (GPoly.toPoly M₁ ηc).natDegree := by
    have := (GPoly.natDegree_toPoly_of_trim_ne_nil M₁ htηc).1
    omega
  have hW : GPoly.toPoly M₂ (expWArgE a₁ a) = C η₂ * X := by
    rw [expWArgE, GPoly.toPoly_cons, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
      CField.sem_zero, C_0, zero_add, hsemη, mul_comm]
  have ht : t′ = algebraMap K₂ K₃ (valP x₀ t₁ ηc) * t := by
    rw [hη₂eq, htd, deriv_algebraMap, hD₃, ← hCφ₃]
    simp [implicitDeriv]
    rfl
  have ht0 : t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K₂[X] K₃)).mpr X_ne_zero
  have hD₃' : ∀ P : K₂[X], P′ = implicitDeriv (GPoly.toPoly M₂ (expWArgE a₁ a)) P :=
    fun P ↦ by rw [hW]; exact hD₃ P
  have hconst := exp_arg_no_new_constants (K₁ := K₁) (K₂ := K₂) hder (GPoly.toPoly M₁ ηc) hgdeg
    (fun P ↦ by rw [hD₃, ← hη₂poly])
  have hDne : GPoly.toPoly M₂ D ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₂ D).mpr hz] at hD0
    exact Bool.noConfusion hD0
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M₂ A D hDne
  simp only [integrateExpArgExp]
  generalize GPoly.expSplit (ops₂e a₁) A D = sp at hsp1 hsp2 hsp3 ⊢
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly M₂ sp.2.2.2 ≠ 0 := fun h ↦ hDne (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : K₂[X], Irreducible p → p ∣ GPoly.toPoly M₂ sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₂ (expWArgE a₁ a)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η₂ hD₃ hconst hp (by rw [hD₃']; exact hsp')).trans hpd)
  -- (2) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M₂ (expWArgE a₁ a) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₃) M₂ (expWArgE a₁ a) sp.1 sp.2.2.2
    _ hD₃' hchk
  have hsdvd := GPoly.hermite_s_dvd M₂ (expWArgE a₁ a) sp.1 sp.2.2.2 hd₁0
  generalize GPoly.hermite (ops₂e a₁) (expWArgE a₁ a) sp.1 sp.2.2.2 = h
    at hchk hid hsq hsdvd ⊢
  set S := GPoly.toPoly M₂ h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ S := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) polynomial part and proper part
  have hdm := GPoly.divMod_spec M₂ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₂ h.b h.s hS0
  generalize GPoly.divMod (ops₂e a₁) h.b h.s = qr at hdm hdeglt ⊢
  set Λ := GPoly.add (ops₂e a₁)
    (GPoly.mul (ops₂e a₁) qr.1 (GPoly.monomial (ops₂e a₁) k (ops₂e a₁).one))
    sp.2.1 with hΛ
  have hΛpoly : GPoly.toPoly M₂ Λ = GPoly.toPoly M₂ qr.1 * X ^ k + GPoly.toPoly M₂ sp.2.1 := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M₂.sem_one, C_1, one_mul]
  -- (4) the residue polynomial
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M₂ (expWArgE a₁ a)) S) S := by
    rw [← hD₃']
    exact isCoprime_deriv_of_squarefree (s := S) hsq fun p hp hpS ↦ by
      rw [hD₃']; exact hnormal p hp (hpS.trans hsdvd)
  have hr := GPoly.residuePoly_spec M₂ (expWArgE a₁ a) qr.2 h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly M₂ (GPoly.residuePoly (ops₂e a₁) (expWArgE a₁ a) qr.2 h.s) *
      (mapCoeffs S + C (valP x₀ t₁ ηc) * X * derivative S) -
      GPoly.toPoly M₂ qr.2 := by
    have hidd : implicitDeriv (GPoly.toPoly M₂ (expWArgE a₁ a)) S =
        mapCoeffs S + C (valP x₀ t₁ ηc) * X * derivative S := by
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
      rw [hM₂, sem_ModelE_cf, sem_ModelE_cf, hz']
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
    rw [hM₂, sem_ModelE_cf]
    simp
  have key := expArgExpFull_decides (K := K₃) hR x₀ t₁ hx₀ a₁ M.ha₁ ht₁0 ht₁ hgen₀ a hηc t ht0
    hgen ht (φ₃ (GPoly.toPoly M₂ h.gn) / φ₃ (GPoly.toPoly M₂ h.gd)) N k
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
    GPoly.residueCheck_iff M₂ (expWArgE a₁ a) qr.2 h.s hS0, List.all_eq_true, and_assoc]
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
