import RischTragerBronstein.Computable.LogResidueDecision
import RischTragerBronstein.Computable.PrimFullDecision
import RischTragerBronstein.Computable.GHermiteComplete

/-!
# The integrator for `R(x)(t)`, `t` primitive: a verified decision procedure

`Tower.integratePrim En Ed Iη A D : Bool` decides whether `A / D ∈ R(x)(t)`, `t′ = η = En / Ed ∈ R(x)`
not a derivative (`t = log x`, `log b(x)`, `arctan x`, …), has an elementary integral:

1. Hermite reduction in `t` (generic `GPoly.hermite`, always certified:
   `GPoly.hermiteCheck_hermite`);
2. Euclidean division of the remaining numerator: polynomial part `q` and proper part `rem / s`;
3. the resultant-free residue test `GPoly.residueCheck` on `rem / s`;
4. the recursive limited-integration loop `CPoly.primLoop` on the coefficients of `q`.

`integratePrim_decides`: the integrand has an elementary integral **iff** the procedure answers
`true` — both directions proved, no assumption on constants.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Tower

section Generic

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

/-- Replace a fraction code with zero denominator (value `0`) by `0 / 1`. -/
def normFrac (q : GFrac R) : GFrac R := if CPoly.isZero q.2 then ([], [1]) else q

/-- Numerator of the `j`-th coefficient of the polynomial part. -/
def polyA (q : GPoly (GFrac R)) (j : ℕ) : CPoly R := (normFrac (q.getD j ([], [1]))).1

/-- Denominator of the `j`-th coefficient of the polynomial part. -/
def polyD (q : GPoly (GFrac R)) (j : ℕ) : CPoly R := (normFrac (q.getD j ([], [1]))).2

/-- **The integrator for `R(x)(log x)`**, as a decision procedure. -/
def integratePrim (En Ed : CPoly R) (Iη : CPoly.RationalIntegral R) (A D : GPoly (GFrac R)) :
    Bool :=
  let h := GPoly.hermite (ops₁g R) [(En, Ed)] A D
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  GPoly.residueCheck (ops₁g R) [(En, Ed)] qr.2 h.s &&
    (CPoly.primLoop En Ed Iη (polyA qr.1) (polyD qr.1) qr.1.length ([], [1])).isSome

lemma sem_normFrac (h0 : ∀ r : R, r′ = 0) (q : GFrac R) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    (M₁g h0).sem (normFrac q) = (M₁g h0).sem q ∧ CPoly.toPoly (normFrac q).2 ≠ 0 := by
  unfold normFrac
  split_ifs with hz
  · have hz' := (CPoly.isZero_iff _).mp hz
    refine ⟨?_, by simp⟩
    rw [sem_M₁g, sem_M₁g, hz']
    simp
  · exact ⟨rfl, fun h ↦ hz ((CPoly.isZero_iff _).mpr h)⟩

theorem integratePrim_decides (h0 : ∀ r : R, r′ = 0) (En Ed : CPoly R)
    (Iη : CPoly.RationalIntegral R) (hcη : CPoly.rationalCheck En Ed Iη = true)
    (hη0 : CPoly.isZero Iη.r = false) (A D : GPoly (GFrac R))
    (hD0 : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      GPoly.toPoly (M₁g h0) D ≠ 0) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
    HasElementaryIntegral (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R))
        (GPoly.toPoly (M₁g h0) A) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D)) ↔
      integratePrim En Ed Iη A D = true := by
  let _ : Differential R[X] := polynomialOfDeriv (GPoly.toPoly (M₀g h0) [1])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv _
  have hDA0' : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have h1 : GPoly.toPoly (M₀g h0) [1] = 1 := by
    simp [GPoly.toPoly, M₀g, CField.ofDecidableField]
  -- `η = 1 / x`
  set η : RatFunc R := aeval (RatFunc.X : RatFunc R) (CPoly.toPoly En) /
    aeval (RatFunc.X : RatFunc R) (CPoly.toPoly Ed) with hη
  have hW : GPoly.toPoly (M₁g h0) [(En, Ed)] = C η := by
    have : (M₁g h0).sem (En, Ed) = η := sem_M₁g h0 (En, Ed)
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, this]
  have hR : ∀ r : R, (algebraMap R (RatFunc R) r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, h0, map_zero]
  have hx₀ : (RatFunc.X : RatFunc R)′ = 1 := by
    rw [ratFuncOfDeriv_X, h1, map_one]
  have ht : (RatFunc.X : RatFunc (RatFunc R))′ = algebraMap (RatFunc R) (RatFunc (RatFunc R)) η := by
    rw [ratFuncOfDeriv_X, hW, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  have hD : ∀ P : (RatFunc R)[X], P′ = implicitDeriv (C η) P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) P = _
    rw [hW]
  have hDx : ∀ P : R[X], P′ = derivative P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₀g h0) [1]) P = _
    rw [h1]
    exact implicitDeriv_one_of_trivial h0 P
  -- `η` is not a derivative in `R(x)`
  obtain ⟨hdecη, hsqη, hdegη⟩ :=
    CPoly.rationalCheck_sound_map (K := RatFunc R) (RingHom.id R) hDx En Ed Iη hcη
  simp only [Polynomial.map_id] at hdecη hsqη hdegη
  have hrη0 : CPoly.toPoly Iη.r ≠ 0 := by
    rw [Ne, ← CPoly.isZero_iff, hη0]
    exact Bool.noConfusion
  have hηnd : ∀ y : RatFunc R, y′ ≠ η := fun y hy ↦ hrη0 <| by
    refine eq_zero_of_deriv_eq_proper_fraction (K := RatFunc R) hDx _ _ hsqη hdegη
      (y - (algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.gn) /
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.gd) +
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.Q))) ?_
    have hηφ : η = algebraMap R[X] (RatFunc R) (CPoly.toPoly En) /
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Ed) := by
      rw [hη, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap]
    rw [CPoly.deriv_sub', hy, hηφ, hdecη]
    ring
  -- normality and coprimality
  have hconstP : ∀ P : (RatFunc R)[X], P′ = 0 → ∃ e : RatFunc R, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero η hηnd (by rw [← hD, hP])
  have hnormal : ∀ p : (RatFunc R)[X], Irreducible p →
      ¬p ∣ implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) p := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive η hD hconstP hp
  -- (1) Hermite reduction, always certified
  have hchk := GPoly.hermiteCheck_hermite (M₁g h0) [(En, Ed)] A D (fun p hp _ ↦ hnormal p hp) hD0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound (M₁g h0) [(En, Ed)] A D _ hchk
  set h := GPoly.hermite (ops₁g R) [(En, Ed)] A D with hh
  set S := GPoly.toPoly (M₁g h0) h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  -- (2) polynomial part and proper part
  have hdm := GPoly.divMod_spec (M₁g h0) h.b h.s
  have hdeglt := GPoly.divMod_degree_lt (M₁g h0) h.b h.s hS0
  set q := (GPoly.divMod (ops₁g R) h.b h.s).1 with hq
  set rem := (GPoly.divMod (ops₁g R) h.b h.s).2 with hrem
  -- (3) the residue polynomial
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) S) S :=
    isCoprime_deriv_of_squarefree (s := S) hsq fun p hp _ ↦ hnormal p hp
  have hr := GPoly.residuePoly_spec (M₁g h0) [(En, Ed)] rem h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly (M₁g h0) (GPoly.residuePoly (ops₁g R) [(En, Ed)] rem h.s) *
      (mapCoeffs S + C η * derivative S) - GPoly.toPoly (M₁g h0) rem := by
    have hidd : implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) S =
        mapCoeffs S + C η * derivative S := by
      rw [hW]
      simp [implicitDeriv]
    rwa [hidd] at hr
  have hst : aeval (RatFunc.X : RatFunc (RatFunc R)) S ≠ 0 := by
    rw [RatFunc.aeval_X_left_eq_algebraMap]
    exact RatFunc.algebraMap_ne_zero hS0
  -- (4) the polynomial part, coefficientwise
  have hqsum : GPoly.toPoly (M₁g h0) q = ∑ j ∈ Finset.range (q.length + 1),
      C (aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyA q j)) /
        aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyD q j))) * X ^ j := by
    ext n
    rw [GPoly.coeff_toPoly, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hn : n < q.length + 1
    · rw [Finset.sum_eq_single n (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), mul_zero])
        (fun h' ↦ absurd (Finset.mem_range.mpr hn) h'), if_pos rfl, mul_one, polyA, polyD,
        ← sem_M₁g h0, (sem_normFrac h0 _).1]
      by_cases hn' : n < q.length
      · rw [List.getD_eq_getElem _ _ (by simpa using hn'), List.getElem_map,
          List.getD_eq_getElem _ _ hn']
      · rw [List.getD_eq_default _ _ (by simpa using hn'), List.getD_eq_default _ _ (by omega),
          sem_M₁g]
        simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      refine (Finset.sum_eq_zero fun b hb ↦ ?_).symm
      rw [if_neg (by have := Finset.mem_range.mp hb; omega), mul_zero]
  have key := CPoly.primFull_decides (R := R) (F₀ := RatFunc R) (K := RatFunc (RatFunc R))
    hR RatFunc.X hx₀ RatFunc.adjoin_X RatFunc.X RatFunc.adjoin_X En Ed ht Iη hcη hη0
    (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gn) /
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gd))
    q.length (polyA q) (polyD q) (fun j _ ↦ (sem_normFrac h0 _).2)
    (GPoly.toPoly (M₁g h0) rem) S _ hsq hdeglt hst hr'
  have hform : algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) A) /
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D) =
      (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gn) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gd))′ +
      ∑ j ∈ Finset.range (q.length + 1),
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) (CPoly.toPoly (polyA q j)) /
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
            (CPoly.toPoly (polyD q j)) * RatFunc.X ^ j +
      aeval (RatFunc.X : RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) rem) /
        aeval (RatFunc.X : RatFunc (RatFunc R)) S := by
    have hφS : algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) S ≠ 0 :=
      RatFunc.algebraMap_ne_zero hS0
    have hsumφ : ∑ j ∈ Finset.range (q.length + 1),
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) (CPoly.toPoly (polyA q j)) /
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
            (CPoly.toPoly (polyD q j)) * RatFunc.X ^ j =
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) q) := by
      rw [hqsum, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
        aeval_algebraMap_apply, aeval_algebraMap_apply, ← map_div₀, RatFunc.algebraMap_eq_C]
    rw [hid, hsumφ, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap, hdm,
      map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one]
    ring
  rw [hform, key, integratePrim, Bool.and_eq_true, GPoly.residueCheck_iff (M₁g h0) [(En, Ed)] rem h.s hS0]


/-- The data computed by the integrator: Hermite part, the list returned by `primLoop`, and the
proper part `rem / s` for the logarithmic terms. -/
def integratePrimData (En Ed : CPoly R) (Iη : CPoly.RationalIntegral R) (A D : GPoly (GFrac R)) :
    Option (GPoly.HermiteResult (GFrac R) × List (R × (CPoly R × CPoly R)) × GPoly (GFrac R)) :=
  let h := GPoly.hermite (ops₁g R) [(En, Ed)] A D
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  if GPoly.residueCheck (ops₁g R) [(En, Ed)] qr.2 h.s then
    (CPoly.primLoop En Ed Iη (polyA qr.1) (polyD qr.1) qr.1.length ([], [1])).map
      fun L ↦ (h, L, qr.2)
  else none

lemma integratePrimData_isSome (En Ed : CPoly R) (Iη : CPoly.RationalIntegral R)
    (A D : GPoly (GFrac R)) :
    (integratePrimData En Ed Iη A D).isSome = integratePrim En Ed Iη A D := by
  simp only [integratePrimData, integratePrim]
  split_ifs with hc <;> simp [hc]

/-- **The result is an antiderivative.** When the integrator succeeds with data `(h, L, rem)`,

  `A / D = (h.gn / h.gd + W)′ + ρ + rem / h.s`,

where `W = primW … L` is an explicit element of `R(x)(t)`, `ρ = f₀ - η Q₁ ∈ R(x)` is a rational
function (integrated by `integrateRational`), and `rem / h.s` passes the residue test, so that
`∫ rem / h.s = ∑_{s(α) = 0} r(α) log (t - α)` (`hasElementaryIntegral_of_residueTest`). -/
theorem integratePrimData_antiderivative (h0 : ∀ r : R, r′ = 0) (En Ed : CPoly R)
    (Iη : CPoly.RationalIntegral R) (hcη : CPoly.rationalCheck En Ed Iη = true)
    (hη0 : CPoly.isZero Iη.r = false) (A D : GPoly (GFrac R))
    (hD0 : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      GPoly.toPoly (M₁g h0) D ≠ 0)
    {hr : GPoly.HermiteResult (GFrac R)} {Lr : List (R × (CPoly R × CPoly R))}
    {remr : GPoly (GFrac R)} (hdata : integratePrimData En Ed Iη A D = some (hr, Lr, remr)) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
    letI x : RatFunc (RatFunc R) := algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X
    letI q := (GPoly.divMod (ops₁g R) hr.b hr.s).1
    algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) A) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D) =
      (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) hr.gn) /
          algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) hr.gd) +
        CPoly.primW x RatFunc.X (q.length + 1) ([], [1]) Lr)′ +
      (CPoly.evx x (polyA q 0, polyD q 0) -
        CPoly.evx x (En, Ed) * CPoly.evx x (CPoly.primLast ([], [1]) Lr)) +
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) remr) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) hr.s) := by

  let _ : Differential R[X] := polynomialOfDeriv (GPoly.toPoly (M₀g h0) [1])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv _
  have hDA0' : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have h1 : GPoly.toPoly (M₀g h0) [1] = 1 := by
    simp [GPoly.toPoly, M₀g, CField.ofDecidableField]
  -- `η = 1 / x`
  set η : RatFunc R := aeval (RatFunc.X : RatFunc R) (CPoly.toPoly En) /
    aeval (RatFunc.X : RatFunc R) (CPoly.toPoly Ed) with hη
  have hW : GPoly.toPoly (M₁g h0) [(En, Ed)] = C η := by
    have : (M₁g h0).sem (En, Ed) = η := sem_M₁g h0 (En, Ed)
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, this]
  have hR : ∀ r : R, (algebraMap R (RatFunc R) r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, h0, map_zero]
  have hx₀ : (RatFunc.X : RatFunc R)′ = 1 := by
    rw [ratFuncOfDeriv_X, h1, map_one]
  have ht : (RatFunc.X : RatFunc (RatFunc R))′ = algebraMap (RatFunc R) (RatFunc (RatFunc R)) η := by
    rw [ratFuncOfDeriv_X, hW, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  have hD : ∀ P : (RatFunc R)[X], P′ = implicitDeriv (C η) P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) P = _
    rw [hW]
  have hDx : ∀ P : R[X], P′ = derivative P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₀g h0) [1]) P = _
    rw [h1]
    exact implicitDeriv_one_of_trivial h0 P
  -- `η` is not a derivative in `R(x)`
  obtain ⟨hdecη, hsqη, hdegη⟩ :=
    CPoly.rationalCheck_sound_map (K := RatFunc R) (RingHom.id R) hDx En Ed Iη hcη
  simp only [Polynomial.map_id] at hdecη hsqη hdegη
  have hrη0 : CPoly.toPoly Iη.r ≠ 0 := by
    rw [Ne, ← CPoly.isZero_iff, hη0]
    exact Bool.noConfusion
  have hηnd : ∀ y : RatFunc R, y′ ≠ η := fun y hy ↦ hrη0 <| by
    refine eq_zero_of_deriv_eq_proper_fraction (K := RatFunc R) hDx _ _ hsqη hdegη
      (y - (algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.gn) /
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.gd) +
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.Q))) ?_
    have hηφ : η = algebraMap R[X] (RatFunc R) (CPoly.toPoly En) /
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Ed) := by
      rw [hη, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap]
    rw [CPoly.deriv_sub', hy, hηφ, hdecη]
    ring
  -- normality and coprimality
  have hconstP : ∀ P : (RatFunc R)[X], P′ = 0 → ∃ e : RatFunc R, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero η hηnd (by rw [← hD, hP])
  have hnormal : ∀ p : (RatFunc R)[X], Irreducible p →
      ¬p ∣ implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) p := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive η hD hconstP hp
  -- (1) Hermite reduction, always certified
  have hchk := GPoly.hermiteCheck_hermite (M₁g h0) [(En, Ed)] A D (fun p hp _ ↦ hnormal p hp) hD0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound (M₁g h0) [(En, Ed)] A D _ hchk
  set h := GPoly.hermite (ops₁g R) [(En, Ed)] A D with hh
  set S := GPoly.toPoly (M₁g h0) h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  -- (2) polynomial part and proper part
  have hdm := GPoly.divMod_spec (M₁g h0) h.b h.s
  have hdeglt := GPoly.divMod_degree_lt (M₁g h0) h.b h.s hS0
  set q := (GPoly.divMod (ops₁g R) h.b h.s).1 with hq
  set rem := (GPoly.divMod (ops₁g R) h.b h.s).2 with hrem
  -- (3) the residue polynomial
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) S) S :=
    isCoprime_deriv_of_squarefree (s := S) hsq fun p hp _ ↦ hnormal p hp
  have hr := GPoly.residuePoly_spec (M₁g h0) [(En, Ed)] rem h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly (M₁g h0) (GPoly.residuePoly (ops₁g R) [(En, Ed)] rem h.s) *
      (mapCoeffs S + C η * derivative S) - GPoly.toPoly (M₁g h0) rem := by
    have hidd : implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) S =
        mapCoeffs S + C η * derivative S := by
      rw [hW]
      simp [implicitDeriv]
    rwa [hidd] at hr
  have hst : aeval (RatFunc.X : RatFunc (RatFunc R)) S ≠ 0 := by
    rw [RatFunc.aeval_X_left_eq_algebraMap]
    exact RatFunc.algebraMap_ne_zero hS0
  -- (4) the polynomial part, coefficientwise
  have hqsum : GPoly.toPoly (M₁g h0) q = ∑ j ∈ Finset.range (q.length + 1),
      C (aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyA q j)) /
        aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyD q j))) * X ^ j := by
    ext n
    rw [GPoly.coeff_toPoly, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hn : n < q.length + 1
    · rw [Finset.sum_eq_single n (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), mul_zero])
        (fun h' ↦ absurd (Finset.mem_range.mpr hn) h'), if_pos rfl, mul_one, polyA, polyD,
        ← sem_M₁g h0, (sem_normFrac h0 _).1]
      by_cases hn' : n < q.length
      · rw [List.getD_eq_getElem _ _ (by simpa using hn'), List.getElem_map,
          List.getD_eq_getElem _ _ hn']
      · rw [List.getD_eq_default _ _ (by simpa using hn'), List.getD_eq_default _ _ (by omega),
          sem_M₁g]
        simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      refine (Finset.sum_eq_zero fun b hb ↦ ?_).symm
      rw [if_neg (by have := Finset.mem_range.mp hb; omega), mul_zero]
  have hform : algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) A) /
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D) =
      (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gn) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gd))′ +
      ∑ j ∈ Finset.range (q.length + 1),
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) (CPoly.toPoly (polyA q j)) /
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
            (CPoly.toPoly (polyD q j)) * RatFunc.X ^ j +
      aeval (RatFunc.X : RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) rem) /
        aeval (RatFunc.X : RatFunc (RatFunc R)) S := by
    have hφS : algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) S ≠ 0 :=
      RatFunc.algebraMap_ne_zero hS0
    have hsumφ : ∑ j ∈ Finset.range (q.length + 1),
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) (CPoly.toPoly (polyA q j)) /
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
            (CPoly.toPoly (polyD q j)) * RatFunc.X ^ j =
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) q) := by
      rw [hqsum, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
        aeval_algebraMap_apply, aeval_algebraMap_apply, ← map_div₀, RatFunc.algebraMap_eq_C]
    rw [hid, hsumφ, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap, hdm,
      map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one]
    ring
  -- unpack the data
  simp only [integratePrimData] at hdata
  split_ifs at hdata with hchk'
  rw [Option.map_eq_some_iff] at hdata
  obtain ⟨L₀, hL₀, hpair⟩ := hdata
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, rfl, rfl⟩ := hpair
  have hDAR : DifferentialAlgebra R (RatFunc (RatFunc R)) := ⟨fun r ↦ by
    have : algebraMap R (RatFunc (RatFunc R)) r =
        algebraMap (RatFunc R) (RatFunc (RatFunc R)) (algebraMap R (RatFunc R) r) := rfl
    rw [this, deriv_algebraMap, deriv_algebraMap]
    rfl⟩
  have hEd : CPoly.toPoly Ed ≠ 0 := by
    have hc := hcη
    rw [CPoly.rationalCheck, Bool.and_eq_true] at hc
    exact ((CPoly.hermiteCheck_iff _ _ _).mp hc.1).1
  have hxK : (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)′ = 1 := by
    rw [deriv_algebraMap, hx₀, map_one]
  have htK : (RatFunc.X : RatFunc (RatFunc R))′ =
      CPoly.evx (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) (En, Ed) := by
    rw [ht, CPoly.evx, map_div₀, aeval_algebraMap_apply, aeval_algebraMap_apply]
  have hanti := CPoly.primLoop_antiderivative h0
    (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) RatFunc.X hxK En Ed htK Iη hcη hEd
    (polyA q) (polyD q) q.length (fun j _ _ ↦ (sem_normFrac h0 _).2) ([], [1]) (by simp) hL₀
  have hz : (CPoly.evx (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
      (([] : CPoly R), ([1] : CPoly R)))′ = 0 := by simp [CPoly.evx]
  rw [hz, zero_mul, zero_add] at hanti
  simp only [CPoly.evx] at hanti ⊢
  rw [hform, hanti, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap,
    map_add]
  ring

/-- **The integrator for `R(x)(log x)`.** -/
def integrateLog (Iη : CPoly.RationalIntegral R) (A D : GPoly (GFrac R)) : Bool :=
  integratePrim logEn logEd Iη A D

end Generic

end Tower

namespace Tower

open CPoly.PrimPolyExample

/-- **The verified integrator for `ℚ(x)(log x)`.** -/
theorem integrateLog_decides_rat (A D : GPoly (GFrac ℚ))
    (hD0 : letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
      GPoly.toPoly M₁ D ≠ 0) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (GPoly.toPoly M₁ [invX])
    HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ A) /
        algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ D)) ↔
      integrateLog Iη A D = true :=
  integratePrim_decides (fun _ ↦ rfl) En Ed Iη check_η η_not_derivative A D hD0

-- `log x` : elementary
#eval integrateLog Iη [ops₁.zero, ops₁.one] [ops₁.one]
-- `1 / log x` : not elementary
#eval integrateLog Iη [ops₁.one] [ops₁.zero, ops₁.one]
-- `1 / log² x` : not elementary
#eval integrateLog Iη [ops₁.one] [ops₁.zero, ops₁.zero, ops₁.one]
-- `1 / (x log² x)` : elementary
#eval integrateLog Iη [invX] [ops₁.zero, ops₁.zero, ops₁.one]
-- `log x / (x + 1)` : not elementary (dilogarithm)
#eval integrateLog Iη [ops₁.zero, (([1] : GPoly ℚ), ([1, 1] : GPoly ℚ))] [ops₁.one]
-- `(log x - 1) / log² x` : elementary (`x / log x`)
#eval integrateLog Iη [(([-1] : GPoly ℚ), ([1] : GPoly ℚ)), ops₁.one]
  [ops₁.zero, ops₁.zero, ops₁.one]
-- `1 / (x (log² x + 1))` : elementary
#eval integrateLog Iη [invX] [ops₁.one, ops₁.zero, ops₁.one]
-- `x / (log² x + 1)`
#eval integrateLog Iη [(([0, 1] : GPoly ℚ), ([1] : GPoly ℚ))] [ops₁.one, ops₁.zero, ops₁.one]

-- the computed data for `∫ log² x dx`: `(cₖ, Qₖ) = (0, x), (0, -2x)`, i.e. `x log² x - 2x log x + ∫ 2`
#eval (integratePrimData En Ed Iη [ops₁.zero, ops₁.zero, ops₁.one] [ops₁.one]).map (·.2.1)

/-! ### Another primitive: `t = arctan x`, `η = 1 / (x² + 1)` -/

/-- Hermite data of `1 / (x² + 1)`. -/
def IηArctan : CPoly.RationalIntegral ℚ := CPoly.integrateRational [1] [1, 0, 1]

theorem check_arctan : CPoly.rationalCheck [1] [1, 0, 1] IηArctan = true := by decide +kernel

theorem arctan_not_derivative : CPoly.isZero IηArctan.r = false := by decide +kernel

/-- The verified integrator for `ℚ(x)(arctan x)`. -/
theorem integrateArctan_decides (A D : GPoly (GFrac ℚ))
    (hD0 : letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
      GPoly.toPoly M₁ D ≠ 0) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (GPoly.toPoly M₁ [(([1] : GPoly ℚ), ([1, 0, 1] : GPoly ℚ))])
    HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ A) /
        algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ D)) ↔
      integratePrim [1] [1, 0, 1] IηArctan A D = true :=
  integratePrim_decides (fun _ ↦ rfl) [1] [1, 0, 1] IηArctan check_arctan arctan_not_derivative
    A D hD0

-- `arctan x` : elementary
#eval integratePrim [1] [1, 0, 1] IηArctan [ops₁.zero, ops₁.one] [ops₁.one]
-- `arctan x / x` : not elementary
#eval integratePrim [1] [1, 0, 1] IηArctan [ops₁.zero, invX] [ops₁.one]
-- `arctan x / (x² + 1)` : elementary
#eval integratePrim [1] [1, 0, 1] IηArctan
  [ops₁.zero, (([1] : GPoly ℚ), ([1, 0, 1] : GPoly ℚ))] [ops₁.one]

end Tower
