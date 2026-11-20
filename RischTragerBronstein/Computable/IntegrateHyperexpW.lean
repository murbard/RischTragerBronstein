import RischTragerBronstein.Computable.IntegrateLog
import RischTragerBronstein.Computable.IntegrateExp
import RischTragerBronstein.Computable.HyperexpWFullDecision
import RischTragerBronstein.RDE.HyperexpConstantsW
import RischTragerBronstein.Computable.IntegrateHyperexp
import RischTragerBronstein.Computable.GSplitX
import RischTragerBronstein.RDE.ExpPolynomial

/-!
# The integrator for `R(x)(t)`, `t′ = η t` hyperexponential, `η ∈ R(x)` **arbitrary**

`η = Gn / Gd ∈ R(x)` in lowest terms, with the single hypothesis that `t` is a monomial:
`η` is not the logarithmic derivative of a radical, certified by
`CPoly.hyperexpMonomialCheck Gn Gd μ` (`μ` an annihilating polynomial of the residues of `η` at its
simple poles, e.g. `μ = CPoly.findMu …`). This covers `exp (arctan x)` (`η = 1 / (x² + 1)`),
`exp (a(x))` for every rational `a`, and hyperexponentials whose `η` has simple poles with
non-rational residues.

`Tower.integrateHyperexpW Gn Gd μ A D : Bool` decides whether `A / D ∈ R(x)(t)` has an
elementary integral, by the same pipeline as `integrateHyperexp`, with the Risch differential
equations `y′ + (j - k) η y = Λⱼ` solved by the weakly normalised solver `CPoly.rdeRationalW`.

`integrateHyperexpW_decides`: both directions proved, no assumption on constants.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Tower

section Generic

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [CPoly.HasRatRoots R] [HasNatTest R]

/-- **The integrator for a hyperexponential over `R(x)`**, as a decision procedure. -/
def integrateHyperexpW (Gn Gd μ : CPoly R) (A D : GPoly (GFrac R)) : Bool :=
  let sp := GPoly.expSplit (ops₁g R) A D
  let h := GPoly.hermite (ops₁g R) (hexpW Gn Gd) sp.1 sp.2.2.2
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  let Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1
  GPoly.residueCheck (ops₁g R) (hexpW Gn Gd) qr.2 h.s &&
    (List.range (Λ.length + sp.2.2.1 + 1)).all fun j ↦
      decide (j = sp.2.2.1) ||
        (CPoly.rdeRationalW (CPoly.scaleMu ((((j : ℤ) - sp.2.2.1 : ℤ)) : R) μ)
          (CPoly.smul ((((j : ℤ) - sp.2.2.1 : ℤ)) : R) Gn) Gd (polyA Λ j) (polyD Λ j)).isSome

set_option maxHeartbeats 1000000 in
theorem integrateHyperexpW_decides (h0 : ∀ r : R, r′ = 0) (Gn Gd μ : CPoly R)
    (hGn0 : CPoly.toPoly Gn ≠ 0) (hGd0 : CPoly.toPoly Gd ≠ 0)
    (hcopη : IsCoprime (CPoly.toPoly Gn) (CPoly.toPoly Gd))
    (hcert : CPoly.hyperexpMonomialCheck Gn Gd μ = true)
    (A D : GPoly (GFrac R))
    (hD0 : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      GPoly.toPoly (M₁g h0) D ≠ 0) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd))
    HasElementaryIntegral (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R))
        (GPoly.toPoly (M₁g h0) A) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D)) ↔
      integrateHyperexpW Gn Gd μ A D = true := by
  let _ : Differential R[X] := polynomialOfDeriv (GPoly.toPoly (M₀g h0) [1])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv _
  have hDA0' : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd))
  let _ : Differential (RatFunc (RatFunc R)) :=
    ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd))
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have h1 : GPoly.toPoly (M₀g h0) [1] = 1 := by
    simp [GPoly.toPoly, M₀g, CField.ofDecidableField]
  -- `η = a′(x)`
  set η : RatFunc R := aeval (RatFunc.X : RatFunc R) (CPoly.toPoly Gn) /
    aeval (RatFunc.X : RatFunc R) (CPoly.toPoly Gd) with hη
  have hηφ : η = algebraMap R[X] (RatFunc R) (CPoly.toPoly Gn) /
      algebraMap R[X] (RatFunc R) (CPoly.toPoly Gd) := by
    rw [hη, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap]
  have hW : GPoly.toPoly (M₁g h0) (hexpW Gn Gd) = C η * X := by
    have hsem : (M₁g h0).sem (Gn, Gd) = η := sem_M₁g h0 (Gn, Gd)
    have hexp : GPoly.toPoly (M₁g h0) (hexpW Gn Gd) = C ((M₁g h0).sem (ops₁g R).zero) +
        X * (C ((M₁g h0).sem (Gn, Gd)) + X * 0) := rfl
    rw [hexp, (M₁g h0).sem_zero, hsem, C_0, zero_add, mul_zero, add_zero, mul_comm]
  have hR : ∀ r : R, (algebraMap R (RatFunc R) r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, h0, map_zero]
  have hx₀ : (RatFunc.X : RatFunc R)′ = 1 := by
    rw [ratFuncOfDeriv_X, h1, map_one]
  have ht : (RatFunc.X : RatFunc (RatFunc R))′ =
      algebraMap (RatFunc R) (RatFunc (RatFunc R)) η * RatFunc.X := by
    rw [ratFuncOfDeriv_X, hW, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      RatFunc.algebraMap_eq_C]
  have hD : ∀ P : (RatFunc R)[X], P′ = implicitDeriv (C η * X) P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) P = _
    rw [hW]
  have hDx : ∀ P : R[X], P′ = derivative P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₀g h0) [1]) P = _
    rw [h1]
    exact implicitDeriv_one_of_trivial h0 P
  -- no new constants
  have hconst : ∀ (P : (RatFunc R)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : RatFunc R, P = C e * X ^ n :=
    hyperexp_no_new_constants_W (CPoly.toPoly Gn) (CPoly.toPoly Gd)
      (fun c hc y hy ↦ CPoly.hyperexpW_homogeneous (K := RatFunc R) (RingHom.id R) hDx hGn0 hGd0
        hcopη hcert c hc y (by simpa only [Polynomial.map_id] using hy))
      (fun P ↦ by rw [hD, hηφ])
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec (M₁g h0) A D hD0
  set sp := GPoly.expSplit (ops₁g R) A D with hsp
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly (M₁g h0) sp.2.2.2 ≠ 0 := fun h ↦ hD0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (RatFunc R)[X], Irreducible p → p ∣ GPoly.toPoly (M₁g h0) sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η hD hconst hp hsp').trans hpd)
  -- (2) Hermite reduction, always certified
  have hchk := GPoly.hermiteCheck_hermite (M₁g h0) (hexpW Gn Gd) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound (M₁g h0) (hexpW Gn Gd) sp.1 sp.2.2.2 _ hchk
  have hsdvd := GPoly.hermite_s_dvd (M₁g h0) (hexpW Gn Gd) sp.1 sp.2.2.2 hd₁0
  set h := GPoly.hermite (ops₁g R) (hexpW Gn Gd) sp.1 sp.2.2.2 with hh
  set S := GPoly.toPoly (M₁g h0) h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ S := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) polynomial part and proper part
  have hdm := GPoly.divMod_spec (M₁g h0) h.b h.s
  have hdeglt := GPoly.divMod_degree_lt (M₁g h0) h.b h.s hS0
  set q := (GPoly.divMod (ops₁g R) h.b h.s).1 with hq
  set rem := (GPoly.divMod (ops₁g R) h.b h.s).2 with hrem
  set Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) q (GPoly.monomial (ops₁g R) k (ops₁g R).one)) sp.2.1 with hΛ
  have hΛpoly : GPoly.toPoly (M₁g h0) Λ =
      GPoly.toPoly (M₁g h0) q * X ^ k + GPoly.toPoly (M₁g h0) sp.2.1 := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, (M₁g h0).sem_one, C_1,
      one_mul]
  -- (4) the residue polynomial
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) S) S :=
    isCoprime_deriv_of_squarefree (s := S) hsq fun p hp hpS ↦
      hnormal p hp (hpS.trans hsdvd)
  have hr := GPoly.residuePoly_spec (M₁g h0) (hexpW Gn Gd) rem h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly (M₁g h0) (GPoly.residuePoly (ops₁g R) (hexpW Gn Gd) rem h.s) *
      (mapCoeffs S + C η * X * derivative S) - GPoly.toPoly (M₁g h0) rem := by
    have hidd : implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) S =
        mapCoeffs S + C η * X * derivative S := by
      rw [hW]
      simp [implicitDeriv]
    rwa [hidd] at hr
  have hst : aeval (RatFunc.X : RatFunc (RatFunc R)) S ≠ 0 := by
    rw [RatFunc.aeval_X_left_eq_algebraMap]
    exact RatFunc.algebraMap_ne_zero hS0
  have ht0 : (RatFunc.X : RatFunc (RatFunc R)) ≠ 0 := RatFunc.X_ne_zero
  -- (5) the Laurent part, coefficientwise
  set N := Λ.length + k + 1 with hN
  have hΛsum := toPoly_M₁g_eq_sum h0 Λ N (by omega)
  have key := CPoly.hyperexpWFull_decides (R := R) (F₀ := RatFunc R) (K := RatFunc (RatFunc R))
    hR RatFunc.X hx₀ RatFunc.adjoin_X RatFunc.X RatFunc.adjoin_X ht0 Gn Gd μ hGn0 hGd0 hcopη hcert ht
    (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gn) /
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gd))
    N k (polyA Λ) (polyD Λ) (polyA Λ k) (polyD Λ k) (sem_normFrac h0 _).2
    (fun j _ ↦ (sem_normFrac h0 _).2)
    (GPoly.toPoly (M₁g h0) rem) S _ hsq hXS hdeglt hst hr'
  set φ := algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) with hφ
  have hφX : φ X = RatFunc.X := RatFunc.algebraMap_X
  have hform : φ (GPoly.toPoly (M₁g h0) A) / φ (GPoly.toPoly (M₁g h0) D) =
      (φ (GPoly.toPoly (M₁g h0) h.gn) / φ (GPoly.toPoly (M₁g h0) h.gd))′ +
      (aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyA Λ k)) /
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyD Λ k)) +
        ∑ j ∈ (Finset.range N).erase k,
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyA Λ j)) /
            aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyD Λ j)) * RatFunc.X ^ j / RatFunc.X ^ k) +
      aeval (RatFunc.X : RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) rem) /
        aeval (RatFunc.X : RatFunc (RatFunc R)) S := by
    have hφS : φ S ≠ 0 := RatFunc.algebraMap_ne_zero hS0
    have hφd₁ : φ (GPoly.toPoly (M₁g h0) sp.2.2.2) ≠ 0 := RatFunc.algebraMap_ne_zero hd₁0
    have hXk : (RatFunc.X : RatFunc (RatFunc R)) ^ k ≠ 0 := pow_ne_zero _ ht0
    have hterm : ∀ j, aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyA Λ j)) /
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyD Λ j)) =
        φ (C (aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyA Λ j)) /
          aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyD Λ j)))) := fun j ↦ by
      rw [hφ, RatFunc.algebraMap_C, aeval_algebraMap_apply, aeval_algebraMap_apply, ← map_div₀,
        RatFunc.algebraMap_eq_C]
    have hLaurent : aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyA Λ k)) /
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyD Λ k)) +
        ∑ j ∈ (Finset.range N).erase k,
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyA Λ j)) /
            aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyD Λ j)) * RatFunc.X ^ j / RatFunc.X ^ k =
        φ (GPoly.toPoly (M₁g h0) Λ) / RatFunc.X ^ k := by
      rw [hΛsum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : k < N)),
        add_div, Finset.sum_div]
      congr 1
      · rw [map_mul, map_pow, hφX, hterm, mul_div_assoc, div_self hXk, mul_one]
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_mul, map_pow, hφX, hterm]
    have hAD : φ (GPoly.toPoly (M₁g h0) A) / φ (GPoly.toPoly (M₁g h0) D) =
        φ (GPoly.toPoly (M₁g h0) sp.1) / φ (GPoly.toPoly (M₁g h0) sp.2.2.2) +
          φ (GPoly.toPoly (M₁g h0) sp.2.1) / RatFunc.X ^ k := by
      rw [← hsp1, hsp2, map_add, map_mul, map_mul, map_mul, map_pow, hφX]
      field_simp
    have hbS : φ (GPoly.toPoly (M₁g h0) h.b) / φ S =
        φ (GPoly.toPoly (M₁g h0) q) + φ (GPoly.toPoly (M₁g h0) rem) / φ S := by
      rw [hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one]
    have hΛk : φ (GPoly.toPoly (M₁g h0) Λ) / RatFunc.X ^ k =
        φ (GPoly.toPoly (M₁g h0) q) + φ (GPoly.toPoly (M₁g h0) sp.2.1) / RatFunc.X ^ k := by
      rw [hΛpoly, map_add, map_mul, map_pow, hφX, add_div, mul_div_assoc, div_self hXk, mul_one]
    rw [hLaurent, hAD, hid, RatFunc.aeval_X_left_eq_algebraMap,
      RatFunc.aeval_X_left_eq_algebraMap, hbS, hΛk]
    ring
  rw [hform, key, integrateHyperexpW, Bool.and_eq_true,
    GPoly.residueCheck_iff (M₁g h0) (hexpW Gn Gd) rem h.s hS0, List.all_eq_true]
  refine and_congr Iff.rfl ⟨fun hall j hj ↦ ?_, fun hall j hj hjk ↦ ?_⟩
  · rw [List.mem_range] at hj
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hjk : j = k
    · exact Or.inl hjk
    · exact Or.inr (hall j hj hjk)
  · have := hall j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.resolve_left hjk

/-- The solution `yⱼ = Y / G` of the `j`-th Risch differential equation (default `0 / 1`). -/
def hexpSolW (Gn Gd μ : CPoly R) (k : ℕ) (Λ : GPoly (GFrac R)) (j : ℕ) : CPoly R × CPoly R :=
  (CPoly.rdeRationalW (CPoly.scaleMu ((((j : ℤ) - k : ℤ)) : R) μ)
    (CPoly.smul ((((j : ℤ) - k : ℤ)) : R) Gn) Gd (polyA Λ j) (polyD Λ j)).getD ([], [1])

set_option maxHeartbeats 1000000 in
/-- **The result is an antiderivative.** When `integrateExp` succeeds,

  `A / D = (gn / gd + ∑_{j ≠ k} yⱼ t ^ j / t ^ k)′ + Λₖ(x) + rem / s`,

with `yⱼ` the solutions returned by the verified RDE solver, `Λₖ ∈ R(x)` a rational function
(integrated by `integrateRational`), and `rem / s` passing the residue test
(`∫ rem / s = ∑ r(α) log (t - α) - (∑ r(α)) log t`). -/
theorem integrateHyperexpW_antiderivative (h0 : ∀ r : R, r′ = 0) (Gn Gd μ : CPoly R)
    (hGn0 : CPoly.toPoly Gn ≠ 0) (hGd0 : CPoly.toPoly Gd ≠ 0)
    (hcopη : IsCoprime (CPoly.toPoly Gn) (CPoly.toPoly Gd))
    (hcert : CPoly.hyperexpMonomialCheck Gn Gd μ = true)
    (A D : GPoly (GFrac R))
    (hD0 : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      GPoly.toPoly (M₁g h0) D ≠ 0) (hint : integrateHyperexpW Gn Gd μ A D = true) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd))
    letI x : RatFunc (RatFunc R) := algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X
    letI sp := GPoly.expSplit (ops₁g R) A D
    letI h := GPoly.hermite (ops₁g R) (hexpW Gn Gd) sp.1 sp.2.2.2
    letI qr := GPoly.divMod (ops₁g R) h.b h.s
    letI Λ := GPoly.add (ops₁g R)
      (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1
    algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) A) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D) =
      (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gn) /
          algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gd) +
        ∑ j ∈ (Finset.range (Λ.length + sp.2.2.1 + 1)).erase sp.2.2.1,
          aeval x (CPoly.toPoly (hexpSolW Gn Gd μ sp.2.2.1 Λ j).1) /
            aeval x (CPoly.toPoly (hexpSolW Gn Gd μ sp.2.2.1 Λ j).2) * RatFunc.X ^ j /
              RatFunc.X ^ sp.2.2.1)′ +
      aeval x (CPoly.toPoly (polyA Λ sp.2.2.1)) / aeval x (CPoly.toPoly (polyD Λ sp.2.2.1)) +
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) qr.2) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.s) := by

  let _ : Differential R[X] := polynomialOfDeriv (GPoly.toPoly (M₀g h0) [1])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv _
  have hDA0' : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd))
  let _ : Differential (RatFunc (RatFunc R)) :=
    ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd))
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have h1 : GPoly.toPoly (M₀g h0) [1] = 1 := by
    simp [GPoly.toPoly, M₀g, CField.ofDecidableField]
  -- `η = a′(x)`
  set η : RatFunc R := aeval (RatFunc.X : RatFunc R) (CPoly.toPoly Gn) /
    aeval (RatFunc.X : RatFunc R) (CPoly.toPoly Gd) with hη
  have hηφ : η = algebraMap R[X] (RatFunc R) (CPoly.toPoly Gn) /
      algebraMap R[X] (RatFunc R) (CPoly.toPoly Gd) := by
    rw [hη, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap]
  have hW : GPoly.toPoly (M₁g h0) (hexpW Gn Gd) = C η * X := by
    have hsem : (M₁g h0).sem (Gn, Gd) = η := sem_M₁g h0 (Gn, Gd)
    have hexp : GPoly.toPoly (M₁g h0) (hexpW Gn Gd) = C ((M₁g h0).sem (ops₁g R).zero) +
        X * (C ((M₁g h0).sem (Gn, Gd)) + X * 0) := rfl
    rw [hexp, (M₁g h0).sem_zero, hsem, C_0, zero_add, mul_zero, add_zero, mul_comm]
  have hR : ∀ r : R, (algebraMap R (RatFunc R) r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, h0, map_zero]
  have hx₀ : (RatFunc.X : RatFunc R)′ = 1 := by
    rw [ratFuncOfDeriv_X, h1, map_one]
  have ht : (RatFunc.X : RatFunc (RatFunc R))′ =
      algebraMap (RatFunc R) (RatFunc (RatFunc R)) η * RatFunc.X := by
    rw [ratFuncOfDeriv_X, hW, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      RatFunc.algebraMap_eq_C]
  have hD : ∀ P : (RatFunc R)[X], P′ = implicitDeriv (C η * X) P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) P = _
    rw [hW]
  have hDx : ∀ P : R[X], P′ = derivative P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₀g h0) [1]) P = _
    rw [h1]
    exact implicitDeriv_one_of_trivial h0 P
  -- no new constants
  have hconst : ∀ (P : (RatFunc R)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : RatFunc R, P = C e * X ^ n :=
    hyperexp_no_new_constants_W (CPoly.toPoly Gn) (CPoly.toPoly Gd)
      (fun c hc y hy ↦ CPoly.hyperexpW_homogeneous (K := RatFunc R) (RingHom.id R) hDx hGn0 hGd0
        hcopη hcert c hc y (by simpa only [Polynomial.map_id] using hy))
      (fun P ↦ by rw [hD, hηφ])
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec (M₁g h0) A D hD0
  set sp := GPoly.expSplit (ops₁g R) A D with hsp
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly (M₁g h0) sp.2.2.2 ≠ 0 := fun h ↦ hD0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (RatFunc R)[X], Irreducible p → p ∣ GPoly.toPoly (M₁g h0) sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η hD hconst hp hsp').trans hpd)
  -- (2) Hermite reduction, always certified
  have hchk := GPoly.hermiteCheck_hermite (M₁g h0) (hexpW Gn Gd) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound (M₁g h0) (hexpW Gn Gd) sp.1 sp.2.2.2 _ hchk
  have hsdvd := GPoly.hermite_s_dvd (M₁g h0) (hexpW Gn Gd) sp.1 sp.2.2.2 hd₁0
  set h := GPoly.hermite (ops₁g R) (hexpW Gn Gd) sp.1 sp.2.2.2 with hh
  set S := GPoly.toPoly (M₁g h0) h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ S := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) polynomial part and proper part
  have hdm := GPoly.divMod_spec (M₁g h0) h.b h.s
  have hdeglt := GPoly.divMod_degree_lt (M₁g h0) h.b h.s hS0
  set q := (GPoly.divMod (ops₁g R) h.b h.s).1 with hq
  set rem := (GPoly.divMod (ops₁g R) h.b h.s).2 with hrem
  set Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) q (GPoly.monomial (ops₁g R) k (ops₁g R).one)) sp.2.1 with hΛ
  have hΛpoly : GPoly.toPoly (M₁g h0) Λ =
      GPoly.toPoly (M₁g h0) q * X ^ k + GPoly.toPoly (M₁g h0) sp.2.1 := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, (M₁g h0).sem_one, C_1,
      one_mul]
  -- (4) the residue polynomial
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) S) S :=
    isCoprime_deriv_of_squarefree (s := S) hsq fun p hp hpS ↦
      hnormal p hp (hpS.trans hsdvd)
  have hr := GPoly.residuePoly_spec (M₁g h0) (hexpW Gn Gd) rem h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly (M₁g h0) (GPoly.residuePoly (ops₁g R) (hexpW Gn Gd) rem h.s) *
      (mapCoeffs S + C η * X * derivative S) - GPoly.toPoly (M₁g h0) rem := by
    have hidd : implicitDeriv (GPoly.toPoly (M₁g h0) (hexpW Gn Gd)) S =
        mapCoeffs S + C η * X * derivative S := by
      rw [hW]
      simp [implicitDeriv]
    rwa [hidd] at hr
  have hst : aeval (RatFunc.X : RatFunc (RatFunc R)) S ≠ 0 := by
    rw [RatFunc.aeval_X_left_eq_algebraMap]
    exact RatFunc.algebraMap_ne_zero hS0
  have ht0 : (RatFunc.X : RatFunc (RatFunc R)) ≠ 0 := RatFunc.X_ne_zero
  -- (5) the Laurent part, coefficientwise
  set N := Λ.length + k + 1 with hN
  have hΛsum := toPoly_M₁g_eq_sum h0 Λ N (by omega)
  set φ := algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) with hφ
  have hφX : φ X = RatFunc.X := RatFunc.algebraMap_X
  have hform : φ (GPoly.toPoly (M₁g h0) A) / φ (GPoly.toPoly (M₁g h0) D) =
      (φ (GPoly.toPoly (M₁g h0) h.gn) / φ (GPoly.toPoly (M₁g h0) h.gd))′ +
      (aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyA Λ k)) /
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyD Λ k)) +
        ∑ j ∈ (Finset.range N).erase k,
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyA Λ j)) /
            aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyD Λ j)) * RatFunc.X ^ j / RatFunc.X ^ k) +
      aeval (RatFunc.X : RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) rem) /
        aeval (RatFunc.X : RatFunc (RatFunc R)) S := by
    have hφS : φ S ≠ 0 := RatFunc.algebraMap_ne_zero hS0
    have hφd₁ : φ (GPoly.toPoly (M₁g h0) sp.2.2.2) ≠ 0 := RatFunc.algebraMap_ne_zero hd₁0
    have hXk : (RatFunc.X : RatFunc (RatFunc R)) ^ k ≠ 0 := pow_ne_zero _ ht0
    have hterm : ∀ j, aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyA Λ j)) /
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyD Λ j)) =
        φ (C (aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyA Λ j)) /
          aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyD Λ j)))) := fun j ↦ by
      rw [hφ, RatFunc.algebraMap_C, aeval_algebraMap_apply, aeval_algebraMap_apply, ← map_div₀,
        RatFunc.algebraMap_eq_C]
    have hLaurent : aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyA Λ k)) /
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
          (CPoly.toPoly (polyD Λ k)) +
        ∑ j ∈ (Finset.range N).erase k,
          aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyA Λ j)) /
            aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
              (CPoly.toPoly (polyD Λ j)) * RatFunc.X ^ j / RatFunc.X ^ k =
        φ (GPoly.toPoly (M₁g h0) Λ) / RatFunc.X ^ k := by
      rw [hΛsum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : k < N)),
        add_div, Finset.sum_div]
      congr 1
      · rw [map_mul, map_pow, hφX, hterm, mul_div_assoc, div_self hXk, mul_one]
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_mul, map_pow, hφX, hterm]
    have hAD : φ (GPoly.toPoly (M₁g h0) A) / φ (GPoly.toPoly (M₁g h0) D) =
        φ (GPoly.toPoly (M₁g h0) sp.1) / φ (GPoly.toPoly (M₁g h0) sp.2.2.2) +
          φ (GPoly.toPoly (M₁g h0) sp.2.1) / RatFunc.X ^ k := by
      rw [← hsp1, hsp2, map_add, map_mul, map_mul, map_mul, map_pow, hφX]
      field_simp
    have hbS : φ (GPoly.toPoly (M₁g h0) h.b) / φ S =
        φ (GPoly.toPoly (M₁g h0) q) + φ (GPoly.toPoly (M₁g h0) rem) / φ S := by
      rw [hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one]
    have hΛk : φ (GPoly.toPoly (M₁g h0) Λ) / RatFunc.X ^ k =
        φ (GPoly.toPoly (M₁g h0) q) + φ (GPoly.toPoly (M₁g h0) sp.2.1) / RatFunc.X ^ k := by
      rw [hΛpoly, map_add, map_mul, map_pow, hφX, add_div, mul_div_assoc, div_self hXk, mul_one]
    rw [hLaurent, hAD, hid, RatFunc.aeval_X_left_eq_algebraMap,
      RatFunc.aeval_X_left_eq_algebraMap, hbS, hΛk]
    ring
  -- the RDE solutions
  have hall : ∀ j < N, j ≠ k → CPoly.rdeRationalW (CPoly.scaleMu ((((j : ℤ) - k : ℤ)) : R) μ)
      (CPoly.smul ((((j : ℤ) - k : ℤ)) : R) Gn) Gd (polyA Λ j) (polyD Λ j) =
        some ((hexpSolW Gn Gd μ k Λ j).1, (hexpSolW Gn Gd μ k Λ j).2) := by
    intro j hj hjk
    simp only [integrateHyperexpW, Bool.and_eq_true, List.all_eq_true] at hint
    have := hint.2 j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq] at this
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (this.resolve_left hjk)
    rw [hexpSolW, hp]
    rfl
  let _ : Differential R := inferInstance
  have hDAR : DifferentialAlgebra R (RatFunc (RatFunc R)) := ⟨fun r ↦ by
    have : algebraMap R (RatFunc (RatFunc R)) r =
        algebraMap (RatFunc R) (RatFunc (RatFunc R)) (algebraMap R (RatFunc R) r) := rfl
    rw [this, deriv_algebraMap, deriv_algebraMap]
    rfl⟩
  have hxK : (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)′ = 1 := by
    rw [deriv_algebraMap, hx₀, map_one]
  have htK : (RatFunc.X : RatFunc (RatFunc R))′ =
      aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) (CPoly.toPoly Gn) /
        aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) (CPoly.toPoly Gd) *
          RatFunc.X := by
    rw [ht, map_div₀, aeval_algebraMap_apply, aeval_algebraMap_apply]
  have hanti := CPoly.hyperexpLaurentW_antiderivative h0
    (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) RatFunc.X hxK ht0 μ Gn Gd hGd0 htK N k
    (polyA Λ) (polyD Λ) (fun j ↦ (hexpSolW Gn Gd μ k Λ j).1) (fun j ↦ (hexpSolW Gn Gd μ k Λ j).2)
    (fun j _ ↦ (sem_normFrac h0 _).2) hall
  rw [hform, map_add, hanti, RatFunc.aeval_X_left_eq_algebraMap,
    RatFunc.aeval_X_left_eq_algebraMap]
  ring


end Generic

/-- `μ` for `η = Gn / Gd`, computed by Gaussian elimination and verified by `muCheck`. -/
def hexpMu (Gn Gd : CPoly ℚ) : CPoly ℚ :=
  CPoly.findMu (CPoly.simplePart Gd) (CPoly.residuePolyW Gn Gd)

-- `t = exp (arctan x)`, `η = 1 / (x² + 1)`: `∫ exp (arctan x)` ✗
#eval integrateHyperexpW (R := ℚ) [1] [1, 0, 1] (hexpMu [1] [1, 0, 1]) [ops₁.zero, ops₁.one]
  [ops₁.one]
-- `∫ exp (arctan x) / (x² + 1)` ✓ (`= exp (arctan x)`)
#eval integrateHyperexpW (R := ℚ) [1] [1, 0, 1] (hexpMu [1] [1, 0, 1])
  [ops₁.zero, (([1] : GPoly ℚ), ([1, 0, 1] : GPoly ℚ))] [ops₁.one]
-- `∫ (x + 1) exp (arctan x) / (x² + 1)` ✗ ... actually `= x exp(arctan x)`? no: `(x e)′ = e + x e/(x²+1) = e (x² + x + 1)/(x²+1)`
#eval integrateHyperexpW (R := ℚ) [1] [1, 0, 1] (hexpMu [1] [1, 0, 1])
  [ops₁.zero, (([1, 1, 1] : GPoly ℚ), ([1, 0, 1] : GPoly ℚ))] [ops₁.one]
-- `t = e^{1/x}`, `η = -1 / x²`: `∫ e^{1/x}` ✗, `∫ e^{1/x} / x²` ✓
#eval integrateHyperexpW (R := ℚ) [-1] [0, 0, 1] (hexpMu [-1] [0, 0, 1]) [ops₁.zero, ops₁.one]
  [ops₁.one]
#eval integrateHyperexpW (R := ℚ) [-1] [0, 0, 1] (hexpMu [-1] [0, 0, 1])
  [ops₁.zero, (([1] : GPoly ℚ), ([0, 0, 1] : GPoly ℚ))] [ops₁.one]
#eval CPoly.hyperexpMonomialCheck ([1] : CPoly ℚ) [1, 0, 1] (hexpMu [1] [1, 0, 1])

/-- **`∫ exp (arctan x) dx` is not elementary**, decided by the verified integrator
(`t′ = t / (x² + 1)`). -/
theorem exp_arctan_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (GPoly.toPoly M₁ (hexpW ([1] : CPoly ℚ) [1, 0, 1]))
    ¬HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
        (GPoly.toPoly M₁ [ops₁.zero, ops₁.one]) /
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ [ops₁.one])) := by
  let _ : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
  have hGn : CPoly.toPoly ([1] : CPoly ℚ) = 1 := by simp [CPoly.toPoly]
  have hGd : CPoly.toPoly ([1, 0, 1] : CPoly ℚ) = X ^ 2 + 1 := by
    simp [CPoly.toPoly]; ring
  have hone : GPoly.toPoly M₁ [ops₁.one] = 1 := by simp [GPoly.toPoly, M₁.sem_one]
  have := integrateHyperexpW_decides (R := ℚ) (fun _ ↦ rfl) [1] [1, 0, 1] (hexpMu [1] [1, 0, 1])
    (by rw [hGn]; exact one_ne_zero)
    (by rw [hGd]; exact (X_pow_add_C_ne_zero two_pos 1))
    (by rw [hGn]; exact isCoprime_one_left)
    (by decide +kernel)
    [ops₁.zero, ops₁.one] [ops₁.one] (by
      change GPoly.toPoly M₁ [ops₁.one] ≠ 0
      rw [hone]; exact one_ne_zero)
  refine fun hint ↦ absurd (this.mp hint) ?_
  decide +kernel

/-- **`∫ exp (arctan x) / (x² + 1) dx` is elementary** (`= exp (arctan x)`), decided by the
verified integrator. -/
theorem exp_arctan_div_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (GPoly.toPoly M₁ (hexpW ([1] : CPoly ℚ) [1, 0, 1]))
    HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
        (GPoly.toPoly M₁ [ops₁.zero, (([1] : GPoly ℚ), ([1, 0, 1] : GPoly ℚ))]) /
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ [ops₁.one])) := by
  let _ : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
  have hGn : CPoly.toPoly ([1] : CPoly ℚ) = 1 := by simp [CPoly.toPoly]
  have hGd : CPoly.toPoly ([1, 0, 1] : CPoly ℚ) = X ^ 2 + 1 := by
    simp [CPoly.toPoly]; ring
  have hone : GPoly.toPoly M₁ [ops₁.one] = 1 := by simp [GPoly.toPoly, M₁.sem_one]
  have := integrateHyperexpW_decides (R := ℚ) (fun _ ↦ rfl) [1] [1, 0, 1] (hexpMu [1] [1, 0, 1])
    (by rw [hGn]; exact one_ne_zero)
    (by rw [hGd]; exact (X_pow_add_C_ne_zero two_pos 1))
    (by rw [hGn]; exact isCoprime_one_left)
    (by decide +kernel)
    [ops₁.zero, (([1] : GPoly ℚ), ([1, 0, 1] : GPoly ℚ))] [ops₁.one] (by
      change GPoly.toPoly M₁ [ops₁.one] ≠ 0
      rw [hone]; exact one_ne_zero)
  exact this.mpr (by decide +kernel)

end Tower
