import RischTragerBronstein.Computable.IntegrateLog
import RischTragerBronstein.Computable.ExpFullDecision
import RischTragerBronstein.Computable.GSplitX
import RischTragerBronstein.RDE.ExpPolynomial

/-!
# The integrator for `R(x)(t)`, `t = exp a(x)`: a verified decision procedure

`Tower.integrateExp a A D : Bool` decides whether `A / D ∈ R(x)(t)`, `t′ = a′(x) t`, `a ∈ R[x]`
nonconstant, has an elementary integral:

1. split off the powers of `t` in the denominator: `A / D = u / d₁ + v / t ^ k` (`GPoly.expSplit`);
2. Hermite reduction of `u / d₁` (all prime factors of `d₁` are normal, so the generic `GPoly.hermite`
   is always certified);
3. Euclidean division: polynomial part `q`, proper part `rem / s`; the Laurent part is
   `Λ / t ^ k`, `Λ = q t ^ k + v`;
4. the resultant-free residue test on `rem / s`;
5. one Risch differential equation `y′ + (j - k) a′ y = Λⱼ` over `R(x)` per coefficient `j ≠ k`
   (`CPoly.rdeRational`).

`integrateExp_decides`: the integrand has an elementary integral **iff** the procedure answers
`true` — both directions proved, no assumption on constants.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Tower

section Generic

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

/-- The code of `t′ = a′ t`. -/
def expW (a : CPoly R) : GPoly (GFrac R) := [(ops₁g R).zero, (CPoly.deriv a, [1])]

/-- **The integrator for `R(x)(exp a(x))`**, as a decision procedure. -/
def integrateExp (a : CPoly R) (A D : GPoly (GFrac R)) : Bool :=
  let sp := GPoly.expSplit (ops₁g R) A D
  let h := GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  let Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1
  GPoly.residueCheck (ops₁g R) (expW a) qr.2 h.s &&
    (List.range (Λ.length + sp.2.2.1 + 1)).all fun j ↦
      decide (j = sp.2.2.1) ||
        (CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - sp.2.2.1)) (polyA Λ j) (polyD Λ j)).isSome

/-- A polynomial over `R(x)` as the sum of its coefficient fractions. -/
lemma toPoly_M₁g_eq_sum (h0 : ∀ r : R, r′ = 0) (q : GPoly (GFrac R)) (N : ℕ)
    (hN : q.length ≤ N) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    GPoly.toPoly (M₁g h0) q = ∑ j ∈ Finset.range N,
      C (aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyA q j)) /
        aeval (RatFunc.X : RatFunc R) (CPoly.toPoly (polyD q j))) * X ^ j := by
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  ext n
  rw [GPoly.coeff_toPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hn : n < N
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

set_option maxHeartbeats 1000000 in
theorem integrateExp_decides (h0 : ∀ r : R, r′ = 0) (a : CPoly R)
    (ha : CPoly.trim (CPoly.deriv a) ≠ []) (A D : GPoly (GFrac R))
    (hD0 : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      GPoly.toPoly (M₁g h0) D ≠ 0) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (expW a))
    HasElementaryIntegral (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R))
        (GPoly.toPoly (M₁g h0) A) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D)) ↔
      integrateExp a A D = true := by
  let _ : Differential R[X] := polynomialOfDeriv (GPoly.toPoly (M₀g h0) [1])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv _
  have hDA0' : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (GPoly.toPoly (M₁g h0) (expW a))
  let _ : Differential (RatFunc (RatFunc R)) :=
    ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (expW a))
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have h1 : GPoly.toPoly (M₀g h0) [1] = 1 := by
    simp [GPoly.toPoly, M₀g, CField.ofDecidableField]
  -- `η = a′(x)`
  set η : RatFunc R := aeval (RatFunc.X : RatFunc R) (derivative (CPoly.toPoly a)) with hη
  have hηφ : η = algebraMap R[X] (RatFunc R) (derivative (CPoly.toPoly a)) :=
    RatFunc.aeval_X_left_eq_algebraMap _
  have hW : GPoly.toPoly (M₁g h0) (expW a) = C η * X := by
    have hsem : (M₁g h0).sem (CPoly.deriv a, [1]) = η := by
      rw [sem_M₁g, CPoly.toPoly_deriv]
      simp [hη]
    have hexp : GPoly.toPoly (M₁g h0) (expW a) = C ((M₁g h0).sem (ops₁g R).zero) +
        X * (C ((M₁g h0).sem (CPoly.deriv a, [1])) + X * 0) := rfl
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
    change implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) P = _
    rw [hW]
  have hDx : ∀ P : R[X], P′ = derivative P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₀g h0) [1]) P = _
    rw [h1]
    exact implicitDeriv_one_of_trivial h0 P
  -- no new constants
  have hdega : 1 ≤ (CPoly.toPoly a).natDegree := by
    by_contra hlt
    have h0' : derivative (CPoly.toPoly a) = 0 := by
      rw [eq_C_of_natDegree_eq_zero (by omega : (CPoly.toPoly a).natDegree = 0), derivative_C]
    exact ha ((CPoly.trim_eq_nil_iff _).mpr (by rw [CPoly.toPoly_deriv, h0']))
  have hconst : ∀ (P : (RatFunc R)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : RatFunc R, P = C e * X ^ n :=
    exp_polynomial_no_new_constants hDx (CPoly.toPoly a) hdega
      (fun P ↦ by rw [hD, hηφ])
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec (M₁g h0) A D hD0
  set sp := GPoly.expSplit (ops₁g R) A D with hsp
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly (M₁g h0) sp.2.2.2 ≠ 0 := fun h ↦ hD0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (RatFunc R)[X], Irreducible p → p ∣ GPoly.toPoly (M₁g h0) sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η hD hconst hp hsp').trans hpd)
  -- (2) Hermite reduction, always certified
  have hchk := GPoly.hermiteCheck_hermite (M₁g h0) (expW a) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound (M₁g h0) (expW a) sp.1 sp.2.2.2 _ hchk
  have hsdvd := GPoly.hermite_s_dvd (M₁g h0) (expW a) sp.1 sp.2.2.2 hd₁0
  set h := GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2 with hh
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
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) S) S :=
    isCoprime_deriv_of_squarefree (s := S) hsq fun p hp hpS ↦
      hnormal p hp (hpS.trans hsdvd)
  have hr := GPoly.residuePoly_spec (M₁g h0) (expW a) rem h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly (M₁g h0) (GPoly.residuePoly (ops₁g R) (expW a) rem h.s) *
      (mapCoeffs S + C η * X * derivative S) - GPoly.toPoly (M₁g h0) rem := by
    have hidd : implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) S =
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
  have key := CPoly.expFull_decides (R := R) (F₀ := RatFunc R) (K := RatFunc (RatFunc R))
    hR RatFunc.X hx₀ RatFunc.adjoin_X RatFunc.X RatFunc.adjoin_X ht0 a ha ht
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
  rw [hform, key, integrateExp, Bool.and_eq_true,
    GPoly.residueCheck_iff (M₁g h0) (expW a) rem h.s hS0, List.all_eq_true]
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
def expSol (a : CPoly R) (k : ℕ) (Λ : GPoly (GFrac R)) (j : ℕ) : CPoly R × CPoly R :=
  (CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - k)) (polyA Λ j) (polyD Λ j)).getD ([], [1])

set_option maxHeartbeats 1000000 in
/-- **The result is an antiderivative.** When `integrateExp` succeeds,

  `A / D = (gn / gd + ∑_{j ≠ k} yⱼ t ^ j / t ^ k)′ + Λₖ(x) + rem / s`,

with `yⱼ` the solutions returned by the verified RDE solver, `Λₖ ∈ R(x)` a rational function
(integrated by `integrateRational`), and `rem / s` passing the residue test
(`∫ rem / s = ∑ r(α) log (t - α) - (∑ r(α)) a`). -/
theorem integrateExp_antiderivative (h0 : ∀ r : R, r′ = 0) (a : CPoly R)
    (ha : CPoly.trim (CPoly.deriv a) ≠ []) (A D : GPoly (GFrac R))
    (hD0 : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      GPoly.toPoly (M₁g h0) D ≠ 0) (hint : integrateExp a A D = true) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (expW a))
    letI x : RatFunc (RatFunc R) := algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X
    letI sp := GPoly.expSplit (ops₁g R) A D
    letI h := GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2
    letI qr := GPoly.divMod (ops₁g R) h.b h.s
    letI Λ := GPoly.add (ops₁g R)
      (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1
    algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) A) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D) =
      (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gn) /
          algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.gd) +
        ∑ j ∈ (Finset.range (Λ.length + sp.2.2.1 + 1)).erase sp.2.2.1,
          aeval x (CPoly.toPoly (expSol a sp.2.2.1 Λ j).1) /
            aeval x (CPoly.toPoly (expSol a sp.2.2.1 Λ j).2) * RatFunc.X ^ j /
              RatFunc.X ^ sp.2.2.1)′ +
      aeval x (CPoly.toPoly (polyA Λ sp.2.2.1)) / aeval x (CPoly.toPoly (polyD Λ sp.2.2.1)) +
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) qr.2) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) h.s) := by

  let _ : Differential R[X] := polynomialOfDeriv (GPoly.toPoly (M₀g h0) [1])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv _
  have hDA0' : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (GPoly.toPoly (M₁g h0) (expW a))
  let _ : Differential (RatFunc (RatFunc R)) :=
    ratFuncOfDeriv (GPoly.toPoly (M₁g h0) (expW a))
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have h1 : GPoly.toPoly (M₀g h0) [1] = 1 := by
    simp [GPoly.toPoly, M₀g, CField.ofDecidableField]
  -- `η = a′(x)`
  set η : RatFunc R := aeval (RatFunc.X : RatFunc R) (derivative (CPoly.toPoly a)) with hη
  have hηφ : η = algebraMap R[X] (RatFunc R) (derivative (CPoly.toPoly a)) :=
    RatFunc.aeval_X_left_eq_algebraMap _
  have hW : GPoly.toPoly (M₁g h0) (expW a) = C η * X := by
    have hsem : (M₁g h0).sem (CPoly.deriv a, [1]) = η := by
      rw [sem_M₁g, CPoly.toPoly_deriv]
      simp [hη]
    have hexp : GPoly.toPoly (M₁g h0) (expW a) = C ((M₁g h0).sem (ops₁g R).zero) +
        X * (C ((M₁g h0).sem (CPoly.deriv a, [1])) + X * 0) := rfl
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
    change implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) P = _
    rw [hW]
  have hDx : ∀ P : R[X], P′ = derivative P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₀g h0) [1]) P = _
    rw [h1]
    exact implicitDeriv_one_of_trivial h0 P
  -- no new constants
  have hdega : 1 ≤ (CPoly.toPoly a).natDegree := by
    by_contra hlt
    have h0' : derivative (CPoly.toPoly a) = 0 := by
      rw [eq_C_of_natDegree_eq_zero (by omega : (CPoly.toPoly a).natDegree = 0), derivative_C]
    exact ha ((CPoly.trim_eq_nil_iff _).mpr (by rw [CPoly.toPoly_deriv, h0']))
  have hconst : ∀ (P : (RatFunc R)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : RatFunc R, P = C e * X ^ n :=
    exp_polynomial_no_new_constants hDx (CPoly.toPoly a) hdega
      (fun P ↦ by rw [hD, hηφ])
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec (M₁g h0) A D hD0
  set sp := GPoly.expSplit (ops₁g R) A D with hsp
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly (M₁g h0) sp.2.2.2 ≠ 0 := fun h ↦ hD0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (RatFunc R)[X], Irreducible p → p ∣ GPoly.toPoly (M₁g h0) sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η hD hconst hp hsp').trans hpd)
  -- (2) Hermite reduction, always certified
  have hchk := GPoly.hermiteCheck_hermite (M₁g h0) (expW a) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound (M₁g h0) (expW a) sp.1 sp.2.2.2 _ hchk
  have hsdvd := GPoly.hermite_s_dvd (M₁g h0) (expW a) sp.1 sp.2.2.2 hd₁0
  set h := GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2 with hh
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
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) S) S :=
    isCoprime_deriv_of_squarefree (s := S) hsq fun p hp hpS ↦
      hnormal p hp (hpS.trans hsdvd)
  have hr := GPoly.residuePoly_spec (M₁g h0) (expW a) rem h.s hS0 hcop
  have hr' : S ∣ GPoly.toPoly (M₁g h0) (GPoly.residuePoly (ops₁g R) (expW a) rem h.s) *
      (mapCoeffs S + C η * X * derivative S) - GPoly.toPoly (M₁g h0) rem := by
    have hidd : implicitDeriv (GPoly.toPoly (M₁g h0) (expW a)) S =
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
  have hall : ∀ j < N, j ≠ k → CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - k))
      (polyA Λ j) (polyD Λ j) = some ((expSol a k Λ j).1, (expSol a k Λ j).2) := by
    intro j hj hjk
    simp only [integrateExp, Bool.and_eq_true, List.all_eq_true] at hint
    have := hint.2 j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq] at this
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (this.resolve_left hjk)
    rw [expSol, hp]
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
      aeval (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X)
        (derivative (CPoly.toPoly a)) * RatFunc.X := by
    rw [ht, aeval_algebraMap_apply]
  have hanti := CPoly.expLaurent_antiderivative h0
    (algebraMap (RatFunc R) (RatFunc (RatFunc R)) RatFunc.X) RatFunc.X hxK ht0 a htK N k
    (polyA Λ) (polyD Λ) (fun j ↦ (expSol a k Λ j).1) (fun j ↦ (expSol a k Λ j).2)
    (fun j _ ↦ (sem_normFrac h0 _).2) hall
  rw [hform, map_add, hanti, RatFunc.aeval_X_left_eq_algebraMap,
    RatFunc.aeval_X_left_eq_algebraMap]
  ring


end Generic

end Tower

namespace Tower

/-- **The verified integrator for `ℚ(x)(exp a(x))`.** -/
theorem integrateExp_decides_rat (a : CPoly ℚ) (ha : CPoly.trim (CPoly.deriv a) ≠ [])
    (A D : GPoly (GFrac ℚ))
    (hD0 : letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
      GPoly.toPoly M₁ D ≠ 0) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (GPoly.toPoly M₁ (expW a))
    HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ A) /
        algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ D)) ↔
      integrateExp a A D = true :=
  integrateExp_decides (fun _ ↦ rfl) a ha A D hD0

/-- The code of `x ∈ ℚ(x)`. -/
def cx : GFrac ℚ := ([0, 1], [1])

-- t = exp(x):  `∫ eˣ` ✓
#eval integrateExp [0, 1] [ops₁.zero, ops₁.one] [ops₁.one]
-- `∫ eˣ / x` ✗
#eval integrateExp [0, 1] [ops₁.zero, invX] [ops₁.one]
-- `∫ x eˣ` ✓
#eval integrateExp [0, 1] [ops₁.zero, cx] [ops₁.one]
-- `∫ 1 / (eˣ + 1)` ✓  (= x - log (eˣ + 1))
#eval integrateExp [0, 1] [ops₁.one] [ops₁.one, ops₁.one]
-- `∫ x / (eˣ + 1)` ✗
#eval integrateExp [0, 1] [cx] [ops₁.one, ops₁.one]
-- `∫ e⁻ˣ = ∫ 1 / t` ✓
#eval integrateExp [0, 1] [ops₁.one] [ops₁.zero, ops₁.one]
-- `∫ eˣ / (eˣ + 1)²` ✓
#eval integrateExp [0, 1] [ops₁.zero, ops₁.one] [ops₁.one, (([2] : GPoly ℚ), ([1] : GPoly ℚ)), ops₁.one]
-- t = exp(x²):  `∫ e^{x²}` ✗
#eval integrateExp [0, 0, 1] [ops₁.zero, ops₁.one] [ops₁.one]
-- `∫ x e^{x²}` ✓
#eval integrateExp [0, 0, 1] [ops₁.zero, cx] [ops₁.one]
-- `∫ e^{-x²} = ∫ 1 / t` ✗  (the error function)
#eval integrateExp [0, 0, 1] [ops₁.one] [ops₁.zero, ops₁.one]
-- `∫ (2x² + 1) e^{x²}` ✓ (= x e^{x²})
#eval integrateExp [0, 0, 1] [ops₁.zero, (([1, 0, 2] : GPoly ℚ), ([1] : GPoly ℚ))] [ops₁.one]

/-- **The error function is not elementary**: `∫ e^{-x²} dx`, decided by the verified integrator. -/
theorem erf_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (GPoly.toPoly M₁ (expW ([0, 0, 1] : CPoly ℚ)))
    ¬HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
        (GPoly.toPoly M₁ [ops₁.one]) /
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ [ops₁.zero, ops₁.one])) := by
  let _ : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
  have hs : GPoly.toPoly M₁ [ops₁.zero, ops₁.one] = X := by
    simp [GPoly.toPoly, M₁.sem_zero, M₁.sem_one]
  have := integrateExp_decides_rat [0, 0, 1] (by decide +kernel) [ops₁.one] [ops₁.zero, ops₁.one]
    (by rw [hs]; exact X_ne_zero)
  rw [this]
  decide +kernel

end Tower
