import RischTragerBronstein.Computable.RDERationalW

/-!
# The monomial certificate for a hyperexponential `t′ = η t`, `η ∈ R(x)` arbitrary

`t` is a monomial over `R(x)` with no new constants iff `η = Gn / Gd` is not the logarithmic
derivative of a radical (Bronstein, Thm. 5.1.2). `hyperexpMonomialCheck Gn Gd μ` certifies this by
one of

* `Gd` is not squarefree (a pole of order `≥ 2`),
* `deg Gn ≥ deg Gd` (a nonzero polynomial part),
* a simple prime of `Gd` at which the residue is not a rational number: `S ∤ ∏ (r - q)` over the
  rational roots `q` of the annihilating polynomial `μ` (checked by `muCheck`),

and `hyperexpW_homogeneous` derives, over any extension of the constants, that `y′ = c η y` has
only the zero solution for `c ∈ ℤ ∖ {0}` — the hypothesis of the transcendence and no-new-constants
theorems.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasRatRoots R]

/-- `∏ (r - q)` over a list of rationals. -/
def ratShiftProd (r : CPoly R) (l : List ℚ) : CPoly R :=
  (l.map fun (q : ℚ) ↦ sub r [((q : ℚ) : R)]).foldr mul [1]

/-- **The monomial certificate** for `η = Gn / Gd`, with `μ` an annihilating polynomial of the
residues at the simple poles. -/
def hyperexpMonomialCheck (Gn Gd μ : CPoly R) : Bool :=
  let S := simplePart Gd
  let r := residuePolyW Gn Gd
  muCheck S r μ &&
    (!squarefreeCheck Gd || decide ((trim Gd).length ≤ (trim Gn).length) ||
      !isZero (divMod (ratShiftProd r (HasRatRoots.ratRoots μ)) S).2)

end Defs

section Spec

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [HasRatRoots R]

lemma toPoly_ratShiftProd (r : CPoly R) (l : List ℚ) :
    toPoly (ratShiftProd r l) = (l.map fun (q : ℚ) ↦ toPoly r - C ((q : ℚ) : R)).prod := by
  unfold ratShiftProd
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.foldr_cons, toPoly_mul, List.prod_cons, toPoly_sub, toPoly_cons,
      toPoly_nil, mul_zero, add_zero]
    rw [ih]

/-- A failed squarefreeness check exhibits a repeated factor of positive degree. -/
lemma exists_sq_dvd_of_squarefreeCheck {s : CPoly R} (hs0 : toPoly s ≠ 0)
    (h : squarefreeCheck s = false) : ∃ p : R[X], 1 ≤ p.natDegree ∧ p ^ 2 ∣ toPoly s := by
  rw [squarefreeCheck, beq_eq_false_iff_ne] at h
  obtain ⟨hgs, hgs'⟩ := egcd_dvd s (deriv s)
  rw [toPoly_deriv] at hgs'
  set g := (egcd s (deriv s)).1 with hg
  have hg0 : toPoly g ≠ 0 := fun h0 ↦ hs0 (by simpa [h0] using hgs)
  have htg : trim g ≠ [] := fun h0 ↦ hg0 ((trim_eq_nil_iff _).mp h0)
  obtain ⟨hdeg, -, -⟩ := natDegree_toPoly_of_trim_ne_nil htg
  have hlen := List.length_pos_of_ne_nil htg
  have hdeg1 : 1 ≤ (toPoly g).natDegree := by omega
  -- an irreducible factor of `g` divides `s` and `s′`, hence `p ^ 2 ∣ s`
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor
    (fun hu ↦ by rw [natDegree_eq_zero_of_isUnit hu] at hdeg1; omega) hg0
  refine ⟨p, hp.natDegree_pos, ?_⟩
  obtain ⟨w, hw⟩ := hpg.trans hgs
  have hd : p ∣ derivative (toPoly s) := hpg.trans hgs'
  rw [hw, derivative_mul] at hd
  have hnp : ¬p ∣ derivative p := not_dvd_derivative_self hp
  have : p ∣ derivative p * w := (dvd_add_left (dvd_mul_right p _)).mp hd
  obtain ⟨w', hw'⟩ := (hp.prime.dvd_or_dvd this).resolve_left hnp
  exact ⟨w', by rw [hw, hw']; ring⟩

lemma hyperexpMonomialCheck_mu {Gn Gd μ : CPoly R} (h : hyperexpMonomialCheck Gn Gd μ = true) :
    muCheck (simplePart Gd) (residuePolyW Gn Gd) μ = true := by
  simp only [hyperexpMonomialCheck, Bool.and_eq_true] at h
  exact h.1

/-- The residue polynomial of `c Gn / Gd` is `c r` modulo `S`. -/
lemma residuePolyW_smul (Gn Gd : CPoly R) (hGd0 : toPoly Gd ≠ 0) (c : R) :
    toPoly (simplePart Gd) ∣
      toPoly (residuePolyW (smul c Gn) Gd) - C c * toPoly (residuePolyW Gn Gd) := by
  obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := simplePart_data Gd hGd0
  obtain ⟨hS0, -, hcop, -, -, -⟩ := simplePart_props hGd0 E1 E2 E3 E4 E5 E6
  obtain ⟨t, ht⟩ := residuePolyW_bezout Gn Gd hS0 hcop.symm
  obtain ⟨t', ht'⟩ := residuePolyW_bezout (smul c Gn) Gd hS0 hcop.symm
  rw [toPoly_smul] at ht'
  refine hcop.dvd_of_dvd_mul_right ⟨C c * t - t', ?_⟩
  linear_combination ht' - C c * ht

variable {S K : Type*} [Field S] [CharZero S] [Differential S[X]] [Field K] [Algebra S[X] K]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

/-- **The homogeneous equation has only the zero solution**, over any extension `S` of the
constants, given the monomial certificate. -/
theorem hyperexpW_homogeneous (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Gn Gd μ : CPoly R} (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (hcop : IsCoprime (toPoly Gn) (toPoly Gd)) (hcert : hyperexpMonomialCheck Gn Gd μ = true)
    (c : ℤ) (hc : c ≠ 0) (y : K)
    (h : y′ = φ (C (c : S)) * (φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι)) * y) : y = 0 := by
  have hιinj : Function.Injective ι := ι.injective
  simp only [hyperexpMonomialCheck, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hcert
  obtain ⟨hμ, hdisj⟩ := hcert
  obtain ⟨⟨hS0, hcopR⟩, hS0', hSd', hcop', hScop', hS', hsqS⟩ := simplePart_props_map ι Gd hGd0
  obtain ⟨t, ht⟩ := residuePolyW_bezout Gn Gd hS0 hcopR.symm
  obtain ⟨hμ0, q, hq⟩ := muCheck_spec hμ
  have hGnS : (toPoly Gn).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hGn0
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hGd0
  have hrS : (toPoly (simplePart Gd)).map ι ∣
      (toPoly (residuePolyW Gn Gd)).map ι * derivative ((toPoly Gd).map ι) - (toPoly Gn).map ι := by
    refine ⟨-(t.map ι), ?_⟩
    have := congrArg (Polynomial.map ι) ht
    simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map] at this
    rw [← this]; ring
  have hμS : (toPoly (simplePart Gd)).map ι ∣
      ((toPoly μ).map ι).comp ((toPoly (residuePolyW Gn Gd)).map ι) :=
    ⟨q.map ι, by rw [← Polynomial.map_comp, hq, Polynomial.map_mul]⟩
  refine rde_homogeneous_W hD _ _ _ _ _ hGnS hGdS (hcop.map (mapRingHom ι)) hSd' hScop' hrS hμS
    ?_ c hc y h
  rcases hdisj with (hsq | hdeg) | hres
  · -- a repeated factor
    left
    obtain ⟨p, hp1, hp2⟩ := exists_sq_dvd_of_squarefreeCheck hGd0 hsq
    have hpS : (p.map ι) ^ 2 ∣ (toPoly Gd).map ι := by
      rw [← Polynomial.map_pow]; exact Polynomial.map_dvd ι hp2
    have hpS0 : p.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr (fun h0 ↦ by
      rw [h0, natDegree_zero] at hp1; omega)
    obtain ⟨p', hp', hp'p⟩ := WfDvdMonoid.exists_irreducible_factor
      (fun hu ↦ by
        have := natDegree_eq_zero_of_isUnit hu
        rw [natDegree_map] at this; omega) hpS0
    exact ⟨p', hp', (pow_dvd_pow_of_dvd hp'p 2).trans hpS⟩
  · -- a nonzero polynomial part
    right; left
    have htGn : trim Gn ≠ [] := fun h0 ↦ hGn0 ((trim_eq_nil_iff _).mp h0)
    have htGd : trim Gd ≠ [] := fun h0 ↦ hGd0 ((trim_eq_nil_iff _).mp h0)
    obtain ⟨hdGn, -, -⟩ := natDegree_toPoly_of_trim_ne_nil htGn
    obtain ⟨hdGd, -, -⟩ := natDegree_toPoly_of_trim_ne_nil htGd
    rw [natDegree_map, natDegree_map, hdGn, hdGd]
    omega
  · -- a non-rational residue
    right; right
    generalize hP : ratShiftProd (residuePolyW Gn Gd) (HasRatRoots.ratRoots μ) = P at hres
    have hPpoly : toPoly P = ((HasRatRoots.ratRoots μ).map fun (q : ℚ) ↦
        toPoly (residuePolyW Gn Gd) - C ((q : ℚ) : R)).prod := by
      rw [← hP, toPoly_ratShiftProd]
    generalize hSp : simplePart Gd = Sp at hS0 hS0' hSd' hcop' hScop' hS' hsqS hrS hμS hres
    generalize hr : residuePolyW Gn Gd = r at hrS hμS hPpoly
    obtain ⟨Qd, Rm, hdm⟩ : ∃ Qd Rm, divMod P Sp = (Qd, Rm) := ⟨_, _, rfl⟩
    have hspec := divMod_spec P Sp
    have hlt := divMod_degree_lt P Sp hS0
    rw [hdm] at hspec hlt hres
    have hrem : toPoly Rm ≠ 0 := fun h0 ↦ by
      have := (isZero_iff _).mpr h0
      simp [this] at hres
    have hndvd : ¬(toPoly Sp).map ι ∣ (toPoly P).map ι := by
      intro hdvd
      have hremS : (toPoly Sp).map ι ∣ (toPoly Rm).map ι := by
        have : (toPoly Rm).map ι = (toPoly P).map ι - (toPoly Qd).map ι * (toPoly Sp).map ι := by
          rw [← Polynomial.map_mul, ← Polynomial.map_sub]
          exact congrArg (Polynomial.map ι) (by rw [hspec]; ring)
        rw [this]
        exact dvd_sub hdvd (dvd_mul_left _ _)
      have h0 := eq_zero_of_dvd_of_degree_lt hremS (by rw [degree_map, degree_map]; exact hlt)
      exact hrem ((Polynomial.map_eq_zero_iff hιinj).mp h0)
    by_contra hall
    push Not at hall
    refine hndvd (dvd_of_squarefree_of_irreducible_dvd hsqS fun p hp hpS ↦ ?_)
    obtain ⟨q', hq', hpq'⟩ := hall p hp hpS
    rw [hPpoly, Polynomial.map_list_prod, List.map_map]
    have hqR : (toPoly μ).eval ((q' : ℚ) : R) = 0 := by
      rw [← map_ratCast ι, eval_map, eval₂_at_apply] at hq'
      exact hιinj (by rw [hq', map_zero])
    have hmem := HasRatRoots.ratRoots_spec μ q' hμ0 hqR
    refine hpq'.trans (List.dvd_prod ?_)
    refine List.mem_map.mpr ⟨q', hmem, ?_⟩
    simp only [Function.comp_apply, Polynomial.map_sub, map_C, map_ratCast]

end Spec

end CPoly

-- `η = 1 / (x² + 1)` (`exp (arctan x)`): certified monomial
#eval CPoly.hyperexpMonomialCheck ([1] : CPoly ℚ) [1, 0, 1]
  (CPoly.findMu (CPoly.simplePart [1, 0, 1]) (CPoly.residuePolyW [1] [1, 0, 1]))
-- `η = 3 / x` (`t = x³`, algebraic): the certificate fails
#eval CPoly.hyperexpMonomialCheck ([3] : CPoly ℚ) [0, 1]
  (CPoly.findMu (CPoly.simplePart [0, 1]) (CPoly.residuePolyW [3] [0, 1]))
-- `η = 1 / x²` (`exp (-1/x)`): certified
#eval CPoly.hyperexpMonomialCheck ([1] : CPoly ℚ) [0, 0, 1]
  (CPoly.findMu (CPoly.simplePart [0, 0, 1]) (CPoly.residuePolyW [1] [0, 0, 1]))
