import RischTragerBronstein.Computable.CFracIn
import RischTragerBronstein.Computable.IntegrateLog
import RischTragerBronstein.Computable.LimitedPrimPolyComplete

/-!
# The level-one model over extended constants

For `ι : R →+* S` and any model `K₁` of `S(x)` (fraction field of `S[X]`, `d/dx`), the codes
`GFrac R` of `R(x)` with the executable operations `ops₁g R` are modelled in `K₁`
(`Tower.M₁In`), with semantics `ev K₁ ι`. Consequently polynomials in `t₁` over `R(x)` given by
generic codes `GPoly (GFrac R)` are the polynomials `polyOfCodes` of their coefficient fractions.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

variable {R S K₁ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁]
variable [Differential K₁] [DifferentialAlgebra S[X] K₁]

lemma toPoly_ofHom (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (l : List R) :
    GPoly.toPoly (CField.ofHom ι h0) l = (CPoly.toPoly l).map ι := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [GPoly.toPoly_cons, CPoly.toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul, map_C,
      map_X]
    rfl

/-- The model of `R(x)` inside a model `K₁` of `S(x)`. -/
noncomputable def M₁In (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) : CField (GFrac R) K₁ (ops₁g R) :=
  ((CField.ofHom ι h0).monomialIn [1] K₁ fun P ↦ by
    have h1 : GPoly.toPoly (CField.ofHom ι h0) [1] = 1 := by
      rw [toPoly_ofHom]
      simp [CPoly.toPoly]
    rw [h1, hD, implicitDeriv_one_of_trivial h0]).normalizeBy CPoly.normCoeff fun q ↦ by
      change GFrac.semIn (CField.ofHom ι h0) K₁ _ = GFrac.semIn (CField.ofHom ι h0) K₁ q
      simp only [GFrac.semIn, toPoly_ofHom]
      exact CPoly.normCoeff_spec ((algebraMap S[X] K₁).comp (mapRingHom ι))
        ((IsFractionRing.injective S[X] K₁).comp (Polynomial.map_injective ι ι.injective)) q

lemma sem_M₁In (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
    (q : GFrac R) : (M₁In (K₁ := K₁) ι h0 hD).sem q = CPoly.ev K₁ ι q := by
  change GFrac.semIn (CField.ofHom ι h0) K₁ q = _
  rw [GFrac.semIn, toPoly_ofHom, toPoly_ofHom]
  rfl

lemma normFrac_den_ne_zero (q : GFrac R) : CPoly.toPoly (normFrac q).2 ≠ 0 := by
  unfold normFrac
  split_ifs with hz
  · simp
  · exact fun h ↦ hz ((CPoly.isZero_iff _).mpr h)

lemma ev_normFrac (ι : R →+* S) (q : GFrac R) :
    CPoly.ev K₁ ι (normFrac q) = CPoly.ev K₁ ι q := by
  unfold normFrac
  split_ifs with hz
  · have hz' := (CPoly.isZero_iff _).mp hz
    simp [CPoly.ev, hz']
  · rfl

/-- A polynomial in `t₁` given by generic codes is the polynomial of its coefficient fractions. -/
lemma toPoly_M₁In_eq_polyOfCodes (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) (q : GPoly (GFrac R)) (d : ℕ) (hd : q.length ≤ d + 1) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) q =
      CPoly.polyOfCodes (K₁ := K₁) ι (polyA q) (polyD q) d := by
  ext n
  rw [GPoly.coeff_toPoly, CPoly.polyOfCodes, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hn : n < d + 1
  · rw [Finset.sum_eq_single n (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), mul_zero])
      (fun h' ↦ absurd (Finset.mem_range.mpr hn) h'), if_pos rfl, mul_one, polyA, polyD,
      Prod.mk.eta, ev_normFrac]
    by_cases hn' : n < q.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hn'), List.getElem_map,
        List.getD_eq_getElem _ _ hn', sem_M₁In]
    · rw [List.getD_eq_default _ _ (by simpa using hn'), List.getD_eq_default _ _ (by omega)]
      simp [CPoly.ev]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    refine (Finset.sum_eq_zero fun b hb ↦ ?_).symm
    rw [if_neg (by have := Finset.mem_range.mp hb; omega), mul_zero]

end Tower

namespace GPoly

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- A polynomial given by codes is the sum of its coefficient monomials. -/
lemma toPoly_eq_sum_range (p : GPoly α) (dflt : α) :
    toPoly M p = ∑ j ∈ Finset.range p.length, C (M.sem (p.getD j dflt)) * X ^ j := by
  ext m
  rw [coeff_toPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hm : m < p.length
  · rw [Finset.sum_eq_single m (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), mul_zero])
      (fun h' ↦ absurd (Finset.mem_range.mpr hm) h'), if_pos rfl, mul_one,
      List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map,
      List.getD_eq_getElem _ _ hm]
  · rw [List.getD_eq_default _ _ (by simpa using hm)]
    refine (Finset.sum_eq_zero fun b hb ↦ ?_).symm
    rw [if_neg (by have := Finset.mem_range.mp hb; omega), mul_zero]

end GPoly

namespace Tower

variable {R F₀ : Type*} [Field R] [Field F₀] [Algebra R F₀]

/-- The value in `F₀ = R(x₀)(t₁)` of a polynomial in `t₁` given by generic codes. -/
noncomputable def valP (x₀ t₁ : F₀) (p : GPoly (GFrac R)) : F₀ :=
  ∑ j ∈ Finset.range p.length,
    aeval x₀ (CPoly.toPoly (p.getD j ([], [1])).1) /
      aeval x₀ (CPoly.toPoly (p.getD j ([], [1])).2) * t₁ ^ j

/-- The value in `F₀` of a fraction code of `R(x)(t₁)`. -/
noncomputable def valG (x₀ t₁ : F₀) (q : GFrac (GFrac R)) : F₀ :=
  valP x₀ t₁ q.1 / valP x₀ t₁ q.2

end Tower
