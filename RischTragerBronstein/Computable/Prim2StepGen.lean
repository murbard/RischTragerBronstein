import RischTragerBronstein.Computable.LimitedPrimGen

/-!
# The `t₂`-loop over general elements of `R(x)(t₁)`: one level

State: a general element `Q ∈ R(x)(t₁)`, as a fraction code `GFrac (GFrac R)` with the
executable field operations `ops₂p = (ops₁g R).monomial [η₁]`. Level `k` forms
`G = Aₖ - (k + 1) η₂ Q` with these operations and calls `limitedPrimGen`; the solution
`y = gn / gd + ∑ Pⱼ t₁ ^ j` is returned again as a fraction code (`solCode`).

`sem_solCode`, `prim2StepGen_sound`: semantics and soundness in every two-level model.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Operations of `R(x)(t₁)`. -/
def ops₂p (En₁ Ed₁ : CPoly R) : COps (GFrac (GFrac R)) := (ops₁g R).monomial [(En₁, Ed₁)]

/-- The code of `η₂ ∈ R(x)` inside `R(x)(t₁)`. -/
def etaCode (En₂ Ed₂ : CPoly R) : GFrac (GFrac R) := ([(En₂, Ed₂)], [(ops₁g R).one])

/-- `gn / gd + ∑_{j ≤ n} Pⱼ t₁ ^ j` as a fraction code. -/
def solCode (En₁ Ed₁ : CPoly R) (h : GPoly.HermiteResult (GFrac R))
    (P : ℕ → CPoly R × CPoly R) (n : ℕ) : GFrac (GFrac R) :=
  (ops₂p En₁ Ed₁).add (h.gn, h.gd) ((List.range (n + 1)).map P, [(ops₁g R).one])

/-- `Aₖ - (k + 1) η₂ Q`. -/
def gCode (En₁ Ed₁ En₂ Ed₂ : CPoly R) (k : ℕ) (Ak Q : GFrac (GFrac R)) : GFrac (GFrac R) :=
  (ops₂p En₁ Ed₁).add Ak ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).mul
    ((ops₂p En₁ Ed₁).mul ((ops₂p En₁ Ed₁).natCast (k + 1)) (etaCode En₂ Ed₂)) Q))

/-- Replace a fraction code with zero denominator (value `0`) by `0 / 1`. -/
def normF₂ (q : GFrac (GFrac R)) : GFrac (GFrac R) :=
  if GPoly.isZero (ops₁g R) q.2 then ([], [(ops₁g R).one]) else q

/-- One level of the general `t₂`-loop. -/
def prim2StepGen (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R) (En₂ Ed₂ : CPoly R)
    (Iη₂ : CPoly.RationalIntegral R) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    Option (R × GFrac (GFrac R)) :=
  let G := normF₂ (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q)
  (limitedPrimGen En₁ Ed₁ Iη₁ Iη₂ G.1 G.2).map fun r ↦
    (r.1, solCode En₁ Ed₁ r.2.1 r.2.2 ((GPoly.divMod (ops₁g R) r.2.1.b r.2.1.s).1.length + 1))

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The model of `R(x)(t₁)` inside `K₂`, over extended constants. -/
noncomputable def M₂In (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂) :
    CField (GFrac (GFrac R)) K₂ (ops₂p En₁ Ed₁) :=
  (M₁In (K₁ := K₁) ι h0 M.hD).monomialIn [(En₁, Ed₁)] K₂ fun P ↦ by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, sem_M₁In]
    exact M.hD₂ P

lemma sem_M₂In (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂) (q : GFrac (GFrac R)) :
    (M₂In ι h0 M).sem q = φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) q.1) /
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) q.2) := rfl

/-- A list of coefficient fractions as a polynomial in `t₁`. -/
lemma toPoly_map_range (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) (P : ℕ → CPoly R × CPoly R) (n : ℕ) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) ((List.range (n + 1)).map P) =
      ∑ j ∈ Finset.range (n + 1), C (CPoly.ev K₁ ι (P j)) * X ^ j := by
  ext m
  rw [GPoly.coeff_toPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hm : m < n + 1
  · rw [Finset.sum_eq_single m (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), mul_zero])
      (fun h' ↦ absurd (Finset.mem_range.mpr hm) h'), if_pos rfl, mul_one,
      List.getD_eq_getElem _ _ (by simpa using hm)]
    simp [sem_M₁In]
  · rw [List.getD_eq_default _ _ (by simpa using hm)]
    refine (Finset.sum_eq_zero fun b hb ↦ ?_).symm
    rw [if_neg (by have := Finset.mem_range.mp hb; omega), mul_zero]

/-- **Semantics of the solution code.** -/
theorem sem_solCode (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂)
    (h : GPoly.HermiteResult (GFrac R)) (P : ℕ → CPoly R × CPoly R) (n : ℕ) :
    (M₂In ι h0 M).sem (solCode En₁ Ed₁ h P n) =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) h.gn) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) h.gd) +
        CPoly.ev₂ (K₁ := K₁) ι (φ₂ X) P n := by
  rw [solCode, (M₂In ι h0 M).sem_add, sem_M₂In, sem_M₂In, toPoly_map_range]
  simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1,
    map_one, div_one, CPoly.ev₂, map_sum, map_mul, map_pow]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, Polynomial.algebraMap_eq]

lemma sem_etaCode (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂) :
    (M₂In ι h0 M).sem (etaCode En₂ Ed₂) = algebraMap K₁ K₂ (CPoly.ev K₁ ι (En₂, Ed₂)) := by
  have h1 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) [(ops₁g R).one] = 1 := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1]
  rw [sem_M₂In, etaCode, h1, map_one, div_one, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero,
    add_zero, sem_M₁In, IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, Polynomial.algebraMap_eq]

lemma sem_gCode (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂) (k : ℕ)
    (Ak Q : GFrac (GFrac R)) :
    (M₂In ι h0 M).sem (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q) = (M₂In ι h0 M).sem Ak -
      ((k + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (CPoly.ev K₁ ι (En₂, Ed₂)) *
        (M₂In ι h0 M).sem Q := by
  rw [gCode, CField.sem_add, CField.sem_neg, CField.sem_mul, CField.sem_mul,
    CField.sem_natCast, sem_etaCode]
  ring

lemma normF₂_spec (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂) (q : GFrac (GFrac R)) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) (normF₂ q).2 ≠ 0 ∧
      (M₂In ι h0 M).sem (normF₂ q) = (M₂In ι h0 M).sem q := by
  unfold normF₂
  split_ifs with hz
  · have hz' := (GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 M.hD) _).mp hz
    refine ⟨by simp [CField.sem_one], ?_⟩
    rw [sem_M₂In, sem_M₂In, hz']
    simp
  · exact ⟨fun h ↦ hz ((GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 M.hD) _).mpr h), rfl⟩

/-- **Soundness of one level of the general `t₂`-loop.** -/
theorem prim2StepGen_sound (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂)
    {Iη₁ Iη₂ : CPoly.RationalIntegral R} (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : CPoly.rationalCheck En₂ Ed₂ Iη₂ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (k : ℕ) (Ak Q : GFrac (GFrac R)) {c : R} {Q' : GFrac (GFrac R)}
    (h : prim2StepGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ k Ak Q = some (c, Q')) :
    ((M₂In ι h0 M).sem Q')′ = (M₂In ι h0 M).sem Ak -
      ((k + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (CPoly.ev K₁ ι (En₂, Ed₂)) * (M₂In ι h0 M).sem Q -
      algebraMap K₁ K₂ (φ (C (ι c)) * CPoly.ev K₁ ι (En₂, Ed₂)) := by
  simp only [prim2StepGen, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨c₀, hr, P⟩, hsome, rfl, rfl⟩ := h
  obtain ⟨hden, hsem⟩ := normF₂_spec (K₁ := K₁) (K₂ := K₂) ι h0 M (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q)
  have := limitedPrimGen_sound (K₁ := K₁) (K₂ := K₂) ι h0 M hcη₁ hcη₂ hEd₁ _ _ hden hsome
  rw [sem_solCode ι h0 M, this, ← sem_M₂In ι h0 M, hsem, sem_gCode]

/-- **Completeness of one level of the general `t₂`-loop.** -/
theorem prim2StepGen_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂)
    {Iη₁ Iη₂ : CPoly.RationalIntegral R} (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : CPoly.rationalCheck En₂ Ed₂ Iη₂ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hη0 : CPoly.isZero Iη₁.r = false) (k : ℕ) (Ak Q : GFrac (GFrac R)) (Pk : K₂) (b : S)
    (hP : Pk′ + ((k + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (CPoly.ev K₁ ι (En₂, Ed₂)) *
      ((M₂In ι h0 M).sem Q + algebraMap K₁ K₂ (φ (C b))) = (M₂In ι h0 M).sem Ak) :
    ∃ c Q', prim2StepGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ k Ak Q = some (c, Q') ∧
      ∃ b' : S, Pk = (M₂In ι h0 M).sem Q' + algebraMap K₁ K₂ (φ (C b')) := by
  obtain ⟨hden, hsem⟩ := normF₂_spec (K₁ := K₁) (K₂ := K₂) ι h0 M (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q)
  set G := normF₂ (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q) with hG
  have hcast : φ (C (((k + 1 : ℕ) : S) * b)) = ((k + 1 : ℕ) : K₁) * φ (C b) := by
    rw [C_mul, map_mul, map_natCast (C : S →+* S[X]), map_natCast]
  have hz : Pk′ = φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) G.1) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) G.2) -
      φ₂ (C (φ (C (((k + 1 : ℕ) : S) * b)) * CPoly.ev K₁ ι (En₂, Ed₂))) := by
    rw [← sem_M₂In ι h0 M, hsem, sem_gCode, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, hcast, map_mul, map_mul, map_natCast]
    linear_combination hP
  obtain ⟨c', hr, P, hsome, hc'⟩ := limitedPrimGen_complete (K₁ := K₁) (K₂ := K₂) ι h0 M hcη₁ hcη₂
    hEd₁ hη0 G.1 G.2 hden Pk _ hz
  have hstep : prim2StepGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ k Ak Q = some (c',
      solCode En₁ Ed₁ hr P ((GPoly.divMod (ops₁g R) hr.b hr.s).1.length + 1)) := by
    simp only [prim2StepGen, ← hG, hsome, Option.map_some]
  refine ⟨c', _, hstep, ?_⟩
  have hsound := prim2StepGen_sound (K₁ := K₁) (K₂ := K₂) ι h0 M hcη₁ hcη₂ hEd₁ k Ak Q hstep
  have hconst : (Pk - (M₂In ι h0 M).sem (solCode En₁ Ed₁ hr P
      ((GPoly.divMod (ops₁g R) hr.b hr.s).1.length + 1)))′ = 0 := by
    rw [map_sub, hsound, hc', hcast, map_mul, map_mul, map_natCast]
    linear_combination hP
  obtain ⟨b', hb'⟩ := M.hK₂const _ hconst
  exact ⟨b', by rw [← hb']; ring⟩

end Tower
