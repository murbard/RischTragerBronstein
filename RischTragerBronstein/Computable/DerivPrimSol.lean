import RischTragerBronstein.Computable.DerivPrim

/-!
# In-field integration in `R(x)(t₁)`: the antiderivative

`CPoly.derivPolySol` turns the output of `derivPolyCodes` into coefficient codes `P` with
`(∑ Pⱼ t₁ ^ j)′ = ∑ (Aⱼ / Dⱼ) t₁ ^ j`; `Tower.derivPrimSol` adds the Hermite part:
if it returns `(h, P)` then `(h.gn / h.gd + ∑ Pⱼ t₁ ^ j)′ = A / D`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Coefficient codes of an antiderivative of `∑_{j ≤ d} (Aⱼ / Dⱼ) t₁ ^ j`. -/
def derivPolySol (En Ed : CPoly R) (Iη : RationalIntegral R) (A D : ℕ → CPoly R) (d : ℕ) :
    Option (ℕ → CPoly R × CPoly R) :=
  (derivPolyCodes En Ed Iη A D d).map fun r ↦ fun j ↦
    if j = 0 then r.2.2 else coeffFn (d + 1) ([], [1]) r.1 r.2.1 j

lemma derivPolySol_isSome (En Ed : CPoly R) (Iη : RationalIntegral R) (A D : ℕ → CPoly R)
    (d : ℕ) : (derivPolySol En Ed Iη A D d).isSome = (derivPolyCodes En Ed Iη A D d).isSome := by
  simp [derivPolySol]

end Defs

section Level1

variable {R S K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

/-- **The codes solve all coefficient equations.** -/
theorem derivPolySol_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (A D : ℕ → CPoly R) (d : ℕ) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0)
    {P : ℕ → CPoly R × CPoly R} (h : derivPolySol En Ed Iη A D d = some P) :
    (∀ j ≤ d + 1, toPoly (P j).2 ≠ 0) ∧
      (∀ j, 1 ≤ j → j ≤ d → (ev K ι (P j))′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) *
        ev K ι (P (j + 1)) = ev K ι (A j, D j)) ∧
      (ev K ι (P 0))′ + ev K ι (En, Ed) * ev K ι (P 1) = ev K ι (A 0, D 0) ∧
      (ev K ι (P (d + 1)))′ = 0 := by
  simp only [derivPolySol, derivPolyCodes, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨⟨L, c, Q₀⟩, ⟨L', hL, hstep⟩, rfl⟩ := h
  obtain ⟨⟨c', Q₀'⟩, hstep, hpair⟩ := hstep
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, rfl, rfl⟩ := hpair
  have hlast := primLastQ_den_ne_zero K ι hD hcη hEd A D d _ L'
    (fun j _ hj ↦ hD0 j hj) (by simp) hL
  obtain ⟨hden, ⟨γ, hγ⟩, hpe, hp1⟩ := primLoop_codes (K := K) ι hD hcη hEd A D d
    (fun j _ hj ↦ hD0 j hj) ([], [1]) (by simp) hL c'
  obtain ⟨hQ₀, hsol⟩ := primStep_sound (K := K) ι hD hcη hEd (hD0 0 (Nat.zero_le d)) hlast hstep
  refine ⟨fun j hj ↦ ?_, fun j h1 h2 ↦ ?_, ?_, ?_⟩
  · by_cases hj0 : j = 0
    · simpa [hj0] using hQ₀
    · simpa [hj0] using hden j (by omega) hj
  · have := hpe j h1 h2
    simpa [show j ≠ 0 by omega] using this
  · simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false]
    rw [hsol, hp1]
    simp only [zero_add, Nat.cast_one, one_mul]
    ring
  · simp only [show d + 1 ≠ 0 by omega, if_false]
    rw [hγ, map_add, deriv_algebraMap, hD, derivative_C, map_zero, add_zero]
    simp [ev]

end Level1

section Level2

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁]
variable [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Field K₂] [Differential K₂] [Algebra K₁ K₂] [DifferentialAlgebra K₁ K₂]

theorem derivPolySol_sound_poly (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (t₁ : K₂) (ht₁ : t₁′ = algebraMap K₁ K₂ (ev K₁ ι (En, Ed)))
    (A D : ℕ → CPoly R) (d : ℕ) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0)
    {P : ℕ → CPoly R × CPoly R} (h : derivPolySol En Ed Iη A D d = some P) :
    (ev₂ (K₁ := K₁) ι t₁ P (d + 1))′ = ev₂ (K₁ := K₁) ι t₁ (fun j ↦ (A j, D j)) d := by
  obtain ⟨-, hpe, hp0, hpd⟩ := derivPolySol_sound (K := K₁) ι hD hcη hEd A D d hD0 h
  set η₁ : K₂ := algebraMap K₁ K₂ (ev K₁ ι (En, Ed)) with hη₁
  let q : ℕ → K₂ := fun j ↦ algebraMap K₁ K₂ (ev K₁ ι (P j))
  have hqe : ∀ j, 1 ≤ j → j ≤ d → (q j)′ + ((j + 1 : ℕ) : K₂) * η₁ * q (j + 1) =
      algebraMap K₁ K₂ (ev K₁ ι (A j, D j)) := fun j h1 h2 ↦ by
    have := congrArg (algebraMap K₁ K₂) (hpe j h1 h2)
    simp only [map_add, map_mul, map_natCast] at this
    rw [← this, deriv_algebraMap]
  have hq0 : (q 0)′ + η₁ * q 1 = algebraMap K₁ K₂ (ev K₁ ι (A 0, D 0)) := by
    have := congrArg (algebraMap K₁ K₂) hp0
    simp only [map_add, map_mul] at this
    rw [← this, deriv_algebraMap]
  have hqd : (q (d + 1))′ = 0 := by
    change (algebraMap K₁ K₂ _)′ = 0
    rw [deriv_algebraMap, hpd, map_zero]
  change (∑ j ∈ Finset.range (d + 1 + 1), q j * t₁ ^ j)′ = _
  rw [deriv_sum_mul_pow t₁ η₁ ht₁ q (d + 1), hqd, zero_mul, add_zero, ev₂,
    Finset.sum_range_succ' _ d, Finset.sum_range_succ' (fun j ↦
      algebraMap K₁ K₂ (ev K₁ ι (A j, D j)) * t₁ ^ j) d]
  have h1 : ∑ j ∈ Finset.range d, ((q (j + 1))′ + ((j + 1 + 1 : ℕ) : K₂) * η₁ * q (j + 1 + 1)) *
      t₁ ^ (j + 1) = ∑ j ∈ Finset.range d,
      algebraMap K₁ K₂ (ev K₁ ι (A (j + 1), D (j + 1))) * t₁ ^ (j + 1) :=
    Finset.sum_congr rfl fun j hj ↦ by
      rw [hqe (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)]
  rw [h1]
  simp only [pow_zero, mul_one, Nat.cast_one, zero_add, one_mul]
  rw [hq0]

end Level2

end CPoly

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- An antiderivative of `A / D` in `R(x)(t₁)`, if there is one: Hermite data and the coefficient
codes of the polynomial part, `y = h.gn / h.gd + ∑ Pⱼ t₁ ^ j`. -/
def derivPrimSol (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R) (A D : GPoly (GFrac R)) :
    Option (GPoly.HermiteResult (GFrac R) × (ℕ → CPoly R × CPoly R)) :=
  let h := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] A D
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  if GPoly.isZero (ops₁g R) qr.2 then
    (CPoly.derivPolySol En₁ Ed₁ Iη₁ (polyA qr.1) (polyD qr.1) qr.1.length).map fun P ↦ (h, P)
  else none

lemma derivPrimSol_isSome (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R)
    (A D : GPoly (GFrac R)) :
    (derivPrimSol En₁ Ed₁ Iη₁ A D).isSome = isDerivPrim En₁ Ed₁ Iη₁ A D := by
  simp only [derivPrimSol, isDerivPrim]
  split_ifs with hz
  · simp [hz, CPoly.derivPolySol_isSome]
  · simp [hz]

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

set_option maxHeartbeats 800000 in
/-- **Soundness**: the returned data is an antiderivative, in every model. -/
theorem derivPrimSol_sound (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P)
    {En₁ Ed₁ : CPoly R} {Iη₁ : CPoly.RationalIntegral R}
    (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e)
    (A D : GPoly (GFrac R)) (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D ≠ 0)
    {hr : GPoly.HermiteResult (GFrac R)} {P : ℕ → CPoly R × CPoly R}
    (hsome : derivPrimSol En₁ Ed₁ Iη₁ A D = some (hr, P)) :
    (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) hr.gn) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) hr.gd) +
        CPoly.ev₂ (K₁ := K₁) ι (φ₂ X) P
          ((GPoly.divMod (ops₁g R) hr.b hr.s).1.length + 1))′ =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D) := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hW : GPoly.toPoly M₁ [(En₁, Ed₁)] = C (CPoly.ev K₁ ι (En₁, Ed₁)) := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, sem_M₁In]
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) P := fun P ↦ by
    rw [hW]; exact hD₂ P
  have hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive (CPoly.ev K₁ ι (En₁, Ed₁)) hD₂ hconst₂ hp
  have hchk := GPoly.hermiteCheck_hermite M₁ [(En₁, Ed₁)] A D
    (fun p hp _ hdvd ↦ hnorm p hp (by rw [hDW]; exact hdvd)) hD0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ [(En₁, Ed₁)] A D _ hDW hchk
  simp only [derivPrimSol] at hsome
  split_ifs at hsome with hz
  rw [Option.map_eq_some_iff] at hsome
  obtain ⟨P₀, hP, hpair⟩ := hsome
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, rfl⟩ := hpair
  set h := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] A D with hh
  have hs0 : GPoly.toPoly M₁ h.s ≠ 0 := hsq.ne_zero
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  set q := (GPoly.divMod (ops₁g R) h.b h.s).1 with hq
  have hrem0 : GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) h.b h.s).2 = 0 :=
    (GPoly.isZero_iff M₁ _).mp hz
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφs : φ₂ (GPoly.toPoly M₁ h.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hs0
  have ht₁ : (φ₂ X)′ = algebraMap K₁ K₂ (CPoly.ev K₁ ι (En₁, Ed₁)) := by
    rw [deriv_algebraMap, hD₂, implicitDeriv_X, IsScalarTower.algebraMap_apply K₁ K₁[X] K₂,
      Polynomial.algebraMap_eq]
  have hP' := CPoly.derivPolySol_sound_poly (K₁ := K₁) (K₂ := K₂) ι hD hcη₁ hEd₁
    (φ₂ X) ht₁ (polyA q) (polyD q) q.length (fun j _ ↦ normFrac_den_ne_zero _) hP
  have hqpoly := toPoly_M₁In_eq_polyOfCodes (K₁ := K₁) ι h0 hD q q.length (Nat.le_succ _)
  rw [map_add, hP', ← CPoly.map_polyOfCodes, ← hqpoly, hid, hdm, hrem0, add_zero,
    map_mul φ₂, mul_div_assoc, div_self hφs, mul_one]

end Tower
