import RischTragerBronstein.Computable.LimitedPrimGen

/-!
# Is `f ∈ R(x)(t₁)` a derivative?  (in-field integration in a primitive extension)

`Tower.isDerivPrim En₁ Ed₁ Iη₁ A D` decides whether `A / D ∈ R(x)(t₁)` (`t₁′ = η₁ ∈ R(x)`) is the
derivative of an element of `S(x)(t₁)`, for **every** extension `S ⊇ R` of the constants:
Hermite reduction, the proper part must vanish, and the coefficient equations of the polynomial part
are solved from the top by `primLoop`, with one more `primStep` at level `0`.

This is the certificate needed to put a further primitive `t₂′ = η₂ ∈ R(x)(t₁)` on top of the tower
(`log log x`, `li x = ∫ dx / log x`, …): `t₂` is transcendental with no new constants iff `η₂` is not
a derivative.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Solve all coefficient equations `pⱼ′ + (j + 1) η pⱼ₊₁ = Aⱼ / Dⱼ`, `0 ≤ j ≤ d`. -/
def derivPolyCodes (En Ed : CPoly R) (Iη : RationalIntegral R) (A D : ℕ → CPoly R) (d : ℕ) :
    Option (List (R × (CPoly R × CPoly R)) × R × (CPoly R × CPoly R)) :=
  (primLoop En Ed Iη A D d ([], [1])).bind fun L ↦
    (primStep En Ed Iη 0 (A 0) (D 0) (primLastQ ([], [1]) L)).map fun cQ ↦ (L, cQ)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁]
variable [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- **Completeness for polynomials in `t₁`**: a derivative is always recognised. -/
theorem derivPolyCodes_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K₁, y′ = 0 → ∃ b : S, y = φ (C b))
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (hη0 : isZero Iη.r = false)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ev K₁ ι (En, Ed))) P)
    (hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e)
    (A D : ℕ → CPoly R) (d : ℕ) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) (z : K₂)
    (hz : z′ = φ₂ (polyOfCodes (K₁ := K₁) ι A D d)) :
    (derivPolyCodes En Ed Iη A D d).isSome = true := by
  obtain ⟨-, p, hpe, hpd⟩ := coeffs_of_deriv_in_primitive (K := K₂) (ev K₁ ι (En, Ed)) hD₂ hconst₂
    (polyOfCodes (K₁ := K₁) ι A D d) 0 1 squarefree_one (by simp) z
    (by rw [hz, map_zero, zero_div, add_zero])
  have hcoeffA : ∀ i, i ≤ d → (polyOfCodes (K₁ := K₁) ι A D d).coeff i =
      ev K₁ ι (A i, D i) := fun i hi ↦ by
    simp only [polyOfCodes, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_range.mpr (by omega)) h'
  have hdegA : (polyOfCodes (K₁ := K₁) ι A D d).natDegree ≤ d := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp hi; omega)
  obtain ⟨b₀, hb₀⟩ := hKconst _ (hpd d hdegA).1
  obtain ⟨L, hL, hlast, b, hb⟩ := primLoop_complete_last (K := K₁) ι hD hKconst hcη hEd hη0 A D p d
    (fun j _ hj ↦ hD0 j hj) (fun j _ hj ↦ by rw [hpe j, hcoeffA j hj]) ([], [1]) (by simp) b₀
    (by rw [hb₀]; simp [ev])
  obtain ⟨c, Q', hstep, -⟩ := primStep_complete (K := K₁) ι hD hKconst hcη hEd hη0 (k := 0)
    (hD0 0 (Nat.zero_le d)) hlast (p 0) b (by
      rw [← hb, hpe 0, hcoeffA 0 (Nat.zero_le d)])
  simp [derivPolyCodes, hL, hstep]

end CPoly

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Is `A / D ∈ R(x)(t₁)` a derivative in `R(x)(t₁)`? -/
def isDerivPrim (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R) (A D : GPoly (GFrac R)) :
    Bool :=
  let h := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] A D
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  GPoly.isZero (ops₁g R) qr.2 &&
    (CPoly.derivPolyCodes En₁ Ed₁ Iη₁ (polyA qr.1) (polyD qr.1) qr.1.length).isSome

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

set_option maxHeartbeats 800000 in
/-- **Completeness**: if `A / D` is a derivative in `S(x)(t₁)` for some extension `S` of the
constants, `isDerivPrim` answers `true`. Hence `isDerivPrim = false` certifies that a new
primitive with this derivative is a transcendental monomial over every constant extension. -/
theorem isDerivPrim_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K₁, y′ = 0 → ∃ b : S, y = φ (C b))
    {En₁ Ed₁ : CPoly R} {Iη₁ : CPoly.RationalIntegral R}
    (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hη0 : CPoly.isZero Iη₁.r = false)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e)
    (A D : GPoly (GFrac R)) (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D ≠ 0) (z : K₂)
    (hz : z′ = φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D)) :
    isDerivPrim En₁ Ed₁ Iη₁ A D = true := by
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
  set h := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] A D with hh
  have hs0 : GPoly.toPoly M₁ h.s ≠ 0 := hsq.ne_zero
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₁ h.b h.s hs0
  set q := (GPoly.divMod (ops₁g R) h.b h.s).1 with hq
  set rem := (GPoly.divMod (ops₁g R) h.b h.s).2 with hrem
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφs : φ₂ (GPoly.toPoly M₁ h.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hs0
  have hz₁ : (z - φ₂ (GPoly.toPoly M₁ h.gn) / φ₂ (GPoly.toPoly M₁ h.gd))′ =
      φ₂ (GPoly.toPoly M₁ q) + φ₂ (GPoly.toPoly M₁ rem) / φ₂ (GPoly.toPoly M₁ h.s) := by
    rw [map_sub, hz, hid, hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφs, mul_one]
    ring
  obtain ⟨hrem0, -, -, -⟩ := deriv_eq_poly_add_proper (K := K₂) hnorm _ _ _ hsq hdeglt _ hz₁
  have hremZ : GPoly.isZero (ops₁g R) rem = true := (GPoly.isZero_iff M₁ rem).mpr hrem0
  have hqpoly := toPoly_M₁In_eq_polyOfCodes (K₁ := K₁) ι h0 hD q q.length (Nat.le_succ _)
  rw [hrem0, map_zero, zero_div, add_zero, hqpoly] at hz₁
  have hpoly := CPoly.derivPolyCodes_complete (K₁ := K₁) (K₂ := K₂) ι hD hKconst hcη₁ hEd₁ hη0 hD₂
    hconst₂ (polyA q) (polyD q) q.length (fun j _ ↦ normFrac_den_ne_zero _) _ hz₁
  simp only [isDerivPrim, ← hh, ← hq, ← hrem, hremZ, hpoly, Bool.and_self]

end Tower
