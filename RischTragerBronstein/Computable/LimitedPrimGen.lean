import RischTragerBronstein.Computable.ModelIn
import RischTragerBronstein.Computable.Prim2LoopComplete
import RischTragerBronstein.Computable.GHermiteIn
import RischTragerBronstein.Liouville.HermitePrimitive

/-!
# Limited integration inside `R(x)(t₁)` for general elements

Problem: given `f = A / D ∈ R(x)(t₁)` (generic codes) and `η₂ ∈ R(x)`, find a constant `c` and
`y ∈ R(x)(t₁)` with `y′ = f - c η₂`.

`limitedPrimGen`: Hermite reduction in `t₁` (always certified in a primitive extension), Euclidean
division; the proper part must vanish (`deriv_eq_poly_add_proper`), and the polynomial part is
handled by `limitedPrimCodes`. `limitedPrimGen_complete`: if a solution exists over **any**
extension of the constants, the procedure succeeds and returns that constant.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Returns `(c, Hermite data, coefficient codes of the polynomial part)`:
`y = gn / gd + ∑ Pⱼ t₁ ^ j`. -/
def limitedPrimGen (En₁ Ed₁ : CPoly R) (Iη₁ Iη₂ : CPoly.RationalIntegral R)
    (A D : GPoly (GFrac R)) :
    Option (R × GPoly.HermiteResult (GFrac R) × (ℕ → CPoly R × CPoly R)) :=
  let h := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] A D
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  if GPoly.isZero (ops₁g R) qr.2 then
    (CPoly.limitedPrimCodes En₁ Ed₁ Iη₁ Iη₂ (polyA qr.1) (polyD qr.1) qr.1.length).map
      fun cP ↦ (cP.1, h, cP.2)
  else none

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
theorem limitedPrimGen_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂)
    {Iη₁ Iη₂ : CPoly.RationalIntegral R} (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : CPoly.rationalCheck En₂ Ed₂ Iη₂ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hη0 : CPoly.isZero Iη₁.r = false) (A D : GPoly (GFrac R))
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) D ≠ 0) (z : K₂) (c : S)
    (hz : z′ = φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) A) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) D) -
      φ₂ (C (φ (C c) * CPoly.ev K₁ ι (En₂, Ed₂)))) :
    ∃ c' hr P, limitedPrimGen En₁ Ed₁ Iη₁ Iη₂ A D = some (c', hr, P) ∧ ι c' = c := by
  set M₁ := M₁In (K₁ := K₁) ι h0 M.hD with hM₁
  have hW : GPoly.toPoly M₁ [(En₁, Ed₁)] = C (CPoly.ev K₁ ι (En₁, Ed₁)) := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, sem_M₁In]
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) P := fun P ↦ by
    rw [hW]; exact M.hD₂ P
  have hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive (CPoly.ev K₁ ι (En₁, Ed₁)) M.hD₂ M.hconst₂ hp
  -- Hermite reduction, always certified
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
  -- the proper part must vanish
  have hz₁ : (z - φ₂ (GPoly.toPoly M₁ h.gn) / φ₂ (GPoly.toPoly M₁ h.gd))′ =
      φ₂ (GPoly.toPoly M₁ q - C (φ (C c) * CPoly.ev K₁ ι (En₂, Ed₂))) +
        φ₂ (GPoly.toPoly M₁ rem) / φ₂ (GPoly.toPoly M₁ h.s) := by
    rw [map_sub, hz, hid, hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφs, mul_one,
      map_sub]
    ring
  obtain ⟨hrem0, -, -, -⟩ := deriv_eq_poly_add_proper (K := K₂) hnorm _ _ _ hsq hdeglt _ hz₁
  have hremZ : GPoly.isZero (ops₁g R) rem = true := (GPoly.isZero_iff M₁ rem).mpr hrem0
  -- the polynomial part
  have hqpoly := toPoly_M₁In_eq_polyOfCodes (K₁ := K₁) ι h0 M.hD q q.length (Nat.le_succ _)
  rw [hrem0, map_zero, zero_div, add_zero, hqpoly] at hz₁
  obtain ⟨c', P, hcP, hc', -⟩ := CPoly.limitedPrimCodes_complete_poly (K₁ := K₁) (K₂ := K₂) ι M.hD
    M.hKconst hcη₁ hcη₂ hEd₁ hη0 M.hD₂ M.hconst₂ M.hη₂nd (polyA q) (polyD q) q.length
    (fun j _ ↦ normFrac_den_ne_zero _) _ c hz₁
  refine ⟨c', h, P, ?_, hc'⟩
  simp only [limitedPrimGen, ← hh, ← hq, ← hrem, hremZ, if_true, hcP, Option.map_some]

set_option maxHeartbeats 800000 in
/-- **Soundness.** A returned `(c, h, P)` gives the antiderivative
`y = h.gn / h.gd + ∑ Pⱼ t₁ ^ j` of `A / D - c η₂`, in every two-level model. -/
theorem limitedPrimGen_sound (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂)
    {Iη₁ Iη₂ : CPoly.RationalIntegral R} (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : CPoly.rationalCheck En₂ Ed₂ Iη₂ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (A D : GPoly (GFrac R))
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) D ≠ 0) {c : R}
    {hr : GPoly.HermiteResult (GFrac R)} {P : ℕ → CPoly R × CPoly R}
    (hsome : limitedPrimGen En₁ Ed₁ Iη₁ Iη₂ A D = some (c, hr, P)) :
    (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) hr.gn) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) hr.gd) +
        CPoly.ev₂ (K₁ := K₁) ι (φ₂ X) P
          ((GPoly.divMod (ops₁g R) hr.b hr.s).1.length + 1))′ =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) A) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) D) -
        algebraMap K₁ K₂ (φ (C (ι c)) * CPoly.ev K₁ ι (En₂, Ed₂)) := by
  set M₁ := M₁In (K₁ := K₁) ι h0 M.hD with hM₁
  have hW : GPoly.toPoly M₁ [(En₁, Ed₁)] = C (CPoly.ev K₁ ι (En₁, Ed₁)) := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, sem_M₁In]
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) P := fun P ↦ by
    rw [hW]; exact M.hD₂ P
  have hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive (CPoly.ev K₁ ι (En₁, Ed₁)) M.hD₂ M.hconst₂ hp
  have hchk := GPoly.hermiteCheck_hermite M₁ [(En₁, Ed₁)] A D
    (fun p hp _ hdvd ↦ hnorm p hp (by rw [hDW]; exact hdvd)) hD0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ [(En₁, Ed₁)] A D _ hDW hchk
  -- unpack the result
  simp only [limitedPrimGen] at hsome
  split_ifs at hsome with hz
  rw [Option.map_eq_some_iff] at hsome
  obtain ⟨⟨c₀, P₀⟩, hcP, hpair⟩ := hsome
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, rfl, rfl⟩ := hpair
  set h := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] A D with hh
  have hs0 : GPoly.toPoly M₁ h.s ≠ 0 := hsq.ne_zero
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  set q := (GPoly.divMod (ops₁g R) h.b h.s).1 with hq
  have hrem0 : GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) h.b h.s).2 = 0 :=
    (GPoly.isZero_iff M₁ _).mp hz
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφs : φ₂ (GPoly.toPoly M₁ h.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hs0
  have ht₁ : (φ₂ X)′ = algebraMap K₁ K₂ (CPoly.ev K₁ ι (En₁, Ed₁)) := by
    rw [deriv_algebraMap, M.hD₂, implicitDeriv_X, IsScalarTower.algebraMap_apply K₁ K₁[X] K₂,
      Polynomial.algebraMap_eq]
  obtain ⟨-, hP'⟩ := CPoly.limitedPrimCodes_sound_poly (K₁ := K₁) (K₂ := K₂) ι M.hD hcη₁ hcη₂ hEd₁
    (φ₂ X) ht₁ (polyA q) (polyD q) q.length (fun j _ ↦ normFrac_den_ne_zero _) hcP
  have hqpoly := toPoly_M₁In_eq_polyOfCodes (K₁ := K₁) ι h0 M.hD q q.length (Nat.le_succ _)
  rw [map_add, hP', ← CPoly.map_polyOfCodes, ← hqpoly, hid, hdm, hrem0, add_zero,
    map_mul φ₂, mul_div_assoc, div_self hφs, mul_one]
  ring

end Tower
