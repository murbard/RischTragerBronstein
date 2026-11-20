import RischTragerBronstein.Computable.RDERational
import RischTragerBronstein.Computable.LimitedPrimWComplete
import RischTragerBronstein.RDE.PrimitiveDenominator
import RischTragerBronstein.Computable.RDERationalW
import RischTragerBronstein.Computable.RDEPrim

/-!
# The Risch differential equation `y′ + g y = A / D` over `R(x)(t₁)`, `g ∈ R(x)` arbitrary

The same top-degree recursion as `rdePrim`, with the coefficient `g = gq ∈ R(x)` a rational
function (`g = n η` for a hyperexponential `t₂′ = η t₂`) and the weakly normalised solver
`rdeRationalW` (with the annihilator `μ` of the residues of `g`) for the coefficient equations.

* `rdePrimW_sound`: `y = Y / D` solves the equation, in every model.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- `y_d = L · z` from `z′ + g z = top / L²`. -/
def rdeTopCoeffW (gq : GFrac R) (μ : CPoly R) (L top : GFrac R) : Option (GFrac R) :=
  (CPoly.rdeRationalW μ gq.1 gq.2 (CPoly.mul (CPoly.mul top.1 L.2) L.2)
    (CPoly.mul (CPoly.mul top.2 L.1) L.1)).map fun z ↦ (ops₁g R).mul L z

/-- The top-degree recursion for `D Y′ + P₀ Y = Ap`. -/
def rdePolyPrimAuxW (En₁ Ed₁ : CPoly R) (gq : GFrac R) (μ : CPoly R) (D P₀ : GPoly (GFrac R)) :
    ℕ → GPoly (GFrac R) → GPoly (GFrac R) → Option (GPoly (GFrac R))
  | 0, Ap, acc => if GPoly.isZero (ops₁g R) Ap then some acc else none
  | fuel + 1, Ap, acc =>
    if GPoly.isZero (ops₁g R) Ap then some acc
    else
      let dA := (GPoly.trim (ops₁g R) Ap).length - 1
      let d₁ := (GPoly.trim (ops₁g R) D).length - 1
      if dA < d₁ then none
      else
        match rdeTopCoeffW gq μ (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D))
            (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) with
        | none => none
        | some yd =>
          let Yd := GPoly.monomial (ops₁g R) (dA - d₁) yd
          rdePolyPrimAuxW En₁ Ed₁ gq μ D P₀ fuel
            (GPoly.sub (ops₁g R) Ap (GPoly.add (ops₁g R)
              (GPoly.mul (ops₁g R) D (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] Yd))
              (GPoly.mul (ops₁g R) P₀ Yd)))
            (GPoly.add (ops₁g R) acc Yd)

/-- `P₀ = g D - D′`. -/
def rdeP₀W (En₁ Ed₁ : CPoly R) (gq : GFrac R) (D : GPoly (GFrac R)) : GPoly (GFrac R) :=
  GPoly.sub (ops₁g R) (GPoly.smul (ops₁g R) gq D) (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] D)

/-- Solve `y′ + g y = A / D` over `R(x)(t₁)`; the solution is `Y / D`. -/
def rdePrimW (En₁ Ed₁ : CPoly R) (gq : GFrac R) (μ : CPoly R) (A D : GPoly (GFrac R)) :
    Option (GPoly (GFrac R)) :=
  rdePolyPrimAuxW En₁ Ed₁ gq μ D (rdeP₀W En₁ Ed₁ gq D) ((GPoly.mul (ops₁g R) A D).length + 1)
    (GPoly.mul (ops₁g R) A D) []

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [CPoly.HasRatRoots R] [HasNatTest R]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
  {En₁ Ed₁ : CPoly R}

include h0 hD in
/-- **Soundness of the top coefficient.** -/
lemma rdeTopCoeffW_sound (gq : GFrac R) (μ : CPoly R) (hGd0 : CPoly.toPoly gq.2 ≠ 0)
    (L top : GFrac R) (hL : CPoly.toPoly L.1 ≠ 0)
    (hL2 : CPoly.toPoly L.2 ≠ 0) (htop2 : CPoly.toPoly top.2 ≠ 0) {yd : GFrac R}
    (h : rdeTopCoeffW gq μ L top = some yd) :
    (CPoly.ev K₁ ι yd)′ + (CPoly.ev K₁ ι gq - (CPoly.ev K₁ ι L)′ / CPoly.ev K₁ ι L) *
      CPoly.ev K₁ ι yd = CPoly.ev K₁ ι top / CPoly.ev K₁ ι L := by
  simp only [rdeTopCoeffW, Option.map_eq_some_iff] at h
  obtain ⟨⟨Yz, Gz⟩, hz, rfl⟩ := h
  have hden : CPoly.toPoly (CPoly.mul (CPoly.mul top.2 L.1) L.1) ≠ 0 := by
    simp only [CPoly.toPoly_mul]
    exact mul_ne_zero (mul_ne_zero htop2 hL) hL
  have hsol := CPoly.rdeRationalW_sound (K := K₁) ι hD hden hGd0 hz
  simp only [CPoly.toPoly_mul, Polynomial.map_mul, map_mul] at hsol
  have hev : ∀ q : GFrac R, CPoly.ev K₁ ι q =
      φ ((CPoly.toPoly q.1).map ι) / φ ((CPoly.toPoly q.2).map ι) := fun q ↦ rfl
  have hφ : ∀ {P : CPoly R}, CPoly.toPoly P ≠ 0 → φ ((CPoly.toPoly P).map ι) ≠ 0 := fun hP ↦
    CPoly.map_toPoly_ne_zero ι hP
  have hL1' := hφ hL
  have hL2' := hφ hL2
  have htop2' := hφ htop2
  set z : K₁ := CPoly.ev K₁ ι (Yz, Gz) with hz'
  have hyd : CPoly.ev K₁ ι ((ops₁g R).mul L (Yz, Gz)) = CPoly.ev K₁ ι L * z := by
    rw [← sem_M₁In (K₁ := K₁) ι h0 hD, (M₁In (K₁ := K₁) ι h0 hD).sem_mul, sem_M₁In, sem_M₁In]
  have hLne : CPoly.ev K₁ ι L ≠ 0 := by
    rw [hev]; exact div_ne_zero hL1' hL2'
  have hsol' : z′ + CPoly.ev K₁ ι gq * z =
      CPoly.ev K₁ ι top / CPoly.ev K₁ ι L ^ 2 := by
    rw [hz', hev, hev, hev, hev, hsol]
    field_simp
  have hkey : CPoly.ev K₁ ι L * (z′ + CPoly.ev K₁ ι gq * z) =
      CPoly.ev K₁ ι top / CPoly.ev K₁ ι L := by
    rw [hsol']
    field_simp
  rw [hyd, Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [← hkey]
  field_simp
  ring

include h0 hD in
/-- **Soundness of the recursion**: the invariant `D acc′ + P₀ acc + Ap` is preserved. -/
theorem rdePolyPrimAuxW_sound
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (gq : GFrac R) (μ : CPoly R) (D P₀ : GPoly (GFrac R)) (fuel : ℕ) (Ap acc Y : GPoly (GFrac R))
    (h : rdePolyPrimAuxW En₁ Ed₁ gq μ D P₀ fuel Ap acc = some Y) :
    let M₁ := M₁In (K₁ := K₁) ι h0 hD
    GPoly.toPoly M₁ D * (GPoly.toPoly M₁ Y)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ Y =
      GPoly.toPoly M₁ D * (GPoly.toPoly M₁ acc)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ acc +
        GPoly.toPoly M₁ Ap := by
  intro M₁
  induction fuel generalizing Ap acc with
  | zero =>
    simp only [rdePolyPrimAuxW] at h
    split_ifs at h with hz
    rw [Option.some.injEq] at h
    subst h
    rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
  | succ fuel ih =>
    simp only [rdePolyPrimAuxW] at h
    split_ifs at h with hz hlt
    · rw [Option.some.injEq] at h
      subst h
      rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
    · revert h
      cases rdeTopCoeffW gq μ (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D))
          (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) with
      | none => intro h; exact absurd h (by simp)
      | some yd =>
        intro h
        simp only at h
        have := ih _ _ h
        rw [this]
        simp only [GPoly.toPoly_add, GPoly.toPoly_sub, GPoly.toPoly_mul, map_add]
        rw [toPoly_derivT_η ι h0 hD hD₂]
        ring

include h0 hD in
/-- **Soundness of `rdePrimW`**: `y = Y / D` solves `y′ + g y = A / D`, in every model. -/
theorem rdePrimW_sound (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (gq : GFrac R) (μ : CPoly R) (A D : GPoly (GFrac R))
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D ≠ 0) {Y : GPoly (GFrac R)}
    (h : rdePrimW En₁ Ed₁ gq μ A D = some Y) :
    (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) / φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D))′ +
        φ₂ (C (CPoly.ev K₁ ι gq)) *
          (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) /
            φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D)) =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D) := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hinv := rdePolyPrimAuxW_sound ι h0 hD hD₂ gq μ D (rdeP₀W En₁ Ed₁ gq D) _ _ [] Y h
  simp only [GPoly.toPoly_nil, map_zero, mul_zero, zero_add, GPoly.toPoly_mul] at hinv
  have hP₀ : GPoly.toPoly M₁ (rdeP₀W En₁ Ed₁ gq D) =
      C (CPoly.ev K₁ ι gq) * GPoly.toPoly M₁ D - (GPoly.toPoly M₁ D)′ := by
    rw [rdeP₀W, GPoly.toPoly_sub, GPoly.toPoly_smul, toPoly_derivT_η ι h0 hD hD₂, hM₁, sem_M₁In]
  rw [hP₀] at hinv
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφD : φ₂ (GPoly.toPoly M₁ D) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hD0
  have hCg : φ₂ (C (CPoly.ev K₁ ι gq)) * φ₂ (GPoly.toPoly M₁ D) =
      φ₂ (C (CPoly.ev K₁ ι gq) * GPoly.toPoly M₁ D) := by rw [map_mul]
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap]
  simp only [smul_eq_mul]
  have h2 := congrArg φ₂ hinv
  simp only [map_add, map_mul, map_sub] at h2
  rw [eq_div_iff hφD]
  have hD2 : (φ₂ (GPoly.toPoly M₁ D))⁻¹ ^ 2 * (φ₂ (GPoly.toPoly M₁ D) * φ₂ (GPoly.toPoly M₁ Y)′ -
      φ₂ (GPoly.toPoly M₁ Y) * φ₂ (GPoly.toPoly M₁ D)′) * φ₂ (GPoly.toPoly M₁ D) =
      (φ₂ (GPoly.toPoly M₁ D) * φ₂ (GPoly.toPoly M₁ Y)′ -
        φ₂ (GPoly.toPoly M₁ Y) * φ₂ (GPoly.toPoly M₁ D)′) / φ₂ (GPoly.toPoly M₁ D) := by
    field_simp
  have hg2 : φ₂ (C (CPoly.ev K₁ ι gq)) * (φ₂ (GPoly.toPoly M₁ Y) /
      φ₂ (GPoly.toPoly M₁ D)) * φ₂ (GPoly.toPoly M₁ D) =
      φ₂ (C (CPoly.ev K₁ ι gq)) * φ₂ (GPoly.toPoly M₁ Y) := by
    field_simp
  rw [add_mul, hD2, hg2, div_add' _ _ _ hφD, div_eq_iff hφD]
  linear_combination h2

end Tower
