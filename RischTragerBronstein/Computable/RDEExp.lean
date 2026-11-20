import RischTragerBronstein.Computable.RDEPrimComplete
import RischTragerBronstein.RDE.ExponentialDenominator
import RischTragerBronstein.Computable.IntegrateExp

/-!
# The Risch differential equation `y′ + g y = A / (t₁^m D₁)` over `R(x)(t₁)`, `t₁ = exp a`

`g ∈ R[x]` (typically `g = k b′` for `t₂ = exp b`). By `rde_denominator_exp`,
`y = Y / (t₁^m D₁)` with `D₁ Y′ + ((g - m a′) D₁ - D₁′) Y = A D₁`, and the polynomial `Y` is found
from the top: the coefficient of `t₁^{δ+d}` is `L² (z′ + (g + (d - m - δ) a′) z)`, `y_d = L z`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Top

variable {F : Type*} [Field F] [Differential F] [Differential F[X]]

lemma natDegree_implicitDeriv_C_mul_X_le (η : F) (Y : F[X]) :
    (implicitDeriv (C η * X) Y).natDegree ≤ Y.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_
  rw [coeff_implicitDeriv_C_mul_X, coeff_eq_zero_of_natDegree_lt hk, map_zero, mul_zero,
    zero_add, mul_zero]

theorem rde_poly_top_exp (η g : F) (hD₂ : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (D Y : F[X]) (hD0 : D ≠ 0) (hY : Y ≠ 0)
    (hgnl : ∀ e : F, e ≠ 0 → e′ + (g + ((Y.natDegree : F) - D.natDegree) * η) * e ≠ 0) :
    (D * Y′ + (C g * D - D′) * Y).natDegree = D.natDegree + Y.natDegree ∧
      (D * Y′ + (C g * D - D′) * Y).coeff (D.natDegree + Y.natDegree) =
        D.leadingCoeff ^ 2 * ((Y.leadingCoeff / D.leadingCoeff)′ +
          (g + ((Y.natDegree : F) - D.natDegree) * η) * (Y.leadingCoeff / D.leadingCoeff)) ∧
      D * Y′ + (C g * D - D′) * Y ≠ 0 := by
  set L := D.leadingCoeff with hL
  set y := Y.leadingCoeff with hy
  have hL0 : L ≠ 0 := leadingCoeff_ne_zero.mpr hD0
  have hy0 : y ≠ 0 := leadingCoeff_ne_zero.mpr hY
  have hz0 : y / L ≠ 0 := div_ne_zero hy0 hL0
  have hY' : Y′.natDegree ≤ Y.natDegree := by
    rw [hD₂]; exact natDegree_implicitDeriv_C_mul_X_le η Y
  have hD' : D′.natDegree ≤ D.natDegree := by
    rw [hD₂]; exact natDegree_implicitDeriv_C_mul_X_le η D
  have hP₀ : (C g * D - D′).natDegree ≤ D.natDegree :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _)) hD')
  have hle : (D * Y′ + (C g * D - D′) * Y).natDegree ≤ D.natDegree + Y.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_mul_le.trans (by omega)
    · exact natDegree_mul_le.trans (by omega)
  have hc1 : (D * Y′).coeff (D.natDegree + Y.natDegree) = L * (y′ + η * (Y.natDegree * y)) := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl hY', hD₂, coeff_implicitDeriv_C_mul_X]
    rfl
  have hc2 : ((C g * D - D′) * Y).coeff (D.natDegree + Y.natDegree) =
      (g * L - (L′ + η * (D.natDegree * L))) * y := by
    rw [coeff_mul_add_eq_of_natDegree_le hP₀ le_rfl, coeff_sub, coeff_C_mul, hD₂,
      coeff_implicitDeriv_C_mul_X]
    rfl
  have hcoeff : (D * Y′ + (C g * D - D′) * Y).coeff (D.natDegree + Y.natDegree) =
      L ^ 2 * ((y / L)′ + (g + ((Y.natDegree : F) - D.natDegree) * η) * (y / L)) := by
    rw [coeff_add, hc1, hc2, Derivation.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hne : L ^ 2 * ((y / L)′ + (g + ((Y.natDegree : F) - D.natDegree) * η) * (y / L)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hL0) (hgnl _ hz0)
  have hdeg : (D * Y′ + (C g * D - D′) * Y).natDegree = D.natDegree + Y.natDegree :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoeff]; exact hne))
  exact ⟨hdeg, hcoeff, fun h0 ↦ hne (by rw [← hcoeff, h0, coeff_zero])⟩

end Top

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The coefficient `g + (d - m - δ) a′` of the top-coefficient equation. -/
def expGd (a g : CPoly R) (m δ d : ℕ) : CPoly R :=
  CPoly.add g (CPoly.smul ((((d : ℤ) - m - δ : ℤ)) : R) (CPoly.deriv a))

/-- The top-degree recursion for `D Y′ + P₀ Y = Ap` in an exponential extension. -/
def rdePolyExpAux (a g : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) :
    ℕ → GPoly (GFrac R) → GPoly (GFrac R) → Option (GPoly (GFrac R))
  | 0, Ap, acc => if GPoly.isZero (ops₁g R) Ap then some acc else none
  | fuel + 1, Ap, acc =>
    if GPoly.isZero (ops₁g R) Ap then some acc
    else
      let dA := (GPoly.trim (ops₁g R) Ap).length - 1
      let d₁ := (GPoly.trim (ops₁g R) D).length - 1
      if dA < d₁ then none
      else
        match rdeTopCoeff (expGd a g m d₁ (dA - d₁))
            (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D))
            (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) with
        | none => none
        | some yd =>
          let Yd := GPoly.monomial (ops₁g R) (dA - d₁) yd
          rdePolyExpAux a g m D P₀ fuel
            (GPoly.sub (ops₁g R) Ap (GPoly.add (ops₁g R)
              (GPoly.mul (ops₁g R) D (GPoly.derivT (ops₁g R) (expW a) Yd))
              (GPoly.mul (ops₁g R) P₀ Yd)))
            (GPoly.add (ops₁g R) acc Yd)

/-- `P₀ = (g - m a′) D₁ - D₁′`. -/
def rdeP₀E (a g : CPoly R) (m : ℕ) (D : GPoly (GFrac R)) : GPoly (GFrac R) :=
  GPoly.sub (ops₁g R)
    (GPoly.smul (ops₁g R) (CPoly.sub g (CPoly.smul (m : R) (CPoly.deriv a)), [1]) D)
    (GPoly.derivT (ops₁g R) (expW a) D)

/-- Solve `y′ + g y = A / (t₁^m D₁)` over `R(x)(exp a)`; the solution is `Y / (t₁^m D₁)`. -/
def rdeExp (a g : CPoly R) (A D₁ : GPoly (GFrac R)) (m : ℕ) : Option (GPoly (GFrac R)) :=
  rdePolyExpAux a g m D₁ (rdeP₀E a g m D₁) ((GPoly.mul (ops₁g R) A D₁).length + 1)
    (GPoly.mul (ops₁g R) A D₁) []

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P) (a : CPoly R)

/-- The value of `a′` in `K₁`. -/
noncomputable abbrev ηa : K₁ := φ ((derivative (CPoly.toPoly a)).map ι)

lemma toPoly_expW_In :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expW a) = C (ηa ι a) * X := by
  have hexp : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expW a) =
      C ((M₁In (K₁ := K₁) ι h0 hD).sem (ops₁g R).zero) +
        X * (C ((M₁In (K₁ := K₁) ι h0 hD).sem (CPoly.deriv a, [1])) + X * 0) := rfl
  rw [hexp, CField.sem_zero, sem_M₁In, C_0, zero_add, mul_zero, add_zero, mul_comm]
  congr 2
  rw [CPoly.ev, CPoly.toPoly_deriv]
  simp [CPoly.toPoly]

include hD in
lemma toPoly_derivT_expW (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (p : GPoly (GFrac R)) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (GPoly.derivT (ops₁g R) (expW a) p) =
      (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) p)′ := by
  rw [GPoly.toPoly_derivT, hD₂, toPoly_expW_In]

include h0 hD in
/-- **Soundness of the recursion**: the invariant `D acc′ + P₀ acc + Ap` is preserved. -/
theorem rdePolyExpAux_sound (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (g : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) (fuel : ℕ) (Ap acc Y : GPoly (GFrac R))
    (h : rdePolyExpAux a g m D P₀ fuel Ap acc = some Y) :
    let M₁ := M₁In (K₁ := K₁) ι h0 hD
    GPoly.toPoly M₁ D * (GPoly.toPoly M₁ Y)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ Y =
      GPoly.toPoly M₁ D * (GPoly.toPoly M₁ acc)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ acc +
        GPoly.toPoly M₁ Ap := by
  intro M₁
  induction fuel generalizing Ap acc with
  | zero =>
    simp only [rdePolyExpAux] at h
    split_ifs at h with hz
    rw [Option.some.injEq] at h
    subst h
    rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
  | succ fuel ih =>
    simp only [rdePolyExpAux] at h
    split_ifs at h with hz hlt
    · rw [Option.some.injEq] at h
      subst h
      rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
    · revert h
      cases rdeTopCoeff (expGd a g m ((GPoly.trim (ops₁g R) D).length - 1)
          ((GPoly.trim (ops₁g R) Ap).length - 1 - ((GPoly.trim (ops₁g R) D).length - 1)))
          (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D))
          (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) with
      | none => intro h; exact absurd h (by simp)
      | some yd =>
        intro h
        simp only at h
        have := ih _ _ h
        rw [this]
        simp only [GPoly.toPoly_add, GPoly.toPoly_sub, GPoly.toPoly_mul, map_add]
        rw [toPoly_derivT_expW ι h0 hD a hD₂]
        ring

include h0 hD in
/-- **Soundness of `rdeExp`**: `y = Y / (t₁^m D₁)` solves `y′ + g y = A / (t₁^m D₁)`. -/
theorem rdeExp_sound (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (g : CPoly R) (A D₁ : GPoly (GFrac R)) (m : ℕ)
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁ ≠ 0) {Y : GPoly (GFrac R)}
    (h : rdeExp a g A D₁ m = some Y) :
    (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁)))′ +
        φ₂ (C (φ ((CPoly.toPoly g).map ι))) *
          (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) /
            (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁))) =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁)) := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hinv := rdePolyExpAux_sound ι h0 hD a hD₂ g m D₁ (rdeP₀E a g m D₁) _ _ [] Y h
  simp only [GPoly.toPoly_nil, map_zero, mul_zero, zero_add, GPoly.toPoly_mul] at hinv
  set gK : K₁ := φ ((CPoly.toPoly g).map ι) with hgK
  have hP₀ : GPoly.toPoly M₁ (rdeP₀E a g m D₁) =
      C (gK - m * ηa ι a) * GPoly.toPoly M₁ D₁ - (GPoly.toPoly M₁ D₁)′ := by
    rw [rdeP₀E, GPoly.toPoly_sub, GPoly.toPoly_smul, toPoly_derivT_expW ι h0 hD a hD₂, hM₁,
      sem_M₁In]
    congr 3
    rw [CPoly.ev, CPoly.toPoly_sub, CPoly.toPoly_smul, CPoly.toPoly_deriv]
    simp [CPoly.toPoly, hgK, ηa, map_natCast]
  rw [hP₀] at hinv
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφD : φ₂ (GPoly.toPoly M₁ D₁) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hD0
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
  have hXm0 : φ₂ (X : K₁[X]) ^ m ≠ 0 := pow_ne_zero _ hX0
  have hXm' : (φ₂ (X : K₁[X]) ^ m)′ = φ₂ (C (m * ηa ι a)) * φ₂ X ^ m := by
    rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
  have h2 := congrArg φ₂ hinv
  simp only [map_add, map_mul, map_sub, ← deriv_algebraMap] at h2
  set W : K₂ := φ₂ X ^ m * φ₂ (GPoly.toPoly M₁ D₁) with hW
  have hW0 : W ≠ 0 := mul_ne_zero hXm0 hφD
  have hW' : W′ = φ₂ (C (m : K₁)) * φ₂ (C (ηa ι a)) * W + φ₂ X ^ m * (φ₂ (GPoly.toPoly M₁ D₁))′ := by
    rw [hW, Derivation.leibniz, hXm', C_mul, map_mul]
    simp only [smul_eq_mul]
    ring
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [eq_div_iff hW0]
  have e1 : W⁻¹ ^ 2 * (W * (φ₂ (GPoly.toPoly M₁ Y))′ - φ₂ (GPoly.toPoly M₁ Y) * W′) * W =
      (W * (φ₂ (GPoly.toPoly M₁ Y))′ - φ₂ (GPoly.toPoly M₁ Y) * W′) / W := by
    field_simp
  have e2 : φ₂ (C gK) * (φ₂ (GPoly.toPoly M₁ Y) / W) * W = φ₂ (C gK) * φ₂ (GPoly.toPoly M₁ Y) := by
    field_simp
  rw [add_mul, e1, e2, div_add' _ _ _ hW0, div_eq_iff hW0, hW']
  rw [hW]
  linear_combination (φ₂ (X : K₁[X]) ^ m) * h2

end Tower
