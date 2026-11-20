import RischTragerBronstein.Computable.RDERational
import RischTragerBronstein.RDE.ExpRational
import RischTragerBronstein.Computable.LogTimesPositive

/-!
# `∫ f(x) exp (a(x)) dx` with `f` rational: decided

`CPoly.integrateExpRational A D a := rdeRational (deriv a) A D` solves the Risch differential
equation `y′ + a′ y = A / D` over `R(x)`. For a differential field `K` generated over constants `R`
by `x` (`x′ = 1`) and `t ≠ 0` with `t′ = a′(x) t`, `deg a ≥ 1`, `D ≠ 0`:

* `hasElementaryIntegral_expRational`: if it returns `some (Y, G)`, then
  `((Y(x) / G(x)) t)′ = (A(x) / D(x)) t`: `∫ f exp a = (Y / G) exp a`;
* `not_hasElementaryIntegral_expRational`: if it returns `none`, then `f exp a` has **no elementary
  integral**, with no assumption on constants.

This subsumes the polynomial case (`integrateExpPoly`) and the simple-pole theorem
(`not_hasElementaryIntegral_exp_simple_pole`): e.g. `∫ eˣ / x dx` is refuted by computation.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

/-- Integrate `(A / D) exp a`: solve `y′ + a′ y = A / D`. -/
def integrateExpRational {R : Type*} [Field R] [DecidableEq R] (A D a : CPoly R) :
    Option (CPoly R × CPoly R) := rdeRational (deriv a) A D

section Negative

variable {R K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field K] [Algebra R K]
variable [Differential K]

theorem not_elementary_expRational (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (a : CPoly R)
    (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (ha : trim (deriv a) ≠ []) (A D : CPoly R) (hD0 : toPoly D ≠ 0)
    (hnone : integrateExpRational A D a = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  intro hg
  classical
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  -- the field of constants of `E`, as a base field with the trivial derivation
  let Cc := constants E
  let _ : Differential Cc := ⟨0⟩
  have hCc0 : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hDAc : DifferentialAlgebra Cc E := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun m n h ↦ by
    have := congrArg (fun z : Cc ↦ (z : E)) h
    simpa using this⟩
  -- `R → Const E`
  let ι : R →+* Cc :=
    { toFun := fun r ↦ ⟨ψ (algebraMap R K r), by
        rw [mem_constants, hψ, deriv_algebraMap, hR, map_zero]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ ↦ Subtype.ext (by simp) }
  have hι : ∀ (P : R[X]) (z : K), aeval (ψ z) (P.map ι) = ψ (aeval z P) := fun P z ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  set xE := ψ x with hxE
  set tE := ψ t with htE
  have hxE' : xE′ = 1 := by rw [hxE, hψ, deriv_algebraMap, hx, map_one]
  have htE0 : tE ≠ 0 := (map_ne_zero ψ).mpr ht0
  set A' : Cc[X] := (derivative (toPoly a)).map ι with hA'
  have htE' : tE′ = aeval xE A' * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, map_mul, hA', hι]
  have hA'0 : A' ≠ 0 := by
    rw [hA', Ne, Polynomial.map_eq_zero_iff ι.injective, ← toPoly_deriv]
    obtain ⟨-, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil ha
    intro h0
    rw [h0, coeff_zero] at hlc
    exact hlc0 hlc.symm
  -- (1) `x` is transcendental over the constants
  have htrx : Transcendental Cc xE :=
    transcendental_of_deriv_ne_zero hCc0 (by rw [hxE']; exact one_ne_zero)
  -- the field `F₁ = C'(x)`
  have hw : xE′ = aeval xE (1 : Cc[X]) := by rw [hxE', map_one]
  let _ := algebraAdjoinSimple (F := Cc) xE
  let _ : Differential Cc[X] := polynomialOfDeriv (1 : Cc[X])
  let _ : Differential Cc⟮xE⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple xE 1 hw)
  have hFR : IsFractionRing Cc[X] Cc⟮xE⟯ := isFractionRing_adjoin_simple xE htrx
  have hDA1 : DifferentialAlgebra Cc[X] Cc⟮xE⟯ := differentialAlgebra_adjoin_simple xE 1 hw
  have hDA1E : DifferentialAlgebra Cc⟮xE⟯ E :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple xE 1 hw)
  have hchar1 : CharZero Cc⟮xE⟯ :=
    charZero_of_injective_algebraMap (algebraMap Cc Cc⟮xE⟯).injective
  have hD : ∀ P : Cc[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial hCc0 P
  set η₁ : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ A' with hη₁
  have hη₁E : algebraMap Cc⟮xE⟯ E η₁ = aeval xE A' := algebraMap_adjoinSimple xE A'
  have htE'' : tE′ = algebraMap Cc⟮xE⟯ E η₁ * tE := by rw [hη₁E, htE']
  -- (2) `t` is transcendental over `C'(x)`
  have htrt : Transcendental Cc⟮xE⟯ tE := by
    refine transcendental_exponential η₁ htE0 htE'' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := Cc⟮xE⟯) hD (-(C (n : Cc) * A')) ?_ b ?_
    · exact neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)
    · rw [hb, map_neg, map_mul, ← hη₁]
      have : algebraMap Cc[X] Cc⟮xE⟯ (C (n : Cc)) = (n : Cc⟮xE⟯) := by
        rw [show (C (n : Cc) : Cc[X]) = (n : Cc[X]) from map_natCast C n, map_natCast]
      rw [this]
      ring
  -- (3) all constants of `E` lie in `F₁`
  have hconst1 : ∀ z ∈ (Cc⟮xE⟯)⟮tE⟯, z′ = 0 → z ∈ Set.range (algebraMap Cc⟮xE⟯ E) :=
    fun z _ hz ↦ ⟨algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩, rfl⟩
  -- (4) the strong Liouville theorem
  obtain ⟨κ, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
  -- `K(Const E) ⊆ F₁(t)`
  set B : IntermediateField Cc⟮xE⟯ E := (Cc⟮xE⟯)⟮tE⟯ with hB
  have hBconst : ∀ z : E, z′ = 0 → z ∈ B := fun z hz ↦
    B.algebraMap_mem (algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩)
  have hBx : xE ∈ B := B.algebraMap_mem ⟨xE, mem_adjoin_simple_self Cc xE⟩
  have hBt : tE ∈ B := mem_adjoin_simple_self _ tE
  let T : IntermediateField R K :=
    { carrier := {k | ψ k ∈ B}
      mul_mem' := fun {k l} hk hl ↦ by
        change ψ (k * l) ∈ B; rw [map_mul]; exact mul_mem hk hl
      one_mem' := by change ψ 1 ∈ B; rw [map_one]; exact one_mem _
      add_mem' := fun {k l} hk hl ↦ by
        change ψ (k + l) ∈ B; rw [map_add]; exact add_mem hk hl
      zero_mem' := by change ψ 0 ∈ B; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun r ↦ hBconst _ (by rw [hψ, deriv_algebraMap, hR, map_zero])
      inv_mem' := fun k hk ↦ by
        change ψ k⁻¹ ∈ B; rw [map_inv₀]; exact inv_mem hk }
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff]
    rintro k (rfl | rfl)
    · exact hBx
    · exact hBt
  have hKB : ∀ k : K, ψ k ∈ B := fun k ↦ by
    have : k ∈ T := hT ▸ IntermediateField.mem_top
    exact this
  have hcf : ∀ z ∈ constField K E, z ∈ B := by
    let N : IntermediateField K E := { B.toSubfield with algebraMap_mem' := hKB }
    have : constField K E ≤ N := adjoin_le_iff.mpr fun z hz ↦ hBconst z hz
    exact fun z hz ↦ this hz
  -- (5) the Risch differential equation `y′ + a′ y = A / D` over `C'(x)`
  let c' : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  obtain ⟨y, hy⟩ := rde_step_exponential (F := Cc⟮xE⟯) tE htrt η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv)
    (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly A).map ι) / algebraMap Cc[X] Cc⟮xE⟯ ((toPoly D).map ι)) (by
      have hB : algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly A).map ι)) =
          ψ (aeval x (toPoly A)) := (algebraMap_adjoinSimple xE _).trans (hι _ x)
      have hS : algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly D).map ι)) =
          ψ (aeval x (toPoly D)) := (algebraMap_adjoinSimple xE _).trans (hι _ x)
      rw [map_div₀, hB, hS, htE, ← map_div₀, ← map_mul, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  have hg0 : toPoly (deriv a) ≠ 0 := fun h0 ↦ ha ((trim_eq_nil_iff _).mpr h0)
  refine rdeRational_complete (K := Cc⟮xE⟯) ι hD hD0 hg0 hnone y ?_
  rw [toPoly_deriv]
  exact hy

/-- `none` means: no elementary integral. -/
theorem not_hasElementaryIntegral_expRational {K : Type*} [Field K] [Algebra R K]
    [Differential K] [CharZero K] (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (a : CPoly R)
    (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (ha : trim (deriv a) ≠ []) (A D : CPoly R) (hD0 : toPoly D ≠ 0)
    (hnone : integrateExpRational A D a = none) :
    ¬HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_expRational hR x t hx ht0 a ht hgen ha A D hD0 hnone E hE g hg

end Negative

section Positive

universe u

variable {R : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [Field K] [Differential K] [Algebra R K] [DifferentialAlgebra R K]

/-- `some (Y, G)` means: `(Y / G) exp a` is an antiderivative. -/
theorem hasElementaryIntegral_expRational (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (a : CPoly R) (ht : t′ = aeval x (derivative (toPoly a)) * t) (A D : CPoly R)
    (hD0 : toPoly D ≠ 0) {Y G : CPoly R} (hsome : integrateExpRational A D a = some (Y, G)) :
    (aeval x (toPoly Y) / aeval x (toPoly G) * t)′ =
        aeval x (toPoly A) / aeval x (toPoly D) * t ∧
      HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  have htr : Transcendental R x :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx]; exact one_ne_zero)
  have hw : x′ = aeval x (1 : R[X]) := by rw [hx, map_one]
  let _ := algebraAdjoinSimple (F := R) x
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x 1 hw)
  have hFR : IsFractionRing R[X] R⟮x⟯ := isFractionRing_adjoin_simple x htr
  have hDA : DifferentialAlgebra R[X] R⟮x⟯ := differentialAlgebra_adjoin_simple x 1 hw
  have hDpoly : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x⟯ P : R⟮x⟯) : K) = aeval x P :=
    algebraMap_adjoinSimple x
  have hsol := rdeRational_sound (K := R⟮x⟯) (RingHom.id R) hDpoly hD0 hsome
  simp only [Polynomial.map_id, toPoly_deriv] at hsol
  -- the same equation in `K`
  have hsolK : (aeval x (toPoly Y) / aeval x (toPoly G))′ +
      aeval x (derivative (toPoly a)) * (aeval x (toPoly Y) / aeval x (toPoly G)) =
        aeval x (toPoly A) / aeval x (toPoly D) := by
    have := congrArg (fun z : R⟮x⟯ ↦ (z : K)) hsol
    simp only [IntermediateField.coe_div, IntermediateField.coe_add, IntermediateField.coe_mul,
      hcoe] at this
    rw [← this]
    congr 1
    simp only [← hcoe, ← IntermediateField.coe_div]
    rfl
  have hmain : (aeval x (toPoly Y) / aeval x (toPoly G) * t)′ =
      aeval x (toPoly A) / aeval x (toPoly D) * t := by
    rw [Derivation.leibniz, ht, ← hsolK]
    simp only [smul_eq_mul]
    ring
  exact ⟨hmain, hmain ▸ hasElementaryIntegral_of_deriv _⟩

end Positive

end CPoly

-- ∫ ((2x² - 1)/x²) e^{x²} dx = e^{x²}/x ;  ∫ eˣ/x dx: none
#eval CPoly.integrateExpRational ([-1, 0, 2] : CPoly ℚ) [0, 0, 1] [0, 0, 1]
#eval CPoly.integrateExpRational ([1] : CPoly ℚ) [0, 1] [0, 1]
