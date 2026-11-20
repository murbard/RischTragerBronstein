import RischTragerBronstein.Computable.ExpLaurentRat
import RischTragerBronstein.Computable.RDERationalG

/-!
# Laurent polynomials in a hyperexponential `t′ = η t`, `η ∈ R(x)`: the negative answer

`η = Gn / Gd` in lowest terms, without simple poles, `deg Gn + 1 ≠ deg Gd` — e.g. `η = a′` for a
nonconstant **rational** function `a`, `t = exp a(x)` (`e^{1/x}`, `e^{x/(x²+1)}`, …).

If for some `j ≠ n` the verified solver `rdeRationalG` reports that `y′ + (j - n) η y = fⱼ` has no
solution in `R(x)`, then `f₀ + ∑_{j ≠ n} fⱼ t ^ j / t ^ n` has **no elementary integral** — with
no assumption on constants.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field K] [Algebra R K]
variable [Differential K]

theorem not_elementary_hyperexpLaurent (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (Gn Gd G₁ : CPoly R)
    (ht : t′ = aeval x (toPoly Gn) / aeval x (toPoly Gd) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0) (hcop : IsCoprime (toPoly Gn) (toPoly Gd))
    (hr1 : toPoly G₁ ∣ toPoly Gd) (hr2 : toPoly G₁ ∣ derivative (toPoly Gd))
    (hr3 : toPoly Gd ∣ toPoly G₁ ^ 2)
    (hdeg : (toPoly Gn).natDegree + 1 ≠ (toPoly Gd).natDegree)
    (N n : ℕ) (A D : ℕ → CPoly R) (A₀ D₀ : CPoly R)
    (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (j₀ : ℕ) (hj₀ : j₀ < N) (hj₀n : j₀ ≠ n)
    (hnone : rdeRationalG (smul (((j₀ : ℤ) - n : ℤ) : R) Gn) Gd (A j₀) (D j₀) = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n) := by
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
  have hval : ∀ P : R[X], algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ (P.map ι)) =
      ψ (aeval x P) := fun P ↦ (algebraMap_adjoinSimple xE _).trans (hι _ x)
  set η₁ : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Gn).map ι) /
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Gd).map ι) with hη₁
  have htE'' : tE′ = algebraMap Cc⟮xE⟯ E η₁ * tE := by
    rw [hη₁, map_div₀, hval, hval, htE, hψ, deriv_algebraMap, ht, map_mul, map_div₀]
  -- the hypotheses on `η`, over the constants of `E`
  have hGnS : (toPoly Gn).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGn0
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGd0
  have hcopS : IsCoprime ((toPoly Gn).map ι) ((toPoly Gd).map ι) := hcop.map (mapRingHom ι)
  have hsqS := sq_dvd_of_repeated (Polynomial.map_dvd ι hr1)
    (by rw [derivative_map]; exact Polynomial.map_dvd ι hr2)
    (by rw [← Polynomial.map_pow]; exact Polynomial.map_dvd ι hr3)
  have hdegS : ((toPoly Gn).map ι).natDegree + 1 ≠ ((toPoly Gd).map ι).natDegree := by
    rw [natDegree_map, natDegree_map]; exact hdeg
  -- (2) `t` is transcendental over `C'(x)`
  have htrt : Transcendental Cc⟮xE⟯ tE := by
    refine transcendental_exponential η₁ htE0 htE'' fun m hm b hb ↦ ?_
    refine rde_homogeneous_rational (K := Cc⟮xE⟯) hD _ _ hGnS hGdS hcopS hsqS hdegS (m : Cc)
      (Nat.cast_ne_zero.mpr hm) b ?_
    have : algebraMap Cc[X] Cc⟮xE⟯ (C (m : Cc)) = (m : Cc⟮xE⟯) := by
      rw [show (C (m : Cc) : Cc[X]) = (m : Cc[X]) from map_natCast C m, map_natCast]
    rw [hb, this, ← hη₁]
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
  -- (5) the integrand as a polynomial in `t` over `C'(x)`
  let c' : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  let fr : CPoly R → CPoly R → Cc⟮xE⟯ := fun P Q ↦
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly P).map ι) / algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Q).map ι)
  have hfr : ∀ P Q : CPoly R, algebraMap Cc⟮xE⟯ E (fr P Q) =
      ψ (aeval x (toPoly P) / aeval x (toPoly Q)) := fun P Q ↦ by
    have hB : ∀ P' : R[X], algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ (P'.map ι)) =
        ψ (aeval x P') := fun P' ↦ (algebraMap_adjoinSimple xE _).trans (hι _ x)
    simp only [fr]
    rw [map_div₀, hB, hB, map_div₀]
  let Ap : (Cc⟮xE⟯)[X] := C (fr A₀ D₀) * X ^ n +
    ∑ j ∈ (Finset.range N).erase n, C (fr (A j) (D j)) * X ^ j
  have htn : tE ^ n ≠ 0 := pow_ne_zero _ htE0
  have hAp : aeval tE Ap / tE ^ n = ψ (aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n) := by
    simp only [Ap, map_add, map_sum, map_mul, map_pow, aeval_C, aeval_X, hfr]
    rw [add_div, Finset.sum_div, mul_div_assoc, div_self htn, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [map_div₀, map_mul, map_pow]
    rfl
  have hcoeff : Ap.coeff j₀ = fr (A j₀) (D j₀) := by
    simp only [Ap, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [if_neg hj₀n, mul_zero, zero_add, Finset.sum_eq_single j₀]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_erase.mpr ⟨hj₀n, Finset.mem_range.mpr hj₀⟩) h'
  obtain ⟨y, hy⟩ := (rde_step_exponential_laurent (F := Cc⟮xE⟯) tE htrt η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv) Ap n (by
      rw [hAp, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)).1 j₀ hj₀n
  rw [hcoeff] at hy
  have hz : (((j₀ : ℤ) - n : ℤ) : R) ≠ 0 :=
    Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hj₀n))
  have hu : IsUnit (C (((j₀ : ℤ) - n : ℤ) : R) : R[X]) := isUnit_C.mpr hz.isUnit
  refine rdeRationalG_complete (K := Cc⟮xE⟯) ι hD (G₁ := G₁) (hD0 j₀ hj₀)
    (by rw [toPoly_smul]; exact mul_ne_zero (C_ne_zero.mpr hz) hGn0) hGd0
    (by rw [toPoly_smul]; exact (isCoprime_mul_unit_left_left hu _ _).mpr hcop) hr1 hr2 hr3
    (by rw [toPoly_smul, natDegree_C_mul hz]; exact hdeg) hnone y ?_
  rw [toPoly_smul, Polynomial.map_mul, map_C, map_mul]
  have hcast : algebraMap Cc[X] Cc⟮xE⟯ (C (ι (((j₀ : ℤ) - n : ℤ) : R))) =
      (j₀ : Cc⟮xE⟯) - n := by
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
  rw [hcast]
  simp only [fr, hη₁] at hy
  linear_combination hy

/-- If some power of `t` cannot be integrated, the Laurent polynomial has no elementary
integral. -/
theorem not_hasElementaryIntegral_hyperexpLaurent {K : Type*} [Field K] [Algebra R K]
    [Differential K] [CharZero K] (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (Gn Gd G₁ : CPoly R)
    (ht : t′ = aeval x (toPoly Gn) / aeval x (toPoly Gd) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0) (hcop : IsCoprime (toPoly Gn) (toPoly Gd))
    (hr1 : toPoly G₁ ∣ toPoly Gd) (hr2 : toPoly G₁ ∣ derivative (toPoly Gd))
    (hr3 : toPoly Gd ∣ toPoly G₁ ^ 2)
    (hdeg : (toPoly Gn).natDegree + 1 ≠ (toPoly Gd).natDegree)
    (N n : ℕ) (A D : ℕ → CPoly R) (A₀ D₀ : CPoly R)
    (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (j₀ : ℕ) (hj₀ : j₀ < N) (hj₀n : j₀ ≠ n)
    (hnone : rdeRationalG (smul (((j₀ : ℤ) - n : ℤ) : R) Gn) Gd (A j₀) (D j₀) = none) :
    ¬HasElementaryIntegral (aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_hyperexpLaurent hR x t hx ht0 Gn Gd G₁ ht hgen hGn0 hGd0 hcop hr1 hr2 hr3
    hdeg N n A D A₀ D₀ hD0 j₀ hj₀ hj₀n hnone E hE g hg

end CPoly

namespace CPoly

open Differential

section Positive

universe u

variable {R : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [Field K] [Differential K] [Algebra R K] [DifferentialAlgebra R K]

theorem rdeRationalG_sound_in (h0 : ∀ r : R, r′ = 0) (x : K) (hx : x′ = 1)
    {Gn Gd A D Y D' : CPoly R} (hD0 : toPoly D ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (hsome : rdeRationalG Gn Gd A D = some (Y, D')) :
    (aeval x (toPoly Y) / aeval x (toPoly D'))′ +
        aeval x (toPoly Gn) / aeval x (toPoly Gd) * (aeval x (toPoly Y) / aeval x (toPoly D')) =
      aeval x (toPoly A) / aeval x (toPoly D) := by
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
  have hderiv : ∀ y : R⟮x⟯, ((y′ : R⟮x⟯) : K) = (y : K)′ := fun _ ↦ rfl
  have hsol := rdeRationalG_sound (K := R⟮x⟯) (RingHom.id R) hDpoly hD0 hGd0 hsome
  have := congrArg (fun z : R⟮x⟯ ↦ (z : K)) hsol
  simp only [Polynomial.map_id, hderiv, IntermediateField.coe_add, MulMemClass.coe_mul,
    IntermediateField.coe_div, hcoe] at this
  exact this

/-- **The result is an antiderivative**: `W = ∑_{j ≠ n} yⱼ t ^ j / t ^ n`. -/
theorem hyperexpLaurent_antiderivative (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (ht0 : t ≠ 0) (Gn Gd : CPoly R) (hGd0 : toPoly Gd ≠ 0)
    (ht : t′ = aeval x (toPoly Gn) / aeval x (toPoly Gd) * t)
    (N n : ℕ) (A D Y G : ℕ → CPoly R) (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (hsome : ∀ j < N, j ≠ n →
      rdeRationalG (smul (((j : ℤ) - n : ℤ) : R) Gn) Gd (A j) (D j) = some (Y j, G j)) :
    (∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (Y j)) / aeval x (toPoly (G j)) * t ^ j / t ^ n)′ =
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  obtain ⟨hjn, hjN⟩ := Finset.mem_erase.mp hj
  have hjN' := Finset.mem_range.mp hjN
  have hsol := rdeRationalG_sound_in h0 x hx (hD0 j hjN') hGd0 (hsome j hjN' hjn)
  rw [deriv_mul_pow_div_pow _ t _ ht0 ht, ← hsol, toPoly_smul, map_mul, aeval_C]
  simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
  ring

/-- **The positive answer**, with the explicit antiderivative `∑ yⱼ t ^ j / t ^ n + ∫ f₀`. -/
theorem hasElementaryIntegral_hyperexpLaurent (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (ht0 : t ≠ 0) (Gn Gd : CPoly R) (hGd0 : toPoly Gd ≠ 0)
    (ht : t′ = aeval x (toPoly Gn) / aeval x (toPoly Gd) * t)
    (N n : ℕ) (A D Y G : ℕ → CPoly R) (A₀ D₀ : CPoly R) (hD₀ : toPoly D₀ ≠ 0)
    (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (hsome : ∀ j < N, j ≠ n →
      rdeRationalG (smul (((j : ℤ) - n : ℤ) : R) Gn) Gd (A j) (D j) = some (Y j, G j)) :
    HasElementaryIntegral (aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n) := by
  set W : K := ∑ j ∈ (Finset.range N).erase n,
    aeval x (toPoly (Y j)) / aeval x (toPoly (G j)) * t ^ j / t ^ n with hW
  have hW' : W′ = ∑ j ∈ (Finset.range N).erase n,
      aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n := by
    rw [hW, map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    obtain ⟨hjn, hjN⟩ := Finset.mem_erase.mp hj
    have hjN' := Finset.mem_range.mp hjN
    have hsol := rdeRationalG_sound_in h0 x hx (hD0 j hjN') hGd0 (hsome j hjN' hjn)
    rw [deriv_mul_pow_div_pow _ t _ ht0 ht, ← hsol, toPoly_smul, map_mul, aeval_C]
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
    ring
  have hform : aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n =
      W′ + aeval x (toPoly A₀) / aeval x (toPoly D₀) := by rw [hW']; ring
  rw [hform]
  exact hasElementaryIntegral_rational_in h0 x hx _ _ hD₀ W

end Positive

end CPoly
