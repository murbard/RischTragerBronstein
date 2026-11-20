import RischTragerBronstein.Computable.ExpPolyRatPositive
import RischTragerBronstein.Liouville.StepExponentialLaurent

/-!
# Laurent polynomials in `exp (a(x))` with rational coefficients

Integrand: `A₀/D₀ + ∑_{j < N, j ≠ n} fⱼ(x) t ^ j / t ^ n`, `t = exp a`, `fⱼ = Aⱼ / Dⱼ ∈ R(x)`: an
arbitrary Laurent polynomial in `t` over `R(x)` (positive **and negative** powers of `t`).

* `not_hasElementaryIntegral_expLaurentRat`: if for some `j ≠ n` the verified solver reports that
  `y′ + (j - n) a′ y = Aⱼ / Dⱼ` has no solution in `R(x)`, the integrand has **no elementary
  integral** (no assumption on constants).
* `hasElementaryIntegral_expLaurentRat`: if all these equations are solved, the integrand has the
  elementary integral `∑ yⱼ t ^ j / t ^ n + ∫ A₀/D₀`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

section Negative

variable {R K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field K] [Algebra R K]
variable [Differential K]

/-- The coefficient polynomial `z a′` of the Risch differential equation for `t ^ z`, `z ∈ ℤ`. -/
def expCoeffZ (a : CPoly R) (z : ℤ) : CPoly R := smul (z : R) (deriv a)

theorem not_elementary_expLaurentRat (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (a : CPoly R)
    (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (ha : trim (deriv a) ≠ []) (N n : ℕ) (A D : ℕ → CPoly R) (A₀ D₀ : CPoly R)
    (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (j₀ : ℕ) (hj₀ : j₀ < N) (hj₀n : j₀ ≠ n)
    (hnone : rdeRational (expCoeffZ a ((j₀ : ℤ) - n)) (A j₀) (D j₀) = none)
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
  have hg0 : toPoly (expCoeffZ a ((j₀ : ℤ) - n)) ≠ 0 := by
    rw [expCoeffZ, toPoly_smul]
    exact mul_ne_zero (C_ne_zero.mpr hz) fun h0 ↦ ha ((trim_eq_nil_iff _).mpr h0)
  refine rdeRational_complete (K := Cc⟮xE⟯) ι hD (hD0 j₀ hj₀) hg0 hnone y ?_
  rw [expCoeffZ, toPoly_smul, toPoly_deriv, Polynomial.map_mul, map_C, map_mul]
  have hcast : algebraMap Cc[X] Cc⟮xE⟯ (C (ι (((j₀ : ℤ) - n : ℤ) : R))) =
      (j₀ : Cc⟮xE⟯) - n := by
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
  rw [hcast]
  exact hy

/-- If some power of `t` cannot be integrated, the Laurent polynomial has no elementary
integral. -/
theorem not_hasElementaryIntegral_expLaurentRat {K : Type*} [Field K] [Algebra R K]
    [Differential K] [CharZero K] (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (a : CPoly R)
    (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (ha : trim (deriv a) ≠ []) (N n : ℕ) (A D : ℕ → CPoly R) (A₀ D₀ : CPoly R)
    (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (j₀ : ℕ) (hj₀ : j₀ < N) (hj₀n : j₀ ≠ n)
    (hnone : rdeRational (expCoeffZ a ((j₀ : ℤ) - n)) (A j₀) (D j₀) = none) :
    ¬HasElementaryIntegral (aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_expLaurentRat hR x t hx ht0 a ht hgen ha N n A D A₀ D₀ hD0 j₀ hj₀ hj₀n
    hnone E hE g hg

end Negative

section Positive

universe u

variable {R : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [Field K] [Differential K] [Algebra R K] [DifferentialAlgebra R K]

/-- `(y t ^ j / t ^ n)′ = (y′ + (j - n) η y) t ^ j / t ^ n` for an exponential `t′ = η t`. -/
lemma deriv_mul_pow_div_pow {L : Type*} [Field L] [Differential L] (y t η : L) (ht0 : t ≠ 0)
    (ht : t′ = η * t) (j n : ℕ) :
    (y * t ^ j / t ^ n)′ = (y′ + ((j : L) - n) * η * y) * t ^ j / t ^ n := by
  have hj : t ^ j ≠ 0 := pow_ne_zero _ ht0
  have hn : t ^ n ≠ 0 := pow_ne_zero _ ht0
  have hlog : logDeriv (t ^ j / t ^ n) = ((j : L) - n) * η := by
    rw [logDeriv_div _ _ hj hn, logDeriv_pow, logDeriv_pow, logDeriv, ht]
    field_simp
  have hu : (t ^ j / t ^ n)′ = ((j : L) - n) * η * (t ^ j / t ^ n) := by
    rw [← hlog, logDeriv]
    field_simp
  rw [mul_div_assoc, Derivation.leibniz, hu]
  simp only [smul_eq_mul]
  ring

/-- **The result is an antiderivative.** With the solutions `yⱼ = Yⱼ / Gⱼ` returned by the verified
RDE solver, `W = ∑_{j ≠ n} yⱼ t ^ j / t ^ n` differentiates to the Laurent part of the integrand. -/
theorem expLaurent_antiderivative (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (ht0 : t ≠ 0) (a : CPoly R) (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (N n : ℕ) (A D Y G : ℕ → CPoly R) (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (hsome : ∀ j < N, j ≠ n →
      rdeRational (expCoeffZ a ((j : ℤ) - n)) (A j) (D j) = some (Y j, G j)) :
    (∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (Y j)) / aeval x (toPoly (G j)) * t ^ j / t ^ n)′ =
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  obtain ⟨hjn, hjN⟩ := Finset.mem_erase.mp hj
  have hjN' := Finset.mem_range.mp hjN
  have hsol := rdeRational_sound_in h0 x hx (hD0 j hjN') (hsome j hjN' hjn)
  have hg : aeval x (toPoly (expCoeffZ a ((j : ℤ) - n))) =
      ((j : K) - n) * aeval x (derivative (toPoly a)) := by
    rw [expCoeffZ, toPoly_smul, toPoly_deriv, map_mul, aeval_C]
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
  rw [hg] at hsol
  rw [deriv_mul_pow_div_pow _ t _ ht0 ht, ← hsol]

theorem hasElementaryIntegral_expLaurentRat (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (ht0 : t ≠ 0) (a : CPoly R) (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (N n : ℕ) (A D Y G : ℕ → CPoly R) (A₀ D₀ : CPoly R) (hD₀ : toPoly D₀ ≠ 0)
    (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (hsome : ∀ j < N, j ≠ n →
      rdeRational (expCoeffZ a ((j : ℤ) - n)) (A j) (D j) = some (Y j, G j)) :
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
    have hsol := rdeRational_sound_in h0 x hx (hD0 j hjN') (hsome j hjN' hjn)
    have hg : aeval x (toPoly (expCoeffZ a ((j : ℤ) - n))) =
        ((j : K) - n) * aeval x (derivative (toPoly a)) := by
      rw [expCoeffZ, toPoly_smul, toPoly_deriv, map_mul, aeval_C]
      simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
    rw [hg] at hsol
    rw [deriv_mul_pow_div_pow _ t _ ht0 ht, ← hsol]
  have hform : aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase n,
        aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j / t ^ n =
      W′ + aeval x (toPoly A₀) / aeval x (toPoly D₀) := by rw [hW']; ring
  rw [hform]
  exact hasElementaryIntegral_rational_in h0 x hx _ _ hD₀ W

end Positive

end CPoly
