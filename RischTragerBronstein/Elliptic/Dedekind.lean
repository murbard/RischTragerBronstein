import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The coordinate ring of `y² = f(x)` (`f` squarefree cubic) is a Dedekind domain

`isDedekindDomain_coordinateRing`: for a field `K` of characteristic zero and a squarefree monic
cubic `f = x³ + a₂x² + a₄x + a₆`, the affine coordinate ring `K[x, y] / (y² − f)` of the
Weierstrass curve `⟨0, a₂, 0, a₄, a₆⟩` is a Dedekind domain.

It is a finite free `K[X]`-module (hence Noetherian, of dimension `≤ 1`), and integrally closed:
an element `x = (a + b y)/d` of the fraction field integral over it has integral trace `2a/d` and
norm `(a² − b² f)/d²` over `K[X]`, so `d ∣ a` and `d² ∣ b² f`, hence `d ∣ b` as `f` is squarefree.
-/

open Polynomial

namespace EllDedekind

variable {K : Type*} [Field K] [CharZero K] (a₂ a₄ a₆ : K)

/-- The curve `y² = x³ + a₂x² + a₄x + a₆`. -/
noncomputable abbrev Wc : WeierstrassCurve.Affine K := (⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve K).toAffine

/-- The cubic `f`. -/
noncomputable abbrev fc : K[X] := X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆

open WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

/-- The coordinate ring. -/
noncomputable abbrev CR : Type _ := (Wc a₂ a₄ a₆).CoordinateRing

/-- The generator `y`. -/
noncomputable abbrev yR : CR a₂ a₄ a₆ := mk (Wc a₂ a₄ a₆) Polynomial.X

lemma y_sq : yR a₂ a₄ a₆ ^ 2 = algebraMap K[X] (CR a₂ a₄ a₆) (fc a₂ a₄ a₆) := by
  have := smul_basis_mul_Y (W' := Wc a₂ a₄ a₆) 0 1
  simp only [zero_smul, zero_add, one_smul, map_zero, zero_mul, add_zero, mul_zero, sub_zero,
    one_mul] at this
  rw [sq, this, Algebra.smul_def, mul_one]

/-- If `N² ∣ b² f` with `f` squarefree, then `N ∣ b`. -/
lemma dvd_of_sq_dvd_sq_mul_sqf {N b f : K[X]} (hf : Squarefree f) (hN : N ≠ 0)
    (h : N ^ 2 ∣ b ^ 2 * f) : N ∣ b := by
  classical
  obtain ⟨N', b', hN', hb', hu⟩ := extract_gcd N b
  set g := gcd N b
  have hg : g ≠ 0 := by intro h0; rw [h0, zero_mul] at hN'; exact hN hN'
  have hcop : IsCoprime N' b' := (gcd_isUnit_iff N' b').mp hu
  have h2 : N' ^ 2 ∣ b' ^ 2 * f := by
    rw [hN', hb', mul_pow, mul_pow, mul_assoc] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).mp h
  have h3 : N' ^ 2 ∣ f := (hcop.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left h2
  have hunit : IsUnit N' := hf N' (by rw [← sq]; exact h3)
  rw [hN', hb']
  exact mul_dvd_mul_left g hunit.dvd

lemma algebraMap_eq_smul (p : K[X]) :
    algebraMap K[X] (CR a₂ a₄ a₆) p = p • (1 : CR a₂ a₄ a₆) := Algebra.algebraMap_eq_smul_one p

lemma eval₂_polynomial {T : Type*} [CommRing T] (i : K[X] →+* T) (z : T) :
    (Wc a₂ a₄ a₆).polynomial.eval₂ i z = z ^ 2 - i (fc a₂ a₄ a₆) := by
  simp [WeierstrassCurve.Affine.polynomial, fc, eval₂_pow, eval₂_C]

lemma aeval_neg_y :
    (Wc a₂ a₄ a₆).polynomial.eval₂ (Algebra.ofId K[X] (CR a₂ a₄ a₆)) (-yR a₂ a₄ a₆) = 0 := by
  rw [eval₂_polynomial, neg_sq, y_sq]
  simp

/-- The conjugation `y ↦ -y`. -/
noncomputable def conj : CR a₂ a₄ a₆ →ₐ[K[X]] CR a₂ a₄ a₆ :=
  AdjoinRoot.liftAlgHom (Wc a₂ a₄ a₆).polynomial (Algebra.ofId K[X] (CR a₂ a₄ a₆)) (-yR a₂ a₄ a₆)
    (aeval_neg_y a₂ a₄ a₆)

lemma conj_y : conj a₂ a₄ a₆ (yR a₂ a₄ a₆) = -yR a₂ a₄ a₆ := by
  simp only [conj, yR, AdjoinRoot.mk_X, AdjoinRoot.liftAlgHom_root]

lemma conj_conj (r : CR a₂ a₄ a₆) : conj a₂ a₄ a₆ (conj a₂ a₄ a₆ r) = r := by
  have : (conj a₂ a₄ a₆).comp (conj a₂ a₄ a₆) = AlgHom.id _ _ := by
    apply AdjoinRoot.algHom_ext
    change conj a₂ a₄ a₆ (conj a₂ a₄ a₆ (yR a₂ a₄ a₆)) = yR a₂ a₄ a₆
    rw [conj_y, map_neg, conj_y, neg_neg]
  exact congrArg (fun φ : CR a₂ a₄ a₆ →ₐ[K[X]] CR a₂ a₄ a₆ ↦ φ r) this

lemma conj_smul (p q : K[X]) :
    conj a₂ a₄ a₆ (p • (1 : CR a₂ a₄ a₆) + q • yR a₂ a₄ a₆) =
      p • (1 : CR a₂ a₄ a₆) - q • yR a₂ a₄ a₆ := by
  rw [map_add, map_smul, map_smul, map_one, conj_y, smul_neg, sub_eq_add_neg]

instance : Module.Finite K[X] (CR a₂ a₄ a₆) :=
  Module.Finite.of_basis (CoordinateRing.basis (Wc a₂ a₄ a₆))

instance : Algebra.IsIntegral K[X] (CR a₂ a₄ a₆) := Algebra.IsIntegral.of_finite _ _

lemma smul_one_add (p q : K[X]) :
    p • (1 : CR a₂ a₄ a₆) + q • yR a₂ a₄ a₆ =
      algebraMap K[X] (CR a₂ a₄ a₆) p + algebraMap K[X] (CR a₂ a₄ a₆) q * yR a₂ a₄ a₆ := by
  rw [Algebra.smul_def, Algebra.smul_def, mul_one]

set_option maxHeartbeats 800000 in
theorem isIntegrallyClosed_CR (hsq : Squarefree (fc a₂ a₄ a₆)) :
    IsIntegrallyClosed (CR a₂ a₄ a₆) := by
  classical
  set L := FractionRing (CR a₂ a₄ a₆)
  set y := yR a₂ a₄ a₆
  set f := fc a₂ a₄ a₆
  set σ := conj a₂ a₄ a₆
  rw [isIntegrallyClosed_iff L]
  intro x hx
  have hxK : IsIntegral K[X] x := isIntegral_trans (R := K[X]) _ hx
  have hinjRL : Function.Injective (algebraMap (CR a₂ a₄ a₆) L) := IsFractionRing.injective _ _
  have hinjKR : Function.Injective (algebraMap K[X] (CR a₂ a₄ a₆)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hAL : ∀ c : K[X], algebraMap K[X] L c = algebraMap (CR a₂ a₄ a₆) L (algebraMap K[X] _ c) :=
    fun c ↦ IsScalarTower.algebraMap_apply K[X] (CR a₂ a₄ a₆) L c
  have hinjKL : Function.Injective (algebraMap K[X] L) := by
    rw [IsScalarTower.algebraMap_eq K[X] (CR a₂ a₄ a₆) L]; exact hinjRL.comp hinjKR
  set A := algebraMap K[X] L
  set yL := algebraMap (CR a₂ a₄ a₆) L y
  have hyL : yL ^ 2 = A f := by rw [← map_pow, y_sq, ← hAL]
  -- `x = (a + b y) / N`
  obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := CR a₂ a₄ a₆) x
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq (W' := Wc a₂ a₄ a₆) v
  set N := p ^ 2 - q ^ 2 * f with hN
  have hvv : (p • (1 : CR a₂ a₄ a₆) + q • y) * (p • 1 - q • y) = algebraMap K[X] _ N := by
    simp only [Algebra.smul_def, mul_one]
    rw [hN, map_sub, map_mul, map_pow, map_pow, ← y_sq]
    ring
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvv
    have hv' : p • (1 : CR a₂ a₄ a₆) - q • y = 0 := (mul_eq_zero.mp hvv).resolve_left hv0
    rw [sub_eq_add_neg, ← neg_smul] at hv'
    obtain ⟨hp, hq⟩ := smul_basis_eq_zero hv'
    apply hv0
    rw [hp, neg_eq_zero.mp hq, zero_smul, zero_smul, add_zero]
  obtain ⟨a, b, hab⟩ := exists_smul_basis_eq (W' := Wc a₂ a₄ a₆) (u * (p • 1 - q • y))
  have hAN : A N ≠ 0 := (map_ne_zero_iff _ hinjKL).mpr hN0
  have hx : algebraMap (CR a₂ a₄ a₆) L u / algebraMap (CR a₂ a₄ a₆) L (p • 1 + q • y) =
      (A a + A b * yL) / A N := by
    have hv'0 : p • (1 : CR a₂ a₄ a₆) - q • y ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hvv
      exact hN0 (hinjKR (by rw [← hvv, map_zero]))
    have e1 : algebraMap (CR a₂ a₄ a₆) L (u * (p • 1 - q • y)) = A a + A b * yL := by
      rw [← hab, smul_one_add, map_add, map_mul, ← hAL, ← hAL]
    have e2 : algebraMap (CR a₂ a₄ a₆) L ((p • 1 + q • y) * (p • 1 - q • y)) = A N := by
      rw [hvv, ← hAL]
    rw [← e1, ← e2, map_mul, map_mul, mul_div_mul_right _ _
      ((map_ne_zero_iff _ hinjRL).mpr hv'0)]
  rw [hx] at hxK ⊢
  -- the conjugation on `L`
  have hinjσ : Function.Injective ((algebraMap (CR a₂ a₄ a₆) L).comp σ.toRingHom) := by
    refine hinjRL.comp fun r s h ↦ ?_
    have := congrArg σ h
    simpa [σ, conj_conj] using this
  set σL : L →+* L := IsFractionRing.lift hinjσ
  have hσL : ∀ r, σL (algebraMap (CR a₂ a₄ a₆) L r) = algebraMap (CR a₂ a₄ a₆) L (σ r) :=
    fun r ↦ IsFractionRing.lift_algebraMap hinjσ r
  have hσA : ∀ c, σL (A c) = A c := fun c ↦ by
    rw [hAL, hσL, AlgHom.commutes]
  have hσy : σL yL = -yL := by rw [hσL, conj_y, map_neg]
  have hσcomp : σL.comp A = A := RingHom.ext hσA
  have hx'int : IsIntegral K[X] ((A a - A b * yL) / A N) := by
    obtain ⟨P, hPm, hP⟩ := hxK
    refine ⟨P, hPm, ?_⟩
    have := congrArg σL hP
    rw [hom_eval₂, hσcomp, map_zero] at this
    convert this using 2
    rw [map_div₀, map_add, map_mul, hσA, hσA, hσA, hσy]
    ring
  -- trace and norm are in `K[X]`
  have hι : Function.Injective (Algebra.ofId K[X] L) := hinjKL
  set ι := IsFractionRing.liftAlgHom (K := FractionRing K[X]) hι
  have hιA : ∀ c : K[X], ι (algebraMap K[X] (FractionRing K[X]) c) = A c := fun c ↦ by
    rw [IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap]; rfl
  set B := algebraMap K[X] (FractionRing K[X])
  have hinjB : Function.Injective B := IsFractionRing.injective _ _
  have hBN : B N ≠ 0 := (map_ne_zero_iff _ hinjB).mpr hN0
  have htr : IsIntegral K[X] (B (2 * a) / B N) := by
    rw [← isIntegral_algHom_iff ι ι.injective, map_div₀, hιA, hιA]
    have := hxK.add hx'int
    convert this using 1
    rw [map_mul, map_ofNat, ← add_div]
    ring
  have hnm : IsIntegral K[X] (B (a ^ 2 - b ^ 2 * f) / B (N ^ 2)) := by
    rw [← isIntegral_algHom_iff ι ι.injective, map_div₀, hιA, hιA]
    have := hxK.mul hx'int
    convert this using 1
    rw [map_sub, map_mul, map_pow, map_pow, map_pow, div_mul_div_comm, ← hyL]
    ring
  obtain ⟨e, he⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnm
  have he' : e * N = 2 * a := by
    apply hinjB
    rw [map_mul, he, div_mul_cancel₀ _ hBN]
  have hg' : g * N ^ 2 = a ^ 2 - b ^ 2 * f := by
    apply hinjB
    rw [map_mul, hg, div_mul_cancel₀ _ ((map_ne_zero_iff _ hinjB).mpr (pow_ne_zero 2 hN0))]
  -- `N ∣ a`, `N ∣ b`
  have ha : N ∣ a := by
    refine ⟨C (1 / 2 : K) * e, ?_⟩
    have h2 : (C (1 / 2 : K) * 2 : K[X]) = 1 := by
      rw [← map_ofNat C 2, ← C_mul]; norm_num
    linear_combination -(C (1 / 2 : K)) * he' - a * h2
  obtain ⟨a1, rfl⟩ := ha
  have hb : N ∣ b := by
    refine dvd_of_sq_dvd_sq_mul_sqf hsq hN0 ⟨a1 ^ 2 - g, ?_⟩
    linear_combination hg'
  obtain ⟨b1, rfl⟩ := hb
  refine ⟨a1 • (1 : CR a₂ a₄ a₆) + b1 • y, ?_⟩
  rw [smul_one_add, map_add, map_mul, ← hAL, ← hAL, map_mul, map_mul, eq_div_iff hAN]
  ring

instance : IsNoetherianRing (CR a₂ a₄ a₆) := IsNoetherianRing.of_finite K[X] _

instance : Ring.DimensionLEOne (CR a₂ a₄ a₆) := Ring.DimensionLEOne.of_isIntegral K[X] _

end EllDedekind

open Polynomial in
/-- **The coordinate ring of `y² = x³ + a₂x² + a₄x + a₆` (squarefree cubic, characteristic zero) is
a Dedekind domain.** -/
theorem isDedekindDomain_coordinateRing {K : Type*} [Field K] [CharZero K] (a₂ a₄ a₆ : K)
    (hsq : Squarefree (X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆ : K[X])) :
    IsDedekindDomain (WeierstrassCurve.toAffine (⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve K)).CoordinateRing :=
  have := EllDedekind.isIntegrallyClosed_CR a₂ a₄ a₆ hsq
  { (inferInstance : IsNoetherianRing (EllDedekind.CR a₂ a₄ a₆)),
    (inferInstance : Ring.DimensionLEOne (EllDedekind.CR a₂ a₄ a₆)),
    this with : IsDedekindDomain (EllDedekind.CR a₂ a₄ a₆) }
