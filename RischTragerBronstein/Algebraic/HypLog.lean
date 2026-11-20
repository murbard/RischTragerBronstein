import RischTragerBronstein.Algebraic.HypCert
import RischTragerBronstein.Elementary.LiouvilleForm

/-!
# Hyperelliptic integrals with a logarithmic part: certified antiderivatives

`hyp_log_cert`: if `A / (D y) = (W/V · y)′ + (1/K) (u′ / u)` with `u = (a + b y) / d`, which
amounts to the polynomial identities (`N = a² - b² p`, `M = 2p(ab′ - a′b) + abp′`)

  `N′ d = 2 N d′`  (the `C(x)`-component: `N ∝ d²`), and
  `2 A V² N K = D (K N (2(W′V - WV′)p + WVp′) + V² M)`  (the `y`-component),

then `∫ A / (D y) dx = (W/V) y + (1/K) log u` is elementary. This certifies the *elementary* answer
for integrands with a genuine logarithmic part (the non-elementary answer for those needs the torsion
test for divisors on the curve). Example: `∫ dx / (x √(x³+1)) = (1/3) log ((√(x³+1) - 1)² / x³)`.
-/

open Polynomial

namespace Differential

section LogCert

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Certified antiderivatives with a logarithmic part.** -/
theorem hyp_log_cert (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (A D W V a b d : ℚ[X]) (K : ℚ)
    (hD : D ≠ 0) (hV : V ≠ 0) (hd : d ≠ 0) (hK : K ≠ 0) (hN : a ^ 2 - b ^ 2 * p ≠ 0)
    (h1 : derivative (a ^ 2 - b ^ 2 * p) * d = 2 * (a ^ 2 - b ^ 2 * p) * derivative d)
    (h2 : 2 * A * V ^ 2 * (a ^ 2 - b ^ 2 * p) * C K = D * (C K * (a ^ 2 - b ^ 2 * p) *
      (2 * (derivative W * V - W * derivative V) * p + W * V * derivative p) +
        V ^ 2 * (2 * p * (a * derivative b - derivative a * b) + a * b * derivative p))) :
    HasElementaryIntegral (aeval x A / (aeval x D * y)) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hP0 := hne p hp0
  have hy0 : y ≠ 0 := by rintro rfl; apply hP0; rw [← hy]; ring
  set r := aeval x (derivative p) / (2 * (aeval x p)) with hr
  have hyd : y′ = r * y := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [deriv_aeval_rat x hx] at this
    rw [hr, ← hy]
    field_simp
    linear_combination this
  have hNx : (aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p) ≠ 0 := by
    have := hne _ hN; simpa using this
  have hab0 : (aeval x a) + (aeval x b) * y ≠ 0 := by
    intro h0; apply hNx
    rw [← hy, show (aeval x a) = -((aeval x b) * y) by linear_combination h0]; ring
  have hdx := hne d hd
  -- the components of `u′ / u`
  have hld : logDeriv (((aeval x a) + (aeval x b) * y) / aeval x d) =
      (((aeval x a) * (aeval x a)′ - (aeval x b) * ((aeval x b)′ + (aeval x b) * r) * (aeval x p)) / ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p)) -
        aeval x (derivative d) / aeval x d) +
      (((aeval x a) * ((aeval x b)′ + (aeval x b) * r) - (aeval x a)′ * (aeval x b)) / ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p))) * y := by
    rw [logDeriv_div _ _ hab0 hdx, logDeriv_ab y (aeval x a) (aeval x b) (aeval x p) r hy hyd hNx]
    unfold logDeriv
    rw [deriv_aeval_rat x hx d]
    ring
  have hax' : (aeval x a)′ = aeval x (derivative a) := deriv_aeval_rat x hx a
  have hbx' : (aeval x b)′ = aeval x (derivative b) := deriv_aeval_rat x hx b
  -- the `C(x)`-component vanishes
  have hc0 : ((aeval x a) * (aeval x a)′ - (aeval x b) * ((aeval x b)′ + (aeval x b) * r) * (aeval x p)) / ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p)) -
      aeval x (derivative d) / aeval x d = 0 := by
    have e1 := congrArg (aeval x) h1
    simp only [map_mul, map_sub, map_pow, map_ofNat, derivative_mul,
      derivative_pow, map_add, map_natCast] at e1
    rw [hax', hbx', hr]
    field_simp
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at e1
    linear_combination e1
  have hVx := hne V hV
  have hDx := hne D hD
  have hKx : (K : E) ≠ 0 := by exact_mod_cast hK
  have hcoef : aeval x A / (aeval x D * (aeval x p)) =
      (aeval x (derivative W) * aeval x V - aeval x W * aeval x (derivative V)) / aeval x V ^ 2 +
        aeval x W / aeval x V * r + ((1 / K : ℚ) : E) *
          (((aeval x a) * (aeval x (derivative b) + (aeval x b) * r) -
            aeval x (derivative a) * (aeval x b)) /
            ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p))) := by
    have e2 := congrArg (aeval x) h2
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, aeval_C, eq_ratCast] at e2
    rw [hr]
    push_cast
    have hNx' : (aeval x a) ^ 2 - (aeval x p) * (aeval x b) ^ 2 ≠ 0 := by
      rw [mul_comm]; exact hNx
    field_simp
    linear_combination e2
  have hinv : aeval x A / (aeval x D * y) = aeval x A / (aeval x D * (aeval x p)) * y := by
    rw [← hy]; field_simp
  have key : aeval x A / (aeval x D * y) =
      (aeval x W / aeval x V * y)′ + ((1 / K : ℚ) : E) *
        logDeriv (((aeval x a) + (aeval x b) * y) / aeval x d) := by
    rw [hinv, hld, hc0, zero_add, Derivation.leibniz, Derivation.leibniz_div, hyd,
      deriv_aeval_rat x hx W, deriv_aeval_rat x hx V, hbx', hax', hcoef]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [key]
  have := hasElementaryIntegral_of_liouville_form (aeval x W / aeval x V * y)
    [(((1 / K : ℚ) : E), ((aeval x a) + (aeval x b) * y) / aeval x d)] (by
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨deriv_ratCast_L _, div_ne_zero hab0 hdx⟩)
  simpa using this

end LogCert

end Differential
