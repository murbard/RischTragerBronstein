import RischTragerBronstein.Algebraic.HypLog
import RischTragerBronstein.Elementary.Sum
import RischTragerBronstein.Elementary.SqrtExt

/-!
# Removing a logarithmic part: `∫ G/y` versus `∫ R/y`

For `u = a + b y` (`y² = p`) with norm `N = a² − b² p ≠ 0` and `M = 2p(ab′ − a′b) + abp′`,

  `u′ / u = N′ / (2N) + M / (2N y)`.

So if `G = c M / N + R` (a polynomial identity after clearing denominators, checked by the
kernel), then `G / y = R / y + 2c · u′/u − c · N′/N`, and `∫ G/y` is elementary **iff** `∫ R/y` is
(`ell_log_reduce`). With `u` chosen so that `c M / N` carries all the residues of `G`, `R` is a
polynomial and `hyp_decides` finishes the decision.
-/

open Polynomial

namespace Differential

section EllLog

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

omit [CharZero E] in
/-- A constant combination of two logarithmic derivatives is integrable in every extension. -/
theorem hasElementaryIntegralIn_logDeriv₂ {F : Type*} [Field F] [Differential F] (c₁ c₂ u₁ u₂ : F)
    (hc₁ : c₁′ = 0) (hc₂ : c₂′ = 0) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    HasElementaryIntegralIn (c₁ * logDeriv u₁ + c₂ * logDeriv u₂) := by
  intro E' _ _ _ _ _
  have hl : ∀ u : F, algebraMap F E' (logDeriv u) = logDeriv (algebraMap F E' u) := fun u ↦ by
    unfold logDeriv
    rw [map_div₀, deriv_algebraMap]
  have := hasElementaryIntegral_of_liouville_form (0 : E')
    [(algebraMap F E' c₁, algebraMap F E' u₁), (algebraMap F E' c₂, algebraMap F E' u₂)] (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨by rw [deriv_algebraMap, hc₁, map_zero],
          (map_ne_zero_iff _ (algebraMap F E').injective).mpr hu₁⟩
      · exact ⟨by rw [deriv_algebraMap, hc₂, map_zero],
          (map_ne_zero_iff _ (algebraMap F E').injective).mpr hu₂⟩)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_zero,
    zero_add] at this
  rw [map_add, map_mul, map_mul, hl, hl]
  exact this

/-- **The logarithmic part as a decomposition.** If `Gn · N = Gd · (c M + R N)` then
`Gn / (Gd y) = R / y + w` with `w` elementary-integrable in every elementary extension. -/
theorem ell_log_decomp (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (Gn Gd a b R : ℚ[X]) (c : ℚ) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - b ^ 2 * p) = Gd * (C c * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - b ^ 2 * p))) :
    ∃ w : E, HasElementaryIntegralIn w ∧ aeval x Gn / (aeval x Gd * y) = aeval x R / y + w := by
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
  have hGdx := hne Gd hGd
  have hax' : (aeval x a)′ = aeval x (derivative a) := deriv_aeval_rat x hx a
  have hbx' : (aeval x b)′ = aeval x (derivative b) := deriv_aeval_rat x hx b
  have hNd : logDeriv ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p)) =
      aeval x (derivative (a ^ 2 - b ^ 2 * p)) / ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p)) := by
    unfold logDeriv
    rw [show (aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p) = aeval x (a ^ 2 - b ^ 2 * p) by simp,
      deriv_aeval_rat x hx]
  have key : aeval x Gn / (aeval x Gd * y) = aeval x R / y +
      (((2 * c : ℚ) : E) * logDeriv ((aeval x a) + (aeval x b) * y) +
        ((-c : ℚ) : E) * logDeriv ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p))) := by
    rw [logDeriv_ab y (aeval x a) (aeval x b) (aeval x p) r hy hyd hNx, hNd, hax', hbx', hr]
    have e := congrArg (aeval x) hid
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, aeval_C, eq_ratCast,
      derivative_mul, derivative_sub, derivative_pow, map_natCast, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one] at e ⊢
    push_cast
    have hNx' : (aeval x a) ^ 2 - (aeval x p) * (aeval x b) ^ 2 ≠ 0 := by
      rw [mul_comm]; exact hNx
    set A := aeval x a
    set B := aeval x b
    set P := aeval x p
    have hl : aeval x Gn / (aeval x Gd * y) = aeval x Gn / (aeval x Gd * P) * y := by
      rw [← hy]; field_simp
    have hr' : aeval x R / y = aeval x R / P * y := by rw [← hy]; field_simp
    have h0 : 2 * (c : E) * ((A * aeval x (derivative a) - B * (aeval x (derivative b) +
        B * (aeval x (derivative p) / (2 * P))) * P) / (A ^ 2 - B ^ 2 * P)) +
        -(c : E) * ((2 * A * aeval x (derivative a) - (2 * B * aeval x (derivative b) * P +
          B ^ 2 * aeval x (derivative p))) / (A ^ 2 - B ^ 2 * P)) = 0 := by
      field_simp; ring
    have h1 : aeval x Gn / (aeval x Gd * P) = aeval x R / P + 2 * (c : E) *
        ((A * (aeval x (derivative b) + B * (aeval x (derivative p) / (2 * P))) -
          aeval x (derivative a) * B) / (A ^ 2 - B ^ 2 * P)) := by
      field_simp
      linear_combination e
    rw [hl, hr', h1]
    have hPP : P * P⁻¹ = 1 := mul_inv_cancel₀ hP0
    linear_combination h0 + ((c : E) * B ^ 2 * aeval x (derivative p) *
      (-(P * B ^ 2) + A ^ 2)⁻¹ * 2) * hPP
  exact ⟨_, hasElementaryIntegralIn_logDeriv₂ (((2 * c : ℚ) : E)) (((-c : ℚ) : E))
    ((aeval x a) + (aeval x b) * y) ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p))
    (deriv_ratCast_L _) (deriv_ratCast_L _) hab0 hNx, key⟩

/-- **Removing a logarithmic part.** If `Gn · N = Gd · (c M + R N)` then `∫ Gn / (Gd y)` is
elementary iff `∫ R / y` is. -/
theorem ell_log_reduce (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (Gn Gd a b R : ℚ[X]) (c : ℚ) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - b ^ 2 * p) = Gd * (C c * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - b ^ 2 * p))) :
    HasElementaryIntegral (aeval x Gn / (aeval x Gd * y)) ↔
      HasElementaryIntegral (aeval x R / y) := by
  obtain ⟨w, hL, key⟩ := ell_log_decomp hC x y hx p hp0 hy Gn Gd a b R c hGd hN hid
  rw [key]
  constructor
  · intro h
    have := h.sub_in hL
    rwa [add_sub_cancel_right] at this
  · intro h
    exact h.add_in hL

/-- `ell_log_reduce` with an arbitrary extra summand. -/
theorem ell_log_reduce_add (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (Gn Gd a b R : ℚ[X]) (c : ℚ) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - b ^ 2 * p) = Gd * (C c * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - b ^ 2 * p))) (f : E) :
    HasElementaryIntegral (f + aeval x Gn / (aeval x Gd * y)) ↔
      HasElementaryIntegral (f + aeval x R / y) := by
  obtain ⟨w, hL, key⟩ := ell_log_decomp hC x y hx p hp0 hy Gn Gd a b R c hGd hN hid
  rw [key, ← add_assoc]
  constructor
  · intro h
    have := h.sub_in hL
    rwa [add_sub_cancel_right] at this
  · intro h
    exact h.add_in hL

omit [CharZero E] in
/-- Multiplying by a non-zero constant does not change elementary integrability. -/
lemma hasElementaryIntegral_const_mul_iff {F : Type*} [Field F] [Differential F] (c f : F)
    (hc : c′ = 0) (hc0 : c ≠ 0) : HasElementaryIntegral (c * f) ↔ HasElementaryIntegral f := by
  have key : ∀ (c f : F), c′ = 0 → HasElementaryIntegral f → HasElementaryIntegral (c * f) := by
    intro c f hc h
    obtain ⟨L, _, _, _, _, hE, g, hg⟩ := h
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hE,
      algebraMap F L c * g, ?_⟩
    rw [Derivation.leibniz, deriv_algebraMap, hc, map_zero, smul_zero, add_zero, hg, smul_eq_mul,
      map_mul]
  refine ⟨fun h ↦ ?_, key c f hc⟩
  have h' := key c⁻¹ (c * f) (by rw [Derivation.leibniz_inv, hc]; simp) h
  rwa [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at h'

/-- **Removing a logarithmic part, twisted**: `u = a + s b y` with `s′ = 0`, `s² = d`;
if `Gn · N = Gd · (q M + R N)` (`N = a² − d b² p`) then `∫ Gn / (Gd y)` is elementary iff
`∫ R / y` is. (Apply `ell_log_reduce` to `y' = s y`, `y'² = d p`.) -/
theorem ell_log_reduce_twist (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (s : E) (hs : s′ = 0) (d : ℚ) (hsd : s ^ 2 = d)
    (hs0 : s ≠ 0) (Gn Gd a b R : ℚ[X]) (q : ℚ) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - C d * b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - C d * b ^ 2 * p) = Gd * (C q * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - C d * b ^ 2 * p))) :
    HasElementaryIntegral (aeval x Gn / (aeval x Gd * y)) ↔
      HasElementaryIntegral (aeval x R / y) := by
  have hd0 : d ≠ 0 := by
    rintro rfl; apply hs0; simpa using hsd
  have hy' : (s * y) ^ 2 = aeval x (C d * p) := by
    rw [mul_pow, hsd, hy, map_mul, aeval_C, eq_ratCast]
  have hp0' : C d * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hd0) hp0
  have hred := ell_log_reduce hC x (s * y) hx (C d * p) hp0' hy' Gn Gd a b R (q / d) hGd
    (by rw [show a ^ 2 - b ^ 2 * (C d * p) = a ^ 2 - C d * b ^ 2 * p by ring]; exact hN) (by
      have hq : C (q / d) * C d = C q := by rw [← C_mul, div_mul_cancel₀ q hd0]
      rw [derivative_mul, derivative_C, zero_mul, zero_add]
      linear_combination hid - Gd * (2 * p * (a * derivative b - derivative a * b) +
        a * b * derivative p) * hq)
  have e1 : aeval x Gn / (aeval x Gd * (s * y)) = s⁻¹ * (aeval x Gn / (aeval x Gd * y)) := by
    field_simp
  have e2 : aeval x R / (s * y) = s⁻¹ * (aeval x R / y) := by field_simp
  have hsi : s⁻¹′ = 0 := by rw [Derivation.leibniz_inv, hs]; simp
  rw [e1, e2, hasElementaryIntegral_const_mul_iff _ _ hsi (inv_ne_zero hs0),
    hasElementaryIntegral_const_mul_iff _ _ hsi (inv_ne_zero hs0)] at hred
  exact hred

/-- **Removing a twisted logarithmic part, no `√d` needed in the base**: passing to
`L(√d)` for the elementary extension `L` witnessing either side. -/
theorem ell_log_reduce_twist' (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (d : ℚ) (hd0 : d ≠ 0)
    (Gn Gd a b R : ℚ[X]) (q : ℚ) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - C d * b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - C d * b ^ 2 * p) = Gd * (C q * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - C d * b ^ 2 * p))) :
    HasElementaryIntegral (aeval x Gn / (aeval x Gd * y)) ↔
      HasElementaryIntegral (aeval x R / y) := by
  -- transfer through `L(√d)` for any elementary extension `L` of `E`
  have transfer : ∀ (f₁ f₂ : E), (∀ {M : Type _} [Field M] [Differential M] [Algebra E M]
      [DifferentialAlgebra E M] [CharZero M] (s : M), s′ = 0 → s ^ 2 = ((d : ℚ) : M) → s ≠ 0 →
        HasElementaryIntegral (algebraMap E M f₁) → HasElementaryIntegral (algebraMap E M f₂)) →
      HasElementaryIntegral f₁ → HasElementaryIntegral f₂ := by
    intro f₁ f₂ hT h1
    obtain ⟨L0, _, _, _, _, hE0, g, hg⟩ := h1
    have : CharZero L0 := charZero_of_injective_algebraMap (algebraMap E L0).injective
    obtain ⟨L, _, _, _, _, hEL, sq, hsq2, hsq', -⟩ := exists_sqrt_ext (((d : ℚ) : L0))
      (deriv_ratCast_L _) (by exact_mod_cast hd0)
    letI : Algebra E L := ((algebraMap L0 L).comp (algebraMap E L0)).toAlgebra
    haveI : IsScalarTower E L0 L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hDA : DifferentialAlgebra E L :=
      ⟨fun a ↦ by
        change (algebraMap L0 L (algebraMap E L0 a))′ = algebraMap L0 L (algebraMap E L0 a′)
        rw [deriv_algebraMap, deriv_algebraMap]⟩
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
    have hsq2' : sq ^ 2 = ((d : ℚ) : L) := by rw [hsq2, map_ratCast]
    have hs0 : sq ≠ 0 := by
      intro h0; apply hd0; have : ((d : ℚ) : L) = 0 := by rw [← hsq2', h0]; ring
      exact_mod_cast this
    have hL : HasElementaryIntegral (algebraMap E L f₁) := by
      have := hasElementaryIntegral_of_deriv (algebraMap L0 L g)
      rwa [deriv_algebraMap, hg] at this
    exact HasElementaryIntegral.of_extension (hE0.trans hEL) (hT sq hsq' hsq2' hs0 hL)
  -- the identity in any extension containing `√d`
  have inM : ∀ {M : Type _} [Field M] [Differential M] [Algebra E M] [DifferentialAlgebra E M]
      [CharZero M] (s : M), s′ = 0 → s ^ 2 = ((d : ℚ) : M) → s ≠ 0 →
      (HasElementaryIntegral (algebraMap E M (aeval x Gn / (aeval x Gd * y))) ↔
        HasElementaryIntegral (algebraMap E M (aeval x R / y))) := by
    intro M _ _ _ _ _ s hs hsd hs0
    letI : Algebra Kc M := ((algebraMap E M).comp (algebraMap Kc E)).toAlgebra
    have hDA : DifferentialAlgebra Kc M :=
      ⟨fun r ↦ by
        change (algebraMap E M (algebraMap Kc E r))′ = algebraMap E M (algebraMap Kc E r′)
        rw [deriv_algebraMap, deriv_algebraMap]⟩
    have hxM : (algebraMap E M x)′ = 1 := by rw [deriv_algebraMap, hx, map_one]
    have hyM : (algebraMap E M y) ^ 2 = aeval (algebraMap E M x) p := by
      rw [← map_pow, hy, aeval_algebraMap_apply]
    have key := ell_log_reduce_twist hC (algebraMap E M x) (algebraMap E M y) hxM p hp0 hyM s hs d
      hsd hs0 Gn Gd a b R q hGd hN hid
    simpa only [map_div₀, map_mul, aeval_algebraMap_apply] using key
  exact ⟨transfer _ _ fun s hs hsd hs0 h ↦ (inM s hs hsd hs0).mp h,
    transfer _ _ fun s hs hsd hs0 h ↦ (inM s hs hsd hs0).mpr h⟩

/-- `ell_log_reduce_twist` with an arbitrary extra summand. -/
theorem ell_log_reduce_twist_add (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (s : E) (hs : s′ = 0) (d : ℚ) (hsd : s ^ 2 = d)
    (hs0 : s ≠ 0) (Gn Gd a b R : ℚ[X]) (q : ℚ) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - C d * b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - C d * b ^ 2 * p) = Gd * (C q * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - C d * b ^ 2 * p))) (f : E) :
    HasElementaryIntegral (f + aeval x Gn / (aeval x Gd * y)) ↔
      HasElementaryIntegral (f + aeval x R / y) := by
  have hd0 : d ≠ 0 := by
    rintro rfl; apply hs0; simpa using hsd
  have hy' : (s * y) ^ 2 = aeval x (C d * p) := by
    rw [mul_pow, hsd, hy, map_mul, aeval_C, eq_ratCast]
  have hp0' : C d * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hd0) hp0
  have hred := ell_log_reduce_add hC x (s * y) hx (C d * p) hp0' hy' Gn Gd a b R (q / d) hGd
    (by rw [show a ^ 2 - b ^ 2 * (C d * p) = a ^ 2 - C d * b ^ 2 * p by ring]; exact hN) (by
      have hq : C (q / d) * C d = C q := by rw [← C_mul, div_mul_cancel₀ q hd0]
      rw [derivative_mul, derivative_C, zero_mul, zero_add]
      linear_combination hid - Gd * (2 * p * (a * derivative b - derivative a * b) +
        a * b * derivative p) * hq) (s⁻¹ * f)
  have e1 : s⁻¹ * f + aeval x Gn / (aeval x Gd * (s * y)) =
      s⁻¹ * (f + aeval x Gn / (aeval x Gd * y)) := by
    rw [mul_add]; congr 1; field_simp
  have e2 : s⁻¹ * f + aeval x R / (s * y) = s⁻¹ * (f + aeval x R / y) := by
    rw [mul_add]; congr 1; field_simp
  have hsi : s⁻¹′ = 0 := by rw [Derivation.leibniz_inv, hs]; simp
  rw [e1, e2, hasElementaryIntegral_const_mul_iff _ _ hsi (inv_ne_zero hs0),
    hasElementaryIntegral_const_mul_iff _ _ hsi (inv_ne_zero hs0)] at hred
  exact hred

/-- `ell_log_reduce_twist'` with an arbitrary extra summand. -/
theorem ell_log_reduce_twist'_add (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : ℚ[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (d : ℚ) (hd0 : d ≠ 0)
    (Gn Gd a b R : ℚ[X]) (q : ℚ) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - C d * b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - C d * b ^ 2 * p) = Gd * (C q * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - C d * b ^ 2 * p))) (f : E) :
    HasElementaryIntegral (f + aeval x Gn / (aeval x Gd * y)) ↔
      HasElementaryIntegral (f + aeval x R / y) := by
  have transfer : ∀ (f₁ f₂ : E), (∀ {M : Type _} [Field M] [Differential M] [Algebra E M]
      [DifferentialAlgebra E M] [CharZero M] (s : M), s′ = 0 → s ^ 2 = ((d : ℚ) : M) → s ≠ 0 →
        HasElementaryIntegral (algebraMap E M f₁) → HasElementaryIntegral (algebraMap E M f₂)) →
      HasElementaryIntegral f₁ → HasElementaryIntegral f₂ := by
    intro f₁ f₂ hT h1
    obtain ⟨L0, _, _, _, _, hE0, g, hg⟩ := h1
    have : CharZero L0 := charZero_of_injective_algebraMap (algebraMap E L0).injective
    obtain ⟨L, _, _, _, _, hEL, sq, hsq2, hsq', -⟩ := exists_sqrt_ext (((d : ℚ) : L0))
      (deriv_ratCast_L _) (by exact_mod_cast hd0)
    letI : Algebra E L := ((algebraMap L0 L).comp (algebraMap E L0)).toAlgebra
    haveI : IsScalarTower E L0 L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hDA : DifferentialAlgebra E L :=
      ⟨fun a ↦ by
        change (algebraMap L0 L (algebraMap E L0 a))′ = algebraMap L0 L (algebraMap E L0 a′)
        rw [deriv_algebraMap, deriv_algebraMap]⟩
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
    have hsq2' : sq ^ 2 = ((d : ℚ) : L) := by rw [hsq2, map_ratCast]
    have hs0 : sq ≠ 0 := by
      intro h0; apply hd0; have : ((d : ℚ) : L) = 0 := by rw [← hsq2', h0]; ring
      exact_mod_cast this
    have hL : HasElementaryIntegral (algebraMap E L f₁) := by
      have := hasElementaryIntegral_of_deriv (algebraMap L0 L g)
      rwa [deriv_algebraMap, hg] at this
    exact HasElementaryIntegral.of_extension (hE0.trans hEL) (hT sq hsq' hsq2' hs0 hL)
  have inM : ∀ {M : Type _} [Field M] [Differential M] [Algebra E M] [DifferentialAlgebra E M]
      [CharZero M] (s : M), s′ = 0 → s ^ 2 = ((d : ℚ) : M) → s ≠ 0 →
      (HasElementaryIntegral (algebraMap E M (f + aeval x Gn / (aeval x Gd * y))) ↔
        HasElementaryIntegral (algebraMap E M (f + aeval x R / y))) := by
    intro M _ _ _ _ _ s hs hsd hs0
    letI : Algebra Kc M := ((algebraMap E M).comp (algebraMap Kc E)).toAlgebra
    have hDA : DifferentialAlgebra Kc M :=
      ⟨fun r ↦ by
        change (algebraMap E M (algebraMap Kc E r))′ = algebraMap E M (algebraMap Kc E r′)
        rw [deriv_algebraMap, deriv_algebraMap]⟩
    have hxM : (algebraMap E M x)′ = 1 := by rw [deriv_algebraMap, hx, map_one]
    have hyM : (algebraMap E M y) ^ 2 = aeval (algebraMap E M x) p := by
      rw [← map_pow, hy, aeval_algebraMap_apply]
    have key := ell_log_reduce_twist_add hC (algebraMap E M x) (algebraMap E M y) hxM p hp0 hyM
      s hs d hsd hs0 Gn Gd a b R q hGd hN hid (algebraMap E M f)
    simpa only [map_add, map_div₀, map_mul, aeval_algebraMap_apply] using key
  exact ⟨transfer _ _ fun s hs hsd hs0 h ↦ (inM s hs hsd hs0).mp h,
    transfer _ _ fun s hs hsd hs0 h ↦ (inM s hs hsd hs0).mpr h⟩

end EllLog

end Differential
