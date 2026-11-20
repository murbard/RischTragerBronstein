import RischTragerBronstein.Mixed.KECodes

/-!
# Rational non-squares stay non-squares in the fields `Kₘ` (linear base)

A constant whose square root lies in `K(X)` is a square in `K` (`sq_const_ratFunc`); hence a
rational square in `Kₘ₊₁ = Kₘ(t)` is a square in `Kₘ` (`sq_const_RFC`), and down to
`K₀ = ℚ(x)[y]/(y + c₀(x))`, which embeds into `ℚ(x)` for a linear base curve. So a non-square
`δ ∈ ℚ` is a non-square in every `Kₘ` (`not_isSquare_KF`): the quadratic extensions `Kₘ(√δ)` used
by the conjugation certificate at levels `m + 1` are fields.
-/

open Polynomial CPoly

namespace Curves.MT

/-- **Constants with a square root in `K(X)` are squares in `K`.** -/
theorem sq_const_ratFunc {K : Type*} [Field K] (r : RatFunc K) (c : K)
    (h : r ^ 2 = algebraMap K (RatFunc K) c) : IsSquare c := by
  set p := r.num
  set q := r.denom
  have hq : q ≠ 0 := RatFunc.denom_ne_zero r
  have hc : IsCoprime p q := RatFunc.isCoprime_num_denom r
  have hr : r = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q :=
    (RatFunc.num_div_denom r).symm
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hιq : algebraMap K[X] (RatFunc K) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
  have hpq : p ^ 2 = Polynomial.C c * q ^ 2 := by
    apply hinj
    rw [map_pow, map_mul, map_pow, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
    rw [hr, div_pow, div_eq_iff (pow_ne_zero 2 hιq)] at h
    exact h
  have hqu : IsUnit q := by
    have hdvd : q ∣ p ^ 2 := ⟨Polynomial.C c * q, by rw [hpq]; ring⟩
    exact (hc.pow_left (m := 2)).symm.isUnit_of_dvd' (dvd_refl q) hdvd
  have hq1 : q = 1 := Polynomial.Monic.eq_one_of_isUnit (RatFunc.monic_denom r) hqu
  rw [hq1, one_pow, mul_one] at hpq
  have hdeg : p.natDegree = 0 := by
    have := congrArg Polynomial.natDegree hpq
    rw [natDegree_pow, natDegree_C] at this
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, ← Polynomial.C_pow] at hpq
  exact ⟨p.coeff 0, by rw [← sq]; exact (Polynomial.C_injective hpq).symm⟩

/-- **The same over the computable `K(t)`.** -/
theorem sq_const_RFC {K : Type} [Field K] [DecidableEq K] [CharZero K] (r : RFC.RatFuncC K) (q : ℚ)
    (h : r ^ 2 = (q : RFC.RatFuncC K)) : IsSquare (q : K) := by
  apply sq_const_ratFunc (RFC.toRF r)
  have := congrArg RFC.toRF h
  rw [RFC.toRF_ratCast] at this
  rw [map_ratCast, ← this, sq, sq, RFC.toRF_mul]

/-- Rational squares descend from `Kₘ` to `K₀`. -/
theorem sq_KF_descend (Fc : Sup.BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (q : ℚ) :
    ∀ m : ℕ, IsSquare ((q : ℚ) : KF Fc m) → IsSquare ((q : ℚ) : KF Fc 0)
  | 0, h => h
  | m + 1, ⟨r, hr⟩ => sq_KF_descend Fc q m (sq_const_RFC (K := KF Fc m) r q (by rw [sq]; exact hr.symm))

/-- **Rational non-squares stay non-squares in every `Kₘ`** (linear base curve). -/
theorem not_isSquare_KF (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))] (q : ℚ)
    (hq : ¬ IsSquare q) (m : ℕ) : ¬ IsSquare ((q : ℚ) : KF [c0, [1]] m) := by
  intro h
  obtain ⟨r, hr⟩ := sq_KF_descend [c0, [1]] q m h
  -- `K₀ → AdjoinRoot (X + c₀) → ℚ(x)`
  set f := toPoly (fKc [c0, [1]])
  have h1 : (RFC.mk [1] [1] : RFC.RatFuncC ℚ) = 1 :=
    RFC.toRF_injective (by rw [RFC.toRF_const, map_one, RFC.toRF_one])
  have hf : f = Polynomial.C (RFC.mk c0 [1]) + Polynomial.X := by
    simp [f, fKc, toPoly, h1]
  have hroot : f.eval₂ (RingHom.id (RFC.RatFuncC ℚ)) (-(RFC.mk c0 [1])) = 0 := by
    rw [hf]; simp
  let ψ : KF [c0, [1]] 0 →+* RFC.RatFuncC ℚ :=
    (AdjoinRoot.lift (RingHom.id _) _ hroot).comp (NFK.toARHom (fKc [c0, [1]]))
  have hψ : ψ (r * r) = (q : RFC.RatFuncC ℚ) := by rw [← hr, map_ratCast]
  rw [map_mul] at hψ
  exact hq (sq_const_RFC (K := ℚ) (ψ r) q (by rw [sq]; exact hψ))

/-- `not_isSquare_KF` for a base curve equal to a linear one. -/
theorem not_isSquare_KF' (Fc : Sup.BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (c0 : CPoly ℚ)
    (hFc : Fc = [c0, [1]]) (q : ℚ) (hq : ¬ IsSquare q) (m : ℕ) : ¬ IsSquare ((q : ℚ) : KF Fc m) := by
  subst hFc
  exact not_isSquare_KF c0 q hq m

end Curves.MT
