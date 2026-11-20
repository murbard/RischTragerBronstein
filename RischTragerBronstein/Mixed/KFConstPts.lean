import RischTragerBronstein.Mixed.KFSquare
import RischTragerBronstein.Mixed.EllConstPts

/-!
# Points of constant curves over the fields `Kₘ` are rational (linear base)

`y² = x³ + a x + b` with `a, b ∈ ℚ`, `4a³ + 27b² ≠ 0`: over `Kₘ₊₁ = Kₘ(t)` the points are constant
(`EllConst.weierstrass_const`, through `toRFHom`), and `K₀ ↪ ℚ(x)` for a linear base; so every point
of `E(Kₘ)` has rational coordinates (`KF_point_rat`).
-/

open Polynomial CPoly

namespace Curves.MT

variable {k : Type*} [Field k] [CharZero k]

/-- A constant curve over `k(t)`: its points come from `k`. -/
lemma ratFunc_point_const (a b : ℚ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (x y : RatFunc k)
    (h : y ^ 2 = x ^ 3 + (a : RatFunc k) * x + (b : RatFunc k)) :
    ∃ c d : k, x = RatFunc.C c ∧ d ^ 2 = c ^ 3 + (a : k) * c + (b : k) := by
  have hΔk : 4 * (a : k) ^ 3 + 27 * (b : k) ^ 2 ≠ 0 := by exact_mod_cast hΔ
  obtain ⟨c, hc⟩ := EllConst.weierstrass_const (a : k) (b : k) hΔk x y (by
    rw [map_ratCast, map_ratCast]; exact h)
  have hsq : y ^ 2 = algebraMap k (RatFunc k) (c ^ 3 + (a : k) * c + (b : k)) := by
    rw [h, hc]; simp [RatFunc.algebraMap_C, map_ratCast]
  obtain ⟨d, hd⟩ := sq_const_ratFunc y _ hsq
  exact ⟨c, d, hc, by rw [sq, ← hd]⟩

/-- **Points of constant curves over `Kₘ` have rational abscissa** (linear base). -/
theorem KF_point_rat (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))] (a b : ℚ)
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    ∀ m : ℕ, ∀ x y : KF [c0, [1]] m, y ^ 2 = x ^ 3 + (a : KF [c0, [1]] m) * x + (b : KF [c0, [1]] m) →
      ∃ q : ℚ, x = (q : KF [c0, [1]] m)
  | 0, x, y, h => by
    set f := toPoly (fKc [c0, [1]])
    have h1 : (RFC.mk [1] [1] : RFC.RatFuncC ℚ) = 1 :=
      RFC.toRF_injective (by rw [RFC.toRF_const, map_one, RFC.toRF_one])
    have hf : f = Polynomial.C (RFC.mk c0 [1]) + Polynomial.X := by
      simp [f, fKc, toPoly, h1]
    have hroot : f.eval₂ (RingHom.id (RFC.RatFuncC ℚ)) (-(RFC.mk c0 [1])) = 0 := by
      rw [hf]; simp
    let ψ : KF [c0, [1]] 0 →+* RatFunc ℚ := RFC.toRFHom.comp
      ((AdjoinRoot.lift (RingHom.id _) _ hroot).comp (NFK.toARHom (fKc [c0, [1]])))
    have hψ := congrArg ψ h
    simp only [map_add, map_mul, map_pow, map_ratCast] at hψ
    obtain ⟨c, d, hc, -⟩ := ratFunc_point_const (k := ℚ) a b hΔ (ψ x) (ψ y) hψ
    refine ⟨c, ψ.injective ?_⟩
    rw [hc, map_ratCast]
    exact (eq_ratCast (RatFunc.C) c).trans rfl
  | m + 1, x, y, h => by
    let ψ : KF [c0, [1]] (m + 1) →+* RatFunc (KF [c0, [1]] m) := RFC.toRFHom
    have hψ := congrArg ψ h
    simp only [map_add, map_mul, map_pow, map_ratCast] at hψ
    obtain ⟨c, d, hc, hd⟩ := ratFunc_point_const a b hΔ (ψ x) (ψ y) hψ
    obtain ⟨q, rfl⟩ := KF_point_rat c0 a b hΔ m c d hd
    refine ⟨q, RFC.toRF_injective ?_⟩
    rw [RFC.toRF_ratCast]
    exact hc.trans (map_ratCast _ q)

end Curves.MT
