import RischTragerBronstein.Jacobian.NFEmbed

/-!
# Reduction of number-field elements modulo `p`

For `K = ℚ[θ]/(M)`, `z ∈ ℤ_p` a root of `M` (over `ℤ`), the reduction `redL p (z mod p)` of
`p`-integral elements is additive and multiplicative (`redL_add`, `redL_sub`, `redL_mul`), sends
`1` to `1`, and a non-zero element with `p`-integral inverse has non-zero reduction
(`redL_ne_zero`). All via the lifts `exists_lift_NF` to `ℤ_p` and the injectivity of
`ℤ_p → ℚ_p`.
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

variable {p : ℕ} [hp : Fact p.Prime] {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]
variable (fZ : ℤ[X]) (hfZ : toPoly M = fZ.map (Int.castRingHom ℚ)) (z : ℤ_[p])
  (hz : aeval z fZ = 0)

include hfZ hz in
lemma lift_eq {x : NFC.NF M} (hx : pIntL p x.1 = true) {w : ℤ_[p]}
    (hw : (w : ℚ_[p]) = embedZ fZ hfZ z hz x) : PadicInt.toZMod w = redL p (PadicInt.toZMod z) x.1 := by
  obtain ⟨w', h1, h2⟩ := exists_lift_NF fZ hfZ z hz x hx
  have : w = w' := Subtype.ext (hw.trans h1.symm)
  rw [this, h2]

include hfZ hz in
lemma redL_mul {x y : NFC.NF M} (hx : pIntL p x.1 = true) (hy : pIntL p y.1 = true)
    (hxy : pIntL p (x * y).1 = true) :
    redL p (PadicInt.toZMod z) (x * y).1 =
      redL p (PadicInt.toZMod z) x.1 * redL p (PadicInt.toZMod z) y.1 := by
  obtain ⟨wx, hx1, hx2⟩ := exists_lift_NF fZ hfZ z hz x hx
  obtain ⟨wy, hy1, hy2⟩ := exists_lift_NF fZ hfZ z hz y hy
  rw [← hx2, ← hy2, ← map_mul]
  exact (lift_eq fZ hfZ z hz hxy (by push_cast; rw [hx1, hy1, map_mul])).symm

include hfZ hz in
lemma redL_add {x y : NFC.NF M} (hx : pIntL p x.1 = true) (hy : pIntL p y.1 = true)
    (hxy : pIntL p (x + y).1 = true) :
    redL p (PadicInt.toZMod z) (x + y).1 =
      redL p (PadicInt.toZMod z) x.1 + redL p (PadicInt.toZMod z) y.1 := by
  obtain ⟨wx, hx1, hx2⟩ := exists_lift_NF fZ hfZ z hz x hx
  obtain ⟨wy, hy1, hy2⟩ := exists_lift_NF fZ hfZ z hz y hy
  rw [← hx2, ← hy2, ← map_add]
  exact (lift_eq fZ hfZ z hz hxy (by push_cast; rw [hx1, hy1, map_add])).symm

include hfZ hz in
lemma redL_sub {x y : NFC.NF M} (hx : pIntL p x.1 = true) (hy : pIntL p y.1 = true)
    (hxy : pIntL p (x - y).1 = true) :
    redL p (PadicInt.toZMod z) (x - y).1 =
      redL p (PadicInt.toZMod z) x.1 - redL p (PadicInt.toZMod z) y.1 := by
  obtain ⟨wx, hx1, hx2⟩ := exists_lift_NF fZ hfZ z hz x hx
  obtain ⟨wy, hy1, hy2⟩ := exists_lift_NF fZ hfZ z hz y hy
  rw [← hx2, ← hy2, ← map_sub]
  exact (lift_eq fZ hfZ z hz hxy (by push_cast; rw [hx1, hy1, map_sub])).symm

include hfZ hz in
lemma redL_intCast (n : ℤ) (hn : pIntL p ((n : NFC.NF M)).1 = true) :
    redL p (PadicInt.toZMod z) ((n : NFC.NF M)).1 = (n : ZMod p) := by
  have := lift_eq fZ hfZ z hz hn (w := (n : ℤ_[p])) (by rw [map_intCast]; push_cast; rfl)
  rw [← this, map_intCast]

include hfZ hz in
/-- **Non-zero elements with `p`-integral inverse reduce to non-zero elements.** -/
lemma redL_ne_zero {x : NFC.NF M} (hx0 : x ≠ 0) (hx : pIntL p x.1 = true)
    (hxi : pIntL p x⁻¹.1 = true) : redL p (PadicInt.toZMod z) x.1 ≠ 0 := by
  obtain ⟨wx, hx1, hx2⟩ := exists_lift_NF fZ hfZ z hz x hx
  obtain ⟨wi, hi1, hi2⟩ := exists_lift_NF fZ hfZ z hz x⁻¹ hxi
  have hprod : wx * wi = 1 := by
    apply Subtype.ext
    show ((wx * wi : ℤ_[p]) : ℚ_[p]) = ((1 : ℤ_[p]) : ℚ_[p])
    push_cast
    rw [hx1, hi1, ← map_mul, mul_inv_cancel₀ hx0, map_one]
  intro h0
  have := congrArg PadicInt.toZMod hprod
  rw [map_mul, hx2, h0, zero_mul, map_one] at this
  exact zero_ne_one this

end Jac
