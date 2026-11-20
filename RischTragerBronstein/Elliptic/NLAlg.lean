import RischTragerBronstein.Elliptic.PVal

/-!
# Nagell–Lutz: the algebra of the formal-group congruence

For the curve `y² = x³ + a x² + b x + c` (`a, b, c ∈ ℤ`) and points in the `p`-adic filtration
(`v_p(y) ≤ -3r`, `r ≥ 1`), with `t = x/y`, `s = 1/y`:

* `third`: if `x₁, x₂, x₃` are the three roots of `X³ + aX² + bX + c - (ℓX + m)²` (Vieta) with
  `y₁ = ℓx₁ + m`, `y₂ = ℓx₂ + m`, `ℓ = -α/β`, `m = 1/β`, `α ∈ p^{2r}`, `β ∈ p^{3r}`, then the third
  point `(x₃, y₃ = -(ℓx₃ + m))` has `1/y₃ ∈ p^{3r}` and `t₃ ≡ t₁ + t₂ (mod p^{3r})`.
-/

namespace EllNL

open PVal

variable {p : ℕ} [hp : Fact p.Prime]

/-- `1 + u`-type units: `1 + a α + b α² + c α³` for `α ∈ p ℤ_(p)`. -/
lemma unit_cubic (a b c : ℤ) {α : ℚ} (hα : PDvd p 1 α) :
    padicValRat p (1 + (a * α + b * α ^ 2 + c * α ^ 3)) = 0 ∧
      1 + (a * α + b * α ^ 2 + c * α ^ 3) ≠ 0 := by
  apply val_one_add
  have h1 : PDvd p 1 ((a : ℚ) * α) := by simpa using (pdvd_intCast (p := p) a).mul hα
  have h2 : PDvd p 1 ((b : ℚ) * α ^ 2) :=
    ((pdvd_intCast (p := p) b).mul (hα.pow 2)).mono (by norm_num)
  have h3 : PDvd p 1 ((c : ℚ) * α ^ 3) :=
    ((pdvd_intCast (p := p) c).mul (hα.pow 3)).mono (by norm_num)
  exact (h1.add h2).add h3

/-- **The third point.** -/
theorem third (a b c : ℤ) (r : ℕ) (hr : 1 ≤ r) (x1 x2 x3 y1 y2 ℓ m α β : ℚ) (hβ : β ≠ 0)
    (hℓ : ℓ = -α / β) (hm : m = 1 / β) (hy1 : y1 = ℓ * x1 + m) (hy2 : y2 = ℓ * x2 + m)
    (hy10 : y1 ≠ 0) (hy20 : y2 ≠ 0)
    (V1 : x1 + x2 + x3 = ℓ ^ 2 - a) (V2 : x1 * x2 + x1 * x3 + x2 * x3 = b - 2 * ℓ * m)
    (V3 : x1 * x2 * x3 = m ^ 2 - c)
    (hα : PDvd p (2 * r) α) (hβv : PDvd p (3 * r) β)
    (ht1 : PDvd p r (x1 / y1)) (ht2 : PDvd p r (x2 / y2)) :
    ℓ * x3 + m ≠ 0 ∧ PDvd p (3 * r) (x3 / (-(ℓ * x3 + m)) - x1 / y1 - x2 / y2) ∧
      PDvd p (3 * r) (1 / (-(ℓ * x3 + m))) ∧ PDvd p r (x3 / (-(ℓ * x3 + m))) := by
  have hα1 : PDvd p 1 α := hα.mono (by omega)
  obtain ⟨hU, hU0⟩ := unit_cubic (p := p) a b c hα1
  set U := 1 + (a * α + b * α ^ 2 + c * α ^ 3) with hUdef
  -- `y₁ y₂ (ℓx₃ + m) β³ = U`
  have hD : y1 * y2 * (ℓ * x3 + m) * β ^ 3 = U := by
    rw [hy1, hy2]
    have e : (ℓ * x1 + m) * (ℓ * x2 + m) * (ℓ * x3 + m) =
        ℓ ^ 3 * (x1 * x2 * x3) + ℓ ^ 2 * m * (x1 * x2 + x1 * x3 + x2 * x3) +
          ℓ * m ^ 2 * (x1 + x2 + x3) + m ^ 3 := by ring
    rw [e, V1, V2, V3, hℓ, hm, hUdef]
    field_simp
    ring
  have hl3 : ℓ * x3 + m ≠ 0 := by
    intro h0; rw [h0, mul_zero, zero_mul] at hD; exact hU0 hD.symm
  -- the sum of the three `τᵢ = xᵢ / (ℓxᵢ + m)`
  have hK : x3 / (-(ℓ * x3 + m)) - x1 / y1 - x2 / y2 =
      β * (a + 2 * b * α + 3 * c * α ^ 2) / U := by
    have hN : x1 * y2 * (ℓ * x3 + m) + x2 * y1 * (ℓ * x3 + m) + x3 * y1 * y2 =
        -a * m ^ 2 + 2 * b * ℓ * m - 3 * c * ℓ ^ 2 := by
      rw [hy1, hy2]
      linear_combination (3 * ℓ ^ 2) * V3 + (2 * ℓ * m) * V2 + m ^ 2 * V1
    have hsum : x3 / (-(ℓ * x3 + m)) - x1 / y1 - x2 / y2 =
        -(x1 * y2 * (ℓ * x3 + m) + x2 * y1 * (ℓ * x3 + m) + x3 * y1 * y2) /
          (y1 * y2 * (ℓ * x3 + m)) := by
      have hl3' : x3 * ℓ + m ≠ 0 := by rwa [mul_comm]
      field_simp
      ring
    have hDen : y1 * y2 * (ℓ * x3 + m) = U / β ^ 3 := by
      rw [← hD]; field_simp
    rw [hsum, hN, hDen, hℓ, hm]
    field_simp
    ring
  have hKv : PDvd p (3 * r) (β * (a + 2 * b * α + 3 * c * α ^ 2) / U) := by
    refine PDvd.div_unit ?_ hU hU0
    have h1 : PDvd p 0 ((a : ℚ) + 2 * b * α + 3 * c * α ^ 2) := by
      have ha := pdvd_intCast (p := p) a
      have hb : PDvd p 0 (2 * (b : ℚ) * α) := by
        have := ((pdvd_intCast (p := p) 2).mul (pdvd_intCast (p := p) b)).mul (hα.mono (show (0 : ℤ) ≤ 2 * r by omega))
        simpa using this
      have hc : PDvd p 0 (3 * (c : ℚ) * α ^ 2) := by
        have := ((pdvd_intCast (p := p) 3).mul (pdvd_intCast (p := p) c)).mul
          ((hα.mono (show (0 : ℤ) ≤ 2 * r by omega)).pow 2)
        simpa using this
      exact (ha.add hb).add hc
    simpa using hβv.mul h1
  have ht3 : PDvd p r (x3 / (-(ℓ * x3 + m))) := by
    have e : x3 / (-(ℓ * x3 + m)) = (x3 / (-(ℓ * x3 + m)) - x1 / y1 - x2 / y2) + x1 / y1 +
      x2 / y2 := by ring
    rw [e]
    exact ((hK ▸ hKv).mono (by omega)).add ht1 |>.add ht2
  refine ⟨hl3, hK ▸ hKv, ?_, ht3⟩
  -- `1/y₃ = α t₃ - β`
  have hs : 1 / (-(ℓ * x3 + m)) = α * (x3 / (-(ℓ * x3 + m))) - β := by
    have hL : β * (ℓ * x3 + m) = 1 - α * x3 := by rw [hℓ, hm]; field_simp; ring
    have hl3' : x3 * ℓ + m ≠ 0 := by rwa [mul_comm]
    field_simp
    linear_combination hL
  rw [hs]
  exact ((hα.mul ht3).mono (by push_cast; omega)).sub hβv

end EllNL
