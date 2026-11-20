import RischTragerBronstein.Elliptic.NLTorsion

/-!
# Nagell–Lutz: the bound on `y`, and deciding torsion of rational points

`torsion_y_dvd`: for a torsion point `(x, y)` with `y ≠ 0`, `y` is an integer dividing the
discriminant `D = a²b² − 4b³ − 4a³c − 27c² + 18abc` of `x³ + ax² + bx + c`.

`not_torsion_of`: a multiple `kP` with a non-integral coordinate, or with `y ≠ 0` not dividing `D`,
proves that `P` has infinite order. With `k • P = 0` for some `k ≥ 1` proving finite order, the two
certificates decide torsion (both found by computing multiples; the search terminates since the
multiples of a torsion point lie in a finite set).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllNL

variable (a b c : ℤ)

/-- The discriminant of `x³ + ax² + bx + c`. -/
def disc : ℤ := a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c

/-- `D = r f + s f′` with integer polynomials. -/
lemma disc_bezout (x : ℤ) :
    disc a b c = ((-6 * a ^ 2 + 18 * b) * x + (-4 * a ^ 3 + 15 * a * b - 27 * c)) *
        (x ^ 3 + a * x ^ 2 + b * x + c) +
      ((2 * a ^ 2 - 6 * b) * x ^ 2 + (2 * a ^ 3 - 7 * a * b + 9 * c) * x +
        (a ^ 2 * b + 3 * a * c - 4 * b ^ 2)) * (3 * x ^ 2 + 2 * a * x + b) := by
  unfold disc; ring

/-- A rational whose square is an integer is an integer. -/
lemma int_of_sq_int (q : ℚ) (h : ∃ z : ℤ, q ^ 2 = z) : ∃ z : ℤ, q = z := by
  obtain ⟨z, hz⟩ := h
  refine int_of_padicValRat_nonneg q fun p hp ↦ ?_
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hq : q = 0
  · simp [hq]
  have h1 : padicValRat p (q ^ 2) = 2 * padicValRat p q := by
    rw [padicValRat.pow q]; push_cast; ring
  have h2 : 0 ≤ padicValRat p (q ^ 2) := by
    rw [hz, padicValRat.of_int]; exact_mod_cast Nat.zero_le _
  omega

/-- **Nagell–Lutz (bound): `y ∣ D` for a torsion point with `y ≠ 0`.** -/
theorem torsion_y_dvd {x y : ℚ} (h : (W a b c).toAffine.Nonsingular x y)
    (ht : IsOfFinAddOrder (Point.some x y h)) (hy : y ≠ 0) :
    ∃ X Y : ℤ, x = X ∧ y = Y ∧ Y ∣ disc a b c := by
  obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := torsion_integral a b c h ht
  refine ⟨X, Y, rfl, rfl, ?_⟩
  have hc := (equation_W a b c).mp h.1
  have hyn : (Y : ℚ) ≠ (W a b c).toAffine.negY X Y := by
    rw [negY_W]; intro h0; apply hy; linarith
  -- `2P` is torsion, hence integral
  have h2 : Point.some (X : ℚ) Y h + Point.some (X : ℚ) Y h =
      Point.some _ _ (nonsingular_add h h fun hxy ↦ hyn hxy.right) :=
    Point.add_self_of_Y_ne hyn
  have ht2 : IsOfFinAddOrder (Point.some (X : ℚ) Y h + Point.some (X : ℚ) Y h) := ht.add ht
  rw [h2] at ht2
  obtain ⟨⟨X2, hX2⟩, -⟩ := torsion_integral a b c _ ht2
  rw [slope_of_Y_ne rfl hyn] at hX2
  set ℓ := (3 * (X : ℚ) ^ 2 + 2 * (W a b c).a₂ * X + (W a b c).a₄ - (W a b c).a₁ * Y) /
    (Y - (W a b c).toAffine.negY X Y) with hℓ
  have hℓ' : ℓ = (3 * (X : ℚ) ^ 2 + 2 * a * X + b) / (2 * Y) := by
    rw [hℓ, negY_W]; simp [W]; ring
  -- `ℓ` is an integer
  obtain ⟨L, hL⟩ := int_of_sq_int ℓ ⟨X2 + a + 2 * X, by
    have : (W a b c).toAffine.addX X X ℓ = ℓ ^ 2 - a - X - X := by simp [addX, W]
    rw [this] at hX2; push_cast; linarith⟩
  -- `Y ∣ f′(X)` and `Y ∣ f(X)`
  have hfp : (3 * X ^ 2 + 2 * a * X + b : ℤ) = 2 * Y * L := by
    have : (3 * (X : ℚ) ^ 2 + 2 * a * X + b) = 2 * Y * ℓ := by
      rw [hℓ']; field_simp
    rw [hL] at this; exact_mod_cast this
  have hf : (Y ^ 2 : ℤ) = X ^ 3 + a * X ^ 2 + b * X + c := by
    unfold OnCurve at hc; exact_mod_cast hc
  rw [disc_bezout a b c X, ← hf, hfp]
  exact dvd_add (dvd_mul_of_dvd_right (dvd_pow_self Y two_ne_zero) _)
    (dvd_mul_of_dvd_right (by rw [mul_comm 2 Y, mul_assoc]; exact dvd_mul_right _ _) _)

/-- **A certificate of infinite order**: some multiple has a non-integral coordinate, or a
non-zero `y` not dividing `D`. -/
theorem not_torsion_of {P : (W a b c).toAffine.Point} (k : ℕ) {x y : ℚ}
    (h : (W a b c).toAffine.Nonsingular x y) (hk : k • P = Point.some x y h)
    (hbad : x.den ≠ 1 ∨ y.den ≠ 1 ∨ (y ≠ 0 ∧ ¬(y.num ∣ disc a b c))) :
    ¬IsOfFinAddOrder P := by
  intro ht
  have htk : IsOfFinAddOrder (Point.some x y h) := hk ▸ ht.nsmul
  obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := torsion_integral a b c h htk
  rcases hbad with h1 | h1 | ⟨hy, h1⟩
  · exact h1 (by simp)
  · exact h1 (by simp)
  · obtain ⟨X', Y', hX, hY, hdvd⟩ := torsion_y_dvd a b c h htk hy
    apply h1
    have hYY : Y = Y' := by exact_mod_cast hY
    simpa [hYY] using hdvd

/-- A certificate of finite order. -/
theorem torsion_of {P : (W a b c).toAffine.Point} (k : ℕ) (hk0 : 0 < k) (hk : k • P = 0) :
    IsOfFinAddOrder P :=
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, hk0, hk⟩

/-- Is `k • P` a certificate of infinite order? -/
def badMultiple (P : (W a b c).toAffine.Point) (k : ℕ) : Bool :=
  match k • P with
  | .zero => false
  | .some x y _ => x.den != 1 || y.den != 1 || (y != 0 && !decide (y.num ∣ disc a b c))

/-- **The torsion test**: `some true` (finite order), `some false` (infinite order), or `none`
(fuel exhausted). -/
def torsionTest (P : (W a b c).toAffine.Point) : ℕ → Option Bool
  | 0 => none
  | fuel + 1 =>
    match torsionTest P fuel with
    | some r => some r
    | none =>
      if (fuel + 1) • P = 0 then some true
      else if badMultiple a b c P (fuel + 1) then some false else none

lemma not_torsion_of_bad (P : (W a b c).toAffine.Point) (k : ℕ)
    (hb : badMultiple a b c P k = true) : ¬IsOfFinAddOrder P := by
  unfold badMultiple at hb
  split at hb
  · exact absurd hb (by simp)
  · rename_i x y h hk
    refine not_torsion_of a b c k h hk ?_
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hb
    rcases hb with (h1 | h1) | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- **Soundness of the torsion test.** -/
theorem torsionTest_spec (P : (W a b c).toAffine.Point) :
    ∀ (fuel : ℕ) (r : Bool), torsionTest a b c P fuel = some r → (r = true ↔ IsOfFinAddOrder P)
  | 0, r, h => by simp [torsionTest] at h
  | fuel + 1, r, h => by
    unfold torsionTest at h
    split at h
    · rename_i r' hr'
      simp only [Option.some.injEq] at h
      subst h
      exact torsionTest_spec P fuel r' hr'
    · split_ifs at h with h1 h2
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨fun _ ↦ torsion_of a b c (fuel + 1) (by omega) h1, fun _ ↦ rfl⟩
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨fun h ↦ absurd h (by simp), fun ht ↦ absurd ht (not_torsion_of_bad a b c P _ h2)⟩

end EllNL
