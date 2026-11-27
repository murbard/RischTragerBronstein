import RischTragerBronstein.Mixed.EllScale
import RischTragerBronstein.Mixed.ExHVal

/-!
# Points of non-singular reduction form a subgroup

For `y² = x³ + a x + b` over a field `K` with a valuation `V` (`a`, `b` integral), a point is
*singular at `V`* (`Sing`) if `x` is integral and `f(x) = x³ + a x + b`, `f′(x) = 3x² + a` both lie
in `𝔭`. Everything is done without `y`-coordinates and without residue fields, through

* **`xpm`**: for `x₁ ≠ x₂`, the `x`-coordinates `t, t′` of `P + Q` and `P − Q` satisfy
  `(t + t′)(x₁ − x₂)² = 2(x₁x₂ + a)(x₁ + x₂) + 4b`, `t t′ (x₁ − x₂)² = (x₁x₂ − a)² − 4b(x₁ + x₂)`.
* **`sing_add`**: singular ± non-singular is singular; hence **`E0`**, the subgroup of points of
  non-singular reduction.
* **`related`**: a criterion for `P + Q` or `P − Q` to have `x`-coordinate not congruent to `e`.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

variable {K : Type*} [Field K] (V : LVal K) (a b : K)

/-- Singular reduction at `V`. -/
def Sing : (shortF a b).toAffine.Point → Prop
  | .zero => False
  | .some x _ _ => Dv V 0 x ∧ Dv V 1 (x ^ 3 + a * x + b) ∧ Dv V 1 (3 * x ^ 2 + a)

variable {V a b}

lemma addX_short (x1 x2 l : K) : (shortF a b).toAffine.addX x1 x2 l = l ^ 2 - x1 - x2 := by
  simp [addX, shortF]

/-- **Sum and product of `x(P + Q)` and `x(P − Q)`.** -/
theorem xpm {x1 y1 x2 y2 : K} (h1 : (shortF a b).toAffine.Nonsingular x1 y1)
    (h2 : (shortF a b).toAffine.Nonsingular x2 y2) (hx : x1 ≠ x2) :
    ∃ (t t' u u' : K) (ht : (shortF a b).toAffine.Nonsingular t u)
      (ht' : (shortF a b).toAffine.Nonsingular t' u'),
      Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ ht ∧
      Point.some _ _ h1 - Point.some _ _ h2 = Point.some _ _ ht' ∧
      (t + t') * (x1 - x2) ^ 2 = 2 * (x1 * x2 + a) * (x1 + x2) + 4 * b ∧
      t * t' * (x1 - x2) ^ 2 = (x1 * x2 - a) ^ 2 - 4 * b * (x1 + x2) := by
  have e1 := ((ns_short a b x1 y1).mp h1).1
  have e2 := ((ns_short a b x2 y2).mp h2).1
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  have h2' : (shortF a b).toAffine.Nonsingular x2 ((shortF a b).toAffine.negY x2 y2) :=
    (nonsingular_neg ..).mpr h2
  refine ⟨_, _, _, _, nonsingular_add h1 h2 (fun h ↦ hx h.1),
    nonsingular_add h1 h2' (fun h ↦ hx h.1), Point.add_of_X_ne hx, ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, Point.neg_some]; exact Point.add_of_X_ne hx
  all_goals
    rw [addX_short, addX_short, slope_of_X_ne hx, slope_of_X_ne hx, negY_shortF]
    set l := (y1 - y2) / (x1 - x2) with hl
    set l' := (y1 - -y2) / (x1 - x2) with hl'
    have hl1 : l * (x1 - x2) = y1 - y2 := by rw [hl]; field_simp
    have hl2 : l' * (x1 - x2) = y1 + y2 := by rw [hl']; field_simp; ring
  · linear_combination (l * (x1 - x2) + (y1 - y2)) * hl1 + (l' * (x1 - x2) + (y1 + y2)) * hl2 +
      2 * e1 + 2 * e2
  · have hq : l * l' * (x1 - x2) = x1 ^ 2 + x1 * x2 + x2 ^ 2 + a := by
      apply mul_right_cancel₀ hd
      linear_combination l' * (x1 - x2) * hl1 + (y1 - y2) * hl2 + e1 - e2
    linear_combination (l * l' * (x1 - x2) + (x1 ^ 2 + x1 * x2 + x2 ^ 2 + a)) * hq -
      (x1 + x2) * ((l * (x1 - x2) + (y1 - y2)) * hl1 + (l' * (x1 - x2) + (y1 + y2)) * hl2) -
      2 * (x1 + x2) * e1 - 2 * (x1 + x2) * e2

/-- Congruent `x`-coordinates: singularity is inherited. -/
lemma sing_congr (ha : Dv V 0 a) {x t : K} (hx : Dv V 0 x)
    (hf : Dv V 1 (x ^ 3 + a * x + b)) (hg : Dv V 1 (3 * x ^ 2 + a)) (ht : Dv V 1 (t - x)) :
    Dv V 0 t ∧ Dv V 1 (t ^ 3 + a * t + b) ∧ Dv V 1 (3 * t ^ 2 + a) := by
  have ht0 : Dv V 0 t := by
    have := (ht.mono (show (0 : ℤ) ≤ 1 by omega)).add hx
    simpa using this
  refine ⟨ht0, ?_, ?_⟩
  · have e : t ^ 3 + a * t + b = (x ^ 3 + a * x + b) + (t - x) * (t ^ 2 + t * x + x ^ 2 + a) := by
      ring
    rw [e]
    refine hf.add ((ht.mul (((((ht0.pow 2).mono (by norm_num)).add
      ((ht0.mul hx).mono (by norm_num))).add ((hx.pow 2).mono (by norm_num))).add ha)).mono
      (by norm_num))
  · have e : 3 * t ^ 2 + a = (3 * x ^ 2 + a) + (t - x) * (3 * (t + x)) := by ring
    rw [e]
    exact hg.add ((ht.mul ((ht0.add hx).ofNat_mul 3)).mono (by norm_num))

/-- If the sum and product of `t, t′` are congruent to `2x`, `x²`, then `t ≡ x`. -/
lemma congr_of_sp {x t t' : K} (hx : Dv V 0 x) (hs : Dv V 1 (t + t' - 2 * x))
    (hp : Dv V 1 (t * t' - x ^ 2)) : Dv V 1 (t - x) := by
  refine root_small (s := t + t' - 2 * x)
    (p := (t * t' - x ^ 2) - (t + t' - 2 * x) * x) (by ring) hs (hp.sub ?_)
  exact (hs.mul hx).mono (by norm_num)

/-- **Singular ± non-singular is singular** (affine points, in coordinates). -/
theorem sing_pm (ha : Dv V 0 a) (hb : Dv V 0 b) {x1 y1 x2 y2 : K}
    (h1 : (shortF a b).toAffine.Nonsingular x1 y1) (h2 : (shortF a b).toAffine.Nonsingular x2 y2)
    (hS : Sing V a b (.some _ _ h1)) (hN : ¬Sing V a b (.some _ _ h2)) :
    Sing V a b (.some _ _ h1 + .some _ _ h2) ∧ Sing V a b (.some _ _ h1 - .some _ _ h2) := by
  obtain ⟨hx, hf, hg⟩ := hS
  -- the denominator `d = (x1 - x2)²`, and the numerators
  have key : ∃ k : ℤ, Ex V k ((x1 - x2) ^ 2) ∧
      Dv V (k + 1) (4 * (x1 ^ 3 + a * x1 + b) - 2 * (x1 - x2) * (3 * x1 ^ 2 + a)) ∧
      Dv V (k + 1) ((3 * x1 ^ 2 + a) * (x1 ^ 2 + 2 * x1 * x2 + a) -
        4 * (x1 + x2) * (x1 ^ 3 + a * x1 + b)) := by
    rcases dv_or_ex (V := V) x2 0 with h20 | ⟨l, hl, hx2⟩
    · -- `x2` integral: `x1 - x2` is a unit
      have hu : Ex V 0 (x1 - x2) := by
        rcases dv_or_ex (V := V) (x1 - x2) 1 with hc | ⟨l, hl, hc⟩
        · exfalso
          apply hN
          have : Dv V 1 (x2 - x1) := by simpa using hc.neg
          exact sing_congr ha hx hf hg this
        · have h0 : Dv V 0 (x1 - x2) := hx.sub h20
          have : l = 0 := by
            have := dv_of_ne h0 hc.1
            have := hc.2
            omega
          exact this ▸ hc
      refine ⟨0, by simpa using hu.pow 2, ?_, ?_⟩
      · refine (hf.ofNat_mul 4).sub ?_
        have := ((hx.sub h20).ofNat_mul 2).mul hg
        simpa using this
      · refine Dv.sub ?_ ?_
        · have := hg.mul ((((hx.pow 2).mono (by norm_num)).add
            (((hx.ofNat_mul 2).mul h20).mono (by norm_num))).add ha)
          simpa using this
        · have := ((hx.add h20).ofNat_mul 4).mul hf
          simpa using this
    · -- `x2` has a pole of order `-l`
      have hu : Ex V l (x1 - x2) := by
        have := hx2.neg.dv_add hx hl
        rwa [← sub_eq_add_neg] at this
      have hx2d : Dv V l x2 := hx2.dv
      have hx1d : Dv V l x1 := hx.mono hl.le
      have hf0 : Dv V 0 (x1 ^ 3 + a * x1 + b) := hf.mono (by norm_num)
      have hg0 : Dv V 0 (3 * x1 ^ 2 + a) := hg.mono (by norm_num)
      refine ⟨2 * l, by simpa using hu.pow 2, ?_, ?_⟩
      · refine ((hf0.ofNat_mul 4).mono (by omega)).sub ?_
        have := ((hx1d.sub hx2d).ofNat_mul 2).mul hg0
        exact this.mono (by omega)
      · refine Dv.sub ?_ ?_
        · have := hg0.mul ((((hx.pow 2).mono (show l ≤ ((2 : ℕ) : ℤ) * 0 by omega)).add
            (((hx.ofNat_mul 2).mul hx2d).mono (show l ≤ 0 + l by omega))).add (ha.mono hl.le))
          exact this.mono (by omega)
        · have := ((hx1d.add hx2d).ofNat_mul 4).mul hf0
          exact this.mono (by omega)
  obtain ⟨k, hd, hNs, hNp⟩ := key
  have hne : x1 ≠ x2 := fun h ↦ by
    have := hd.1; rw [h] at this; simp at this
  obtain ⟨t, t', u, u', ht, ht', hadd, hsub, hsum, hprod⟩ := xpm h1 h2 hne
  have hs : Dv V 1 (t + t' - 2 * x1) := by
    have e : t + t' - 2 * x1 = (4 * (x1 ^ 3 + a * x1 + b) - 2 * (x1 - x2) * (3 * x1 ^ 2 + a)) /
        (x1 - x2) ^ 2 := by
      rw [eq_div_iff hd.1]; linear_combination hsum
    rw [e]
    exact (hNs.div_ex hd).mono (by omega)
  have hp : Dv V 1 (t * t' - x1 ^ 2) := by
    have e : t * t' - x1 ^ 2 = ((3 * x1 ^ 2 + a) * (x1 ^ 2 + 2 * x1 * x2 + a) -
        4 * (x1 + x2) * (x1 ^ 3 + a * x1 + b)) / (x1 - x2) ^ 2 := by
      rw [eq_div_iff hd.1]; linear_combination hprod
    rw [e]
    exact (hNp.div_ex hd).mono (by omega)
  have hs' : Dv V 1 (t' + t - 2 * x1) := by rwa [add_comm]
  have hp' : Dv V 1 (t' * t - x1 ^ 2) := by rwa [mul_comm]
  rw [hadd, hsub]
  exact ⟨sing_congr ha hx hf hg (congr_of_sp hx hs hp),
    sing_congr ha hx hf hg (congr_of_sp hx hs' hp')⟩

lemma sing_neg (P : (shortF a b).toAffine.Point) : Sing V a b (-P) ↔ Sing V a b P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

variable (V a b) in
/-- **The subgroup of points of non-singular reduction.** -/
def E0 (ha : Dv V 0 a) (hb : Dv V 0 b) : AddSubgroup (shortF a b).toAffine.Point where
  carrier := {P | ¬Sing V a b P}
  zero_mem' := fun h ↦ h
  neg_mem' := fun {P} hP ↦ by rwa [Set.mem_setOf_eq, sing_neg]
  add_mem' := by
    intro P Q hP hQ hS
    rcases P with _ | ⟨x1, y1, h1⟩
    · have e0 : (Point.zero : (shortF a b).toAffine.Point) + Q = Q := zero_add Q
      have hS' : Sing V a b (Point.zero + Q) := hS
      rw [e0] at hS'
      exact hQ hS'
    rcases hR : (Point.some _ _ h1 + Q : (shortF a b).toAffine.Point) with _ | ⟨x3, y3, h3⟩
    · have hS' : Sing V a b (Point.some _ _ h1 + Q) := hS
      rw [hR] at hS'; exact hS'
    have hS' : Sing V a b (Point.some _ _ h3) := by
      have : Sing V a b (Point.some _ _ h1 + Q) := hS
      rwa [hR] at this
    have := (sing_pm ha hb h3 h1 hS' hP).2
    rw [← hR, add_sub_cancel_left] at this
    exact hQ this

lemma mem_E0 (ha : Dv V 0 a) (hb : Dv V 0 b) (P : (shortF a b).toAffine.Point) :
    P ∈ E0 V a b ha hb ↔ ¬Sing V a b P := Iff.rfl

/-- **Related points**: for `x₁ ≠ x₂` and a centre `e`, if the numerator of the sum or of the
product of `x(P ± Q) − e` has valuation at most that of `(x₁ − x₂)²`, then one of `P + Q`, `P − Q`
is `0` or has `x`-coordinate not congruent to `e`. -/
theorem related {x1 y1 x2 y2 : K} (h1 : (shortF a b).toAffine.Nonsingular x1 y1)
    (h2 : (shortF a b).toAffine.Nonsingular x2 y2) (e : K) {k j : ℤ} (hjk : j ≤ k)
    (hd : Ex V k ((x1 - x2) ^ 2))
    (h : Ex V j (2 * (x1 * x2 + a) * (x1 + x2) + 4 * b - 2 * e * (x1 - x2) ^ 2) ∨
      Ex V j ((x1 * x2 - a) ^ 2 - 4 * b * (x1 + x2) -
        e * (2 * (x1 * x2 + a) * (x1 + x2) + 4 * b) + e ^ 2 * (x1 - x2) ^ 2)) :
    ∃ (t u : K) (ht : (shortF a b).toAffine.Nonsingular t u), ¬Dv V 1 (t - e) ∧
      (Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ ht ∨
        Point.some _ _ h1 - Point.some _ _ h2 = Point.some _ _ ht) := by
  have hne : x1 ≠ x2 := fun h ↦ by
    have := hd.1; rw [h] at this; simp at this
  obtain ⟨t, t', u, u', ht, ht', hadd, hsub, hsum, hprod⟩ := xpm h1 h2 hne
  by_contra hcon
  have c1 : Dv V 1 (t - e) := by
    by_contra hc; exact hcon ⟨t, u, ht, hc, Or.inl hadd⟩
  have c2 : Dv V 1 (t' - e) := by
    by_contra hc; exact hcon ⟨t', u', ht', hc, Or.inr hsub⟩
  obtain ⟨hs, hp⟩ := coeffs_small c1 c2
  rcases h with h | h
  · have e1 : (t - e + (t' - e)) * (x1 - x2) ^ 2 =
        2 * (x1 * x2 + a) * (x1 + x2) + 4 * b - 2 * e * (x1 - x2) ^ 2 := by
      linear_combination hsum
    have := hs.mul hd.dv
    rw [e1] at this
    exact h.not_dv (by omega) this
  · have e1 : (t - e) * (t' - e) * (x1 - x2) ^ 2 = (x1 * x2 - a) ^ 2 - 4 * b * (x1 + x2) -
        e * (2 * (x1 * x2 + a) * (x1 + x2) + 4 * b) + e ^ 2 * (x1 - x2) ^ 2 := by
      linear_combination hprod - e * hsum
    have := hp.mul hd.dv
    rw [e1] at this
    exact h.not_dv (by omega) this

end ExH
