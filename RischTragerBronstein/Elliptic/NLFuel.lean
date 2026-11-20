import RischTragerBronstein.Elliptic.NLBound

/-!
# The torsion test always terminates: an explicit fuel bound

If `torsionTest P F = none` then `P, 2P, …, FP` are distinct, non-zero, and none is a
certificate of infinite order: each has integer coordinates `(X, Y)` with `Y = 0` or `Y ∣ D`, so
`|Y| ≤ |D|` (`D ≠ 0`) and, `X` being a root of `X³ + aX² + bX + (c − Y²)`, `|X| ≤ 1 + |a| + |b| +
|c| + D²` (Cauchy). Hence `F ≤ (2B + 1)(2|D| + 1)`, and `torsionTest P (fuelBound a b c) ≠ none`
(`torsionTest_isSome`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllNL

variable (a b c : ℤ)

/-- The bound on `|X|`. -/
def xBound : ℤ := 1 + |a| + |b| + |c| + disc a b c ^ 2

/-- Enough fuel for the torsion test. -/
def fuelBound : ℕ := ((2 * xBound a b c + 1) * (2 * |disc a b c| + 1)).toNat + 1

lemma torsionTest_none {P : (W a b c).toAffine.Point} :
    ∀ {F : ℕ}, torsionTest a b c P F = none →
      ∀ k, 1 ≤ k → k ≤ F → k • P ≠ 0 ∧ badMultiple a b c P k = false
  | 0, _, k, h1, h2 => by omega
  | F + 1, h, k, h1, h2 => by
    unfold torsionTest at h
    split at h
    · exact absurd h (by simp)
    · rename_i hF
      split_ifs at h with hz hb
      rcases Nat.lt_or_ge k (F + 1) with hk | hk
      · exact torsionTest_none hF k h1 (by omega)
      · have : k = F + 1 := by omega
        subst this
        exact ⟨hz, by simpa using hb⟩

/-- Cauchy's bound for an integer root of a monic cubic. -/
lemma cauchy (X a b c' : ℤ) (h : X ^ 3 + a * X ^ 2 + b * X + c' = 0) :
    |X| ≤ 1 + |a| + |b| + |c'| := by
  by_contra hlt
  push_neg at hlt
  have hX1 : 1 ≤ |X| := by linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c']
  have e : |X| ^ 3 = |a * X ^ 2 + b * X + c'| := by
    rw [← abs_pow, show X ^ 3 = -(a * X ^ 2 + b * X + c') by linarith, abs_neg]
  have hle : |a * X ^ 2 + b * X + c'| ≤ (|a| + |b| + |c'|) * |X| ^ 2 := by
    calc |a * X ^ 2 + b * X + c'| ≤ |a * X ^ 2| + |b * X| + |c'| := abs_add_three _ _ _
      _ = |a| * |X| ^ 2 + |b| * |X| + |c'| := by rw [abs_mul, abs_mul, abs_pow]
      _ ≤ (|a| + |b| + |c'|) * |X| ^ 2 := by
        have h1 : |X| ≤ |X| ^ 2 := by nlinarith
        have h2 : 1 ≤ |X| ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg b),
          mul_le_mul_of_nonneg_left h2 (abs_nonneg c')]
  have : |X| ^ 3 > (|a| + |b| + |c'|) * |X| ^ 2 := by
    have hX2 : 0 < |X| ^ 2 := by positivity
    have : |X| > |a| + |b| + |c'| := by linarith
    calc |X| ^ 3 = |X| * |X| ^ 2 := by ring
      _ > (|a| + |b| + |c'|) * |X| ^ 2 := by nlinarith
  linarith

/-- Integer coordinates of a point (`(0, 0)` for `0`). -/
def coords : (W a b c).toAffine.Point → ℤ × ℤ
  | .zero => (0, 0)
  | .some x y _ => (x.num, y.num)

/-- A good (not a certificate) non-zero point. -/
def Good (Q : (W a b c).toAffine.Point) : Prop :=
  Q ≠ 0 ∧ (match Q with
      | .zero => false
      | .some x y _ => x.den != 1 || y.den != 1 || (y != 0 && !decide (y.num ∣ disc a b c))) = false

lemma coords_box (hD : disc a b c ≠ 0) {Q : (W a b c).toAffine.Point} (hQ : Good a b c Q) :
    (coords a b c Q).1 ∈ Finset.Icc (-xBound a b c) (xBound a b c) ∧
      (coords a b c Q).2 ∈ Finset.Icc (-|disc a b c|) (|disc a b c|) := by
  match Q, hQ with
  | .zero, hQ => exact absurd rfl hQ.1
  | .some x y h, hQ =>
    obtain ⟨-, hb⟩ := hQ
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, Bool.and_eq_false_iff,
      Bool.not_eq_false', decide_eq_true_eq] at hb
    obtain ⟨⟨hx, hy⟩, hdv⟩ := hb
    have hxq : x = (x.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hx).symm
    have hyq : y = (y.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hy).symm
    have hyD : |y.num| ≤ |disc a b c| := by
      rcases hdv with h0 | h0
      · have : y.num = 0 := by
          have : y = 0 := by simpa using h0
          rw [this]; rfl
        rw [this, abs_zero]; exact abs_nonneg _
      · exact Int.le_of_dvd (abs_pos.mpr hD) ((abs_dvd_abs _ _).mpr h0) |>.trans le_rfl
    have hc := (equation_W a b c).mp h.1
    unfold OnCurve at hc
    rw [hxq, hyq] at hc
    have hci : x.num ^ 3 + a * x.num ^ 2 + b * x.num + (c - y.num ^ 2) = 0 := by
      have : ((y.num : ℤ) : ℚ) ^ 2 = (x.num : ℚ) ^ 3 + a * x.num ^ 2 + b * x.num + c := hc
      have h' : ((x.num ^ 3 + a * x.num ^ 2 + b * x.num + (c - y.num ^ 2) : ℤ) : ℚ) = 0 := by
        push_cast; linarith
      exact_mod_cast h'
    have hX := cauchy x.num a b (c - y.num ^ 2) hci
    have hc2 : |c - y.num ^ 2| ≤ |c| + disc a b c ^ 2 := by
      calc |c - y.num ^ 2| ≤ |c| + |y.num ^ 2| := abs_sub _ _
        _ = |c| + |y.num| ^ 2 := by rw [abs_pow]
        _ ≤ |c| + |disc a b c| ^ 2 := by
          gcongr
        _ = |c| + disc a b c ^ 2 := by rw [sq_abs]
    simp only [coords, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have := neg_abs_le x.num; unfold xBound; linarith
    · have := le_abs_self x.num; unfold xBound; linarith
    · have := neg_abs_le y.num; linarith
    · have := le_abs_self y.num; linarith

lemma coords_eq {Q Q' : (W a b c).toAffine.Point} (hQ : Good a b c Q) (hQ' : Good a b c Q')
    (h : coords a b c Q = coords a b c Q') : Q = Q' := by
  match Q, Q', hQ, hQ', h with
  | .zero, _, hQ, _, _ => exact absurd rfl hQ.1
  | _, .zero, _, hQ', _ => exact absurd rfl hQ'.1
  | .some x y hxy, .some x' y' hxy', hQ, hQ', h =>
    obtain ⟨-, hb⟩ := hQ
    obtain ⟨-, hb'⟩ := hQ'
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hb hb'
    simp only [coords, Prod.mk.injEq] at h
    have hx : x = x' := by
      rw [← Rat.coe_int_num_of_den_eq_one hb.1.1, ← Rat.coe_int_num_of_den_eq_one hb'.1.1, h.1]
    have hy : y = y' := by
      rw [← Rat.coe_int_num_of_den_eq_one hb.1.2, ← Rat.coe_int_num_of_den_eq_one hb'.1.2, h.2]
    subst hx hy
    rfl

/-- **The torsion test terminates within `fuelBound`.** -/
theorem torsionTest_isSome (hD : disc a b c ≠ 0) (P : (W a b c).toAffine.Point) :
    torsionTest a b c P (fuelBound a b c) ≠ none := by
  intro hn
  have hall := torsionTest_none a b c hn
  have hgood : ∀ k ∈ Finset.Icc 1 (fuelBound a b c), Good a b c (k • P) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨h1, h2⟩ := hall k hk.1 hk.2
    refine ⟨h1, ?_⟩
    unfold badMultiple at h2
    exact h2
  have hmaps : ∀ k ∈ Finset.Icc 1 (fuelBound a b c), coords a b c (k • P) ∈
      Finset.Icc (-xBound a b c) (xBound a b c) ×ˢ Finset.Icc (-|disc a b c|) (|disc a b c|) := by
    intro k hk
    exact Finset.mem_product.mpr (coords_box a b c hD (hgood k hk))
  have hinj : Set.InjOn (fun k : ℕ ↦ coords a b c (k • P))
      (Finset.Icc 1 (fuelBound a b c) : Set ℕ) := by
    intro i hi j hj hij
    have he := coords_eq a b c (hgood i hi) (hgood j hj) hij
    rw [Finset.coe_Icc, Set.mem_Icc] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (j - i) • P = 0 := by
        rw [sub_nsmul P hlt.le, he]; exact add_neg_cancel _
      exact (hall (j - i) (by omega) (by omega)).1 this
    · have : (i - j) • P = 0 := by
        rw [sub_nsmul P hlt.le, he]; exact add_neg_cancel _
      exact (hall (i - j) (by omega) (by omega)).1 this
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc, Finset.card_product, Int.card_Icc, Int.card_Icc] at hcard
  have hB : 0 ≤ xBound a b c := by
    unfold xBound; positivity
  unfold fuelBound at hcard
  have e1 : (xBound a b c + 1 - -xBound a b c).toNat = (2 * xBound a b c + 1).toNat := by
    congr 1; ring
  have e2 : (|disc a b c| + 1 - -|disc a b c|).toNat = (2 * |disc a b c| + 1).toNat := by
    congr 1; ring
  rw [e1, e2, ← Int.toNat_mul (by positivity) (by positivity)] at hcard
  omega

/-- More fuel gives the same answer. -/
lemma torsionTest_mono {P : (W a b c).toAffine.Point} {r : Bool} {F : ℕ}
    (h : torsionTest a b c P F = some r) : ∀ F', F ≤ F' → torsionTest a b c P F' = some r := by
  intro F' hF
  induction F' with
  | zero =>
    have : F = 0 := by omega
    subst this; simp [torsionTest] at h
  | succ F' ih =>
    rcases Nat.eq_or_lt_of_le hF with hF | hF
    · rw [← hF]; exact h
    · unfold torsionTest
      rw [ih (by omega)]

/-- With at least `fuelBound` fuel the torsion test answers. -/
theorem torsionTest_isSome' (hD : disc a b c ≠ 0) (P : (W a b c).toAffine.Point) (F : ℕ)
    (hF : fuelBound a b c ≤ F) : torsionTest a b c P F ≠ none := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (torsionTest_isSome a b c hD P)
  rw [torsionTest_mono a b c hr F hF]; simp

end EllNL
