import RischTragerBronstein.Elliptic.NLPoint

/-!
# The Nagell–Lutz theorem (integrality)

`torsion_integral`: a point of finite order on `y² = x³ + ax² + bx + c` (`a, b, c ∈ ℤ`) has
integer coordinates.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllNL

open PVal

variable (a b c : ℤ)

/-- A rational number with non-negative valuation at every prime is an integer. -/
lemma int_of_padicValRat_nonneg (q : ℚ) (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q) :
    ∃ z : ℤ, q = z := by
  refine ⟨q.num, ?_⟩
  by_contra hne
  have hden : q.den ≠ 1 := fun h1 ↦ hne (by rw [← Rat.num_div_den q, h1]; simp)
  set p := q.den.minFac
  have hpp : p.Prime := Nat.minFac_prime hden
  have hpd : p ∣ q.den := Nat.minFac_dvd _
  have hv := h p hpp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hnum : ¬(p : ℤ) ∣ q.num := by
    intro hdvd
    have hA : p ∣ q.num.natAbs := Int.natCast_dvd.mp hdvd
    have hg := Nat.dvd_gcd hA hpd
    rw [q.reduced.gcd_eq_one] at hg
    exact hpp.one_lt.ne' (Nat.dvd_one.mp hg)
  rw [padicValRat] at hv
  have h1 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
  have h2 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hpd
  omega

variable {p : ℕ} [hp : Fact p.Prime]

/-- If `x` is not `p`-integral then neither is `y`. -/
lemma y_neg_of_x_neg {x y : ℚ} (h : OnCurve a b c x y) (hx0 : x ≠ 0)
    (hx : padicValRat p x < 0) : y ≠ 0 ∧ padicValRat p y < 0 := by
  set v := padicValRat p x
  have hrest : PDvd p (2 * v) (a * x ^ 2 + b * x + c) := by
    have h2 : PDvd p (2 * v) ((a : ℚ) * x ^ 2) := by
      have := (pdvd_intCast (p := p) a).mul ((show PDvd p v x from Or.inr le_rfl).pow 2)
      simpa using this
    have h1 : PDvd p (2 * v) ((b : ℚ) * x) := by
      have := (pdvd_intCast (p := p) b).mul (show PDvd p v x from Or.inr le_rfl)
      exact (by simpa using this : PDvd p v ((b : ℚ) * x)).mono (by omega)
    have h0 : PDvd p (2 * v) (c : ℚ) := (pdvd_intCast (p := p) c).mono (by omega)
    exact (h2.add h1).add h0
  have hx3 : padicValRat p (x ^ 3) = 3 * v := by rw [padicValRat.pow x]; push_cast; ring
  have hval : padicValRat p (x ^ 3 + (a * x ^ 2 + b * x + c)) = 3 * v ∧
      x ^ 3 + (a * x ^ 2 + b * x + c) ≠ 0 := by
    by_cases h0 : (a : ℚ) * x ^ 2 + b * x + c = 0
    · rw [h0, add_zero, hx3]; exact ⟨rfl, pow_ne_zero _ hx0⟩
    · have hrv := pdvd_of_ne hrest h0
      have hs0 : x ^ 3 + (a * x ^ 2 + b * x + c) ≠ 0 := by
        intro hs
        have : a * x ^ 2 + b * x + c = -x ^ 3 := by linear_combination hs
        rw [this, padicValRat.neg, hx3] at hrv
        omega
      exact ⟨by rw [padicValRat.add_eq_of_lt hs0 (pow_ne_zero _ hx0) h0 (by rw [hx3]; omega), hx3],
        hs0⟩
  have hy2 : y ^ 2 = x ^ 3 + (a * x ^ 2 + b * x + c) := by rw [h]; ring
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0] at hy2; exact hval.2 (by rw [← hy2]; ring)
  refine ⟨hy0, ?_⟩
  have := hval.1
  rw [← hy2, padicValRat.pow y] at this
  push_cast at this
  omega

/-- **Nagell–Lutz (integrality): a torsion point has integer coordinates.** -/
theorem torsion_integral {x y : ℚ} (h : (W a b c).toAffine.Nonsingular x y)
    (ht : IsOfFinAddOrder (Point.some x y h)) : (∃ X : ℤ, x = X) ∧ ∃ Y : ℤ, y = Y := by
  have hc := (equation_W a b c).mp h.1
  -- `y` is `p`-integral for every `p`
  have hyint : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p y := by
    intro p hpp
    haveI : Fact p.Prime := ⟨hpp⟩
    by_contra hneg
    push_neg at hneg
    have hy0 : y ≠ 0 := by rintro rfl; simp at hneg
    obtain ⟨-, k, hk, -, hyk⟩ := point_val (p := p) a b c hc hy0 hneg
    have hF : InF a b c p k (Point.some x y h) := ⟨hy0, by rw [hyk]⟩
    set n := addOrderOf (Point.some x y h) with hn
    have hn0 : 0 < n := ht.addOrderOf_pos
    have hnP : n • Point.some x y h = 0 := addOrderOf_nsmul_eq_zero _
    by_cases hpn : p ∣ n
    · -- `Q = (n/p) P` has order `p`
      obtain ⟨n', hn'⟩ := hpn
      rw [hn'] at hn0 hnP
      have hn'0 : 0 < n' := by
        rcases Nat.eq_zero_or_pos n' with h0 | h0
        · rw [h0, mul_zero] at hn0; omega
        · exact h0
      set Q := n' • Point.some x y h with hQ
      have hQ0 : Q ≠ 0 := by
        intro hQ0
        have := addOrderOf_le_of_nsmul_eq_zero hn'0 hQ0
        rw [← hn, hn'] at this
        have : 2 ≤ p := hpp.two_le
        nlinarith
      have hpQ : p • Q = 0 := by rw [hQ, ← mul_nsmul', ← hnP]
      obtain ⟨hQF, -⟩ := nsmul_filt a b c k hk (Point.some x y h) hF n'
      rw [← hQ] at hQF
      rcases hQ' : Q with _ | ⟨x', y', h'⟩
      · exact hQ0 hQ'
      rw [hQ'] at hQF hpQ
      have hc' := (equation_W a b c).mp h'.1
      obtain ⟨hy'0, hy'v⟩ := hQF
      obtain ⟨-, k', hk', -, hyk'⟩ := point_val (p := p) a b c hc' hy'0 (by omega)
      have hF' : InF a b c p k' (Point.some x' y' h') := ⟨hy'0, by rw [hyk']⟩
      obtain ⟨-, hpd⟩ := nsmul_filt a b c k' hk' _ hF' p
      rw [hpQ] at hpd
      simp only [tv, zero_sub] at hpd
      have hx'0 : x' ≠ 0 := (point_val (p := p) a b c hc' hy'0 (by omega)).1
      have hval : padicValRat p (-(p * (x' / y'))) = 1 + k' := by
        obtain ⟨-, k'', -, hxk, hyk''⟩ := point_val (p := p) a b c hc' hy'0 (by omega)
        have hkk : k'' = k' := by omega
        rw [padicValRat.neg, padicValRat.mul (by exact_mod_cast hpp.ne_zero)
          (div_ne_zero hx'0 hy'0), padicValRat.div hx'0 hy'0, hxk, hyk'',
          padicValRat.self hpp.one_lt, hkk]
        ring
      have := pdvd_of_ne hpd (neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hpp.ne_zero)
        (div_ne_zero hx'0 hy'0)))
      rw [hval] at this
      omega
    · obtain ⟨-, hpd⟩ := nsmul_filt a b c k hk (Point.some x y h) hF n
      rw [hnP] at hpd
      simp only [tv, zero_sub] at hpd
      have hx0 : x ≠ 0 := (point_val (p := p) a b c hc hy0 hneg).1
      have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
      have hval : padicValRat p (-(n * (x / y))) = k := by
        obtain ⟨-, k'', -, hxk, hyk''⟩ := point_val (p := p) a b c hc hy0 hneg
        have hkk : k'' = k := by omega
        rw [padicValRat.neg, padicValRat.mul hnq (div_ne_zero hx0 hy0),
          padicValRat.div hx0 hy0, hxk, hyk'', padicValRat.of_nat,
          padicValNat.eq_zero_of_not_dvd hpn, hkk]
        ring
      have := pdvd_of_ne hpd (neg_ne_zero.mpr (mul_ne_zero hnq (div_ne_zero hx0 hy0)))
      rw [hval] at this
      omega
  have hxint : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p x := by
    intro p hpp
    haveI : Fact p.Prime := ⟨hpp⟩
    by_contra hneg
    push_neg at hneg
    have hx0 : x ≠ 0 := by rintro rfl; simp at hneg
    have := (y_neg_of_x_neg (p := p) a b c hc hx0 hneg).2
    have := hyint p hpp
    omega
  exact ⟨int_of_padicValRat_nonneg x hxint, int_of_padicValRat_nonneg y hyint⟩

end EllNL
