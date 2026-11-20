import RischTragerBronstein.Elliptic.DV.Point

/-!
# The kernel of reduction has no torsion (over any field with a valuation, `v(p) = 1`)

`torsion_integral_y`: for `y² = x³ + ax² + bx + c` (`a, b, c ∈ ℤ`) over a field `K` of
characteristic zero with a discrete valuation `V` normalised by `v(p) = 1` (absolutely unramified),
a torsion point `(x, y)` with `y ≠ 0` has `v(y) ≥ 0`. This is the Nagell–Lutz filtration argument
of `Elliptic/NLTorsion.lean`, now for number fields (via embeddings into `ℚ_p`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllDV

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] {p : ℕ} (V : DVal K p) (a b c : ℤ)

/-- **A torsion point is `𝔭`-integral** (`p` prime, `v(p) = 1`). -/
theorem torsion_integral_y (hpp : p.Prime) {x y : K} (h : (W K a b c).toAffine.Nonsingular x y)
    (ht : IsOfFinAddOrder (Point.some x y h)) (hy0 : y ≠ 0) : 0 ≤ V.v y := by
  have hc := (equation_W a b c).mp h.1
  by_contra hneg
  push_neg at hneg
  obtain ⟨-, k, hk, -, hyk⟩ := point_val V a b c hc hy0 hneg
  have hF : InF V a b c k (Point.some x y h) := ⟨hy0, by rw [hyk]⟩
  set n := addOrderOf (Point.some x y h) with hn
  have hn0 : 0 < n := ht.addOrderOf_pos
  have hnP : n • Point.some x y h = 0 := addOrderOf_nsmul_eq_zero _
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hpp.ne_zero
  by_cases hpn : p ∣ n
  · obtain ⟨n', hn'⟩ := hpn
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
    obtain ⟨hQF, -⟩ := nsmul_filt V a b c k hk (Point.some x y h) hF n'
    rw [← hQ] at hQF
    rcases hQ' : Q with _ | ⟨x', y', h'⟩
    · exact hQ0 hQ'
    rw [hQ'] at hQF hpQ
    have hc' := (equation_W a b c).mp h'.1
    obtain ⟨hy'0, hy'v⟩ := hQF
    obtain ⟨hx'0, k', hk', hxk, hyk'⟩ := point_val V a b c hc' hy'0 (by omega)
    have hF' : InF V a b c k' (Point.some x' y' h') := ⟨hy'0, by rw [hyk']⟩
    obtain ⟨-, hpd⟩ := nsmul_filt V a b c k' hk' _ hF' p
    rw [hpQ] at hpd
    simp only [tv, zero_sub] at hpd
    have hval : V.v (-(p * (x' / y'))) = 1 + k' := by
      rw [V.neg, V.mul hpK (div_ne_zero hx'0 hy'0), V.div hx'0 hy'0, hxk, hyk', V.self]
      ring
    have := pdvd_of_ne hpd (neg_ne_zero.mpr (mul_ne_zero hpK (div_ne_zero hx'0 hy'0)))
    rw [hval] at this
    omega
  · obtain ⟨-, hpd⟩ := nsmul_filt V a b c k hk (Point.some x y h) hF n
    rw [hnP] at hpd
    simp only [tv, zero_sub] at hpd
    obtain ⟨hx0, k'', -, hxk, hyk''⟩ := point_val V a b c hc hy0 hneg
    have hnq : (n : K) ≠ 0 := by exact_mod_cast hn0.ne'
    have hval : V.v (-(n * (x / y))) = k := by
      have hkk : k'' = k := by omega
      rw [V.neg, V.mul hnq (div_ne_zero hx0 hy0), V.div hx0 hy0, hxk, hyk'',
        V.natCast_unit n hpn, hkk]
      ring
    have := pdvd_of_ne hpd (neg_ne_zero.mpr (mul_ne_zero hnq (div_ne_zero hx0 hy0)))
    rw [hval] at this
    omega

end EllDV
