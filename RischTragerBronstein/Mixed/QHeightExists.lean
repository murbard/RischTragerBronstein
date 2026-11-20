import RischTragerBronstein.Mixed.QHeight

/-!
# Height certificates over `ℚ` exist for points of infinite order

Northcott over `ℚ`: finitely many rationals have height `≤ B` (`finite_Hq_le`). If `P` has infinite
order, the doublings `2ᵏP` are affine with `ψ(x) ≠ 0` (`xIter_total`), and their `x`-coordinates
cannot stay of bounded height — two of them would coincide, giving `(2ʲ ∓ 2ⁱ) P = 0`. Hence
`certH` passes for some `k` (**`certH_exists`**): the certificate search of the constant-curve
deciders always succeeds on a point of infinite order.
-/

open FFHeight WeierstrassCurve WeierstrassCurve.Affine

namespace QHeight

/-- **Northcott over `ℚ`.** -/
lemma finite_Hq_le (B : ℕ) : {q : ℚ | Hq q ≤ B}.Finite := by
  have hfin : ((Set.Icc (-(B : ℤ)) B) ×ˢ (Set.Icc 0 B)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine (hfin.image fun p : ℤ × ℕ ↦ (p.1 : ℚ) / p.2).subset fun q hq ↦ ?_
  simp only [Set.mem_setOf_eq, Hq, max_le_iff] at hq
  refine ⟨(q.num, q.den), ⟨⟨?_, ?_⟩, ⟨Nat.zero_le _, hq.2⟩⟩, Rat.num_div_den q⟩
  · have := hq.1; omega
  · have := hq.1; omega

/-- The doubling is defined on an affine point with `P + P ≠ 0`. -/
lemma xDbl_some (a b : ℤ) (x y : ℚ) (h : (qW a b).toAffine.Nonsingular x y)
    (h2 : Point.some x y h + Point.some x y h ≠ 0) :
    ∃ x' y' h', xDbl a b x = some x' ∧ Point.some x y h + Point.some x y h = Point.some x' y' h' := by
  by_cases hψ : evZ a b x.num x.den psiE = 0
  · exfalso
    apply h2
    have hb2 : (qW a b).b₂ = 0 := by simp [WeierstrassCurve.b₂, qW]
    have hb4 : (qW a b).b₄ = 2 * a := by simp [WeierstrassCurve.b₄, qW]
    have hb6 : (qW a b).b₆ = 4 * b := by simp [WeierstrassCurve.b₆, qW]
    have hnum : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
    have hwq : ((x.den : ℤ) : ℚ) ≠ 0 := by simp
    have hpsi : ((evZ a b x.num x.den psiE : ℤ) : ℚ) = ((x.den : ℤ) : ℚ) ^ 4 *
        (4 * x ^ 3 + 0 * x ^ 2 + 2 * (2 * a) * x + 4 * b) := by
      simp only [evZ, psiE]; push_cast; rw [hnum]; ring
    have hden : 4 * x ^ 3 + (qW a b).b₂ * x ^ 2 + 2 * (qW a b).b₄ * x + (qW a b).b₆ = 0 := by
      rw [hb2, hb4, hb6]
      have : ((evZ a b x.num x.den psiE : ℤ) : ℚ) = 0 := by exact_mod_cast hψ
      rw [hpsi] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 4 hwq)
    have hy : y = (qW a b).toAffine.negY x y := (den_duplication_eq_zero_iff h.1).mp hden
    exact Point.add_of_Y_eq rfl hy
  · obtain ⟨y', h', e⟩ := dbl_some a b x y h hψ
    exact ⟨_, y', h', by simp [xDbl, hψ], e⟩

/-- **The doublings of a point of infinite order are all defined.** -/
lemma xIter_total (a b : ℤ) : ∀ (k : ℕ) (x y : ℚ) (h : (qW a b).toAffine.Nonsingular x y),
    (∀ n : ℕ, 0 < n → n • Point.some x y h ≠ 0) →
    ∃ x' y' h', xIter a b k x = some x' ∧ MWPair.dbl^[k] (Point.some x y h) = Point.some x' y' h'
  | 0, x, y, h, _ => ⟨x, y, h, rfl, rfl⟩
  | k + 1, x, y, h, hnt => by
    obtain ⟨x1, y1, h1, hx1, e1⟩ := xDbl_some a b x y h (by
      have := hnt 2 two_pos; rwa [two_nsmul] at this)
    have hnt1 : ∀ n : ℕ, 0 < n → n • Point.some x1 y1 h1 ≠ 0 := fun n hn ↦ by
      rw [← e1, ← two_nsmul, ← mul_nsmul']
      exact hnt _ (by omega)
    obtain ⟨x', y', h', hx', e'⟩ := xIter_total a b k x1 y1 h1 hnt1
    refine ⟨x', y', h', ?_, ?_⟩
    · simp only [xIter, hx1, Option.bind_some, hx']
    · rw [Function.iterate_succ_apply, MWPair.dbl, e1, e']

/-- **Height certificates exist for points of infinite order.** -/
theorem certH_exists (a b : ℤ) (x y : ℚ) (h : (qW a b).toAffine.Nonsingular x y)
    (hnt : ∀ n : ℕ, 0 < n → n • Point.some x y h ≠ 0) : ∃ k, certH a b k x = true := by
  by_contra hall
  push_neg at hall
  have hex := fun k ↦ xIter_total a b k x y h hnt
  choose xs ys hs hxs hpt using hex
  set B : ℕ := (Cq a b).toNat with hB
  have hbd : ∀ k, xs k ∈ {q : ℚ | Hq q ≤ B} := fun k ↦ by
    have hk := hall k
    unfold certH at hk
    rw [hxs k] at hk
    simp only [ne_eq, decide_eq_true_eq, not_lt] at hk
    have h1 := one_le_Hq (xs k)
    show Hq (xs k) ≤ B
    have : (Hq (xs k) : ℤ) ≤ (Hq (xs k) : ℤ) ^ 3 := by
      have h1' : (1 : ℤ) ≤ Hq (xs k) := by exact_mod_cast h1
      simpa using pow_le_pow_right₀ h1' (by norm_num : 1 ≤ 3)
    omega
  obtain ⟨i, -, j, -, hij, hxij⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo
    (fun k _ ↦ hbd k) (finite_Hq_le B)
  -- `2ⁱ P` and `2ʲ P` have the same `x`
  have key : ∀ i j : ℕ, i < j → xs i = xs j → False := by
    intro i j hlt hx
    have hpi := hpt i
    have hpj := hpt j
    rw [MWPair.dbl_iter] at hpi hpj
    obtain ⟨d, hd⟩ : ∃ d, 2 ^ j = 2 ^ i + d := ⟨2 ^ j - 2 ^ i, by
      have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt; omega⟩
    have hd0 : 0 < d := by have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt; omega
    rcases Y_eq_of_X_eq (hs j).1 (hs i).1 hx.symm with hy | hy
    · apply hnt d hd0
      have e : (2 ^ j : ℕ) • Point.some x y h = (2 ^ i : ℕ) • Point.some x y h := by
        rw [hpi, hpj]; simp only [Point.some.injEq]; exact ⟨hx.symm, hy⟩
      rw [hd, add_nsmul] at e
      exact (add_eq_left.mp e)
    · apply hnt (2 ^ j + 2 ^ i) (by positivity)
      rw [add_nsmul, hpi, hpj]
      exact Point.add_of_Y_eq hx.symm hy
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key i j h1 hxij
  · exact key j i h1 hxij.symm

end QHeight
