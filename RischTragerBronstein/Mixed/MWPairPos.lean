import RischTragerBronstein.Mixed.MWPair
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Positivity of the Gram determinant from a Northcott property

For a symmetric `ℤ`-bilinear real pairing `B`, write `q(m, n) = B(mP + nQ, mP + nQ)`. If `q > 0`
off `(0, 0)` and only finitely many `(m, n)` have `q(m, n) ≤ c` (for every `c`), then the Gram
determinant of `P, Q` is positive (`gram_pos_of_finite`): otherwise
`q(m, n) ≤ a (m + t n)²` (`a = q(1, 0)`, `t = B(P, Q)/a`), and Dirichlet's approximation gives
lattice vectors with `0 < q ≤ a/(N + 1)²`, infinitely many of them in the finite set `q ≤ a`.
-/

open Real

namespace MWPair

variable {G : Type*} [AddCommGroup G]

lemma quad_expand (B : G →+ G →+ ℝ) (hsym : ∀ P Q, B P Q = B Q P) (P Q : G) (m n : ℤ) :
    B (m • P + n • Q) (m • P + n • Q) =
      (m : ℝ) ^ 2 * B P P + 2 * m * n * B P Q + (n : ℝ) ^ 2 * B Q Q := by
  simp only [map_add, AddMonoidHom.add_apply, map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul]
  rw [hsym Q P]; ring

lemma quad_smul (B : G →+ G →+ ℝ) (R : G) (j : ℤ) : B (j • R) (j • R) = (j : ℝ) ^ 2 * B R R := by
  simp only [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul]; ring

/-- **Positivity of the Gram determinant.** -/
theorem gram_pos_of_finite (B : G →+ G →+ ℝ) (hsym : ∀ P Q, B P Q = B Q P) (P Q : G)
    (hpos : ∀ m n : ℤ, (m, n) ≠ (0, 0) → 0 < B (m • P + n • Q) (m • P + n • Q))
    (hfin : ∀ c : ℝ, {v : ℤ × ℤ | B (v.1 • P + v.2 • Q) (v.1 • P + v.2 • Q) ≤ c}.Finite) :
    0 < gram B P Q := by
  set q : ℤ × ℤ → ℝ := fun v ↦ B (v.1 • P + v.2 • Q) (v.1 • P + v.2 • Q) with hq
  have ha : 0 < B P P := by
    have := hpos 1 0 (by simp); simpa using this
  set a := B P P
  set p := B P Q
  set t := p / a
  by_contra hg
  push_neg at hg
  have hgram : gram B P Q = a * B Q Q - p ^ 2 := by unfold gram; rw [hsym Q P]; ring
  -- `q(m, n) ≤ a (m + t n)²`
  have hle : ∀ m n : ℤ, q (m, n) ≤ a * (m + t * n) ^ 2 := fun m n ↦ by
    simp only [hq]
    rw [quad_expand B hsym]
    have e : a * ((m : ℝ) + t * n) ^ 2 = (m : ℝ) ^ 2 * a + 2 * m * n * p + (n : ℝ) ^ 2 * (p ^ 2 / a) := by
      simp only [t]; field_simp; ring
    rw [e]
    have : (n : ℝ) ^ 2 * B Q Q ≤ (n : ℝ) ^ 2 * (p ^ 2 / a) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [le_div_iff₀ ha]; nlinarith [hgram]
    linarith
  -- the finite set `q ≤ a` and its least value
  set S := {v : ℤ × ℤ | q v ≤ a}
  have hS := hfin a
  have hS0 : (1, 0) ∈ S := by
    show q (1, 0) ≤ a; simp only [hq]; simp; exact le_rfl
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ v ∈ S, v ≠ (0, 0) → δ ≤ q v := by
    set T := hS.toFinset.filter (· ≠ (0, 0))
    have hT : T.Nonempty := ⟨(1, 0), Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hS0, by simp⟩⟩
    refine ⟨T.inf' hT q, ?_, fun v hv hv0 ↦ Finset.inf'_le _
      (Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hv, hv0⟩)⟩
    show 0 < _
    rw [Finset.lt_inf'_iff]
    intro v hv
    simp only [T, Finset.mem_filter] at hv
    exact hpos v.1 v.2 hv.2
  -- Dirichlet
  obtain ⟨N, hN1, hN⟩ : ∃ N : ℕ, 0 < N ∧ a / ((N : ℝ) + 1) ^ 2 < δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (a / δ)
    refine ⟨N + 1, by omega, ?_⟩
    push_cast
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ0] at hN
    nlinarith
  obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le t (n := N) hN1
  have hv : q (-j, k) ≤ a / ((N : ℝ) + 1) ^ 2 := by
    have h1 := hle (-j) k
    have h2 : ((-j : ℤ) : ℝ) + t * k = k * t - j := by push_cast; ring
    rw [h2] at h1
    have h3 : (k * t - j) ^ 2 ≤ (1 / ((N : ℝ) + 1)) ^ 2 := by
      have := hjk; push_cast at this
      exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    calc q (-j, k) ≤ a * (k * t - j) ^ 2 := h1
      _ ≤ a * (1 / ((N : ℝ) + 1)) ^ 2 := mul_le_mul_of_nonneg_left h3 ha.le
      _ = a / ((N : ℝ) + 1) ^ 2 := by field_simp
  have hvS : (-j, k) ∈ S := by
    show q (-j, k) ≤ a
    refine hv.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ N := by positivity
      nlinarith
    nlinarith [ha]
  have hv0 : ((-j, k) : ℤ × ℤ) ≠ (0, 0) := by simp [hk0.ne']
  linarith [hδ _ hvS hv0]

end MWPair
