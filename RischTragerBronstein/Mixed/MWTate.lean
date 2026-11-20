import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tate's telescoping construction of the canonical height

Let `d : G → G` be a map (doubling on a Mordell–Weil group) and `h : G → ℝ` a naive height with
`|h (d P) - 4 h P| ≤ C` for all `P`. Then `ĥ P = lim h (dⁿ P) / 4ⁿ` exists (`tendsto_canon`), it
differs from `h` by at most `C / 3` (`abs_canon_sub_le`), it satisfies `ĥ (d P) = 4 ĥ P`
(`canon_double`), and it is the unique function with these two properties (`canon_unique`).

This is the analytic layer of the Mordell–Weil plan: the naive Weil height of `FFHeight` and a
bound `C` give the canonical height, whose pairing feeds `MW.gram_ne_zero_indep`.
-/

open Filter Topology

namespace MWTate

variable {G : Type*} (d : G → G) (h : G → ℝ) (C : ℝ)

/-- The telescoping sequence `h (dⁿ P) / 4ⁿ`. -/
noncomputable def seq (P : G) (n : ℕ) : ℝ := h (d^[n] P) / 4 ^ n

/-- The canonical height: the limit of `seq`. -/
noncomputable def canon (P : G) : ℝ := limUnder atTop (seq d h P)

variable {d h C}

lemma dist_seq_le (hC : ∀ P, |h (d P) - 4 * h P| ≤ C) (P : G) (n : ℕ) :
    dist (seq d h P n) (seq d h P (n + 1)) ≤ C / 4 * (1 / 4) ^ n := by
  rw [Real.dist_eq, seq, seq, Function.iterate_succ_apply']
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have e : h (d^[n] P) / 4 ^ n - h (d (d^[n] P)) / 4 ^ (n + 1) =
      -(h (d (d^[n] P)) - 4 * h (d^[n] P)) / 4 ^ (n + 1) := by
    field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (n + 1))]
  rw [div_le_iff₀ (by positivity), one_div_pow, pow_succ]
  have := hC (d^[n] P)
  calc _ ≤ C := this
    _ = C / 4 * (1 / 4 ^ n) * (4 ^ n * 4) := by field_simp

theorem tendsto_canon (hC : ∀ P, |h (d P) - 4 * h P| ≤ C) (P : G) :
    Tendsto (seq d h P) atTop (𝓝 (canon d h P)) :=
  (cauchySeq_of_le_geometric (1 / 4 : ℝ) (C / 4) (by norm_num) (dist_seq_le hC P)).tendsto_limUnder

theorem abs_canon_sub_le (hC : ∀ P, |h (d P) - 4 * h P| ≤ C) (P : G) :
    |canon d h P - h P| ≤ C / 3 := by
  have := dist_le_of_le_geometric_of_tendsto₀ (1 / 4 : ℝ) (C / 4) (by norm_num) (dist_seq_le hC P)
    (tendsto_canon hC P)
  have e : C / 4 / (1 - 1 / 4) = C / 3 := by ring
  rw [e, Real.dist_eq, abs_sub_comm] at this
  simpa [seq] using this

theorem canon_double (hC : ∀ P, |h (d P) - 4 * h P| ≤ C) (P : G) :
    canon d h (d P) = 4 * canon d h P := by
  have h1 := tendsto_canon hC (d P)
  have h2 : Tendsto (fun n ↦ 4 * seq d h P (n + 1)) atTop (𝓝 (4 * canon d h P)) :=
    ((tendsto_canon hC P).comp (tendsto_add_atTop_nat 1)).const_mul 4
  have e : (fun n ↦ 4 * seq d h P (n + 1)) = seq d h (d P) := by
    funext n; simp only [seq, Function.iterate_succ_apply]
    rw [pow_succ]; field_simp
  rw [e] at h2
  exact tendsto_nhds_unique h1 h2

/-- Uniqueness: a function `g` with `g (d P) = 4 g P` within bounded distance of `h` is `ĥ`. -/
theorem canon_unique (hC : ∀ P, |h (d P) - 4 * h P| ≤ C) (g : G → ℝ) (B : ℝ)
    (hg : ∀ P, g (d P) = 4 * g P) (hB : ∀ P, |g P - h P| ≤ B) (P : G) : g P = canon d h P := by
  set f : G → ℝ := fun Q ↦ g Q - canon d h Q
  have hf : ∀ Q, f (d Q) = 4 * f Q := fun Q ↦ by
    simp only [f, hg, canon_double hC]; ring
  have hfb : ∀ Q, |f Q| ≤ B + C / 3 := fun Q ↦ by
    have := abs_canon_sub_le hC Q
    calc |f Q| = |(g Q - h Q) - (canon d h Q - h Q)| := by simp only [f]; ring_nf
      _ ≤ |g Q - h Q| + |canon d h Q - h Q| := abs_sub _ _
      _ ≤ B + C / 3 := add_le_add (hB Q) this
  have hit : ∀ n : ℕ, f (d^[n] P) = 4 ^ n * f P := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', hf, ih, pow_succ]; ring
  by_contra hne
  have hf0 : f P ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < |f P| := abs_pos.mpr hf0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((B + C / 3) / |f P|) (by norm_num : (1 : ℝ) < 4)
  have := hfb (d^[n] P)
  rw [hit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n)] at this
  rw [div_lt_iff₀ hpos] at hn
  linarith

end MWTate
