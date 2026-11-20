import RischTragerBronstein.Mixed.EllHeight

/-!
# Auxiliary polynomial lemmas for the parallelogram estimate

* `gauss_deg`: for `x₃ = p₃/q₃`, `x₄ = p₄/q₄`, the coefficients `q₃q₄`, `q₃p₄ + p₃q₄`, `p₃p₄` of
  `(q₃X − p₃)(q₄X − p₄)` have maximal degree at least `ht x₃ + ht x₄` (the Gauss lemma for the
  degree valuation).
* `dvd_of_prim`: if `Z ∣ W₀ · Pᵢ` for the three coefficients and `(p₃, q₃)`, `(p₄, q₄)` are coprime,
  then `Z ∣ W₀` (the three coefficients generate the unit ideal).
* `WE2`: a weighted-degree estimator in `a, b, u₁, v₁, u₂, v₂`.
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K]

/-- **Gauss lemma for the degree.** -/
theorem gauss_deg (p3 q3 p4 q4 : K[X]) (hq3 : q3 ≠ 0) (hq4 : q4 ≠ 0) :
    max p3.natDegree q3.natDegree + max p4.natDegree q4.natDegree ≤
      max (q3 * q4).natDegree (max (q3 * p4 + p3 * q4).natDegree (p3 * p4).natDegree) := by
  rcases le_total p3.natDegree q3.natDegree with h3 | h3 <;>
    rcases le_total p4.natDegree q4.natDegree with h4 | h4
  · rw [max_eq_right h3, max_eq_right h4, natDegree_mul hq3 hq4]; exact le_max_left _ _
  · -- `q₃` and `p₄` dominate
    rw [max_eq_right h3, max_eq_left h4]
    by_cases hp4 : p4 = 0
    · rw [hp4, natDegree_zero] at h4 ⊢
      have : q4.natDegree = 0 := by omega
      rw [natDegree_mul hq3 hq4, this]; simp
    rcases lt_or_eq_of_le h4 with h4' | h4'
    · by_cases hp3 : p3 = 0
      · rw [hp3]; simp [natDegree_mul hq3 hp4]
      have hlt : (p3 * q4).natDegree < (q3 * p4).natDegree := by
        rw [natDegree_mul hp3 hq4, natDegree_mul hq3 hp4]; omega
      rw [natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_mul hq3 hp4]
      exact le_max_of_le_right (le_max_left _ _)
    · rw [← h4', natDegree_mul hq3 hq4]; exact le_max_left _ _
  · -- `p₃` and `q₄` dominate
    rw [max_eq_left h3, max_eq_right h4]
    by_cases hp3 : p3 = 0
    · rw [hp3, natDegree_zero] at h3 ⊢
      have : q3.natDegree = 0 := by omega
      rw [natDegree_mul hq3 hq4, this]; simp
    rcases lt_or_eq_of_le h3 with h3' | h3'
    · by_cases hp4 : p4 = 0
      · rw [hp4]; simp [natDegree_mul hp3 hq4]
      have hlt : (q3 * p4).natDegree < (p3 * q4).natDegree := by
        rw [natDegree_mul hp3 hq4, natDegree_mul hq3 hp4]; omega
      rw [natDegree_add_eq_right_of_natDegree_lt hlt, natDegree_mul hp3 hq4]
      exact le_max_of_le_right (le_max_left _ _)
    · rw [← h3', natDegree_mul hq3 hq4]; exact le_max_left _ _
  · rw [max_eq_left h3, max_eq_left h4]
    by_cases hp3 : p3 = 0
    · rw [hp3, natDegree_zero] at h3
      have e3 : q3.natDegree = 0 := by omega
      rw [hp3]
      simp only [zero_mul, add_zero, natDegree_zero, zero_add]
      by_cases hp4 : p4 = 0
      · simp [hp4]
      · rw [natDegree_mul hq3 hp4, e3, zero_add]; exact le_max_of_le_right (le_max_left _ _)
    by_cases hp4 : p4 = 0
    · rw [hp4, natDegree_zero] at h4
      have e4 : q4.natDegree = 0 := by omega
      rw [hp4]
      simp only [mul_zero, zero_add, natDegree_zero, add_zero]
      rw [natDegree_mul hp3 hq4, e4, add_zero]; exact le_max_of_le_right (le_max_left _ _)
    rw [natDegree_mul hp3 hp4]
    exact le_max_of_le_right (le_max_right _ _)

/-- **The three coefficients generate the unit ideal**: `Z ∣ W₀ Pᵢ` for all `i` gives `Z ∣ W₀`. -/
theorem dvd_of_prim (p3 q3 p4 q4 W0 Z : K[X]) (hc3 : IsCoprime q3 p3) (hc4 : IsCoprime q4 p4)
    (h2 : Z ∣ W0 * (q3 * q4)) (h1 : Z ∣ W0 * (q3 * p4 + p3 * q4)) (h0 : Z ∣ W0 * (p3 * p4)) :
    Z ∣ W0 := by
  -- `(q₃p₄)²` and `(p₃q₄)²` lie in the ideal
  have hA : Z ∣ W0 * (q3 * p4) ^ 2 := by
    have : W0 * (q3 * p4) ^ 2 = W0 * (q3 * p4 + p3 * q4) * (q3 * p4) - W0 * (q3 * q4) * (p3 * p4) := by
      ring
    rw [this]; exact dvd_sub (h1.mul_right _) (h2.mul_right _)
  have hB : Z ∣ W0 * (p3 * q4) ^ 2 := by
    have : W0 * (p3 * q4) ^ 2 = W0 * (q3 * p4 + p3 * q4) * (p3 * q4) - W0 * (q3 * q4) * (p3 * p4) := by
      ring
    rw [this]; exact dvd_sub (h1.mul_right _) (h2.mul_right _)
  obtain ⟨a, b, hab⟩ := hc4.pow (m := 2) (n := 2)
  obtain ⟨c, d, hcd⟩ := hc3.pow (m := 2) (n := 2)
  have hq3 : Z ∣ W0 * q3 ^ 2 := by
    have : W0 * q3 ^ 2 = a * (W0 * (q3 * q4) * (q3 * q4)) + b * (W0 * (q3 * p4) ^ 2) := by
      linear_combination (-(W0 * q3 ^ 2)) * hab
    rw [this]; exact dvd_add ((h2.mul_right _).mul_left _) (hA.mul_left _)
  have hp3 : Z ∣ W0 * p3 ^ 2 := by
    have : W0 * p3 ^ 2 = a * (W0 * (p3 * q4) ^ 2) + b * (W0 * (p3 * p4) * (p3 * p4)) := by
      linear_combination (-(W0 * p3 ^ 2)) * hab
    rw [this]; exact dvd_add (hB.mul_left _) ((h0.mul_right _).mul_left _)
  have : W0 = c * (W0 * q3 ^ 2) + d * (W0 * p3 ^ 2) := by linear_combination (-W0) * hcd
  rw [this]; exact dvd_add (hq3.mul_left _) (hp3.mul_left _)

/-! ### A weighted-degree estimator for two points -/

/-- Expressions in `a, b` (weight `D`), `u₁, v₁` (weight `M₁`), `u₂, v₂` (weight `M₂`). -/
inductive WE2
  | a | b | u1 | v1 | u2 | v2
  | cst (c : ℤ)
  | add (e f : WE2)
  | sub (e f : WE2)
  | mul (e f : WE2)
  | pow (e : WE2) (n : ℕ)

namespace WE2

/-- Evaluation. -/
noncomputable def ev (A B U1 V1 U2 V2 : K[X]) : WE2 → K[X]
  | a => A
  | b => B
  | u1 => U1
  | v1 => V1
  | u2 => U2
  | v2 => V2
  | cst c => (c : K[X])
  | add e f => ev A B U1 V1 U2 V2 e + ev A B U1 V1 U2 V2 f
  | sub e f => ev A B U1 V1 U2 V2 e - ev A B U1 V1 U2 V2 f
  | mul e f => ev A B U1 V1 U2 V2 e * ev A B U1 V1 U2 V2 f
  | pow e n => ev A B U1 V1 U2 V2 e ^ n

/-- The estimate `(i, k₁, k₂)`: degree `≤ i D + k₁ M₁ + k₂ M₂`. -/
def est : WE2 → ℕ × ℕ × ℕ
  | a => (1, 0, 0)
  | b => (1, 0, 0)
  | u1 => (0, 1, 0)
  | v1 => (0, 1, 0)
  | u2 => (0, 0, 1)
  | v2 => (0, 0, 1)
  | cst _ => (0, 0, 0)
  | add e f => (max (est e).1 (est f).1, max (est e).2.1 (est f).2.1, max (est e).2.2 (est f).2.2)
  | sub e f => (max (est e).1 (est f).1, max (est e).2.1 (est f).2.1, max (est e).2.2 (est f).2.2)
  | mul e f => ((est e).1 + (est f).1, (est e).2.1 + (est f).2.1, (est e).2.2 + (est f).2.2)
  | pow e n => (n * (est e).1, n * (est e).2.1, n * (est e).2.2)

lemma max_bd (i i' k k' l l' D M N : ℕ) :
    i * D + k * M + l * N ≤ max i i' * D + max k k' * M + max l l' * N :=
  add_le_add (add_le_add (Nat.mul_le_mul_right _ (le_max_left _ _))
    (Nat.mul_le_mul_right _ (le_max_left _ _))) (Nat.mul_le_mul_right _ (le_max_left _ _))

lemma max_bd' (i i' k k' l l' D M N : ℕ) :
    i' * D + k' * M + l' * N ≤ max i i' * D + max k k' * M + max l l' * N :=
  add_le_add (add_le_add (Nat.mul_le_mul_right _ (le_max_right _ _))
    (Nat.mul_le_mul_right _ (le_max_right _ _))) (Nat.mul_le_mul_right _ (le_max_right _ _))

theorem est_sound (A B U1 V1 U2 V2 : K[X]) (D M N : ℕ) (hA : A.natDegree ≤ D)
    (hB : B.natDegree ≤ D) (hU1 : U1.natDegree ≤ M) (hV1 : V1.natDegree ≤ M)
    (hU2 : U2.natDegree ≤ N) (hV2 : V2.natDegree ≤ N) :
    ∀ e : WE2, (ev A B U1 V1 U2 V2 e).natDegree ≤ (est e).1 * D + (est e).2.1 * M + (est e).2.2 * N
  | a => by simp [ev, est, hA]
  | b => by simp [ev, est, hB]
  | u1 => by simp [ev, est, hU1]
  | v1 => by simp [ev, est, hV1]
  | u2 => by simp [ev, est, hU2]
  | v2 => by simp [ev, est, hV2]
  | cst c => by simp [ev, est]
  | add e f => by
    have he := est_sound A B U1 V1 U2 V2 D M N hA hB hU1 hV1 hU2 hV2 e
    have hf := est_sound A B U1 V1 U2 V2 D M N hA hB hU1 hV1 hU2 hV2 f
    simp only [ev, est]
    exact (natDegree_add_le _ _).trans (max_le (he.trans (max_bd ..)) (hf.trans (max_bd' ..)))
  | sub e f => by
    have he := est_sound A B U1 V1 U2 V2 D M N hA hB hU1 hV1 hU2 hV2 e
    have hf := est_sound A B U1 V1 U2 V2 D M N hA hB hU1 hV1 hU2 hV2 f
    simp only [ev, est]
    exact (natDegree_sub_le _ _).trans (max_le (he.trans (max_bd ..)) (hf.trans (max_bd' ..)))
  | mul e f => by
    have he := est_sound A B U1 V1 U2 V2 D M N hA hB hU1 hV1 hU2 hV2 e
    have hf := est_sound A B U1 V1 U2 V2 D M N hA hB hU1 hV1 hU2 hV2 f
    simp only [ev, est]
    refine natDegree_mul_le.trans ?_
    nlinarith
  | pow e n => by
    have he := est_sound A B U1 V1 U2 V2 D M N hA hB hU1 hV1 hU2 hV2 e
    simp only [ev, est]
    refine natDegree_pow_le.trans ?_
    calc n * (ev A B U1 V1 U2 V2 e).natDegree ≤
          n * ((est e).1 * D + (est e).2.1 * M + (est e).2.2 * N) := Nat.mul_le_mul_left _ he
      _ = _ := by ring

end WE2

open WE2 in
/-- `W₀ = (u₁v₂ − u₂v₁)²`. -/
def w0E : WE2 := .pow (.sub (.mul .u1 .v2) (.mul .u2 .v1)) 2

open WE2 in
/-- `W₁ = 2((u₁v₂ + u₂v₁)(u₁u₂ + a v₁v₂) + 2 b v₁²v₂²)`. -/
def w1E : WE2 := .mul (.cst 2) (.add (.mul (.add (.mul .u1 .v2) (.mul .u2 .v1))
  (.add (.mul .u1 .u2) (.mul .a (.mul .v1 .v2)))) (.mul (.mul (.cst 2) .b) (.mul (.pow .v1 2) (.pow .v2 2))))

open WE2 in
/-- `W₂ = (u₁u₂ − a v₁v₂)² − 4b(u₁v₂ + u₂v₁) v₁v₂`. -/
def w2E : WE2 := .sub (.pow (.sub (.mul .u1 .u2) (.mul .a (.mul .v1 .v2))) 2)
  (.mul (.mul (.mul (.cst 4) .b) (.add (.mul .u1 .v2) (.mul .u2 .v1))) (.mul .v1 .v2))

lemma est_w : w0E.est = (0, 2, 2) ∧ w1E.est = (1, 2, 2) ∧ w2E.est = (2, 2, 2) := ⟨rfl, rfl, rfl⟩

end FFHeight
