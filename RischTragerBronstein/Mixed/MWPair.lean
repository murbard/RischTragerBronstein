import RischTragerBronstein.Mixed.MWTate
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The canonical height pairing

On an abelian group `G`, let `h : G → ℝ` be a naive height with bounded doubling defect
`|h (2 • P) - 4 h P| ≤ C` and bounded parallelogram defect
`|h (P + Q) + h (P - Q) - 2 h P - 2 h Q| ≤ C'`. Then the canonical height `ĥ = MWTate.canon`
satisfies the parallelogram law exactly (`canon_parallelogram`), so
`⟨P, Q⟩ = (ĥ (P + Q) - ĥ P - ĥ Q) / 2` is a symmetric `ℤ`-bilinear pairing (`pairing`).
A non-zero Gram determinant of this pairing certifies that two points satisfy no relation
`m • P = n • Q` (`indep_of_gram`): the independence certificate of the Mordell–Weil plan.
-/

open Filter Topology

namespace MWPair

variable {G : Type*} [AddCommGroup G]

/-- Doubling. -/
def dbl (P : G) : G := P + P

lemma dbl_iter (n : ℕ) (P : G) : dbl^[n] P = (2 ^ n : ℕ) • P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, dbl, ← add_nsmul, pow_succ]; congr 1; ring

lemma dbl_iter_add (n : ℕ) (P Q : G) : dbl^[n] (P + Q) = dbl^[n] P + dbl^[n] Q := by
  simp [dbl_iter]

lemma dbl_iter_sub (n : ℕ) (P Q : G) : dbl^[n] (P - Q) = dbl^[n] P - dbl^[n] Q := by
  simp [dbl_iter, nsmul_sub]

variable {h : G → ℝ} {C C' : ℝ}

/-- The parallelogram law, exact, for the canonical height. -/
theorem canon_parallelogram (hC : ∀ P, |h (dbl P) - 4 * h P| ≤ C)
    (hC' : ∀ P Q, |h (P + Q) + h (P - Q) - 2 * h P - 2 * h Q| ≤ C') (P Q : G) :
    MWTate.canon dbl h (P + Q) + MWTate.canon dbl h (P - Q) =
      2 * MWTate.canon dbl h P + 2 * MWTate.canon dbl h Q := by
  set D : ℕ → ℝ := fun n ↦ MWTate.seq dbl h (P + Q) n + MWTate.seq dbl h (P - Q) n -
    2 * MWTate.seq dbl h P n - 2 * MWTate.seq dbl h Q n
  have hlim : Tendsto D atTop (𝓝 (MWTate.canon dbl h (P + Q) + MWTate.canon dbl h (P - Q) -
      2 * MWTate.canon dbl h P - 2 * MWTate.canon dbl h Q)) :=
    ((((MWTate.tendsto_canon hC (P + Q)).add (MWTate.tendsto_canon hC (P - Q))).sub
      ((MWTate.tendsto_canon hC P).const_mul 2)).sub ((MWTate.tendsto_canon hC Q).const_mul 2))
  have hD : ∀ n, |D n| ≤ C' * (1 / 4) ^ n := fun n ↦ by
    have e : D n = (h (dbl^[n] P + dbl^[n] Q) + h (dbl^[n] P - dbl^[n] Q) - 2 * h (dbl^[n] P) -
        2 * h (dbl^[n] Q)) / 4 ^ n := by
      simp only [D, MWTate.seq, dbl_iter_add, dbl_iter_sub]; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n), one_div_pow, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hC' _ _) (by positivity)
  have h0 : Tendsto D atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ ↦ C' * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul C'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hg.neg) hg
      (fun n ↦ (abs_le.mp (hD n)).1) (fun n ↦ (abs_le.mp (hD n)).2)
  have := tendsto_nhds_unique hlim h0
  linarith

section Quadratic

variable (f : G → ℝ) (par : ∀ P Q, f (P + Q) + f (P - Q) = 2 * f P + 2 * f Q)
include par

lemma f_zero : f 0 = 0 := by have := par 0 0; simp at this; linarith

lemma f_neg (Q : G) : f (-Q) = f Q := by
  have := par 0 Q; rw [f_zero f par] at this; simp at this; linarith

/-- The key cubic identity: `f (x+y+z) = f (x+y) + f (x+z) + f (y+z) - f x - f y - f z`. -/
lemma f_three (x y z : G) :
    f (x + y + z) = f (x + y) + f (x + z) + f (y + z) - f x - f y - f z := by
  have p1 := par (x + y) z
  have p2 := par (x + z) y
  have p3 := par x (y - z)
  have p4 := par y z
  have e1 : x + z + y = x + y + z := by abel
  have e3 : x + (y - z) = x + y - z := by abel
  have e4 : x - (y - z) = x + z - y := by abel
  rw [e1] at p2; rw [e3, e4] at p3
  linarith

/-- The polarization `⟨P, Q⟩ = (f (P + Q) - f P - f Q) / 2`. -/
noncomputable def polar (P Q : G) : ℝ := (f (P + Q) - f P - f Q) / 2

lemma polar_add_left (P P' Q : G) : polar f (P + P') Q = polar f P Q + polar f P' Q := by
  unfold polar
  have := f_three f par P P' Q
  linarith

omit par in
lemma polar_comm (P Q : G) : polar f P Q = polar f Q P := by unfold polar; rw [add_comm]; ring

/-- The pairing as a `ℤ`-bilinear map. -/
noncomputable def pairing : G →+ G →+ ℝ where
  toFun P :=
    { toFun := fun Q ↦ polar f P Q
      map_zero' := by unfold polar; simp [f_zero f par]
      map_add' := fun Q Q' ↦ by
        rw [polar_comm f, polar_add_left f par, polar_comm f Q, polar_comm f Q'] }
  map_zero' := by ext Q; simp [polar, f_zero f par]
  map_add' := fun P P' ↦ by ext Q; simp [polar_add_left f par]

lemma pairing_apply (P Q : G) : pairing f par P Q = polar f P Q := rfl

lemma pairing_self (P : G) : pairing f par P P = f P := by
  rw [pairing_apply, polar]
  have := par P P; simp [f_zero f par] at this
  have e : P + P = (2 : ℕ) • P := by simp [two_nsmul]
  linarith

end Quadratic

/-- The Gram determinant of `P, Q` for a real pairing. -/
def gram (B : G →+ G →+ ℝ) (P Q : G) : ℝ := B P P * B Q Q - B P Q * B Q P

/-- **A non-zero Gram determinant certifies independence** (real-valued pairing). -/
theorem gram_ne_zero_indep (B : G →+ G →+ ℝ) (hsym : ∀ P Q, B P Q = B Q P) (P Q : G)
    (hg : gram B P Q ≠ 0) (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 := by
  have h1 : (m : ℝ) * B P P = n * B Q P := by
    have := congrArg (fun x ↦ B x P) hrel
    simpa [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul] using this
  have h2 : (m : ℝ) * B P Q = n * B Q Q := by
    have := congrArg (fun x ↦ B x Q) hrel
    simpa [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul] using this
  unfold gram at hg
  by_contra hne
  rcases not_and_or.mp hne with hm | hn
  · have hmq : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    apply hg
    have e1 : B P P = n / m * B Q P := by field_simp; linarith
    have e2 : B P Q = n / m * B Q Q := by field_simp; linarith
    rw [e1, e2, hsym Q P, e2]; ring
  · have hnq : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    apply hg
    have e1 : B Q Q = m / n * B P Q := by field_simp; linarith
    have e2 : B Q P = m / n * B P P := by field_simp; linarith
    rw [e1, e2, hsym P Q, e2]; ring

/-- **Independence certificate from a naive height**: with bounded doubling and parallelogram
defects, a non-zero Gram determinant of the canonical pairing rules out every relation. -/
theorem indep_of_gram (hC : ∀ P, |h (dbl P) - 4 * h P| ≤ C)
    (hC' : ∀ P Q, |h (P + Q) + h (P - Q) - 2 * h P - 2 * h Q| ≤ C') (P Q : G)
    (hg : gram (pairing _ (canon_parallelogram hC hC')) P Q ≠ 0) (m n : ℤ)
    (hrel : m • P = n • Q) : m = 0 ∧ n = 0 :=
  gram_ne_zero_indep _ (fun _ _ ↦ polar_comm _ _ _) P Q hg m n hrel

/-- `ĥ (dᵏ P) = 4ᵏ ĥ P`. -/
lemma canon_iter (hC : ∀ P, |h (dbl P) - 4 * h P| ≤ C) (k : ℕ) (P : G) :
    MWTate.canon dbl h (dbl^[k] P) = 4 ^ k * MWTate.canon dbl h P := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', MWTate.canon_double hC, ih, pow_succ]; ring

/-- **Computable approximation**: `|ĥ P - h (2ᵏ P) / 4ᵏ| ≤ C / (3 · 4ᵏ)`. -/
theorem canon_approx (hC : ∀ P, |h (dbl P) - 4 * h P| ≤ C) (k : ℕ) (P : G) :
    |MWTate.canon dbl h P - h (dbl^[k] P) / 4 ^ k| ≤ C / 3 / 4 ^ k := by
  have h1 := MWTate.abs_canon_sub_le hC (dbl^[k] P)
  rw [canon_iter hC] at h1
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have e : MWTate.canon dbl h P - h (dbl^[k] P) / 4 ^ k =
      (4 ^ k * MWTate.canon dbl h P - h (dbl^[k] P)) / 4 ^ k := by field_simp
  rw [e, abs_div, abs_of_pos h4]
  exact div_le_div_of_nonneg_right h1 h4.le

/-- The Gram determinant of the canonical pairing in terms of three heights. -/
lemma gram_pairing (f : G → ℝ) (par : ∀ P Q, f (P + Q) + f (P - Q) = 2 * f P + 2 * f Q) (P Q : G) :
    gram (pairing f par) P Q = f P * f Q - ((f (P + Q) - f P - f Q) / 2) ^ 2 := by
  unfold gram
  rw [pairing_self, pairing_self, pairing_apply, pairing_apply, polar_comm f Q P]
  unfold polar; ring

/-- Perturbation bound for `g x y z = x y - ((z - x - y) / 2) ^ 2`. -/
lemma gram_perturb (x y z a b c e : ℝ) (hx : |x - a| ≤ e) (hy : |y - b| ≤ e) (hz : |z - c| ≤ e) :
    |(x * y - ((z - x - y) / 2) ^ 2) - (a * b - ((c - a - b) / 2) ^ 2)| ≤
      e * (|a| + |b| + e) + 3 * e / 2 * (|c - a - b| + 3 * e / 2) := by
  set d1 := x - a; set d2 := y - b
  set w := (c - a - b) / 2; set η := ((z - c) - d1 - d2) / 2
  have he : 0 ≤ e := (abs_nonneg _).trans hx
  have hη : |η| ≤ 3 * e / 2 := by
    have : |(z - c) - d1 - d2| ≤ 3 * e :=
      (abs_sub _ _).trans (by linarith [abs_sub (z - c) d1, abs_sub ((z - c) - d1) d2])
    simp only [η, abs_div, abs_two]; linarith
  have hw : |2 * w + η| ≤ |c - a - b| + 3 * e / 2 := by
    have : 2 * w = c - a - b := by simp only [w]; ring
    rw [this]; exact (abs_add_le _ _).trans (by linarith)
  have e1 : (x * y - ((z - x - y) / 2) ^ 2) - (a * b - ((c - a - b) / 2) ^ 2) =
      (a * d2 + b * d1 + d1 * d2) - η * (2 * w + η) := by
    simp only [d1, d2, w, η]; ring
  rw [e1]
  have t1 : |a * d2 + b * d1 + d1 * d2| ≤ e * (|a| + |b| + e) := by
    have := abs_add_le (a * d2 + b * d1) (d1 * d2)
    have := abs_add_le (a * d2) (b * d1)
    simp only [abs_mul] at *
    have : |a| * |d2| ≤ |a| * e := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    have : |b| * |d1| ≤ |b| * e := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have : |d1| * |d2| ≤ e * e := mul_le_mul hx hy (abs_nonneg _) he
    nlinarith
  have t2 : |η * (2 * w + η)| ≤ 3 * e / 2 * (|c - a - b| + 3 * e / 2) := by
    rw [abs_mul]; exact mul_le_mul hη hw (abs_nonneg _) (by linarith)
  exact (abs_sub _ _).trans (add_le_add t1 t2)

/-- **The certificate**: approximations `a, b, c` of `ĥ P, ĥ Q, ĥ (P + Q)` read off at level `k`
(`canon_approx`) whose Gram value exceeds the perturbation bound prove independence. -/
theorem indep_of_approx (hC : ∀ P, |h (dbl P) - 4 * h P| ≤ C)
    (hC' : ∀ P Q, |h (P + Q) + h (P - Q) - 2 * h P - 2 * h Q| ≤ C') (P Q : G) (k : ℕ)
    (hgap : C / 3 / 4 ^ k * (|h (dbl^[k] P) / 4 ^ k| + |h (dbl^[k] Q) / 4 ^ k| + C / 3 / 4 ^ k) +
        3 * (C / 3 / 4 ^ k) / 2 * (|h (dbl^[k] (P + Q)) / 4 ^ k - h (dbl^[k] P) / 4 ^ k -
          h (dbl^[k] Q) / 4 ^ k| + 3 * (C / 3 / 4 ^ k) / 2) <
      |h (dbl^[k] P) / 4 ^ k * (h (dbl^[k] Q) / 4 ^ k) - ((h (dbl^[k] (P + Q)) / 4 ^ k -
          h (dbl^[k] P) / 4 ^ k - h (dbl^[k] Q) / 4 ^ k) / 2) ^ 2|)
    (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 := by
  refine indep_of_gram hC hC' P Q ?_ m n hrel
  rw [gram_pairing]
  intro h0
  have := gram_perturb _ _ _ _ _ _ _ (canon_approx hC k P) (canon_approx hC k Q)
    (canon_approx hC k (P + Q))
  rw [h0, zero_sub, abs_neg] at this
  linarith

end MWPair
