import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic

/-!
# Abstract discrete valuations with `v(p) = 1` (absolutely unramified residue characteristic `p`)

`DVal K p`: `v : K → ℤ` multiplicative on non-zero elements, ultrametric, `v(−x) = v(x)`,
non-negative on integers, zero on integers prime to `p`, and `v(p) = 1`. Instances: `p`-adic
valuations on `ℚ` and `ℚ_p` (hence on number fields embedded in `ℚ_p`). `PDvd V k q`:
`q ∈ 𝔭^k`, i.e. `q = 0 ∨ k ≤ v(q)`.

This generalises `Elliptic/PVal.lean` (the `p`-adic valuation on `ℚ`) so that the Nagell–Lutz
filtration argument applies to points over number fields.
-/

namespace EllDV

/-- An integer-valued discrete valuation with `v(p) = 1`. -/
structure DVal (K : Type*) [Field K] (p : ℕ) where
  v : K → ℤ
  mul : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  add : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  neg : ∀ x : K, v (-x) = v x
  intCast : ∀ z : ℤ, (z : K) ≠ 0 → 0 ≤ v z
  natCast_unit : ∀ n : ℕ, ¬p ∣ n → v n = 0
  self : v p = 1
  one : v 1 = 0

variable {K : Type*} [Field K] {p : ℕ} (V : DVal K p)

namespace DVal

lemma inv {x : K} (hx : x ≠ 0) : V.v x⁻¹ = -V.v x := by
  have := V.mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, V.one] at this
  omega

lemma div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : V.v (x / y) = V.v x - V.v y := by
  rw [div_eq_mul_inv, V.mul hx (inv_ne_zero hy), V.inv hy]; ring

lemma pow (x : K) (hx : x ≠ 0) (n : ℕ) : V.v (x ^ n) = n * V.v x := by
  induction n with
  | zero => simp [V.one]
  | succ n ih => rw [pow_succ, V.mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

/-- The strict ultrametric equality. -/
lemma add_eq_of_lt {x y : K} (hxy : x + y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (h : V.v x < V.v y) :
    V.v (x + y) = V.v x := by
  have h1 := V.add hx hy hxy
  have h2 : min (V.v (x + y)) (V.v (-y)) ≤ V.v x := by
    have := V.add hxy (neg_ne_zero.mpr hy) (by simpa using hx)
    simpa using this
  rw [V.neg] at h2
  rw [min_eq_left h.le] at h1
  rcases le_total (V.v (x + y)) (V.v y) with h3 | h3
  · rw [min_eq_left h3] at h2; omega
  · rw [min_eq_right h3] at h2; omega

end DVal

/-- `q ∈ 𝔭^k`. -/
def PDvd (k : ℤ) (q : K) : Prop := q = 0 ∨ k ≤ V.v q

variable {V}

lemma pdvd_zero (k : ℤ) : PDvd V k 0 := Or.inl rfl

lemma pdvd_of_ne {k : ℤ} {q : K} (h : PDvd V k q) (hq : q ≠ 0) : k ≤ V.v q := h.resolve_left hq

lemma PDvd.mono {k k' : ℤ} {q : K} (h : PDvd V k q) (hk : k' ≤ k) : PDvd V k' q :=
  h.imp id fun h ↦ hk.trans h

lemma PDvd.neg {k : ℤ} {q : K} (h : PDvd V k q) : PDvd V k (-q) := by
  rcases h with rfl | h
  · simp [pdvd_zero]
  · right; rwa [V.neg]

lemma PDvd.add {k : ℤ} {q r : K} (hq : PDvd V k q) (hr : PDvd V k r) : PDvd V k (q + r) := by
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · rw [add_zero]; exact Or.inr hq
  right
  by_cases hq0 : q = 0
  · subst hq0; simpa using hr
  by_cases hr0 : r = 0
  · subst hr0; simpa using hq
  exact (le_min hq hr).trans (V.add hq0 hr0 hqr)

lemma PDvd.sub {k : ℤ} {q r : K} (hq : PDvd V k q) (hr : PDvd V k r) : PDvd V k (q - r) := by
  rw [sub_eq_add_neg]; exact hq.add hr.neg

lemma PDvd.mul {k l : ℤ} {q r : K} (hq : PDvd V k q) (hr : PDvd V l r) :
    PDvd V (k + l) (q * r) := by
  by_cases h0 : q = 0
  · simp [h0, pdvd_zero]
  by_cases h1 : r = 0
  · simp [h1, pdvd_zero]
  right
  rw [V.mul h0 h1]
  have := pdvd_of_ne hq h0
  have := pdvd_of_ne hr h1
  omega

variable (V) in
lemma pdvd_intCast (z : ℤ) : PDvd V 0 (z : K) := by
  by_cases hz : (z : K) = 0
  · exact Or.inl hz
  exact Or.inr (V.intCast z hz)

variable (V) in
lemma pdvd_natCast (n : ℕ) : PDvd V 0 (n : K) := by exact_mod_cast pdvd_intCast V (n : ℤ)

variable (V) in
lemma pdvd_one : PDvd V 0 (1 : K) := by exact_mod_cast pdvd_natCast V 1

lemma PDvd.pow {k : ℤ} {q : K} (h : PDvd V k q) (n : ℕ) : PDvd V (n * k) (q ^ n) := by
  induction n with
  | zero => simpa using pdvd_one V
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul h
    convert this using 1
    push_cast; ring

/-- `1 + u` is a unit when `u ∈ 𝔭`. -/
lemma val_one_add {u : K} (hu : PDvd V 1 u) : V.v (1 + u) = 0 ∧ 1 + u ≠ 0 := by
  by_cases hu0 : u = 0
  · subst hu0; simp [V.one]
  have hu := pdvd_of_ne hu hu0
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : u = -1 := by linear_combination h
    rw [this, V.neg, V.one] at hu
    omega
  refine ⟨?_, h1u⟩
  rw [V.add_eq_of_lt h1u one_ne_zero hu0 (by rw [V.one]; omega)]
  exact V.one

/-- Division by a unit. -/
lemma PDvd.div_unit {k : ℤ} {q w : K} (h : PDvd V k q) (hw : V.v w = 0)
    (hw0 : w ≠ 0) : PDvd V k (q / w) := by
  rcases h with rfl | h
  · simp [pdvd_zero]
  by_cases hq : q = 0
  · simp [hq, pdvd_zero]
  right
  rw [V.div hq hw0, hw]
  omega

lemma not_pdvd_of_lt {k : ℤ} {q : K} (hq : q ≠ 0) (hk : V.v q < k) : ¬PDvd V k q := by
  rintro (h | h)
  · exact hq h
  · omega

end EllDV
