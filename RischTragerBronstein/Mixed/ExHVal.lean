import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic

/-!
# Integer-valued valuations of residue characteristic `0`

`LVal K`: `v : K → ℤ`, multiplicative on non-zero elements, ultrametric, and zero on the non-zero
natural numbers. `Dv V k q` means `q ∈ 𝔭ᵏ` (`q = 0 ∨ k ≤ v q`), `Ex V k q` means `v q = k` exactly
(`q ≠ 0`). These are the local tools of the exact-height argument (`Mixed/ExH*.lean`): places of
`k(X)` are the instances.
-/

namespace ExH

/-- An integer-valued valuation, trivial on the natural numbers. -/
structure LVal (K : Type*) [Field K] where
  v : K → ℤ
  mul : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  add : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  neg : ∀ x : K, v (-x) = v x
  one : v 1 = 0
  nat : ∀ n : ℕ, (n : K) ≠ 0 → v n = 0

variable {K : Type*} [Field K] (V : LVal K)

namespace LVal

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

end LVal

/-- `q ∈ 𝔭^k`. -/
def Dv (k : ℤ) (q : K) : Prop := q = 0 ∨ k ≤ V.v q

/-- `v q = k` exactly. -/
def Ex (k : ℤ) (q : K) : Prop := q ≠ 0 ∧ V.v q = k

variable {V}

lemma dv_zero (k : ℤ) : Dv V k 0 := Or.inl rfl

lemma dv_of_ne {k : ℤ} {q : K} (h : Dv V k q) (hq : q ≠ 0) : k ≤ V.v q := h.resolve_left hq

lemma Dv.mono {k k' : ℤ} {q : K} (h : Dv V k q) (hk : k' ≤ k) : Dv V k' q :=
  h.imp id fun h ↦ hk.trans h

lemma Dv.neg {k : ℤ} {q : K} (h : Dv V k q) : Dv V k (-q) := by
  rcases h with rfl | h
  · simp [dv_zero]
  · right; rwa [V.neg]

lemma Dv.add {k : ℤ} {q r : K} (hq : Dv V k q) (hr : Dv V k r) : Dv V k (q + r) := by
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

lemma Dv.sub {k : ℤ} {q r : K} (hq : Dv V k q) (hr : Dv V k r) : Dv V k (q - r) := by
  rw [sub_eq_add_neg]; exact hq.add hr.neg

lemma Dv.mul {k l : ℤ} {q r : K} (hq : Dv V k q) (hr : Dv V l r) :
    Dv V (k + l) (q * r) := by
  by_cases h0 : q = 0
  · simp [h0, dv_zero]
  by_cases h1 : r = 0
  · simp [h1, dv_zero]
  right
  rw [V.mul h0 h1]
  have := dv_of_ne hq h0
  have := dv_of_ne hr h1
  omega

/-- Product with an explicit target exponent. -/
lemma Dv.mul' {k l m : ℤ} {q r : K} (hq : Dv V k q) (hr : Dv V l r) (hm : m ≤ k + l) :
    Dv V m (q * r) := (hq.mul hr).mono hm

variable (V) in
lemma dv_natCast (n : ℕ) : Dv V 0 (n : K) := by
  by_cases hz : (n : K) = 0
  · exact Or.inl hz
  exact Or.inr (V.nat n hz).ge

variable (V) in
lemma dv_ofNat (n : ℕ) [n.AtLeastTwo] : Dv V 0 (OfNat.ofNat n : K) := dv_natCast V n

variable (V) in
lemma dv_one : Dv V 0 (1 : K) := by exact_mod_cast dv_natCast V 1

lemma Dv.pow {k : ℤ} {q : K} (h : Dv V k q) (n : ℕ) : Dv V (n * k) (q ^ n) := by
  induction n with
  | zero => simpa using dv_one V
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul h
    convert this using 1
    push_cast; ring

lemma Dv.pow' {k m : ℤ} {q : K} (h : Dv V k q) (n : ℕ) (hm : m ≤ n * k) : Dv V m (q ^ n) :=
  (h.pow n).mono hm

/-- Multiplication by a natural number. -/
lemma Dv.nat_mul {k : ℤ} {q : K} (h : Dv V k q) (n : ℕ) : Dv V k ((n : K) * q) := by
  have := (dv_natCast V n).mul h
  simpa using this

lemma Dv.ofNat_mul {k : ℤ} {q : K} (h : Dv V k q) (n : ℕ) [n.AtLeastTwo] :
    Dv V k ((OfNat.ofNat n : K) * q) := h.nat_mul n

lemma Ex.ne {k : ℤ} {q : K} (h : Ex V k q) : q ≠ 0 := h.1

lemma Ex.dv {k : ℤ} {q : K} (h : Ex V k q) : Dv V k q := Or.inr h.2.ge

lemma Ex.not_dv {k l : ℤ} {q : K} (h : Ex V k q) (hl : k < l) : ¬Dv V l q := by
  rintro (h0 | h0)
  · exact h.1 h0
  · have := h.2; omega

lemma ex_of_ne (q : K) (hq : q ≠ 0) : Ex V (V.v q) q := ⟨hq, rfl⟩

lemma Ex.neg {k : ℤ} {q : K} (h : Ex V k q) : Ex V k (-q) :=
  ⟨neg_ne_zero.mpr h.1, by rw [V.neg]; exact h.2⟩

lemma Ex.mul {k l : ℤ} {q r : K} (hq : Ex V k q) (hr : Ex V l r) : Ex V (k + l) (q * r) :=
  ⟨mul_ne_zero hq.1 hr.1, by rw [V.mul hq.1 hr.1, hq.2, hr.2]⟩

lemma Ex.pow {k : ℤ} {q : K} (h : Ex V k q) (n : ℕ) : Ex V (n * k) (q ^ n) :=
  ⟨pow_ne_zero _ h.1, by rw [V.pow _ h.1, h.2]⟩

lemma Ex.inv {k : ℤ} {q : K} (h : Ex V k q) : Ex V (-k) q⁻¹ :=
  ⟨inv_ne_zero h.1, by rw [V.inv h.1, h.2]⟩

lemma Ex.div {k l : ℤ} {q r : K} (hq : Ex V k q) (hr : Ex V l r) : Ex V (k - l) (q / r) :=
  ⟨div_ne_zero hq.1 hr.1, by rw [V.div hq.1 hr.1, hq.2, hr.2]⟩

variable (V) in
lemma ex_natCast (n : ℕ) (hn : (n : K) ≠ 0) : Ex V 0 (n : K) := ⟨hn, V.nat n hn⟩

variable (V) in
lemma ex_ofNat [CharZero K] (n : ℕ) [n.AtLeastTwo] : Ex V 0 (OfNat.ofNat n : K) :=
  ex_natCast V n (by exact_mod_cast (NeZero.ne n))

variable (V) in
lemma ex_one : Ex V 0 (1 : K) := ⟨one_ne_zero, V.one⟩

/-- **The dominant term**: an element of exact valuation `k` plus an element of `𝔭^{k+1}`. -/
lemma Ex.add_dv {k l : ℤ} {q r : K} (hq : Ex V k q) (hr : Dv V l r) (hl : k < l) :
    Ex V k (q + r) := by
  by_cases hr0 : r = 0
  · subst hr0; simpa using hq
  have hrv := dv_of_ne hr hr0
  have hne : q + r ≠ 0 := by
    intro h
    have : r = -q := by linear_combination h
    rw [this, V.neg, hq.2] at hrv
    omega
  exact ⟨hne, by rw [V.add_eq_of_lt hne hq.1 hr0 (by rw [hq.2]; omega)]; exact hq.2⟩

lemma Ex.dv_add {k l : ℤ} {q r : K} (hq : Ex V k q) (hr : Dv V l r) (hl : k < l) :
    Ex V k (r + q) := by rw [add_comm]; exact hq.add_dv hr hl

lemma Ex.sub_dv {k l : ℤ} {q r : K} (hq : Ex V k q) (hr : Dv V l r) (hl : k < l) :
    Ex V k (q - r) := by rw [sub_eq_add_neg]; exact hq.add_dv hr.neg hl

lemma Ex.dv_sub {k l : ℤ} {q r : K} (hq : Ex V k q) (hr : Dv V l r) (hl : k < l) :
    Ex V k (r - q) := by rw [sub_eq_add_neg, add_comm]; exact hq.neg.add_dv hr hl

/-- Division by an element of exact valuation. -/
lemma Dv.div_ex {k l : ℤ} {q w : K} (h : Dv V k q) (hw : Ex V l w) : Dv V (k - l) (q / w) := by
  by_cases hq : q = 0
  · simp [hq, dv_zero]
  right
  rw [V.div hq hw.1, hw.2]
  have := dv_of_ne h hq
  omega

lemma Dv.mul_ex {k l : ℤ} {q w : K} (h : Dv V k q) (hw : Ex V l w) : Dv V (k + l) (q * w) :=
  h.mul hw.dv

/-- Cancel a factor of exact valuation. -/
lemma dv_of_mul_ex {k l : ℤ} {q w : K} (h : Dv V (k + l) (q * w)) (hw : Ex V l w) : Dv V k q := by
  have := h.div_ex hw
  rw [mul_div_assoc, div_self hw.1, mul_one] at this
  exact this.mono (by omega)

/-- A product in `𝔭^{k+l-1}` has a factor in `𝔭^k` or `𝔭^l`. -/
lemma dv_or_of_mul {k l : ℤ} {q r : K} (h : Dv V (k + l - 1) (q * r)) : Dv V k q ∨ Dv V l r := by
  by_cases hq : q = 0
  · exact Or.inl (Or.inl hq)
  by_cases hr : r = 0
  · exact Or.inr (Or.inl hr)
  have := dv_of_ne h (mul_ne_zero hq hr)
  rw [V.mul hq hr] at this
  by_cases hk : k ≤ V.v q
  · exact Or.inl (Or.inr hk)
  · exact Or.inr (Or.inr (by omega))

/-- **Parity**: a square in `𝔭^k`, `k` odd, lies in `𝔭^{k+1}`. -/
lemma dv_sq_succ {k : ℤ} {y : K} (h : Dv V k (y ^ 2)) (hk : k % 2 = 1) : Dv V (k + 1) (y ^ 2) := by
  by_cases hy : y = 0
  · simp [hy, dv_zero]
  right
  have := dv_of_ne h (pow_ne_zero 2 hy)
  rw [V.pow _ hy] at this ⊢
  push_cast at this ⊢
  omega

/-- A square has even exact valuation. -/
lemma Ex.sq_even {k : ℤ} {y : K} (h : Ex V k (y ^ 2)) : k % 2 = 0 := by
  have hy : y ≠ 0 := fun h0 ↦ h.1 (by simp [h0])
  have := h.2
  rw [V.pow _ hy] at this
  push_cast at this
  omega

/-- The valuation of `y` from that of `y²`. -/
lemma dv_of_sq {k : ℤ} {y : K} (h : Dv V (2 * k) (y ^ 2)) : Dv V k y := by
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  have := dv_of_ne h (pow_ne_zero 2 hy)
  rw [V.pow _ hy] at this
  push_cast at this
  omega

/-- Every element is `0`, in `𝔭`, or has a non-positive exact valuation. -/
lemma dv_or_ex (q : K) (k : ℤ) : Dv V k q ∨ ∃ l, l < k ∧ Ex V l q := by
  by_cases hq : q = 0
  · exact Or.inl (Or.inl hq)
  by_cases h : k ≤ V.v q
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨V.v q, by omega, hq, rfl⟩

/-- **Roots of a quadratic with small coefficients are small**: if `t² = s t − p` with
`s, p ∈ 𝔭`, then `t ∈ 𝔭`. -/
lemma root_small {t s p : K} (h : t ^ 2 = s * t - p) (hs : Dv V 1 s) (hp : Dv V 1 p) :
    Dv V 1 t := by
  rcases dv_or_ex (V := V) t 1 with h1 | ⟨l, hl, ht⟩
  · exact h1
  exfalso
  have h2 : Ex V (2 * l) (t ^ 2) := by simpa using ht.pow 2
  have h3 : Dv V (l + 1) (s * t - p) := ((hs.mul ht.dv).mono (by omega)).sub (hp.mono (by omega))
  rw [← h] at h3
  exact h2.not_dv (by omega) h3

/-- If `t² = s t − p` and `s` or `p` is not in `𝔭`… then some root is not in `𝔭`: here the
contrapositive form used for points: both roots in `𝔭` force `s, p ∈ 𝔭`. -/
lemma coeffs_small {t t' : K} (ht : Dv V 1 t) (ht' : Dv V 1 t') :
    Dv V 1 (t + t') ∧ Dv V 1 (t * t') := ⟨ht.add ht', (ht.mul ht').mono (by omega)⟩

end ExH
