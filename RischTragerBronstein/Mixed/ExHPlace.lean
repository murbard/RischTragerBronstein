import RischTragerBronstein.Mixed.ExHVal
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The places of `K(X)` as valuations

* `Vinf`: the place at infinity, `v(f) = −deg f`.
* `Vp p hp`: the place of an irreducible polynomial `p`, `v(f) = ord_p(num f) − ord_p(den f)`.

Both are `LVal`s (trivial on the non-zero natural numbers). For polynomials:
`Dv (Vp p hp) k (ι q) ↔ pᵏ ∣ q` (`dv_vp_poly`), `Vinf.v (ι q) = −deg q` (`vinf_poly`).
-/

open Polynomial

namespace ExH

variable {K : Type*} [Field K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- The place at infinity of `K(X)`. -/
noncomputable def Vinf : LVal (RatFunc K) where
  v := fun f ↦ -f.intDegree
  mul := fun hx hy ↦ by rw [RatFunc.intDegree_mul hx hy]; ring
  add := fun {x y} _ hy hxy ↦ by
    have := RatFunc.intDegree_add_le hy hxy
    omega
  neg := fun x ↦ by rw [RatFunc.intDegree_neg]
  one := by simp
  nat := fun n _ ↦ by
    rw [show (n : RatFunc K) = RatFunc.C (n : K) by simp, RatFunc.intDegree_C]; simp

lemma vinf_poly (q : K[X]) : (Vinf (K := K)).v (ι q) = -(q.natDegree : ℤ) := by
  simp [Vinf]

lemma ι_ne {q : K[X]} (hq : q ≠ 0) : ι q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hq

/-- The order of a rational function at a polynomial `p`. -/
noncomputable def ordP (p : K[X]) (f : RatFunc K) : ℤ :=
  (multiplicity p f.num : ℤ) - multiplicity p f.denom

lemma finMult {p : K[X]} (hp : Irreducible p) {q : K[X]} (hq : q ≠ 0) : FiniteMultiplicity p q :=
  FiniteMultiplicity.of_not_isUnit hp.not_isUnit hq

lemma mult_mul {p : K[X]} (hp : Irreducible p) {q r : K[X]} (hq : q ≠ 0) (hr : r ≠ 0) :
    multiplicity p (q * r) = multiplicity p q + multiplicity p r :=
  multiplicity_mul hp.prime (finMult hp (mul_ne_zero hq hr))

lemma ordP_div {p : K[X]} (hp : Irreducible p) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordP p (ι a / ι b) = (multiplicity p a : ℤ) - multiplicity p b := by
  have h : (ι a / ι b).num * b = a * (ι a / ι b).denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hb).mpr rfl
  have hx : ι a / ι b ≠ 0 := div_ne_zero (ι_ne ha) (ι_ne hb)
  have e1 := mult_mul hp (RatFunc.num_ne_zero hx) hb
  have e2 := mult_mul hp ha (ι a / ι b).denom_ne_zero
  rw [h] at e1
  unfold ordP
  omega

lemma ordP_eq {p : K[X]} (hp : Irreducible p) {f : RatFunc K} (hf : f ≠ 0) :
    ∃ a b : K[X], a ≠ 0 ∧ b ≠ 0 ∧ f = ι a / ι b ∧
      ordP p f = (multiplicity p a : ℤ) - multiplicity p b :=
  ⟨f.num, f.denom, RatFunc.num_ne_zero hf, f.denom_ne_zero, (RatFunc.num_div_denom f).symm, rfl⟩

lemma mult_add_ge {p : K[X]} (hp : Irreducible p) {q r : K[X]} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : q + r ≠ 0) : min (multiplicity p q) (multiplicity p r) ≤ multiplicity p (q + r) := by
  rw [← (finMult hp hqr).pow_dvd_iff_le_multiplicity]
  refine dvd_add ?_ ?_
  · exact ((finMult hp hq).pow_dvd_iff_le_multiplicity).mpr (min_le_left _ _)
  · exact ((finMult hp hr).pow_dvd_iff_le_multiplicity).mpr (min_le_right _ _)

/-- The place of an irreducible polynomial. -/
noncomputable def Vp (p : K[X]) (hp : Irreducible p) : LVal (RatFunc K) where
  v := ordP p
  mul := fun {x y} hx hy ↦ by
    obtain ⟨a, b, ha, hb, rfl, e1⟩ := ordP_eq hp hx
    obtain ⟨c, d, hc, hd, rfl, e2⟩ := ordP_eq hp hy
    rw [e1, e2, div_mul_div_comm, ← map_mul, ← map_mul,
      ordP_div hp (mul_ne_zero ha hc) (mul_ne_zero hb hd), mult_mul hp ha hc, mult_mul hp hb hd]
    push_cast; ring
  add := fun {x y} hx hy hxy ↦ by
    obtain ⟨a, b, ha, hb, rfl, e1⟩ := ordP_eq hp hx
    obtain ⟨c, d, hc, hd, rfl, e2⟩ := ordP_eq hp hy
    have hsum : ι a / ι b + ι c / ι d = ι (a * d + b * c) / ι (b * d) := by
      rw [div_add_div _ _ (ι_ne hb) (ι_ne hd)]; simp only [map_add, map_mul]
    have hn : a * d + b * c ≠ 0 := by
      intro h0; apply hxy; rw [hsum, h0, map_zero, zero_div]
    rw [e1, e2, hsum, ordP_div hp hn (mul_ne_zero hb hd), mult_mul hp hb hd]
    have h1 := mult_add_ge hp (mul_ne_zero ha hd) (mul_ne_zero hb hc) hn
    rw [mult_mul hp ha hd, mult_mul hp hb hc] at h1
    push_cast
    omega
  neg := fun x ↦ by
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨a, b, ha, hb, rfl, e1⟩ := ordP_eq hp hx
    rw [e1, ← neg_div, ← map_neg, ordP_div hp (neg_ne_zero.mpr ha) hb, multiplicity_neg]
  one := by simp [ordP]
  nat := fun n hn ↦ by
    have hn' : (n : K) ≠ 0 := by
      intro h0; apply hn
      rw [show (n : RatFunc K) = RatFunc.C (n : K) by simp, h0, map_zero]
    have hC : (C (n : K) : K[X]) ≠ 0 := C_ne_zero.mpr hn'
    have e : (n : RatFunc K) = ι (C (n : K)) / ι 1 := by simp
    rw [e, ordP_div hp hC one_ne_zero, multiplicity_of_isUnit_right (isUnit_C.mpr hn'.isUnit),
      multiplicity_one_right]
    simp

lemma vp_poly {p : K[X]} (hp : Irreducible p) {q : K[X]} (hq : q ≠ 0) :
    (Vp p hp).v (ι q) = multiplicity p q := by
  have e : ι q = ι q / ι 1 := by simp
  change ordP p (ι q) = _
  rw [e, ordP_div hp hq one_ne_zero, multiplicity_one_right]
  simp

/-- **Divisibility by powers of `p`**, as a valuation statement. -/
lemma dv_vp_poly {p : K[X]} (hp : Irreducible p) (q : K[X]) (k : ℕ) :
    Dv (Vp p hp) k (ι q) ↔ p ^ k ∣ q := by
  by_cases hq : q = 0
  · subst hq; simp [dv_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (ι_ne hq)
    · rw [vp_poly hp hq] at h
      exact ((finMult hp hq).pow_dvd_iff_le_multiplicity).mpr (by exact_mod_cast h)
  · intro h
    right
    rw [vp_poly hp hq]
    exact_mod_cast ((finMult hp hq).pow_dvd_iff_le_multiplicity).mp h

/-- Polynomials are integral at every finite place. -/
lemma dv_vp_int {p : K[X]} (hp : Irreducible p) (q : K[X]) : Dv (Vp p hp) 0 (ι q) := by
  have := (dv_vp_poly hp q 0).mpr (by simp)
  simpa using this

lemma dv_vp_one {p : K[X]} (hp : Irreducible p) {q : K[X]} (h : p ∣ q) : Dv (Vp p hp) 1 (ι q) := by
  have := (dv_vp_poly hp q 1).mpr (by simpa using h)
  simpa using this

lemma dvd_of_dv_vp_one {p : K[X]} (hp : Irreducible p) {q : K[X]} (h : Dv (Vp p hp) 1 (ι q)) :
    p ∣ q := by
  have := (dv_vp_poly hp q 1).mp (by simpa using h)
  simpa using this

/-- A polynomial prime to `p` is a unit at `p`. -/
lemma ex_vp_unit {p : K[X]} (hp : Irreducible p) {q : K[X]} (hq : q ≠ 0) (h : ¬p ∣ q) :
    Ex (Vp p hp) 0 (ι q) := by
  refine ⟨ι_ne hq, ?_⟩
  rw [vp_poly hp hq, multiplicity_eq_zero_of_not_dvd h]
  simp

/-- The order at `p` is at most the degree. -/
lemma vp_le_natDegree {p : K[X]} (hp : Irreducible p) {q : K[X]} (hq : q ≠ 0) :
    (Vp p hp).v (ι q) ≤ q.natDegree := by
  rw [vp_poly hp hq]
  have hdvd := pow_multiplicity_dvd p q
  have hle := natDegree_le_of_dvd hdvd hq
  rw [natDegree_pow] at hle
  have hpos : 0 < p.natDegree := hp.natDegree_pos
  have : multiplicity p q ≤ q.natDegree := by nlinarith
  exact_mod_cast this

end ExH
