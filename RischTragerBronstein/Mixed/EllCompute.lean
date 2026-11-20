import RischTragerBronstein.Mixed.EllNT
import RischTragerBronstein.Computable.SquarefreePart

/-!
# Computing naive heights (step 4a)

Executable representation of `x`-coordinates over `K(X)` as pairs `(u, v)` of `CPoly K` (for
`K = ℚ` these evaluate). `reduce` divides by the executable gcd; the result is coprime
(`reduce_coprime`) with the same quotient (`reduce_div`), so the naive height is
`max (deg u') (deg v')` (`htPair_spec`, via `ht_div_coprime`).
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K] [DecidableEq K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- The executable degree. -/
def cdeg (p : CPoly K) : ℕ := (CPoly.trim p).length - 1

lemma cdeg_spec (p : CPoly K) : cdeg p = (CPoly.toPoly p).natDegree := by
  unfold cdeg
  by_cases h : CPoly.trim p = []
  · rw [h, (CPoly.trim_eq_nil_iff p).mp h]; simp
  · rw [CPoly.length_trim h]; omega

/-- Divide a pair by its gcd. -/
def reduce (u v : CPoly K) : CPoly K × CPoly K :=
  (CPoly.div u (CPoly.gcd u v), CPoly.div v (CPoly.gcd u v))

lemma gcd_ne_zero (u v : CPoly K) (hv : CPoly.toPoly v ≠ 0) : CPoly.toPoly (CPoly.gcd u v) ≠ 0 := by
  rw [CPoly.toPoly_gcd]
  intro h0
  have := (CPoly.egcd_dvd u v).2
  rw [h0, zero_dvd_iff] at this
  exact hv this

lemma reduce_mul (u v : CPoly K) (hv : CPoly.toPoly v ≠ 0) :
    CPoly.toPoly u = CPoly.toPoly (reduce u v).1 * CPoly.toPoly (CPoly.gcd u v) ∧
      CPoly.toPoly v = CPoly.toPoly (reduce u v).2 * CPoly.toPoly (CPoly.gcd u v) := by
  have hg := gcd_ne_zero u v hv
  have hd := CPoly.egcd_dvd u v
  rw [← CPoly.toPoly_gcd] at hd
  exact ⟨CPoly.div_mul_of_dvd u _ hg hd.1, CPoly.div_mul_of_dvd v _ hg hd.2⟩

lemma reduce_ne_zero (u v : CPoly K) (hv : CPoly.toPoly v ≠ 0) :
    CPoly.toPoly (reduce u v).2 ≠ 0 := by
  intro h0
  have := (reduce_mul u v hv).2
  rw [h0, zero_mul] at this
  exact hv this

/-- **The reduced pair is coprime.** -/
lemma reduce_coprime (u v : CPoly K) (hv : CPoly.toPoly v ≠ 0) :
    IsCoprime (CPoly.toPoly (reduce u v).1) (CPoly.toPoly (reduce u v).2) := by
  have hg := gcd_ne_zero u v hv
  obtain ⟨hu', hv'⟩ := reduce_mul u v hv
  refine IsRelPrime.isCoprime fun h ha hb ↦ ?_
  have hu : h * CPoly.toPoly (CPoly.gcd u v) ∣ CPoly.toPoly u := by
    rw [hu']; exact mul_dvd_mul_right ha _
  have hvv : h * CPoly.toPoly (CPoly.gcd u v) ∣ CPoly.toPoly v := by
    rw [hv']; exact mul_dvd_mul_right hb _
  have hdg := CPoly.dvd_egcd u v hu hvv
  rw [← CPoly.toPoly_gcd] at hdg
  obtain ⟨e, he⟩ := hdg
  have : CPoly.toPoly (CPoly.gcd u v) * (h * e - 1) = 0 := by linear_combination -he
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hg
  · exact IsUnit.of_mul_eq_one e (sub_eq_zero.mp h0)

/-- The reduced pair has the same quotient. -/
lemma reduce_div (u v : CPoly K) (hv : CPoly.toPoly v ≠ 0) :
    ι (CPoly.toPoly (reduce u v).1) / ι (CPoly.toPoly (reduce u v).2) =
      ι (CPoly.toPoly u) / ι (CPoly.toPoly v) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  obtain ⟨hu', hv'⟩ := reduce_mul u v hv
  have hg := gcd_ne_zero u v hv
  have hg' : ι (CPoly.toPoly (CPoly.gcd u v)) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg
  rw [hu', hv', map_mul, map_mul, mul_div_mul_right _ _ hg']

/-- The executable height of the quotient `u / v`. -/
def htPair (u v : CPoly K) : ℕ := max (cdeg (reduce u v).1) (cdeg (reduce u v).2)

/-- **The executable height is the naive height.** -/
theorem htPair_spec (u v : CPoly K) (hv : CPoly.toPoly v ≠ 0) :
    htPair u v = ht (ι (CPoly.toPoly u) / ι (CPoly.toPoly v)) := by
  rw [← reduce_div u v hv, ht_div_coprime _ _ (reduce_ne_zero u v hv) (reduce_coprime u v hv),
    htPair, cdeg_spec, cdeg_spec]

end FFHeight
