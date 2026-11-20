import RischTragerBronstein.Computable.SquarefreePart
import RischTragerBronstein.Mixed.EllCompute

/-!
# Executable `n`-th roots of polynomials up to a constant

`rootP n fuel D`: repeatedly extract the radical `r = sqfreePart D`, divide by `rⁿ`, recurse, and
multiply back. **`rootP_sound`**: an answer `v` satisfies `D = c vⁿ` (`c ≠ 0`). **`rootP_complete`**:
if `D = c wⁿ` (`c, w ≠ 0`, `n ≥ 1`) and the fuel exceeds `deg D`, an answer is returned — the radical
of `c wⁿ` divides `w` (`Squarefree.dvd_pow_iff_dvd`), so `D / rⁿ = c (w/r)ⁿ` has smaller degree.
Used for the "constant times a square / cube" tests and the scaling `u` of curves constant up to
scaling.
-/

open Polynomial

namespace CPoly

variable {K : Type*} [Field K] [DecidableEq K]

/-- `rⁿ` as a code. -/
def powCR (r : CPoly K) (n : ℕ) : CPoly K := (mul r)^[n] [1]

lemma toPoly_powCR (r : CPoly K) (n : ℕ) : toPoly (powCR r n) = toPoly r ^ n := by
  induction n with
  | zero => simp [powCR, CPoly.toPoly]
  | succ n ih =>
    rw [powCR, Function.iterate_succ_apply', ← powCR, toPoly_mul, ih, pow_succ, mul_comm]

/-- **Executable `n`-th root up to a constant.** -/
def rootP (n : ℕ) : ℕ → CPoly K → Option (CPoly K)
  | 0, _ => none
  | f + 1, D =>
    if (trim D).length ≤ 1 then some [1]
    else
      let r := sqfreePart D
      let qr := divMod D (powCR r n)
      if isZero qr.2 then (rootP n f qr.1).map (mul r) else none

lemma natDegree_eq_zero_of_trim (D : CPoly K) (h : (trim D).length ≤ 1) :
    (toPoly D).natDegree = 0 := by
  rw [← FFHeight.cdeg_spec]; unfold FFHeight.cdeg; omega

lemma trim_length_le_one_of_natDegree_zero (D : CPoly K) (h : (toPoly D).natDegree = 0) :
    (trim D).length ≤ 1 := by
  rw [← FFHeight.cdeg_spec] at h; unfold FFHeight.cdeg at h; omega

/-- **Soundness.** -/
theorem rootP_sound (n : ℕ) : ∀ (f : ℕ) (D v : CPoly K), rootP n f D = some v →
    toPoly D ≠ 0 → ∃ c : K, c ≠ 0 ∧ toPoly D = C c * toPoly v ^ n
  | 0, D, v, h, _ => by simp [rootP] at h
  | f + 1, D, v, h, hD => by
    unfold rootP at h
    dsimp only at h
    split_ifs at h with h1 h2
    · cases h
      refine ⟨(toPoly D).coeff 0, ?_, ?_⟩
      · intro h0; apply hD
        rw [eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_trim D h1), h0, C_0]
      · rw [eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_trim D h1)]
        simp [CPoly.toPoly]
    · obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp h
      have hrem : toPoly (divMod D (powCR (sqfreePart D) n)).2 = 0 := (isZero_iff _).mp h2
      have hspec := divMod_spec D (powCR (sqfreePart D) n)
      rw [hrem, add_zero, toPoly_powCR] at hspec
      have hq : toPoly (divMod D (powCR (sqfreePart D) n)).1 ≠ 0 := fun h0 ↦ by
        rw [h0, zero_mul] at hspec; exact hD hspec
      obtain ⟨c, hc, hcq⟩ := rootP_sound n f _ v' hv' hq
      refine ⟨c, hc, ?_⟩
      rw [hspec, hcq, toPoly_mul, mul_pow]; ring

lemma sqfreePart_natDegree_pos (D : CPoly K) [CharZero K] (hD : toPoly D ≠ 0)
    (hdeg : 0 < (toPoly D).natDegree) : 0 < (toPoly (sqfreePart D)).natDegree := by
  by_contra hle
  push_neg at hle
  have h0 : (toPoly (sqfreePart D)).natDegree = 0 := by omega
  have hmul := sqfreePart_mul D hD
  have hg : toPoly (gcd D (deriv D)) ∣ derivative (toPoly D) := by
    rw [toPoly_gcd, ← toPoly_deriv]; exact (egcd_dvd D (deriv D)).2
  have hder : derivative (toPoly D) ≠ 0 := by
    intro h; rw [derivative_eq_zero] at h; omega
  have h1 := natDegree_le_of_dvd hg hder
  have h2 := natDegree_derivative_lt (p := toPoly D) (by omega)
  have hs0 : toPoly (sqfreePart D) ≠ 0 := fun h ↦ by rw [h, zero_mul] at hmul; exact hD hmul
  have hg0 : toPoly (gcd D (deriv D)) ≠ 0 := fun h ↦ by rw [h, mul_zero] at hmul; exact hD hmul
  have h3 := congrArg natDegree hmul
  rw [natDegree_mul hs0 hg0, h0, zero_add] at h3
  omega

/-- **Completeness.** -/
theorem rootP_complete [CharZero K] (n : ℕ) (hn : 0 < n) : ∀ (f : ℕ) (D : CPoly K) (c : K) (w : K[X]),
    c ≠ 0 → w ≠ 0 → toPoly D = C c * w ^ n → (toPoly D).natDegree < f → (rootP n f D).isSome
  | 0, _, _, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, D, c, w, hc, hw, hD, hf => by
    unfold rootP
    dsimp only
    split_ifs with h1 h2
    · rfl
    rotate_left
    · have hD0 : toPoly D ≠ 0 := by rw [hD]; exact mul_ne_zero (by simpa using hc) (pow_ne_zero _ hw)
      have hdeg : 0 < (toPoly D).natDegree := by
        by_contra h0; push_neg at h0
        apply h1
        exact trim_length_le_one_of_natDegree_zero D (by omega)
      set r := sqfreePart D
      have hsq := squarefree_sqfreePart D hD0
      have hrD : toPoly r ∣ toPoly D := ⟨_, sqfreePart_mul D hD0⟩
      have hrw : toPoly r ∣ w := by
        rw [hD] at hrD
        have : toPoly r ∣ w ^ n := (IsUnit.dvd_mul_left (isUnit_C.mpr (Ne.isUnit hc))).mp hrD
        exact (hsq.dvd_pow_iff_dvd hn.ne').mp this
      obtain ⟨w', hw'⟩ := hrw
      have hr0 : toPoly r ≠ 0 := fun h ↦ by rw [h, zero_mul] at hw'; exact hw hw'
      have hw'0 : w' ≠ 0 := fun h ↦ by rw [h, mul_zero] at hw'; exact hw hw'
      have hrn : toPoly (powCR r n) ∣ toPoly D := by
        rw [toPoly_powCR, hD, hw', mul_pow]; exact ⟨C c * w' ^ n, by ring⟩
      have hrn0 : toPoly (powCR r n) ≠ 0 := by rw [toPoly_powCR]; exact pow_ne_zero _ hr0
      exfalso
      apply h2
      rw [isZero_iff]
      exact divMod_exact D _ hrn0 hrn
    · -- the recursion
      have hD0 : toPoly D ≠ 0 := by rw [hD]; exact mul_ne_zero (by simpa using hc) (pow_ne_zero _ hw)
      have hdeg : 0 < (toPoly D).natDegree := by
        by_contra h0; push_neg at h0
        apply h1
        exact trim_length_le_one_of_natDegree_zero D (by omega)
      set r := sqfreePart D
      have hsq := squarefree_sqfreePart D hD0
      have hrD : toPoly r ∣ toPoly D := ⟨_, sqfreePart_mul D hD0⟩
      have hrw : toPoly r ∣ w := by
        rw [hD] at hrD
        have : toPoly r ∣ w ^ n := (IsUnit.dvd_mul_left (isUnit_C.mpr (Ne.isUnit hc))).mp hrD
        exact (hsq.dvd_pow_iff_dvd hn.ne').mp this
      obtain ⟨w', hw'⟩ := hrw
      have hr0 : toPoly r ≠ 0 := fun h ↦ by rw [h, zero_mul] at hw'; exact hw hw'
      have hw'0 : w' ≠ 0 := fun h ↦ by rw [h, mul_zero] at hw'; exact hw hw'
      have hspec := divMod_spec D (powCR r n)
      rw [(isZero_iff _).mp h2, add_zero, toPoly_powCR] at hspec
      set q := (divMod D (powCR r n)).1
      have hq : toPoly q = C c * w' ^ n := by
        have e : toPoly q * toPoly r ^ n = (C c * w' ^ n) * toPoly r ^ n := by
          rw [← hspec, hD, hw', mul_pow]; ring
        exact mul_right_cancel₀ (pow_ne_zero _ hr0) e
      have hrdeg := sqfreePart_natDegree_pos D hD0 hdeg
      have hqdeg : (toPoly q).natDegree < (toPoly D).natDegree := by
        have hq0 : toPoly q ≠ 0 := by rw [hq]; exact mul_ne_zero (by simpa using hc) (pow_ne_zero _ hw'0)
        rw [hspec, natDegree_mul hq0 (pow_ne_zero _ hr0), natDegree_pow]
        have : 0 < n * (toPoly r).natDegree := Nat.mul_pos hn hrdeg
        omega
      have := rootP_complete n hn f q c w' hc hw'0 hq (by omega)
      simp only [Option.isSome_map]
      exact this

end CPoly

