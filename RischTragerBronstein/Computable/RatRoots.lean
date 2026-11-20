import RischTragerBronstein.Computable.Euclid
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.List.GetD

/-!
# Rational roots of a polynomial over the constants

The weak normalisation of a Risch differential equation needs the rational numbers among the
residues of the coefficient; these are the rational roots of an annihilating polynomial `μ`.
`HasRatRoots R` provides a function `ratRoots : CPoly R → List ℚ` whose output contains every
rational root of a nonzero polynomial (it may contain more).

For `R = ℚ` the rational root theorem gives the candidates: clearing denominators and stripping the
factor `x^v`, a root `n / d` in lowest terms satisfies `n ∣ a₀` and `d ∣ lc`, so `|n|, |d|` are
bounded by the largest absolute value `B` of the integer coefficients.
-/

open Polynomial

namespace CPoly

/-- A superset of the rational roots of polynomials over `R`. -/
class HasRatRoots (R : Type*) [Field R] where
  /-- candidate rational roots -/
  ratRoots : CPoly R → List ℚ
  /-- every rational root of a nonzero polynomial is a candidate -/
  ratRoots_spec : ∀ (P : CPoly R) (q : ℚ), toPoly P ≠ 0 → (toPoly P).eval (q : R) = 0 →
    q ∈ ratRoots P

section Rat

/-- Strip the low zero coefficients. -/
def stripLow (P : CPoly ℚ) : CPoly ℚ := P.dropWhile (· = 0)

lemma toPoly_stripLow (P : CPoly ℚ) : ∃ v : ℕ, toPoly P = X ^ v * toPoly (stripLow P) := by
  induction P with
  | nil => exact ⟨0, by simp [stripLow]⟩
  | cons a P ih =>
    by_cases ha : a = 0
    · subst ha
      obtain ⟨v, hv⟩ := ih
      refine ⟨v + 1, ?_⟩
      have : stripLow (0 :: P) = stripLow P := by simp [stripLow]
      rw [this, toPoly_cons, C_0, zero_add, hv, pow_succ]; ring
    · refine ⟨0, ?_⟩
      simp [stripLow, ha]

lemma stripLow_head (P : CPoly ℚ) {a : ℚ} {rest : CPoly ℚ} (h : stripLow P = a :: rest) :
    a ≠ 0 := by
  induction P with
  | nil => simp [stripLow] at h
  | cons b P ih =>
    by_cases hb : b = 0
    · subst hb
      exact ih (by simpa [stripLow] using h)
    · simp [stripLow, hb] at h
      rw [← h.1]; exact hb

/-- A common multiple of the denominators (their lcm). -/
def denProd (P : CPoly ℚ) : ℕ := (P.map Rat.den).foldr Nat.lcm 1

lemma denProd_pos (P : CPoly ℚ) : 0 < denProd P := by
  unfold denProd
  induction P with
  | nil => simp
  | cons a P ih => simp only [List.map_cons, List.foldr_cons]; exact Nat.lcm_pos a.den_pos ih

/-- Integer coefficients after clearing denominators. -/
def intCoeffs (P : CPoly ℚ) : CPoly ℤ := P.map fun a ↦ ((denProd P : ℚ) * a).num

lemma den_dvd_denProd {P : CPoly ℚ} {a : ℚ} (ha : a ∈ P) : a.den ∣ denProd P := by
  unfold denProd
  induction P with
  | nil => simp at ha
  | cons b P ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact Nat.dvd_lcm_left _ _
    · exact (ih ha').trans (Nat.dvd_lcm_right _ _)

lemma intCoeffs_cast {P : CPoly ℚ} {a : ℚ} (ha : a ∈ P) :
    ((((denProd P : ℚ) * a).num : ℤ) : ℚ) = (denProd P : ℚ) * a := by
  obtain ⟨M', hM'⟩ := den_dvd_denProd ha
  have : (denProd P : ℚ) * a = ((M' : ℤ) * a.num : ℤ) := by
    rw [hM']; push_cast
    have := Rat.mul_den_eq_num a
    linear_combination (M' : ℚ) * this
  rw [this, Rat.num_intCast]

/-- `(intCoeffs P)` denotes `M · P`. -/
lemma toPoly_intCoeffs (P : CPoly ℚ) :
    (toPoly (intCoeffs P)).map (Int.castRingHom ℚ) = C (denProd P : ℚ) * toPoly P := by
  ext n
  rw [coeff_map, coeff_toPoly, coeff_C_mul, coeff_toPoly, intCoeffs]
  by_cases hn : n < P.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getElem_map,
      List.getD_eq_getElem _ _ hn]
    exact intCoeffs_cast (List.getElem_mem hn)
  · rw [List.getD_eq_default _ _ (by simpa using hn), List.getD_eq_default _ _ (by omega)]
    simp

/-- The largest absolute value of a list of integers. -/
def absBound (Z : List ℤ) : ℕ := (Z.map Int.natAbs).foldr max 0

lemma le_absBound {Z : List ℤ} {b : ℤ} (hb : b ∈ Z) : b.natAbs ≤ absBound Z := by
  unfold absBound
  induction Z with
  | nil => simp at hb
  | cons a Z ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact le_max_left _ _
    · exact (ih hb').trans (le_max_right _ _)

/-- The divisors of `n` (for `n ≠ 0`). -/
def divsN (n : ℕ) : List ℕ := (List.range (n + 1)).filter (· ∣ n)

lemma mem_divsN {d n : ℕ} (h : d ∣ n) (hn : n ≠ 0) : d ∈ divsN n :=
  List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd
    (Nat.pos_of_ne_zero hn) h)), decide_eq_true h⟩

/-- Candidates `± a / d`, `a ∣ a₀`, `d` dividing a coefficient in `Z`. -/
def ratCandidates (a₀ : ℕ) (Z : List ℤ) : List ℚ :=
  (divsN a₀).flatMap fun (a : ℕ) ↦ (Z.flatMap fun b ↦ divsN b.natAbs).flatMap fun (d : ℕ) ↦
    [((a : ℕ) : ℚ) / ((d : ℕ) : ℚ), -(((a : ℕ) : ℚ) / ((d : ℕ) : ℚ))]

lemma mem_ratCandidates {a₀ : ℕ} {Z : List ℤ} {n : ℤ} {d : ℕ} (hn : n.natAbs ∈ divsN a₀)
    (hd : d ∈ Z.flatMap fun b ↦ divsN b.natAbs) :
    ((n : ℚ) / d) ∈ ratCandidates a₀ Z := by
  refine List.mem_flatMap.mpr ⟨n.natAbs, hn, List.mem_flatMap.mpr ⟨d, hd, ?_⟩⟩
  rcases Int.natAbs_eq n with h | h <;> rw [h] <;> simp [neg_div]

/-- Rational root candidates over `ℚ`. -/
def ratRootsQ (P : CPoly ℚ) : List ℚ :=
  0 :: ratCandidates ((intCoeffs (stripLow P)).getD 0 0).natAbs (intCoeffs (stripLow P))

theorem ratRootsQ_spec (P : CPoly ℚ) (q : ℚ) (hP : toPoly P ≠ 0) (hq : (toPoly P).eval q = 0) :
    q ∈ ratRootsQ P := by
  obtain ⟨v, hv⟩ := toPoly_stripLow P
  rw [hv, eval_mul, eval_pow, eval_X, mul_eq_zero, pow_eq_zero_iff'] at hq
  rcases hq with ⟨rfl, -⟩ | hq
  · exact List.mem_cons_self
  refine List.mem_cons_of_mem _ ?_
  set P' := stripLow P with hP'
  have hP'0 : toPoly P' ≠ 0 := fun h0 ↦ hP (by rw [hv, h0, mul_zero])
  -- `P'` starts with a nonzero coefficient
  obtain ⟨a₀, rest, hcons⟩ : ∃ a₀ rest, P' = a₀ :: rest := by
    cases hP'' : P' with
    | nil => exact absurd (by rw [hP'', toPoly_nil]) hP'0
    | cons a r => exact ⟨a, r, rfl⟩
  have ha₀ : a₀ ≠ 0 := stripLow_head P (by rw [← hP', hcons])
  set Z := intCoeffs P' with hZ
  set M := denProd P' with hM
  have hM0 : (M : ℚ) ≠ 0 := by rw [hM]; exact_mod_cast (denProd_pos P').ne'
  -- `q` is a root of the integer polynomial `Z`
  have hroot : aeval q (toPoly Z) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, hZ, toPoly_intCoeffs, eval_mul, eval_C,
      hq, mul_zero]
  have hZ0 : toPoly Z ≠ 0 := fun h0 ↦ by
    have := toPoly_intCoeffs P'
    rw [← hZ, h0, Polynomial.map_zero] at this
    exact hP'0 ((mul_eq_zero.mp this.symm).resolve_left (C_ne_zero.mpr hM0))
  have hnum := num_dvd_of_is_root hroot
  have hden := den_dvd_of_is_root hroot
  -- the constant coefficient is nonzero
  have hc0 : (toPoly Z).coeff 0 ≠ 0 := by
    have hZ0' : Z.getD 0 0 = ((M : ℚ) * a₀).num := by
      rw [hZ, intCoeffs, ← hM]
      conv_lhs => rw [hcons]
      rw [List.map_cons, List.getD_cons_zero]
    rw [coeff_toPoly, hZ0']
    intro h0
    have := intCoeffs_cast (P := P') (a := a₀) (by rw [hcons]; exact List.mem_cons_self)
    rw [← hM, h0] at this
    exact mul_ne_zero hM0 ha₀ (by exact_mod_cast this.symm)
  have hlc0 : (toPoly Z).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hZ0
  -- both are coefficients of `Z`, bounded by `B`
  have hmem : ∀ n, (toPoly Z).coeff n ≠ 0 → (toPoly Z).coeff n ∈ Z := fun n hn ↦ by
    rw [coeff_toPoly] at hn ⊢
    by_cases hlen : n < Z.length
    · rw [List.getD_eq_getElem _ _ hlen]; exact List.getElem_mem hlen
    · rw [List.getD_eq_default _ _ (by omega)] at hn; exact absurd rfl hn
  have hc0' : (toPoly Z).coeff 0 = Z.getD 0 0 := coeff_toPoly _ _
  have hB0 : (IsFractionRing.num ℤ q).natAbs ∈ divsN (Z.getD 0 0).natAbs :=
    mem_divsN (Int.natAbs_dvd_natAbs.mpr (hc0' ▸ hnum)) (Int.natAbs_ne_zero.mpr (hc0' ▸ hc0))
  have hB1 : (IsFractionRing.den ℤ q : ℤ).natAbs ∈ Z.flatMap fun b ↦ divsN b.natAbs :=
    List.mem_flatMap.mpr ⟨_, hmem _ hlc0,
      mem_divsN (Int.natAbs_dvd_natAbs.mpr hden) (Int.natAbs_ne_zero.mpr hlc0)⟩
  have hq' : q = (IsFractionRing.num ℤ q : ℚ) / ((IsFractionRing.den ℤ q : ℤ) : ℚ) := by
    conv_lhs => rw [← IsFractionRing.mk'_num_den ℤ q]
    rw [IsFractionRing.mk'_eq_div]; rfl
  -- normalise the sign of the denominator
  set n := IsFractionRing.num ℤ q
  set d := (IsFractionRing.den ℤ q : ℤ)
  rcases Int.natAbs_eq d with hd | hd
  · rw [hq', hd]
    exact mem_ratCandidates hB0 hB1
  · rw [hq', hd, Int.cast_neg, div_neg, ← neg_div, ← Int.cast_neg]
    exact mem_ratCandidates (by rw [Int.natAbs_neg]; exact hB0) hB1

instance : HasRatRoots ℚ where
  ratRoots := ratRootsQ
  ratRoots_spec P q hP hq := ratRootsQ_spec P q hP (by simpa using hq)

end Rat

end CPoly

-- roots of `(2x - 1)(x + 3)` = `2x² + 5x - 3`: candidates contain `1/2` and `-3`
#eval ((1 : ℚ) / 2) ∈ CPoly.HasRatRoots.ratRoots ([-3, 5, 2] : CPoly ℚ)
#eval ((-3 : ℚ)) ∈ CPoly.HasRatRoots.ratRoots ([-3, 5, 2] : CPoly ℚ)
