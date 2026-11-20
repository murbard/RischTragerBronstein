import RischTragerBronstein.Computable.RDEPoly

/-!
# Total correctness of executable division

`CPoly.divMod_remainder_lt`: for `d ≠ 0`, the remainder of `divMod p d` has smaller degree than `d`
(in terms of trimmed lengths). Together with `divMod_spec` (`p = q d + r`) this is the full
specification of Euclidean division, including termination within the allotted fuel.

Supporting facts relate trimmed coefficient lists to degrees:
`trim_eq_nil_iff`, `length_trim` (`= natDegree + 1`), `trim_trim`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

lemma trim_eq_nil_iff (p : CPoly R) : trim p = [] ↔ toPoly p = 0 := by
  constructor
  · intro h; rw [← toPoly_trim, h]; rfl
  · intro h
    by_contra hne
    obtain ⟨-, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hne
    rw [h, coeff_zero] at hlc
    exact hlc0 hlc.symm

lemma length_trim {p : CPoly R} (h : trim p ≠ []) :
    (trim p).length = (toPoly p).natDegree + 1 := by
  have := (natDegree_toPoly_of_trim_ne_nil h).1
  have hpos := List.length_pos_of_ne_nil h
  omega

lemma length_trim_le (p : CPoly R) : (trim p).length ≤ p.length := by
  unfold trim
  rw [List.length_reverse]
  exact ((List.dropWhile_sublist _).length_le).trans (by rw [List.length_reverse])

lemma trim_trim (p : CPoly R) : trim (trim p) = trim p := by
  unfold trim
  rw [List.reverse_reverse]
  congr 1
  generalize p.reverse = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = 0
    · simp [List.dropWhile_cons_of_pos, ha, ih]
    · simp [List.dropWhile_cons_of_neg, ha]

/-- One division step strictly lowers the (trimmed) length. -/
lemma length_trim_step_lt {p d : CPoly R} (hp : trim p = p) (hd : trim d = d) (hp0 : p ≠ [])
    (hd0 : d ≠ []) (hle : d.length ≤ p.length) :
    (trim (sub p (mul (monomial (p.length - d.length) (lead p / lead d)) d))).length <
      p.length := by
  have hpne : trim p ≠ [] := hp.symm ▸ hp0
  have hdne : trim d ≠ [] := hd.symm ▸ hd0
  obtain ⟨hpdeg, hplc, hplc0⟩ := natDegree_toPoly_of_trim_ne_nil hpne
  obtain ⟨hddeg, hdlc, hdlc0⟩ := natDegree_toPoly_of_trim_ne_nil hdne
  rw [hp] at hpdeg hplc hplc0
  rw [hd] at hddeg hdlc hdlc0
  set P := toPoly p
  set D := toPoly d
  set k := p.length - d.length
  set c := lead p / lead d
  have hP0 : P ≠ 0 := fun h ↦ hp0 (hp ▸ (trim_eq_nil_iff p).mpr h)
  have hD0 : D ≠ 0 := fun h ↦ hd0 (hd ▸ (trim_eq_nil_iff d).mpr h)
  have hPlc : P.leadingCoeff = lead p := by rw [leadingCoeff, hpdeg, hplc]
  have hDlc : D.leadingCoeff = lead d := by rw [leadingCoeff, hddeg, hdlc]
  have hc0 : c ≠ 0 := div_ne_zero hplc0 hdlc0
  have hQ : toPoly (sub p (mul (monomial k c) d)) = P - C c * X ^ k * D := by simp [P, D]
  have hM0 : C c * X ^ k * D ≠ 0 :=
    mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero _ X_ne_zero)) hD0
  have hMdeg : (C c * X ^ k * D).natDegree = P.natDegree := by
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero _ X_ne_zero)) hD0,
      natDegree_C_mul_X_pow k c hc0, hpdeg, hddeg]
    have := List.length_pos_of_ne_nil hd0
    omega
  have hMlc : (C c * X ^ k * D).leadingCoeff = P.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, mul_one, hDlc,
      hPlc]
    simp only [c]
    field_simp
  have hlt : (P - C c * X ^ k * D).degree < P.degree :=
    degree_sub_lt_left (by rw [degree_eq_natDegree hP0, degree_eq_natDegree hM0, hMdeg]) hP0 hMlc.symm
  by_cases hnil : trim (sub p (mul (monomial k c) d)) = []
  · rw [hnil]; exact List.length_pos_of_ne_nil hp0
  · rw [length_trim hnil, hQ]
    have hQ0 : P - C c * X ^ k * D ≠ 0 := fun h ↦ hnil ((trim_eq_nil_iff _).mpr (hQ.trans h))
    have := natDegree_lt_natDegree hQ0 hlt
    have := List.length_pos_of_ne_nil hp0
    omega

lemma divModAux_remainder_lt (d : CPoly R) (hd : trim d = d) (hd0 : d ≠ []) (fuel : ℕ)
    (acc p : CPoly R) (hfuel : (trim p).length ≤ fuel) :
    (trim (divModAux d fuel acc p).2).length < d.length := by
  induction fuel generalizing acc p with
  | zero =>
    simp only [divModAux]
    have : (trim p).length = 0 := by omega
    rw [this]; exact List.length_pos_of_ne_nil hd0
  | succ fuel ih =>
    simp only [divModAux]
    split_ifs with hstop
    · rw [trim_trim]
      rcases hstop with h | h
      · exact h
      · rw [h]; exact List.length_pos_of_ne_nil hd0
    · rw [not_or, not_lt] at hstop
      apply ih
      have hp0 : trim p ≠ [] := fun h ↦ hstop.2 (by rw [h]; rfl)
      have := length_trim_step_lt (trim_trim p) hd hp0 hd0 hstop.1
      omega

/-- **Remainder bound**: `deg (p mod d) < deg d`, for `d ≠ 0`. -/
theorem divMod_remainder_lt (p d : CPoly R) (hd : trim d ≠ []) :
    (trim (divMod p d).2).length < (trim d).length :=
  divModAux_remainder_lt (trim d) (trim_trim d) hd (p.length + 1) [] p
    ((length_trim_le p).trans (Nat.le_succ _))

/-- The remainder bound in terms of polynomial degrees. -/
theorem divMod_degree_lt (p d : CPoly R) (hd : toPoly d ≠ 0) :
    (toPoly (divMod p d).2).degree < (toPoly d).degree :=
  degree_lt_of_trim_length_lt
    (divMod_remainder_lt p d fun h ↦ hd ((trim_eq_nil_iff d).mp h))

/-- With enough fuel, the result of the Euclidean loop divides both current remainders. -/
lemma egcdAux_dvd (fuel : ℕ) (x y : CPoly R × CPoly R × CPoly R)
    (hfuel : (trim y.1).length < fuel) :
    toPoly (egcdAux fuel x y).1 ∣ toPoly x.1 ∧ toPoly (egcdAux fuel x y).1 ∣ toPoly y.1 := by
  induction fuel generalizing x y with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨r₀, s₀, t₀⟩ := x
    obtain ⟨r₁, s₁, t₁⟩ := y
    simp only [egcdAux]
    split_ifs with hz
    · exact ⟨dvd_rfl, by rw [(isZero_iff r₁).mp hz]; exact dvd_zero _⟩
    · have hr₁ : trim r₁ ≠ [] := fun h ↦ hz ((isZero_iff r₁).mpr ((trim_eq_nil_iff r₁).mp h))
      have hlt := divMod_remainder_lt r₀ r₁ hr₁
      obtain ⟨h1, h2⟩ := ih (r₁, s₁, t₁)
        ((divMod r₀ r₁).2, sub s₀ (mul (divMod r₀ r₁).1 s₁), sub t₀ (mul (divMod r₀ r₁).1 t₁))
        (by simp only at hfuel ⊢; omega)
      refine ⟨?_, h1⟩
      rw [divMod_spec r₀ r₁]
      exact dvd_add (Dvd.dvd.mul_left h1 _) h2

/-- **The executable gcd divides both arguments.** -/
theorem egcd_dvd (p q : CPoly R) :
    toPoly (egcd p q).1 ∣ toPoly p ∧ toPoly (egcd p q).1 ∣ toPoly q :=
  egcdAux_dvd _ (p, [1], []) (q, [], [1]) (by
    have := length_trim_le q
    simp only
    omega)

/-- **The executable gcd is a greatest common divisor**: every common divisor divides it. -/
theorem dvd_egcd (p q : CPoly R) {h : R[X]} (hp : h ∣ toPoly p) (hq : h ∣ toPoly q) :
    h ∣ toPoly (egcd p q).1 := by
  rw [← egcd_spec p q]
  exact dvd_add (Dvd.dvd.mul_left hp _) (Dvd.dvd.mul_left hq _)

end CPoly

-- gcd(x³ - x, x² - 1) ~ x² - 1
#eval CPoly.trim (CPoly.egcd ([0, -1, 0, 1] : CPoly ℚ) [-1, 0, 1]).1
