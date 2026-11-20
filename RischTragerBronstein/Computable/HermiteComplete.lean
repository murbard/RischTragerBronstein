import RischTragerBronstein.Computable.BezoutSolve
import Mathlib.FieldTheory.Perfect

/-!
# The executable Hermite reduction always succeeds

`hermiteCheck_hermite`: for `D ≠ 0` (characteristic zero), the output of `CPoly.hermite A D` passes
the certificate `CPoly.hermiteCheck`. With `hermiteCheck_sound` this makes the executable Hermite
reduction **totally correct**: it always returns `gn, gd, b, s` with `A / D = (gn / gd)′ + b / s`
and `s` squarefree.

Proof: Mack's loop maintains the invariant `HInv` —

  `A₀ gd² (D* D⁻) = (gn′ gd - gn gd′) D₀ (D* D⁻) + A D₀ gd²`,
  `D*` squarefree, `D⁻ ≠ 0`, every irreducible factor of `D⁻` divides `D*` —

using `dvd_mul_derivative` (the Bézout coefficient is a polynomial),
`isCoprime_of_mul_derivative_eq` (the Bézout equation is solvable), `solveBezout_spec`, and exact
divisions; `deg D⁻` strictly decreases, so the fuel suffices; and at exit `D⁻` is a nonzero
constant, so `s = D* D⁻` is squarefree and the invariant is the certificate's identity.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- The squarefreeness certificate succeeds on every squarefree polynomial. -/
theorem squarefreeCheck_complete {s : CPoly R} (hs : Squarefree (toPoly s)) :
    squarefreeCheck s = true := by
  have hsep : (toPoly s).Separable := PerfectField.separable_iff_squarefree.mpr hs
  have hcop : IsCoprime (toPoly s) (toPoly (deriv s)) := by rw [toPoly_deriv]; exact hsep
  obtain ⟨hga, hgb⟩ := egcd_dvd s (deriv s)
  have hunit : IsUnit (toPoly (egcd s (deriv s)).1) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact isUnit_of_dvd_one (huv ▸ dvd_add (Dvd.dvd.mul_left hga u) (Dvd.dvd.mul_left hgb v))
  have hne : trim (egcd s (deriv s)).1 ≠ [] := fun h ↦
    hunit.ne_zero ((trim_eq_nil_iff _).mp h)
  rw [squarefreeCheck, beq_iff_eq, length_trim hne, natDegree_eq_zero_of_isUnit hunit]

/-- The certificate, read through `toPoly`. -/
theorem hermiteCheck_iff (A D : CPoly R) (r : HermiteResult R) :
    hermiteCheck A D r = true ↔
      toPoly D ≠ 0 ∧ toPoly r.gd ≠ 0 ∧ toPoly r.s ≠ 0 ∧
      toPoly A * (toPoly r.gd * toPoly r.gd) * toPoly r.s =
        (derivative (toPoly r.gn) * toPoly r.gd - toPoly r.gn * derivative (toPoly r.gd)) *
            toPoly D * toPoly r.s + toPoly r.b * toPoly D * (toPoly r.gd * toPoly r.gd) ∧
      squarefreeCheck r.s = true := by
  simp only [hermiteCheck, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff,
    beq_iff, toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, ne_eq]
  tauto

/-- The loop invariant of Mack's algorithm, in cross-multiplied polynomial form. -/
def HInv (A₀ D₀ gn gd A Ds Dm : R[X]) : Prop :=
  gd ≠ 0 ∧ Squarefree Ds ∧ Dm ≠ 0 ∧ (∀ p : R[X], Irreducible p → p ∣ Dm → p ∣ Ds) ∧
    A₀ * (gd * gd) * (Ds * Dm) =
      (derivative gn * gd - gn * derivative gd) * D₀ * (Ds * Dm) + A * D₀ * (gd * gd)

/-- At exit (`D⁻` constant) the invariant yields the certificate. -/
theorem hermiteCheck_of_HInv {A₀ D₀ gn gd A Ds Dm : CPoly R} (r : HermiteResult R)
    (hgn : toPoly r.gn = toPoly gn) (hgd' : toPoly r.gd = toPoly gd) (hb : toPoly r.b = toPoly A)
    (hrs : toPoly r.s = toPoly Ds * toPoly Dm) (hD₀ : toPoly D₀ ≠ 0)
    (h : HInv (toPoly A₀) (toPoly D₀) (toPoly gn) (toPoly gd) (toPoly A) (toPoly Ds) (toPoly Dm))
    (hlen : (trim Dm).length ≤ 1) : hermiteCheck A₀ D₀ r = true := by
  obtain ⟨hgd, hsq, hDm0, -, hid⟩ := h
  have hne : trim Dm ≠ [] := fun h0 ↦ hDm0 ((trim_eq_nil_iff Dm).mp h0)
  have hdeg : (toPoly Dm).natDegree = 0 := by
    have := length_trim hne
    omega
  obtain ⟨κ, hκ⟩ : ∃ κ : R, toPoly Dm = C κ := ⟨_, eq_C_of_natDegree_eq_zero hdeg⟩
  have hκ0 : κ ≠ 0 := fun h0 ↦ hDm0 (by rw [hκ, h0, C_0])
  have hs : Squarefree (toPoly r.s) := by
    rw [hrs, hκ]
    exact (squarefree_mul_iff).mpr ⟨(isUnit_C.mpr (isUnit_iff_ne_zero.mpr hκ0)).isRelPrime_right,
      hsq, (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hκ0)).squarefree⟩
  rw [hermiteCheck_iff]
  refine ⟨hD₀, by rwa [hgd'], hs.ne_zero, ?_, squarefreeCheck_complete hs⟩
  rw [hgn, hgd', hb, hrs]
  exact hid

/-- One iteration of Mack's loop preserves the invariant and lowers `deg D⁻`. -/
theorem HInv_step {A₀ D₀ gn gd A Ds Dm : CPoly R}
    (h : HInv (toPoly A₀) (toPoly D₀) (toPoly gn) (toPoly gd) (toPoly A) (toPoly Ds) (toPoly Dm))
    (hlen : ¬(trim Dm).length ≤ 1) :
    HInv (toPoly A₀) (toPoly D₀)
      (toPoly (add (mul gn Dm) (mul (solveBezout (neg (div (mul Ds (deriv Dm)) Dm))
        (div Dm (gcd Dm (deriv Dm))) A).1 gd)))
      (toPoly (mul gd Dm))
      (toPoly (sub (solveBezout (neg (div (mul Ds (deriv Dm)) Dm))
          (div Dm (gcd Dm (deriv Dm))) A).2
        (div (mul (deriv (solveBezout (neg (div (mul Ds (deriv Dm)) Dm))
          (div Dm (gcd Dm (deriv Dm))) A).1) Ds) (div Dm (gcd Dm (deriv Dm))))))
      (toPoly Ds) (toPoly (gcd Dm (deriv Dm))) ∧
    (trim (gcd Dm (deriv Dm))).length < (trim Dm).length := by
  obtain ⟨hgd, hsq, hP0, hprimes, hid⟩ := h
  -- the gcd `G` and the squarefree quotient `Q`
  have hGP : toPoly (gcd Dm (deriv Dm)) ∣ toPoly Dm := by
    rw [toPoly_gcd]; exact (egcd_dvd Dm (deriv Dm)).1
  have hGP' : toPoly (gcd Dm (deriv Dm)) ∣ derivative (toPoly Dm) := by
    rw [toPoly_gcd, ← toPoly_deriv]; exact (egcd_dvd Dm (deriv Dm)).2
  have hG0 : toPoly (gcd Dm (deriv Dm)) ≠ 0 := fun h0 ↦ hP0 (by simpa [h0] using hGP)
  have hPQ := div_mul_of_dvd Dm (gcd Dm (deriv Dm)) hG0 hGP
  have hQ0 : toPoly (div Dm (gcd Dm (deriv Dm))) ≠ 0 := fun h0 ↦ hP0 (by rw [hPQ, h0, zero_mul])
  have hQsq : Squarefree (toPoly (div Dm (gcd Dm (deriv Dm)))) :=
    squarefree_of_gcd_derivative hP0 (by rw [hPQ]; ring) hGP' fun q h1 h2 ↦ by
      rw [toPoly_gcd]; exact dvd_egcd Dm (deriv Dm) h1 (by rwa [toPoly_deriv])
  have hQDs : toPoly (div Dm (gcd Dm (deriv Dm))) ∣ toPoly Ds :=
    dvd_of_squarefree_of_irreducible_dvd hQsq fun p hp hpQ ↦
      hprimes p hp (hPQ ▸ Dvd.dvd.mul_right hpQ _)
  -- (F1), (F2)
  have hF1 : toPoly Dm ∣ toPoly (mul Ds (deriv Dm)) := by
    rw [toPoly_mul, toPoly_deriv]; exact dvd_mul_derivative hP0 hprimes
  have hT := div_mul_of_dvd (mul Ds (deriv Dm)) Dm hP0 hF1
  rw [toPoly_mul, toPoly_deriv] at hT
  have hF2 : IsCoprime (toPoly (div (mul Ds (deriv Dm)) Dm)) (toPoly Dm) :=
    isCoprime_of_mul_derivative_eq hsq hP0 hprimes (by rw [hT]; ring)
  have hcop : IsCoprime (toPoly (neg (div (mul Ds (deriv Dm)) Dm)))
      (toPoly (div Dm (gcd Dm (deriv Dm)))) := by
    rw [toPoly_neg]
    exact (hF2.of_isCoprime_of_dvd_right ⟨_, hPQ⟩).neg_left
  have hbez := solveBezout_spec (neg (div (mul Ds (deriv Dm)) Dm))
    (div Dm (gcd Dm (deriv Dm))) A hQ0 hcop
  rw [toPoly_neg] at hbez
  set B := (solveBezout (neg (div (mul Ds (deriv Dm)) Dm)) (div Dm (gcd Dm (deriv Dm))) A).1
  set Cc := (solveBezout (neg (div (mul Ds (deriv Dm)) Dm)) (div Dm (gcd Dm (deriv Dm))) A).2
  -- the exact division defining `A'`
  have hE := div_mul_of_dvd (mul (deriv B) Ds) (div Dm (gcd Dm (deriv Dm))) hQ0 (by
    rw [toPoly_mul]; exact Dvd.dvd.mul_left hQDs _)
  rw [toPoly_mul, toPoly_deriv] at hE
  refine ⟨⟨?_, hsq, hG0, fun p hp hpG ↦ hprimes p hp (hpG.trans hGP), ?_⟩, ?_⟩
  · rw [toPoly_mul]; exact mul_ne_zero hgd hP0
  · simp only [toPoly_add, toPoly_mul, toPoly_sub, derivative_add, derivative_mul]
    generalize derivative (toPoly Dm) = Pd at hT ⊢
    generalize derivative (toPoly B) = Bd at hE ⊢
    generalize derivative (toPoly gn) = gnd at hid ⊢
    generalize derivative (toPoly gd) = gdd at hid ⊢
    generalize toPoly (div (mul Ds (deriv Dm)) Dm) = T₀ at hT hbez
    generalize toPoly (div (mul (deriv B) Ds) (div Dm (gcd Dm (deriv Dm)))) = E at hE ⊢
    generalize toPoly (div Dm (gcd Dm (deriv Dm))) = Q at hPQ hbez hE
    generalize toPoly (gcd Dm (deriv Dm)) = G at hPQ ⊢
    generalize toPoly B = Bp at hbez hE ⊢
    generalize toPoly Cc = Cp at hbez ⊢
    generalize toPoly Dm = P at hPQ hT hid ⊢
    subst hPQ
    linear_combination (Q * G ^ 2) * hid +
      (toPoly gd * toPoly gd * toPoly D₀ * G * Bp) * hT -
      (toPoly gd * toPoly gd * toPoly D₀ * Q * G ^ 2) * hbez -
      (toPoly gd * toPoly gd * toPoly D₀ * Q * G ^ 2) * hE
  · -- `deg G < deg P`
    have hne : trim Dm ≠ [] := fun h0 ↦ hP0 ((trim_eq_nil_iff Dm).mp h0)
    have hGne : trim (gcd Dm (deriv Dm)) ≠ [] := fun h0 ↦ hG0 ((trim_eq_nil_iff _).mp h0)
    rw [length_trim hne, length_trim hGne]
    have hpos : (toPoly Dm).natDegree ≠ 0 := by
      have := length_trim hne
      omega
    have hP'0 : derivative (toPoly Dm) ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    have := natDegree_le_of_dvd hGP' hP'0
    have := natDegree_derivative_lt hpos
    omega

/-- Mack's loop returns a certified result, given the invariant and enough fuel. -/
theorem hermiteCheck_hermiteLoop {A₀ D₀ : CPoly R} (hD₀ : toPoly D₀ ≠ 0) (fuel : ℕ)
    (gn gd A Ds Dm : CPoly R)
    (h : HInv (toPoly A₀) (toPoly D₀) (toPoly gn) (toPoly gd) (toPoly A) (toPoly Ds) (toPoly Dm))
    (hfuel : (trim Dm).length ≤ fuel + 1) :
    hermiteCheck A₀ D₀ (hermiteLoop fuel gn gd A Ds Dm) = true := by
  induction fuel generalizing gn gd A Dm with
  | zero =>
    simp only [hermiteLoop]
    exact hermiteCheck_of_HInv _ rfl rfl rfl (toPoly_mul _ _) hD₀ h (by omega)
  | succ fuel ih =>
    simp only [hermiteLoop]
    split_ifs with hlen
    · exact hermiteCheck_of_HInv _ (toPoly_trim _) (toPoly_trim _) (toPoly_trim _)
        (by rw [toPoly_trim, toPoly_mul]) hD₀ h hlen
    · obtain ⟨hinv, hlt⟩ := HInv_step h hlen
      exact ih _ _ _ _ hinv (by omega)

/-- **The executable Hermite reduction always passes its certificate.** -/
theorem hermiteCheck_hermite (A D : CPoly R) (hD : toPoly D ≠ 0) :
    hermiteCheck A D (hermite A D) = true := by
  have hGD : toPoly (gcd D (deriv D)) ∣ toPoly D := by
    rw [toPoly_gcd]; exact (egcd_dvd D (deriv D)).1
  have hGD' : toPoly (gcd D (deriv D)) ∣ derivative (toPoly D) := by
    rw [toPoly_gcd, ← toPoly_deriv]; exact (egcd_dvd D (deriv D)).2
  have hG0 : toPoly (gcd D (deriv D)) ≠ 0 := fun h0 ↦ hD (by simpa [h0] using hGD)
  have hmul := sqfreePart_mul D hD
  refine hermiteCheck_hermiteLoop hD _ _ _ _ _ _ ⟨?_, squarefree_sqfreePart D hD, hG0, ?_, ?_⟩ ?_
  · simp
  · intro p hp hpG
    exact irreducible_dvd_sqfreePart hD (hmul.trans (mul_comm _ _)) hGD' hp (hpG.trans hGD)
  · change _ = _
    simp only [toPoly_nil, toPoly_cons, derivative_zero, C_1, mul_zero, add_zero, zero_mul,
      sub_self, zero_add, mul_one]
    have : toPoly (div D (gcd D (deriv D))) = toPoly (sqfreePart D) := rfl
    rw [this, ← hmul]
  · have hGne : trim (gcd D (deriv D)) ≠ [] := fun h0 ↦ hG0 ((trim_eq_nil_iff _).mp h0)
    have hDne : trim D ≠ [] := fun h0 ↦ hD ((trim_eq_nil_iff D).mp h0)
    have h1 := length_trim hGne
    have h2 := length_trim hDne
    have h3 := natDegree_le_of_dvd hGD hD
    have h4 := length_trim_le D
    omega

end CPoly
