import RischTragerBronstein.Computable.GHermite
import RischTragerBronstein.Rational.SquarefreePartD
import Mathlib.FieldTheory.Perfect

/-!
# Hermite reduction in `K(t)` always succeeds when all irreducibles are normal

`GPoly.hermiteCheck_hermite`: let `M` model a field `K` of characteristic zero and `t′ = W`. If
every irreducible `p ∈ K[t]` is normal (`p ∤ D p`, `D` the tower derivation; only the factors of the denominator matter) — as in every
primitive/logarithmic extension without new constants
(`not_dvd_deriv_of_irreducible_primitive`) — then for `D ≠ 0` the output of
`GPoly.hermite O w A D` passes `GPoly.hermiteCheck`.

With `hermiteCheck_sound`, Hermite reduction is then **totally correct at that tower level**.
The proof is the one of `Computable/HermiteComplete.lean`, with the tower derivation in the loop
invariant and the structural facts of `Rational/SquarefreePartD.lean`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [CharZero K] [Differential K] {O : COps α} (M : CField α K O)

theorem squarefreeCheck_complete {s : GPoly α} (hs : Squarefree (toPoly M s)) :
    squarefreeCheck O s = true := by
  have hsep : (toPoly M s).Separable := PerfectField.separable_iff_squarefree.mpr hs
  have hcop : IsCoprime (toPoly M s) (toPoly M (derivX O s)) := by
    rw [toPoly_derivX]; exact hsep
  obtain ⟨hga, hgb⟩ := egcd_dvd M s (derivX O s)
  have hunit : IsUnit (toPoly M (egcd O s (derivX O s)).1) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact isUnit_of_dvd_one (huv ▸ dvd_add (Dvd.dvd.mul_left hga u) (Dvd.dvd.mul_left hgb v))
  have hne : trim O (egcd O s (derivX O s)).1 ≠ [] := fun h ↦
    hunit.ne_zero ((trim_eq_nil_iff M _).mp h)
  rw [squarefreeCheck, beq_iff_eq, length_trim M hne, natDegree_eq_zero_of_isUnit hunit]

theorem hermiteCheck_iff (w A D : GPoly α) (r : HermiteResult α) :
    hermiteCheck O w A D r = true ↔
      toPoly M D ≠ 0 ∧ toPoly M r.gd ≠ 0 ∧ toPoly M r.s ≠ 0 ∧
      toPoly M A * (toPoly M r.gd * toPoly M r.gd) * toPoly M r.s =
        (implicitDeriv (toPoly M w) (toPoly M r.gn) * toPoly M r.gd -
            toPoly M r.gn * implicitDeriv (toPoly M w) (toPoly M r.gd)) *
            toPoly M D * toPoly M r.s + toPoly M r.b * toPoly M D * (toPoly M r.gd * toPoly M r.gd) ∧
      squarefreeCheck O r.s = true := by
  simp only [hermiteCheck, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff M,
    toPoly_mul, toPoly_add, toPoly_sub, toPoly_derivT, ne_eq, sub_eq_zero]
  tauto

/-- The loop invariant, with the tower derivation `D = implicitDeriv W`. -/
def HInv (W A₀ D₀ gn gd A Ds Dm : K[X]) : Prop :=
  gd ≠ 0 ∧ Squarefree Ds ∧ Dm ≠ 0 ∧ (∀ p : K[X], Irreducible p → p ∣ Dm → p ∣ Ds) ∧ Ds ∣ D₀ ∧
    A₀ * (gd * gd) * (Ds * Dm) =
      (implicitDeriv W gn * gd - gn * implicitDeriv W gd) * D₀ * (Ds * Dm) + A * D₀ * (gd * gd)

theorem hermiteCheck_of_HInv {w A₀ D₀ gn gd A Ds Dm : GPoly α} (r : HermiteResult α)
    (hgn : toPoly M r.gn = toPoly M gn) (hgd' : toPoly M r.gd = toPoly M gd)
    (hb : toPoly M r.b = toPoly M A) (hrs : toPoly M r.s = toPoly M Ds * toPoly M Dm)
    (hD₀ : toPoly M D₀ ≠ 0)
    (h : HInv (toPoly M w) (toPoly M A₀) (toPoly M D₀) (toPoly M gn) (toPoly M gd) (toPoly M A)
      (toPoly M Ds) (toPoly M Dm))
    (hlen : (trim O Dm).length ≤ 1) : hermiteCheck O w A₀ D₀ r = true := by
  obtain ⟨hgd, hsq, hDm0, -, -, hid⟩ := h
  have hne : trim O Dm ≠ [] := fun h0 ↦ hDm0 ((trim_eq_nil_iff M Dm).mp h0)
  have hdeg : (toPoly M Dm).natDegree = 0 := by
    have := length_trim M hne
    omega
  obtain ⟨κ, hκ⟩ : ∃ κ : K, toPoly M Dm = C κ := ⟨_, eq_C_of_natDegree_eq_zero hdeg⟩
  have hκ0 : κ ≠ 0 := fun h0 ↦ hDm0 (by rw [hκ, h0, C_0])
  have hs : Squarefree (toPoly M r.s) := by
    rw [hrs, hκ]
    exact (squarefree_mul_iff).mpr ⟨(isUnit_C.mpr (isUnit_iff_ne_zero.mpr hκ0)).isRelPrime_right,
      hsq, (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hκ0)).squarefree⟩
  rw [hermiteCheck_iff M]
  refine ⟨hD₀, by rwa [hgd'], hs.ne_zero, ?_, squarefreeCheck_complete M hs⟩
  rw [hgn, hgd', hb, hrs]
  exact hid

set_option maxHeartbeats 1600000 in
/-- One iteration of the loop preserves the invariant and lowers `deg D⁻`. -/
theorem HInv_step {w A₀ D₀ gn gd A Ds Dm : GPoly α}
    (hnormal : ∀ p : K[X], Irreducible p → p ∣ toPoly M D₀ →
      ¬p ∣ implicitDeriv (toPoly M w) p)
    (h : HInv (toPoly M w) (toPoly M A₀) (toPoly M D₀) (toPoly M gn) (toPoly M gd) (toPoly M A)
      (toPoly M Ds) (toPoly M Dm))
    (hlen : ¬(trim O Dm).length ≤ 1) :
    HInv (toPoly M w) (toPoly M A₀) (toPoly M D₀)
      (toPoly M (add O (mul O gn Dm) (mul O (solveBezout O
        (neg O (div O (mul O Ds (derivT O w Dm)) Dm)) (div O Dm (gcd O Dm (derivX O Dm))) A).1 gd)))
      (toPoly M (mul O gd Dm))
      (toPoly M (sub O (solveBezout O (neg O (div O (mul O Ds (derivT O w Dm)) Dm))
          (div O Dm (gcd O Dm (derivX O Dm))) A).2
        (div O (mul O (derivT O w (solveBezout O (neg O (div O (mul O Ds (derivT O w Dm)) Dm))
          (div O Dm (gcd O Dm (derivX O Dm))) A).1) Ds) (div O Dm (gcd O Dm (derivX O Dm))))))
      (toPoly M Ds) (toPoly M (gcd O Dm (derivX O Dm))) ∧
    (trim O (gcd O Dm (derivX O Dm))).length < (trim O Dm).length := by
  letI : Differential K[X] := polynomialOfDeriv (toPoly M w)
  obtain ⟨hgd, hsq, hP0, hprimes, hDsD, hid⟩ := h
  have hGP : toPoly M (gcd O Dm (derivX O Dm)) ∣ toPoly M Dm := by
    rw [toPoly_gcd]; exact (egcd_dvd M Dm (derivX O Dm)).1
  have hGP' : toPoly M (gcd O Dm (derivX O Dm)) ∣ derivative (toPoly M Dm) := by
    rw [toPoly_gcd, ← toPoly_derivX]; exact (egcd_dvd M Dm (derivX O Dm)).2
  have hG0 : toPoly M (gcd O Dm (derivX O Dm)) ≠ 0 := fun h0 ↦ hP0 (by simpa [h0] using hGP)
  have hPQ := div_mul_of_dvd M Dm (gcd O Dm (derivX O Dm)) hG0 hGP
  change toPoly M Dm = toPoly M (div O Dm (gcd O Dm (derivX O Dm))) * _ at hPQ
  have hQ0 : toPoly M (div O Dm (gcd O Dm (derivX O Dm))) ≠ 0 := fun h0 ↦
    hP0 (by rw [hPQ, h0, zero_mul])
  have hQsq : Squarefree (toPoly M (div O Dm (gcd O Dm (derivX O Dm)))) :=
    squarefree_of_gcd_derivative hP0 (by rw [hPQ]; ring) hGP' fun q h1 h2 ↦ by
      rw [toPoly_gcd]; exact dvd_egcd M Dm (derivX O Dm) h1 (by rwa [toPoly_derivX])
  have hQDs : toPoly M (div O Dm (gcd O Dm (derivX O Dm))) ∣ toPoly M Ds :=
    dvd_of_squarefree_of_irreducible_dvd hQsq fun p hp hpQ ↦
      hprimes p hp (hPQ ▸ Dvd.dvd.mul_right hpQ _)
  -- (F1), (F2) for the tower derivation
  have hF1 : toPoly M Dm ∣ toPoly M (mul O Ds (derivT O w Dm)) := by
    rw [toPoly_mul, toPoly_derivT]; exact dvd_mul_deriv (toPoly M Dm) hprimes
  have hT := div_mul_of_dvd M (mul O Ds (derivT O w Dm)) Dm hP0 hF1
  change _ = toPoly M (div O (mul O Ds (derivT O w Dm)) Dm) * _ at hT
  rw [toPoly_mul, toPoly_derivT] at hT
  have hF2 : IsCoprime (toPoly M (div O (mul O Ds (derivT O w Dm)) Dm)) (toPoly M Dm) :=
    isCoprime_of_mul_deriv_eq hsq hP0 hprimes
      (fun p hp hpM ↦ hnormal p hp ((hprimes p hp hpM).trans hDsD))
      (by change toPoly M Ds * implicitDeriv (toPoly M w) (toPoly M Dm) = _; rw [hT]; ring)
  have hcop : IsCoprime (toPoly M (neg O (div O (mul O Ds (derivT O w Dm)) Dm)))
      (toPoly M (div O Dm (gcd O Dm (derivX O Dm)))) := by
    rw [toPoly_neg]
    exact (hF2.of_isCoprime_of_dvd_right ⟨_, hPQ⟩).neg_left
  have hbez := solveBezout_spec M (neg O (div O (mul O Ds (derivT O w Dm)) Dm))
    (div O Dm (gcd O Dm (derivX O Dm))) A hQ0 hcop
  rw [toPoly_neg] at hbez
  set B := (solveBezout O (neg O (div O (mul O Ds (derivT O w Dm)) Dm))
    (div O Dm (gcd O Dm (derivX O Dm))) A).1
  set Cc := (solveBezout O (neg O (div O (mul O Ds (derivT O w Dm)) Dm))
    (div O Dm (gcd O Dm (derivX O Dm))) A).2
  have hE := div_mul_of_dvd M (mul O (derivT O w B) Ds) (div O Dm (gcd O Dm (derivX O Dm))) hQ0 (by
    rw [toPoly_mul]; exact Dvd.dvd.mul_left hQDs _)
  change _ = toPoly M (div O (mul O (derivT O w B) Ds) (div O Dm (gcd O Dm (derivX O Dm)))) * _
    at hE
  rw [toPoly_mul, toPoly_derivT] at hE
  refine ⟨⟨?_, hsq, hG0, fun p hp hpG ↦ hprimes p hp (hpG.trans hGP), hDsD, ?_⟩, ?_⟩
  · rw [toPoly_mul]; exact mul_ne_zero hgd hP0
  · simp only [toPoly_add, toPoly_mul, toPoly_sub, map_add, Derivation.leibniz, smul_eq_mul]
    generalize implicitDeriv (toPoly M w) (toPoly M Dm) = Pd at hT ⊢
    generalize implicitDeriv (toPoly M w) (toPoly M B) = Bd at hE ⊢
    generalize implicitDeriv (toPoly M w) (toPoly M gn) = gnd at hid ⊢
    generalize implicitDeriv (toPoly M w) (toPoly M gd) = gdd at hid ⊢
    generalize toPoly M (div O (mul O Ds (derivT O w Dm)) Dm) = T₀ at hT hbez
    generalize toPoly M (div O (mul O (derivT O w B) Ds)
      (div O Dm (gcd O Dm (derivX O Dm)))) = E at hE ⊢
    generalize toPoly M (div O Dm (gcd O Dm (derivX O Dm))) = Q at hPQ hbez hE
    generalize toPoly M (gcd O Dm (derivX O Dm)) = G at hPQ ⊢
    generalize toPoly M B = Bp at hbez hE ⊢
    generalize toPoly M Cc = Cp at hbez ⊢
    generalize toPoly M Dm = P at hPQ hT hid ⊢
    subst hPQ
    linear_combination (Q * G ^ 2) * hid +
      (toPoly M gd * toPoly M gd * toPoly M D₀ * G * Bp) * hT -
      (toPoly M gd * toPoly M gd * toPoly M D₀ * Q * G ^ 2) * hbez -
      (toPoly M gd * toPoly M gd * toPoly M D₀ * Q * G ^ 2) * hE
  · have hne : trim O Dm ≠ [] := fun h0 ↦ hP0 ((trim_eq_nil_iff M Dm).mp h0)
    have hGne : trim O (gcd O Dm (derivX O Dm)) ≠ [] := fun h0 ↦
      hG0 ((trim_eq_nil_iff M _).mp h0)
    rw [length_trim M hne, length_trim M hGne]
    have hpos : (toPoly M Dm).natDegree ≠ 0 := by
      have := length_trim M hne
      omega
    have hP'0 : derivative (toPoly M Dm) ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    have := natDegree_le_of_dvd hGP' hP'0
    have := natDegree_derivative_lt hpos
    omega

theorem hermiteCheck_hermiteLoop {w A₀ D₀ : GPoly α}
    (hnormal : ∀ p : K[X], Irreducible p → p ∣ toPoly M D₀ →
      ¬p ∣ implicitDeriv (toPoly M w) p)
    (hD₀ : toPoly M D₀ ≠ 0) (fuel : ℕ) (gn gd A Ds Dm : GPoly α)
    (h : HInv (toPoly M w) (toPoly M A₀) (toPoly M D₀) (toPoly M gn) (toPoly M gd) (toPoly M A)
      (toPoly M Ds) (toPoly M Dm))
    (hfuel : (trim O Dm).length ≤ fuel + 1) :
    hermiteCheck O w A₀ D₀ (hermiteLoop O w fuel gn gd A Ds Dm) = true := by
  induction fuel generalizing gn gd A Dm with
  | zero =>
    simp only [hermiteLoop]
    exact hermiteCheck_of_HInv M _ rfl rfl rfl (toPoly_mul M _ _) hD₀ h (by omega)
  | succ fuel ih =>
    simp only [hermiteLoop]
    split_ifs with hlen
    · exact hermiteCheck_of_HInv M _ (toPoly_trim M _) (toPoly_trim M _) (toPoly_trim M _)
        (by rw [toPoly_trim, toPoly_mul]) hD₀ h hlen
    · obtain ⟨hinv, hlt⟩ := HInv_step M hnormal h hlen
      exact ih _ _ _ _ hinv (by omega)

/-- **Hermite reduction in `K(t)` always passes its certificate**, when all irreducibles are
normal. -/
theorem hermiteCheck_hermite (w A D : GPoly α)
    (hnormal : ∀ p : K[X], Irreducible p → p ∣ toPoly M D →
      ¬p ∣ implicitDeriv (toPoly M w) p)
    (hD : toPoly M D ≠ 0) : hermiteCheck O w A D (hermite O w A D) = true := by
  have hGD : toPoly M (gcd O D (derivX O D)) ∣ toPoly M D := by
    rw [toPoly_gcd]; exact (egcd_dvd M D (derivX O D)).1
  have hGD' : toPoly M (gcd O D (derivX O D)) ∣ derivative (toPoly M D) := by
    rw [toPoly_gcd, ← toPoly_derivX]; exact (egcd_dvd M D (derivX O D)).2
  have hG0 : toPoly M (gcd O D (derivX O D)) ≠ 0 := fun h0 ↦ hD (by simpa [h0] using hGD)
  have hmul := div_mul_of_dvd M D (gcd O D (derivX O D)) hG0 hGD
  change toPoly M D = toPoly M (div O D (gcd O D (derivX O D))) * _ at hmul
  have hsq : Squarefree (toPoly M (div O D (gcd O D (derivX O D)))) :=
    squarefree_of_gcd_derivative hD (by rw [hmul]; ring) hGD' fun q h1 h2 ↦ by
      rw [toPoly_gcd]; exact dvd_egcd M D (derivX O D) h1 (by rwa [toPoly_derivX])
  refine hermiteCheck_hermiteLoop M hnormal hD _ _ _ _ _ _
    ⟨?_, hsq, hG0, ?_, ⟨_, hmul⟩, ?_⟩ ?_
  · simp [M.sem_one]
  · intro p hp hpG
    exact irreducible_dvd_sqfreePart hD (hmul.trans (mul_comm _ _)) hGD' hp (hpG.trans hGD)
  · simp only [toPoly_nil, toPoly_cons, M.sem_one, map_zero, C_1, mul_zero, add_zero, zero_mul,
      sub_self, zero_add, mul_one]
    rw [← hmul]
  · have hGne : trim O (gcd O D (derivX O D)) ≠ [] := fun h0 ↦ hG0 ((trim_eq_nil_iff M _).mp h0)
    have hDne : trim O D ≠ [] := fun h0 ↦ hD ((trim_eq_nil_iff M D).mp h0)
    have h1 := length_trim M hGne
    have h2 := length_trim M hDne
    have h3 := natDegree_le_of_dvd hGD hD
    have h4 := length_trim_le (O := O) D
    omega

/-- The squarefree denominator produced by the loop divides `Ds * Dm`. -/
theorem hermiteLoop_s_dvd (w : GPoly α) (fuel : ℕ) (gn gd A Ds Dm : GPoly α) :
    toPoly M (hermiteLoop O w fuel gn gd A Ds Dm).s ∣ toPoly M Ds * toPoly M Dm := by
  induction fuel generalizing gn gd A Dm with
  | zero => simp only [hermiteLoop, toPoly_mul]; exact dvd_rfl
  | succ fuel ih =>
    simp only [hermiteLoop]
    split_ifs with hlen
    · simp only [toPoly_trim, toPoly_mul]; exact dvd_rfl
    · refine (ih _ _ _ _).trans (mul_dvd_mul_left _ ?_)
      rw [toPoly_gcd]
      exact (egcd_dvd M Dm (derivX O Dm)).1

/-- The squarefree denominator of Hermite reduction divides the original denominator. -/
theorem hermite_s_dvd (w A D : GPoly α) (hD : toPoly M D ≠ 0) :
    toPoly M (hermite O w A D).s ∣ toPoly M D := by
  have hGD : toPoly M (gcd O D (derivX O D)) ∣ toPoly M D := by
    rw [toPoly_gcd]; exact (egcd_dvd M D (derivX O D)).1
  have hG0 : toPoly M (gcd O D (derivX O D)) ≠ 0 := fun h0 ↦ hD (by simpa [h0] using hGD)
  have hmul := div_mul_of_dvd M D (gcd O D (derivX O D)) hG0 hGD
  refine (hermiteLoop_s_dvd M w _ _ _ _ _ _).trans ?_
  change _ ∣ toPoly M D
  rw [hmul]
  exact dvd_rfl

end GPoly
