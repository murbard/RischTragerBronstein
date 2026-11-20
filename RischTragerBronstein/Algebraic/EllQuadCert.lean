import RischTragerBronstein.Algebraic.EllLog
import RischTragerBronstein.Algebraic.HypDecide
import RischTragerBronstein.Algebraic.HypLogField
import RischTragerBronstein.Algebraic.HypRed
import RischTragerBronstein.Algebraic.EllCertValid

/-!
# Removing a logarithmic part with constant coefficients

`ell_log_decompK` is `ell_log_decomp` for polynomials whose coefficients are arbitrary constants
(`Kc[X]`): if `Gn · N = Gd · (c M + R N)` with `N = a² − b² p`, `M = 2p(ab′ − a′b) + abp′`, then
`Gn / (Gd y) = R / y + w` with `w` elementary-integrable in every elementary extension.
-/

open Polynomial

namespace Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The logarithmic part as a decomposition, constant coefficients.** -/
theorem ell_log_decompK (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : Kc[X])
    (hp0 : p ≠ 0) (hy : y ^ 2 = aeval x p) (Gn Gd a b R : Kc[X]) (c : Kc) (hGd : Gd ≠ 0)
    (hN : a ^ 2 - b ^ 2 * p ≠ 0)
    (hid : Gn * (a ^ 2 - b ^ 2 * p) = Gd * (C c * (2 * p * (a * derivative b - derivative a * b) +
      a * b * derivative p) + R * (a ^ 2 - b ^ 2 * p))) :
    ∃ w : E, HasElementaryIntegralIn w ∧ aeval x Gn / (aeval x Gd * y) = aeval x R / y + w := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : Kc[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ aeval_ne_zero_of_tr x htrK hP
  have hder : ∀ Q : Kc[X], (aeval x Q)′ = aeval x (derivative Q) := deriv_aeval_x x hC hx
  have hP0 := hne p hp0
  have hy0 : y ≠ 0 := by rintro rfl; apply hP0; rw [← hy]; ring
  set r := aeval x (derivative p) / (2 * (aeval x p)) with hr
  have hyd : y′ = r * y := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [hder] at this
    rw [hr, ← hy]
    field_simp
    linear_combination this
  have hNx : (aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p) ≠ 0 := by
    have := hne _ hN; simpa using this
  have hab0 : (aeval x a) + (aeval x b) * y ≠ 0 := by
    intro h0; apply hNx
    rw [← hy, show (aeval x a) = -((aeval x b) * y) by linear_combination h0]; ring
  have hGdx := hne Gd hGd
  have hax' : (aeval x a)′ = aeval x (derivative a) := hder a
  have hbx' : (aeval x b)′ = aeval x (derivative b) := hder b
  have hNd : logDeriv ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p)) =
      aeval x (derivative (a ^ 2 - b ^ 2 * p)) / ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p)) := by
    unfold logDeriv
    rw [show (aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p) = aeval x (a ^ 2 - b ^ 2 * p) by simp,
      hder]
  set cE : E := algebraMap Kc E c with hcE
  have hcE' : cE′ = 0 := by rw [hcE, deriv_algebraMap, hC, map_zero]
  have h2 : (2 : E)′ = 0 := by
    rw [← map_ofNat (algebraMap Kc E) 2, deriv_algebraMap, hC, map_zero]
  have key : aeval x Gn / (aeval x Gd * y) = aeval x R / y +
      ((2 * cE) * logDeriv ((aeval x a) + (aeval x b) * y) +
        (-cE) * logDeriv ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p))) := by
    rw [logDeriv_ab y (aeval x a) (aeval x b) (aeval x p) r hy hyd hNx, hNd, hax', hbx', hr]
    have e := congrArg (aeval x) hid
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, aeval_C,
      derivative_mul, derivative_sub, derivative_pow, map_natCast, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one] at e ⊢
    rw [← hcE] at e
    have hNx' : (aeval x a) ^ 2 - (aeval x p) * (aeval x b) ^ 2 ≠ 0 := by
      rw [mul_comm]; exact hNx
    set A := aeval x a
    set B := aeval x b
    set P := aeval x p
    have hl : aeval x Gn / (aeval x Gd * y) = aeval x Gn / (aeval x Gd * P) * y := by
      rw [← hy]; field_simp
    have hr' : aeval x R / y = aeval x R / P * y := by rw [← hy]; field_simp
    have h0 : 2 * cE * ((A * aeval x (derivative a) - B * (aeval x (derivative b) +
        B * (aeval x (derivative p) / (2 * P))) * P) / (A ^ 2 - B ^ 2 * P)) +
        -cE * ((2 * A * aeval x (derivative a) - (2 * B * aeval x (derivative b) * P +
          B ^ 2 * aeval x (derivative p))) / (A ^ 2 - B ^ 2 * P)) = 0 := by
      field_simp; ring
    have h1 : aeval x Gn / (aeval x Gd * P) = aeval x R / P + 2 * cE *
        ((A * (aeval x (derivative b) + B * (aeval x (derivative p) / (2 * P))) -
          aeval x (derivative a) * B) / (A ^ 2 - B ^ 2 * P)) := by
      field_simp
      linear_combination e
    rw [hl, hr', h1]
    have hPP : P * P⁻¹ = 1 := mul_inv_cancel₀ hP0
    linear_combination h0 + (cE * B ^ 2 * aeval x (derivative p) *
      (-(P * B ^ 2) + A ^ 2)⁻¹ * 2) * hPP
  exact ⟨_, hasElementaryIntegralIn_logDeriv₂ (2 * cE) (-cE)
    ((aeval x a) + (aeval x b) * y) ((aeval x a) ^ 2 - (aeval x b) ^ 2 * (aeval x p))
    (by rw [Derivation.leibniz, hcE', h2]; simp) (by rw [map_neg, hcE', neg_zero]) hab0 hNx, key⟩

end Differential

namespace CPoly

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

open Differential

/-- `(C y)′ = (C′ P + C P′ / 2) / y` for `y² = P`. -/
lemma deriv_mul_y_K (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (P C0 : Kc[X])
    (hy : y ^ 2 = aeval x P) (hy0 : y ≠ 0) :
    (aeval x C0 * y)′ = aeval x (derivative C0 * P + C (1 / 2 : Kc) * (C0 * derivative P)) / y := by
  have hder : ∀ Q : Kc[X], (aeval x Q)′ = aeval x (derivative Q) := deriv_aeval_x x hC hx
  have h2 := congrArg (fun z : E ↦ z′) hy
  simp only [pow_two, Derivation.leibniz, smul_eq_mul, hder] at h2
  have hyd : y′ = aeval x (derivative P) / (2 * y) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]; linear_combination h2
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hder, hyd]
  simp only [map_add, map_mul, aeval_C, map_div₀, map_one, map_ofNat]
  rw [← hy]
  field_simp
  ring

/-- **`∫ B / y` over a field of coefficients `F ⊆ Kc`**: elementary iff the remainder of `hypRed`
vanishes (`p` rational, squarefree of odd degree; `B ∈ F[x]`). -/
theorem hyp_decidesF (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (ι : F →+* Kc) (x y : E)
    (hx : x′ = 1) (pQ : CPoly ℚ) (hp : Squarefree (toPoly pQ)) (hodd : Odd (toPoly pQ).natDegree)
    (hy : y ^ 2 = aeval x (toPoly pQ)) (hgen : ∀ z : E, InHyp Kc x y z)
    (p : CPoly F) (hpm : toPoly p = (toPoly pQ).map (algebraMap ℚ F)) (B : CPoly F) :
    HasElementaryIntegral (evF ι x B / y) ↔ isZero (hypRed p B).2 = true := by
  have hp0 : toPoly pQ ≠ 0 := hp.ne_zero
  have hpdeg : (toPoly p).natDegree = (toPoly pQ).natDegree := by
    rw [hpm, natDegree_map_eq_of_injective (algebraMap ℚ F).injective]
  have hp1 : 1 ≤ (toPoly p).natDegree := by rw [hpdeg]; obtain ⟨k, hk⟩ := hodd; omega
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hPK : (toPoly p).map ι = (toPoly pQ).map (algebraMap ℚ Kc) := by
    rw [hpm, Polynomial.map_map]; congr 1; exact RingHom.ext_rat _ _
  have hyK : y ^ 2 = aeval x ((toPoly p).map ι) := by
    rw [hPK, aeval_map_algebraMap]; exact hy
  have hpx : aeval x (toPoly pQ) ≠ 0 := by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hp0)
  have hy0 : y ≠ 0 := by rintro rfl; apply hpx; rw [← hy]; ring
  obtain ⟨hsp, hB0deg⟩ := hypRed_spec p B hp1
  set C0 := (hypRed p B).1
  set B0 := (hypRed p B).2
  have hdec : evF ι x B / y = (aeval x ((toPoly C0).map ι) * y)′ + evF ι x B0 / y := by
    rw [deriv_mul_y_K hC x y hx _ _ hyK hy0, evF, evF, hsp]
    simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map, map_C, map_add]
    rw [map_div₀, map_one, map_ofNat]
    ring
  rw [hdec, isZero_iff]
  constructor
  · intro h
    have := hyp_no_elemK hC hCall x y hx pQ hp hodd hy hgen _ ((toPoly B0).map ι) (by
      rcases hB0deg with h0 | h0
      · left; rw [h0, Polynomial.map_zero]
      · right; rw [natDegree_map_eq_of_injective ι.injective, ← hpdeg]; exact h0) h
    exact (Polynomial.map_eq_zero_iff ι.injective).mp this
  · intro h0
    rw [evF, h0, Polynomial.map_zero, map_zero, zero_div, add_zero]
    exact hasElementaryIntegral_of_deriv _

/-- `fracG` evaluated through `ι : F → Kc`: `Gn / Gd = B + ∑ (z/D) β / (x − α)`. -/
lemma fracG_evF (ι : F →+* Kc) (x : E) (hxa : ∀ z : F, x - algebraMap Kc E (ι z) ≠ 0)
    (B : CPoly F) (D : ℕ) : ∀ pts : List (F × F × ℤ),
    evF ι x (EllAlgo.fracG B D pts).2 ≠ 0 ∧ evF ι x (EllAlgo.fracG B D pts).1 /
      evF ι x (EllAlgo.fracG B D pts).2 = evF ι x B + (pts.map fun q ↦
        algebraMap Kc E (ι ((q.2.2 : F) / D * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum
  | [] => by
    refine ⟨by simp [EllAlgo.fracG, evF, CPoly.toPoly], ?_⟩
    simp [EllAlgo.fracG, evF, CPoly.toPoly]
  | q :: t => by
    obtain ⟨h0, h1⟩ := fracG_evF ι x hxa B D t
    have hlx := hxa q.1
    have hlin : evF ι x ([-q.1, 1] : CPoly F) = x - algebraMap Kc E (ι q.1) := by
      simp [evF, CPoly.toPoly, sub_eq_add_neg, add_comm]
    have hmul : ∀ u w : CPoly F, evF ι x (mul u w) = evF ι x u * evF ι x w := fun u w ↦ by
      simp [evF, toPoly_mul]
    have hadd : ∀ u w : CPoly F, evF ι x (add u w) = evF ι x u + evF ι x w := fun u w ↦ by
      simp [evF, toPoly_add]
    have hsmul : ∀ (t : F) (u : CPoly F), evF ι x (smul t u) = algebraMap Kc E (ι t) * evF ι x u :=
      fun t u ↦ by simp [evF, toPoly_smul]
    refine ⟨?_, ?_⟩
    · simp only [EllAlgo.fracG, hmul, hlin]; exact mul_ne_zero h0 hlx
    · simp only [EllAlgo.fracG, hmul, hadd, hsmul, hlin, List.map_cons, List.sum_cons]
      rw [add_left_comm, ← h1]
      field_simp
      ring

end CPoly
