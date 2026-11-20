import RischTragerBronstein.Computable.ExpExpBaseResiduePos

/-!
# Hermite reduction in `F₀ = R(x₀)(exp a)`, read on values

The executable decomposition `expSplit` + `hermite` + `divMod` gives, in any field
`F₀ ⊇ R` containing `x₀` (`x₀′ = 1`) and `t₁ ≠ 0` with `t₁′ = a′(x₀) t₁`:

`Gn / Gd = (gn / gd)′ + (Λ / t₁^k + rem / s)`

with all the certificates needed by the level-0 theorems.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 3200000 in
theorem hermite_valG_exp_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a : CPoly R) (ha : trim (deriv a) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a)) * t₁)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.isZero (ops₁g R) Gd = false) :
    valG x₀ t₁ (Gn, Gd) = (valG x₀ t₁ ((GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).gn, (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).gd))′ +
        (valP x₀ t₁ (GPoly.add (ops₁g R) (GPoly.mul (ops₁g R) (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).b (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).1 (GPoly.monomial (ops₁g R) (GPoly.expSplit (ops₁g R) Gn Gd).2.2.1 (ops₁g R).one)) (GPoly.expSplit (ops₁g R) Gn Gd).2.1) / t₁ ^ (GPoly.expSplit (ops₁g R) Gn Gd).2.2.1 + valP x₀ t₁ (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).b (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).2 / valP x₀ t₁ (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s) ∧
      GPoly.squarefreeCheck (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s = true ∧
      (GPoly.splitX (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).1 = 0 ∧
      (GPoly.trim (ops₁g R) (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).b (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).2).length < (GPoly.trim (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).length ∧
      GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
        (GPoly.sub (ops₁g R) (GPoly.add (ops₁g R) (GPoly.mul (ops₁g R) (GPoly.add (ops₁g R) (GPoly.mul (ops₁g R) (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).b (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).1 (GPoly.monomial (ops₁g R) (GPoly.expSplit (ops₁g R) Gn Gd).2.2.1 (ops₁g R).one)) (GPoly.expSplit (ops₁g R) Gn Gd).2.1) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s) (GPoly.mul (ops₁g R) (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).b (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).2 (GPoly.monomial (ops₁g R) (GPoly.expSplit (ops₁g R) Gn Gd).2.2.1 (ops₁g R).one)))
          (GPoly.mul (ops₁g R) (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).b (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).2 (GPoly.monomial (ops₁g R) (GPoly.expSplit (ops₁g R) Gn Gd).2.2.1 (ops₁g R).one)))
        (GPoly.hermite (ops₁g R) (expW a) (GPoly.expSplit (ops₁g R) Gn Gd).1 (GPoly.expSplit (ops₁g R) Gn Gd).2.2.2).s).2 = true := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- level one: `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDA' : DifferentialAlgebra R⟮x₀⟯ F₀ :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hchar1 : CharZero R⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap R R⟮x₀⟯).injective
  have hD : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (derivative (toPoly a)) with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (derivative (toPoly a)) := hcoe _
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have hA'0 : derivative (toPoly a) ≠ 0 := fun h' ↦ ha ((trim_eq_nil_iff _).mpr (by
    rw [toPoly_deriv, h']))
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := R⟮x₀⟯) hD (-(C (n : R) * derivative (toPoly a)))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap R[X] R⟮x₀⟯ (C (n : R)) = (n : R⟮x₀⟯) := by
          rw [show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  set M₁ := M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD with hM₁
  -- no new constants in `R(x₀)(t₁)`
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hdega : 1 ≤ (toPoly a).natDegree := by
    by_contra hlt
    have h0' : derivative (toPoly a) = 0 := by
      rw [eq_C_of_natDegree_eq_zero (by omega : (toPoly a).natDegree = 0), derivative_C]
    exact hA'0 h0'
  have hconst : ∀ (P : (R⟮x₀⟯)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : R⟮x₀⟯, P = C e * X ^ n :=
    exp_polynomial_no_new_constants (F := R⟮x₀⟯) (C' := R) hD (toPoly a) hdega (fun P ↦ rfl)
  have hW : GPoly.toPoly M₁ (expW a) = C η₁' * X := by
    rw [hM₁, toPoly_expW_In, ηa, Polynomial.map_id]
  have hDW : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (GPoly.toPoly M₁ (expW a)) P :=
    fun P ↦ by rw [hW]; rfl
  have hGd0 : GPoly.toPoly M₁ Gd ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₁ Gd).mpr hz] at hGd
    exact Bool.noConfusion hGd
  -- (1) split off the powers of `t₁`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M₁ Gn Gd hGd0
  generalize GPoly.expSplit (ops₁g R) Gn Gd = sp at hsp1 hsp2 hsp3 ⊢
  have hd₁0 : GPoly.toPoly M₁ sp.2.2.2 ≠ 0 := fun h ↦ hGd0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (R⟮x₀⟯)[X], Irreducible p → p ∣ GPoly.toPoly M₁ sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₁ (expW a)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η₁' (fun P ↦ rfl) hconst hp (by rw [hDW]; exact hsp')).trans
      hpd)
  -- (2) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M₁ (expW a) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (R⟮x₀⟯)⟮t₁⟯) M₁ (expW a) sp.1 sp.2.2.2 _
    hDW hchk
  have hsdvd := GPoly.hermite_s_dvd M₁ (expW a) sp.1 sp.2.2.2 hd₁0
  generalize GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2 = h at hchk hid hsq hsdvd ⊢
  set S := GPoly.toPoly M₁ h.s with hS
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ S := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) division
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  have hlt := GPoly.divMod_remainder_lt M₁ h.b h.s fun hn ↦ hS0 ((GPoly.trim_eq_nil_iff M₁ _).mp hn)
  generalize GPoly.divMod (ops₁g R) h.b h.s = qr at hdm hlt ⊢
  refine ⟨?_, GPoly.squarefreeCheck_complete M₁ hsq, ?_, hlt, ?_⟩
  · -- the identity, transported to `F₀`
    have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
        (GPoly.toPoly M₁ q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valP x₀ t₁ q := fun q ↦ by
      rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
      simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, hM₁, sem_M₁In, hevc]
    have hXF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ X : (R⟮x₀⟯)⟮t₁⟯) : F₀) = t₁ := by
      rw [algebraMap_adjoinSimple, aeval_X]
    have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
    set φ₂ := algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ with hφ₂
    have hinj : Function.Injective φ₂ := IsFractionRing.injective _ _
    have hφS : φ₂ S ≠ 0 := (map_ne_zero_iff _ hinj).mpr hS0
    have hφd₁ : φ₂ (GPoly.toPoly M₁ sp.2.2.2) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd₁0
    have hX0 : φ₂ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
    have hXk : φ₂ X ^ sp.2.2.1 ≠ 0 := pow_ne_zero _ hX0
    have hΛpoly : GPoly.toPoly M₁ (GPoly.add (ops₁g R) (GPoly.mul (ops₁g R) qr.1
        (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1) =
        GPoly.toPoly M₁ qr.1 * X ^ sp.2.2.1 + GPoly.toPoly M₁ sp.2.1 := by
      rw [GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M₁.sem_one, C_1, one_mul]
    have hid' : φ₂ (GPoly.toPoly M₁ Gn) / φ₂ (GPoly.toPoly M₁ Gd) =
        (φ₂ (GPoly.toPoly M₁ h.gn) / φ₂ (GPoly.toPoly M₁ h.gd))′ +
        (φ₂ (GPoly.toPoly M₁ (GPoly.add (ops₁g R) (GPoly.mul (ops₁g R) qr.1
          (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1)) / φ₂ X ^ sp.2.2.1 +
          φ₂ (GPoly.toPoly M₁ qr.2) / φ₂ S) := by
      have hAD : φ₂ (GPoly.toPoly M₁ Gn) / φ₂ (GPoly.toPoly M₁ Gd) =
          φ₂ (GPoly.toPoly M₁ sp.1) / φ₂ (GPoly.toPoly M₁ sp.2.2.2) +
            φ₂ (GPoly.toPoly M₁ sp.2.1) / φ₂ X ^ sp.2.2.1 := by
        rw [← hsp1, hsp2, map_add, map_mul, map_mul, map_mul, map_pow]
        field_simp
      have hbS : φ₂ (GPoly.toPoly M₁ h.b) / φ₂ S =
          φ₂ (GPoly.toPoly M₁ qr.1) + φ₂ (GPoly.toPoly M₁ qr.2) / φ₂ S := by
        rw [hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one]
      rw [hAD, hid, hbS, hΛpoly, map_add, map_mul, map_pow, add_div, mul_div_assoc, div_self hXk,
        mul_one]
      ring
    have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hid'
    simp only [IntermediateField.coe_add, IntermediateField.coe_div, SubmonoidClass.coe_pow,
      hderiv, hvalP, hXF, hS] at this
    rw [valG, valG]
    exact this
  · -- `s` is prime to `t₁`
    have hsplit := GPoly.toPoly_splitX M₁ h.s
    by_contra hne
    obtain ⟨m, hm⟩ : ∃ m, (GPoly.splitX (ops₁g R) h.s).1 = m + 1 :=
      ⟨(GPoly.splitX (ops₁g R) h.s).1 - 1, by omega⟩
    rw [hm, pow_succ] at hsplit
    exact hXS ⟨X ^ m * GPoly.toPoly M₁ (GPoly.splitX (ops₁g R) h.s).2, by
      rw [hS, hsplit]; ring⟩
  · -- `s ∣ Bn - rem t₁^k`
    refine (GPoly.isZero_iff M₁ _).mpr (GPoly.divMod_exact M₁ _ _ hS0 ?_)
    rw [GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul, add_sub_cancel_right]
    exact dvd_mul_left _ _

end Tower

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
/-- `valP` is a ring homomorphism on codes, and non-zero codes have non-zero values, when `t₁` is
an exponential (hence transcendental). -/
theorem valP_ring_exp (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a : CPoly R) (ha : trim (deriv a) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a)) * t₁) :
    (∀ p q : GPoly (GFrac R), valP x₀ t₁ (GPoly.add (ops₁g R) p q) = valP x₀ t₁ p + valP x₀ t₁ q) ∧
    (∀ p q : GPoly (GFrac R), valP x₀ t₁ (GPoly.mul (ops₁g R) p q) = valP x₀ t₁ p * valP x₀ t₁ q) ∧
    (∀ k : ℕ, valP x₀ t₁ (GPoly.monomial (ops₁g R) k (ops₁g R).one) = t₁ ^ k) ∧
    (∀ q : GPoly (GFrac R), GPoly.isZero (ops₁g R) q = false → valP x₀ t₁ q ≠ 0) ∧
    (∀ q : GPoly (GFrac R), GPoly.squarefreeCheck (ops₁g R) q = true → valP x₀ t₁ q ≠ 0) := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- level one: `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDA' : DifferentialAlgebra R⟮x₀⟯ F₀ :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hchar1 : CharZero R⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap R R⟮x₀⟯).injective
  have hD : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (derivative (toPoly a)) with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (derivative (toPoly a)) := hcoe _
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have hA'0 : derivative (toPoly a) ≠ 0 := fun h' ↦ ha ((trim_eq_nil_iff _).mpr (by
    rw [toPoly_deriv, h']))
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := R⟮x₀⟯) hD (-(C (n : R) * derivative (toPoly a)))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap R[X] R⟮x₀⟯ (C (n : R)) = (n : R⟮x₀⟯) := by
          rw [show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  set M₁ := M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD with hM₁
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly M₁ q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, hM₁, sem_M₁In, hevc]
  have hne : ∀ q : GPoly (GFrac R), GPoly.toPoly M₁ q ≠ 0 → valP x₀ t₁ q ≠ 0 := fun q hq ↦ by
    rw [← hvalP]
    intro h
    have h' : algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ q) = 0 := Subtype.ext h
    exact hq ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h')
  refine ⟨fun p q ↦ ?_, fun p q ↦ ?_, fun k ↦ ?_, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rw [← hvalP, ← hvalP, ← hvalP, GPoly.toPoly_add, map_add]; rfl
  · rw [← hvalP, ← hvalP, ← hvalP, GPoly.toPoly_mul, map_mul]; rfl
  · rw [← hvalP, GPoly.toPoly_monomial, M₁.sem_one, C_1, one_mul, map_pow, SubmonoidClass.coe_pow,
      algebraMap_adjoinSimple, aeval_X]
  · exact hne q fun h ↦ by rw [(GPoly.isZero_iff M₁ q).mpr h] at hq; exact Bool.noConfusion hq
  · exact hne q (GPoly.squarefreeCheck_sound M₁ hq).ne_zero

end Tower
