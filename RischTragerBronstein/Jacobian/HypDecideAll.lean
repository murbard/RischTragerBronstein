import RischTragerBronstein.Jacobian.HypDecideEvenQ
import RischTragerBronstein.Algebraic.Genus0
import RischTragerBronstein.Rational.IntegrableIn

/-!
# Every element of `ℚ(x, √q)`

`hypDecideAll q A D B C N` decides `∫ (A/D + (B/C) y) dx` for `y² = q(x)`, `q ∈ ℚ[x]` squarefree
of degree `≥ 1`:

* the rational part `A/D` always has an elementary integral (`hasElementaryIntegralIn_ratQ`);
* genus zero (`deg q ≤ 2`): every element has an elementary integral (`genus0_linear`,
  `genus0_elementary_gen`);
* otherwise `(B/C) y = Bq/(C y)` is decided by `hypDecideOdd` (odd degree) or `hypDecideEvenQ`
  (even degree).

`hypDecideAll_spec`: every answer is correct; `hypDecideAll_decides`: for all large bounds there is
an answer.
-/

open Polynomial CPoly EllAlgo

namespace Jac

section Theory

open Differential IntermediateField

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

omit [Field Kc] [Algebra Kc E] [Differential Kc] [DifferentialAlgebra Kc E] [CharZero Kc] in
/-- Rational functions of `x` have elementary integrals in every elementary extension. -/
lemma hasElementaryIntegralIn_ratQ (x : E) (hx : x′ = 1) (A D : ℚ[X]) (hD : D ≠ 0) :
    HasElementaryIntegralIn (aeval x A / aeval x D) := by
  intro E' _ _ _ _ _
  have : CharZero E' := charZero_of_injective_algebraMap (algebraMap E E').injective
  letI : Differential ℚ := ⟨0⟩
  haveI : DifferentialAlgebra ℚ E' := ⟨fun q ↦ by
    rw [show (q′ : ℚ) = 0 from rfl, map_zero]
    simpa using deriv_ratCast_L (L := E') q⟩
  have hx' : (algebraMap E E' x)′ = 1 := by rw [deriv_algebraMap, hx, map_one]
  have := hasElementaryIntegral_rational_in (R := ℚ) (fun _ ↦ rfl) (algebraMap E E' x) hx' A D hD 0
  rw [map_zero, zero_add] at this
  have e : ∀ P : ℚ[X], algebraMap E E' (aeval x P) = aeval (algebraMap E E' x) P := fun P ↦
    (aeval_algHom_apply (algebraMap E E').toRatAlgHom x P).symm
  rw [map_div₀, e, e]
  exact this

/-- **Genus zero, linear**: `y² = a x + b` (`a ≠ 0`): every element has an elementary integral. -/
theorem genus0_linear (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (a b : Kc) (ha : a ≠ 0)
    (hy : y ^ 2 = algebraMap Kc E a * x + algebraMap Kc E b)
    (hgen : ∀ z : E, InHyp Kc x y z) (f : E) : HasElementaryIntegral f := by
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have haE : algebraMap Kc E a ≠ 0 := (map_ne_zero_iff _ (algebraMap Kc E).injective).mpr ha
  have hy' : y′ ≠ 0 := by
    intro h0
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, h0, smul_zero, add_zero, map_add, hconstE, hx,
      smul_eq_mul, mul_one, mul_zero] at this
    exact haE this.symm
  have hxy : x ∈ Kc⟮y⟯ := by
    have : x = (y ^ 2 - algebraMap Kc E b) / algebraMap Kc E a := by
      rw [hy]; field_simp; ring
    rw [this]
    exact div_mem (sub_mem (pow_mem (mem_adjoin_simple_self _ _) _)
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.algebraMap_mem _ _)
  have hle : Kc⟮x⟯ ≤ Kc⟮y⟯ := (adjoin_simple_le_iff).mpr hxy
  refine hasElementaryIntegral_of_generated hC y hy' (fun z ↦ ?_) f
  obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
  exact add_mem (hle hα) (mul_mem (hle hβ) (mem_adjoin_simple_self _ _))

end Theory

/-- A squarefree quadratic has a non-zero discriminant. -/
lemma disc_ne_zero_of_squarefree {K : Type*} [Field K] [CharZero K] {a b c : K} (ha : a ≠ 0)
    (hsq : Squarefree (C a * X ^ 2 + C b * X + C c)) : b ^ 2 - 4 * a * c ≠ 0 := by
  intro hd
  set d := b / (2 * a)
  have h2a : (2 : K) * a ≠ 0 := mul_ne_zero two_ne_zero ha
  have e1 : C a * (X + C d) ^ 2 = C a * X ^ 2 + C (2 * a * d) * X + C (a * d ^ 2) := by
    simp only [map_mul, map_pow, map_ofNat]; ring
  have e2 : 2 * a * d = b := by simp only [d]; field_simp
  have e3 : a * d ^ 2 = c := by
    simp only [d]; field_simp; linear_combination hd
  have hfac : C a * X ^ 2 + C b * X + C c = C a * (X + C d) ^ 2 := by rw [e1, e2, e3]
  have := hsq (X + C d) ⟨C a, by rw [hfac]; ring⟩
  exact not_isUnit_X_add_C d this

/-- **The integrand `A/D + (B/C) √q`.** -/
noncomputable def hypDecideAll (q A D B C : CPoly ℚ) (N : ℕ) : Option Bool :=
  if isZero D = true ∨ isZero C = true ∨ squarefreeCheck q = false ∨ (trim q).length ≤ 1 then none
  else if isZero B = true ∨ (trim q).length ≤ 3 then some true
  else if (trim q).length % 2 = 0 then hypDecideOdd (trim q) (mul B q) C N
  else hypDecideEvenQ (trim q) (mul B q) C N

section Spec

open Differential IntermediateField

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `hypDecideAll`.** -/
theorem hypDecideAll_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (hy : y ^ 2 = aeval x (toPoly q)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D B C : CPoly ℚ) (N : ℕ) (ans : Bool) (h : hypDecideAll q A D B C N = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) +
      aeval x (toPoly B) / aeval x (toPoly C) * y) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  unfold hypDecideAll at h
  split_ifs at h with h1 h2 h3
  · -- genus zero or rational
    cases h
    simp only [true_iff]
    simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at h1
    obtain ⟨hDz, hCz, hsqc, hlen⟩ := h1
    have hD : toPoly D ≠ 0 := fun h0 ↦ by rw [(isZero_iff D).mpr h0] at hDz; cases hDz
    have hC0 : toPoly C ≠ 0 := fun h0 ↦ by rw [(isZero_iff C).mpr h0] at hCz; cases hCz
    have hsq : Squarefree (toPoly q) := squarefreeCheck_sound hsqc
    rcases h2 with hB | hl
    · have hB0 : toPoly B = 0 := (isZero_iff B).mp hB
      rw [hB0, map_zero, zero_div, zero_mul, add_zero]
      exact (hasElementaryIntegralIn_ratQ x hx _ _ hD).hasElementaryIntegral
    · have htr : trim q ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
      have hq : toPoly q = toPoly (trim q) := (toPoly_trim q).symm
      have hlast := getLast_trim_ne_zero q htr
      have hexp := toPoly_of_length_le_four (trim q) (by omega)
      set t := trim q with htdef
      have hlen' : t.length = 2 ∨ t.length = 3 := by omega
      have hcoe : ∀ r : ℚ, algebraMap ℚ E r = algebraMap Kc E (algebraMap ℚ Kc r) := fun r ↦ by
        simp
      rcases hlen' with h2 | h3
      · have hl2 : t.getLast htr = t.getD 1 0 := by
          rw [List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by omega)]; congr 1; omega
        have hg2 : t.getD 2 0 = 0 := List.getD_eq_default _ _ (by omega)
        have hg3 : t.getD 3 0 = 0 := List.getD_eq_default _ _ (by omega)
        rw [hq, hexp, hg2, hg3] at hy
        simp only [map_zero, zero_mul, add_zero, map_add, map_mul, aeval_C, aeval_X] at hy
        refine genus0_linear hC x y hx (algebraMap ℚ Kc (t.getD 1 0)) (algebraMap ℚ Kc (t.getD 0 0))
          ((map_ne_zero_iff _ (algebraMap ℚ Kc).injective).mpr (hl2 ▸ hlast)) ?_ hgen _
        rw [hy, hcoe, hcoe]; ring
      · have hl3 : t.getLast htr = t.getD 2 0 := by
          rw [List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by omega)]; congr 1; omega
        have hg3 : t.getD 3 0 = 0 := List.getD_eq_default _ _ (by omega)
        have hsqt : Squarefree (Polynomial.C (t.getD 2 0) * X ^ 2 + Polynomial.C (t.getD 1 0) * X +
            Polynomial.C (t.getD 0 0)) := by
          have : toPoly q = Polynomial.C (t.getD 2 0) * X ^ 2 + Polynomial.C (t.getD 1 0) * X +
              Polynomial.C (t.getD 0 0) := by
            rw [hq, hexp, hg3]; simp only [map_zero, zero_mul, add_zero]; ring
          rw [← this]; exact hsq
        have hdisc := disc_ne_zero_of_squarefree (hl3 ▸ hlast) hsqt
        rw [hq, hexp, hg3] at hy
        simp only [map_zero, zero_mul, add_zero, map_add, map_mul, aeval_C, aeval_X, map_pow] at hy
        refine genus0_elementary_gen hC x y hx (algebraMap ℚ Kc (t.getD 2 0))
          (algebraMap ℚ Kc (t.getD 1 0)) (algebraMap ℚ Kc (t.getD 0 0))
          ((map_ne_zero_iff _ (algebraMap ℚ Kc).injective).mpr (hl3 ▸ hlast)) ?_ ?_ hgen _
        · rw [← map_pow, ← map_ofNat (algebraMap ℚ Kc) 4, ← map_mul, ← map_mul, ← map_sub]
          exact (map_ne_zero_iff _ (algebraMap ℚ Kc).injective).mpr hdisc
        · rw [hy, hcoe, hcoe, hcoe]; ring
  all_goals
    simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at h1
    obtain ⟨hDz, hCz, hsqc, hlen⟩ := h1
    have hD : toPoly D ≠ 0 := fun h0 ↦ by rw [(isZero_iff D).mpr h0] at hDz; cases hDz
    have hC0 : toPoly C ≠ 0 := fun h0 ↦ by rw [(isZero_iff C).mpr h0] at hCz; cases hCz
    have hsq : Squarefree (toPoly q) := squarefreeCheck_sound hsqc
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hne _ hsq.ne_zero
      rw [← hy]; ring
    have hy' : y ^ 2 = aeval x (toPoly (trim q)) := by rw [toPoly_trim]; exact hy
    have hW : aeval x (toPoly B) / aeval x (toPoly C) * y =
        aeval x (toPoly (mul B q)) / (aeval x (toPoly C) * y) := by
      rw [toPoly_mul, map_mul, ← hy]; field_simp
    have hsplit : HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) +
        aeval x (toPoly B) / aeval x (toPoly C) * y) ↔
        HasElementaryIntegral (aeval x (toPoly (mul B q)) / (aeval x (toPoly C) * y)) := by
      have hR := hasElementaryIntegralIn_ratQ x hx (toPoly A) (toPoly D) hD
      rw [hW]
      constructor
      · intro h0
        have := h0.sub_in hR
        rwa [add_sub_cancel_left] at this
      · intro h0
        have := h0.add_in hR
        rwa [add_comm] at this
    rw [hsplit]
  · exact hypDecideOdd_spec hC hCall x y hx (trim q) hy' hgen (mul B q) C N ans h
  · exact hypDecideEvenQ_spec hC hCall x y hx (trim q) hy' hgen (mul B q) C N ans h

/-- **The decision for every element of `ℚ(x, √q)`**: for `q ∈ ℚ[x]` squarefree of degree `≥ 1`
and `D, C ≠ 0`, `hypDecideAll` answers for all large bounds, and the answer is `true` exactly
when `∫ (A/D + (B/C) √q) dx` is elementary. -/
theorem hypDecideAll_decides [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (hsq : Squarefree (toPoly q)) (hq1 : 1 ≤ (toPoly q).natDegree)
    (hy : y ^ 2 = aeval x (toPoly q)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D B C : CPoly ℚ) (hD : toPoly D ≠ 0) (hC0 : toPoly C ≠ 0) :
    ∃ N0, ∀ N, N0 ≤ N → ∃ ans, hypDecideAll q A D B C N = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) +
        aeval x (toPoly B) / aeval x (toPoly C) * y)) := by
  have hDz : isZero D = false := by
    rcases h : isZero D with _ | _
    · rfl
    · exact absurd ((isZero_iff _).mp h) hD
  have hCz : isZero C = false := by
    rcases h : isZero C with _ | _
    · rfl
    · exact absurd ((isZero_iff _).mp h) hC0
  have htr : trim q ≠ [] := fun h0 ↦ hsq.ne_zero ((trim_eq_nil_iff q).mp h0)
  have hL := length_trim htr
  have hbad : ¬ (isZero D = true ∨ isZero C = true ∨ squarefreeCheck q = false ∨
      (trim q).length ≤ 1) := by
    simp only [hDz, hCz, CPoly.squarefreeCheck_complete hsq, not_or]
    refine ⟨by simp, by simp, by simp, by omega⟩
  have hsqt : Squarefree (toPoly (trim q)) := by rw [toPoly_trim]; exact hsq
  have hlast := getLast_trim_ne_zero q htr
  have hgetD : ∀ n, n + 1 = (trim q).length → (trim q).getD n 0 ≠ 0 := by
    intro n hn
    rw [List.getD_eq_getElem _ _ (by omega)]
    rw [List.getLast_eq_getElem] at hlast
    convert hlast using 2
    omega
  suffices hev : ∃ N0, ∀ N, N0 ≤ N → hypDecideAll q A D B C N ≠ none by
    obtain ⟨N0, hN0⟩ := hev
    refine ⟨N0, fun N hN ↦ ?_⟩
    obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (hN0 N hN)
    exact ⟨ans, h, hypDecideAll_spec hC hCall x y hx q hy hgen A D B C N ans h⟩
  by_cases h2 : isZero B = true ∨ (trim q).length ≤ 3
  · exact ⟨0, fun N _ ↦ by simp only [hypDecideAll, if_neg hbad, if_pos h2]; simp⟩
  · have hge : 4 ≤ (trim q).length := by
      simp only [not_or, not_le] at h2; omega
    rcases Nat.even_or_odd (trim q).length with ⟨k, hk⟩ | ⟨k, hk⟩
    · obtain ⟨N0, hN0⟩ := hypDecideOdd_eventually (trim q) (g := k - 1) (by omega)
        (hgetD _ (by omega)) hsqt (mul B q) C hC0
      refine ⟨N0, fun N hN ↦ ?_⟩
      simp only [hypDecideAll, if_neg hbad, if_neg h2, if_pos (show (trim q).length % 2 = 0 by
        omega)]
      exact hN0 N hN
    · obtain ⟨N0, hN0⟩ := hypDecideEvenQ_eventually (trim q) (g := k - 1) (by omega)
        (hgetD _ (by omega)) hsqt (mul B q) C hC0
      refine ⟨N0, fun N hN ↦ ?_⟩
      simp only [hypDecideAll, if_neg hbad, if_neg h2, if_neg (show ¬ (trim q).length % 2 = 0 by
        omega)]
      exact hN0 N hN

end Spec

end Jac
