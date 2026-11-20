import RischTragerBronstein.Algebraic.EllCubic

/-!
# Quartics with a rational root: `∫ A(x) / (D(x) √q(x)) dx`, `deg q = 4`, `q(e) = 0`

The substitution `t = 1/(x − e)`, `Y = y t²` turns `y² = q(x)` into the cubic `Y² = P(t)`
(`P(t) = t⁴ q(e + 1/t)`); `t′ = −t²`, and rescaling the derivation by `−1/t²` makes `t′ = 1`.
`ellDecideQuartic` runs `ellDecideCubic` on the transformed integrand; `ellDecideQuartic_spec`:
every answer is correct. E.g. `∫ dx / √(x⁴ − 1)` is not elementary.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- Separability check: `gcd(P, P′)` is a non-zero constant. -/
def sepCheck (P : CPoly ℚ) : Bool := (trim (egcd P (deriv P)).1).length == 1

lemma sepCheck_sound {P : CPoly ℚ} (h : sepCheck P = true) : (toPoly P).Separable := by
  rw [sepCheck, beq_iff_eq] at h
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp h
  obtain ⟨hγ0, hg⟩ := trim_singleton hγ
  have hbez := egcd_spec P (deriv P)
  rw [hg] at hbez
  show IsCoprime (toPoly P) (derivative (toPoly P))
  refine ⟨C γ⁻¹ * toPoly (egcd P (deriv P)).2.1, C γ⁻¹ * toPoly (egcd P (deriv P)).2.2, ?_⟩
  have : C γ⁻¹ * C γ = (1 : ℚ[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  rw [← toPoly_deriv]
  linear_combination C γ⁻¹ * hbez + this

/-- Reversal: `L^rev(t) = t^{len − 1} L(1/t)`. -/
lemma aeval_reverse {E : Type*} [Field E] [CharZero E] (t : E) (ht : t ≠ 0) :
    ∀ L : CPoly ℚ, L ≠ [] → aeval t (toPoly L.reverse) = t ^ (L.length - 1) * aeval (1 / t) (toPoly L)
  | [], h => absurd rfl h
  | [c], _ => by simp
  | c :: d :: L, _ => by
    have ih := aeval_reverse t ht (d :: L) (List.cons_ne_nil _ _)
    rw [List.reverse_cons, toPoly_append, map_add, ih]
    simp only [List.length_reverse, List.length_cons, toPoly_cons, toPoly_nil, mul_zero, add_zero,
      map_mul, map_pow, aeval_X, aeval_C, eq_ratCast, map_add]
    rw [show L.length + 1 + 1 - 1 = L.length + 1 by omega, show L.length + 1 - 1 = L.length by omega]
    field_simp
    ring

/-- The transformed data `(P, Ã, D̃)`. -/
def quarticData (q : CPoly ℚ) (e : ℚ) (A D : CPoly ℚ) : Option (CPoly ℚ × CPoly ℚ × CPoly ℚ) :=
  let s := trim (shiftPoly q e)
  let P := (s.drop 1).reverse
  let sA := trim (shiftPoly A e)
  let sD := trim (shiftPoly D e)
  if s.length = 5 ∧ s.getD 0 0 = 0 ∧ sepCheck P ∧ sA ≠ [] ∧ sD ≠ [] then
    some (P, smul (-1) (mul sA.reverse (monomial (sD.length - 1) 1)),
      mul sD.reverse (monomial (sA.length - 1) 1))
  else none

/-- **The decision procedure for quartics with a rational root `e`.** -/
def ellDecideQuartic (q : CPoly ℚ) (e : ℚ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match quarticData q e A D with
  | some (P, An, Dn) => ellDecideCubic P An Dn fuel
  | none => none

section Spec

open Differential IntermediateField

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma aeval_shift_trim (P : CPoly ℚ) (e : ℚ) (u : E) :
    aeval u (toPoly (trim (shiftPoly P e))) = aeval (u + (e : E)) (toPoly P) := by
  rw [toPoly_trim, toPoly_shiftPoly, aeval_comp]
  simp

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ellDecideQuartic`.** -/
theorem ellDecideQuartic_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (e : ℚ) (hy : y ^ 2 = aeval x (toPoly q))
    (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool)
    (h : ellDecideQuartic q e A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideQuartic at h
  split at h
  swap
  · exact absurd h (by simp)
  rename_i P An Dn hQD
  unfold quarticData at hQD
  simp only at hQD
  split_ifs at hQD with hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hQD
  obtain ⟨hs5, hs0, hsep, hA0, hD0⟩ := hcond
  obtain ⟨rfl, rfl, rfl⟩ := hQD
  set s := trim (shiftPoly q e)
  set sA := trim (shiftPoly A e)
  set sD := trim (shiftPoly D e)
  -- `x` is not a constant
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxe : x - (e : E) ≠ 0 := by
    intro h0
    have := congrArg (fun z : E ↦ z′) h0
    simp only [map_sub, hx, deriv_ratCast_L, sub_zero, map_zero] at this
    exact one_ne_zero this
  set t : E := 1 / (x - (e : E)) with ht
  have ht0 : t ≠ 0 := one_div_ne_zero hxe
  have hxt : x = 1 / t + (e : E) := by rw [ht]; field_simp; ring
  set Y : E := y * t ^ 2 with hY
  -- `Y² = P(t)`
  have hsplit : s = 0 :: s.drop 1 := by
    have hne : s ≠ [] := by intro h0; rw [h0] at hs5; simp at hs5
    obtain ⟨c, L, hcL⟩ := List.exists_cons_of_ne_nil hne
    rw [hcL] at hs0 ⊢
    simp only [List.getD_cons_zero] at hs0
    rw [hs0]; rfl
  have hYP : Y ^ 2 = aeval t (toPoly (s.drop 1).reverse) := by
    have h1 : aeval x (toPoly q) = aeval (1 / t) (toPoly s) := by
      rw [aeval_shift_trim, ← hxt]
    have h2 : aeval (1 / t) (toPoly s) = 1 / t * aeval (1 / t) (toPoly (s.drop 1)) := by
      conv_lhs => rw [hsplit]
      simp
    have hlen : (s.drop 1).length = 4 := by simp [hs5]
    have h3 := aeval_reverse t ht0 (s.drop 1) (by intro h0; rw [h0] at hlen; simp at hlen)
    rw [hlen, show (4 : ℕ) - 1 = 3 from rfl] at h3
    rw [hY, mul_pow, hy, h1, h2, h3]
    field_simp
  -- the rescaled derivation
  have ht' : t′ = -t ^ 2 := by
    rw [ht, Derivation.leibniz_div, map_sub, hx, deriv_ratCast_L]
    simp only [Derivation.map_one_eq_zero, smul_eq_mul, mul_zero, sub_zero, mul_one, zero_sub]
    field_simp
  set τ : E := -t ^ 2 with hτ
  have hτ0 : τ ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ht0)
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hconst : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ hconstE r
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hT' : D'.deriv t = 1 := by
    show 1 / τ * d0 t = 1
    rw [hd0, ht']; exact one_div_mul_cancel hτ0
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hconst, hC, map_zero, mul_zero])
  have hCall' : ∀ z : E, D'.deriv z = 0 → z ∈ Set.range (algebraMap Kc E) := by
    intro z hz
    apply hCall
    have : 1 / τ * d0 z = 0 := hz
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (one_div_ne_zero hτ0)
    · exact h0
  have hQmem : ∀ (w : E) (r : ℚ), ((r : ℚ) : E) ∈ Kc⟮w⟯ := fun w r ↦ by
    have := IntermediateField.algebraMap_mem Kc⟮w⟯ (r : Kc)
    rwa [map_ratCast] at this
  have hgen' : ∀ z : E, InHyp Kc t Y z := by
    have hxX : Kc⟮x⟯ = Kc⟮t⟯ := by
      apply le_antisymm
      · rw [adjoin_simple_le_iff, hxt]
        exact add_mem (div_mem (one_mem _) (mem_adjoin_simple_self _ _)) (hQmem _ _)
      · rw [adjoin_simple_le_iff, ht]
        exact div_mem (one_mem _) (sub_mem (mem_adjoin_simple_self _ _) (hQmem _ _))
    intro z
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
    refine ⟨α, β / t ^ 2, hxX ▸ hα,
      div_mem (hxX ▸ hβ) (pow_mem (mem_adjoin_simple_self _ _) _), ?_⟩
    rw [hY]; field_simp
  have hspec := @ellDecideCubic_spec Kc E _ _ _ _ D' hDA' _ _ hC hCall' t Y hT' _
    (sepCheck_sound hsep).squarefree hYP hgen' _ _ fuel ans h
  rw [hspec]
  -- transfer back
  have hA := aeval_reverse t ht0 sA hA0
  have hD := aeval_reverse t ht0 sD hD0
  rw [aeval_shift_trim, ← hxt] at hA hD
  have hint : aeval t (toPoly (smul (-1) (mul sA.reverse (monomial (sD.length - 1) 1)))) /
      (aeval t (toPoly (mul sD.reverse (monomial (sA.length - 1) 1))) * Y) =
      1 / τ * (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
    simp only [toPoly_smul, toPoly_mul, toPoly_monomial, map_mul, map_neg, aeval_C, map_one,
      map_pow, aeval_X, eq_ratCast, hA, hD]
    rw [hY, hτ]
    push_cast
    field_simp
  rw [hint]
  exact hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hτ0)

end Spec

section Examples

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / √(x⁴ − 1)` is not elementary.** -/
theorem ex_quartic_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 4 - 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / y) := by
  have h := ellDecideQuartic_spec hC hCall x y hx [-1, 0, 0, 0, 1] 1
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [1] [1] 10 false (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([1] : CPoly ℚ)) / (aeval x (CPoly.toPoly ([1] : CPoly ℚ)) * y) =
      1 / y := by simp [CPoly.toPoly]
  rw [e] at h
  intro h'
  exact Bool.false_ne_true (h.mpr h')

/-- **`∫ x dx / √(x⁴ − 1)` is elementary** (`= ½ log (x² + √(x⁴ − 1))`). -/
theorem ex_quartic_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 4 - 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (x / y) := by
  have h := ellDecideQuartic_spec hC hCall x y hx [-1, 0, 0, 0, 1] 1
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [0, 1] [1] 10 true (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([0, 1] : CPoly ℚ)) /
      (aeval x (CPoly.toPoly ([1] : CPoly ℚ)) * y) = x / y := by simp [CPoly.toPoly]
  rw [e] at h
  exact h.mp rfl

end Examples

end EllAlgo
