import RischTragerBronstein.Algebraic.EllGenMulti
import RischTragerBronstein.Elementary.Rescale

/-!
# Arbitrary cubics: `∫ A(x) / (D(x) √p(x)) dx`, `p = λx³ + μx² + νx + ρ ∈ ℚ[x]` squarefree

The substitution `X = λk²x`, `Z = λk³y` (`k` clearing denominators) turns `y² = p(x)` into the
integral Weierstrass curve `Z² = X³ + μk²X² + νλk⁴X + ρλ²k⁶`; rescaling the derivation by
`1/(λk²)` (`hasElementaryIntegral_rescale_iff`) makes `X′ = 1`. `ellDecideCubic` runs
`ellDecideEll` on the transformed integrand; `ellDecideCubic_spec`: every answer is correct.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- `P(r X)` as a coefficient list. -/
def compScale : CPoly ℚ → ℚ → CPoly ℚ
  | [], _ => []
  | c :: P, r => c :: smul r (compScale P r)

lemma toPoly_compScale (r : ℚ) : ∀ P : CPoly ℚ,
    toPoly (compScale P r) = (toPoly P).comp (C r * X)
  | [] => by simp [compScale]
  | c :: P => by
    simp only [compScale, toPoly_cons, toPoly_smul, toPoly_compScale r P, add_comp, C_comp,
      mul_comp, X_comp]
    ring

/-- The scale `k` clearing the denominators of the normalized curve. -/
def cubicK (lam mu nu rho : ℚ) : ℕ := mu.den * (nu * lam).den * (rho * lam ^ 2).den

/-- The normalized integral curve `(a, b, c)`, or `none`. -/
def cubicABC (p : CPoly ℚ) : Option (ℤ × ℤ × ℤ × ℚ × ℚ) :=
  let rho := p.getD 0 0
  let nu := p.getD 1 0
  let mu := p.getD 2 0
  let lam := p.getD 3 0
  let k : ℚ := cubicK lam mu nu rho
  let a := mu * k ^ 2
  let b := nu * lam * k ^ 4
  let c := rho * lam ^ 2 * k ^ 6
  if lam ≠ 0 ∧ p.length ≤ 4 ∧ a.den = 1 ∧ b.den = 1 ∧ c.den = 1 then
    some (a.num, b.num, c.num, lam * k ^ 2, lam * k ^ 3)
  else none

/-- **The decision procedure for arbitrary cubics.** -/
def ellDecideCubic (p A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match cubicABC p with
  | some (a, b, c, κ, ν) =>
    ellDecideEll a b c (smul (ν / κ) (compScale A (1 / κ))) (compScale D (1 / κ)) fuel
  | none => none

/-! ### Correctness -/

lemma toPoly_of_length_le_four (p : CPoly ℚ) (h : p.length ≤ 4) :
    toPoly p = C (p.getD 0 0) + C (p.getD 1 0) * X + C (p.getD 2 0) * X ^ 2 +
      C (p.getD 3 0) * X ^ 3 := by
  ext i
  rw [coeff_toPoly]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X]
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i <;> simp
  · rw [List.getD_eq_default _ _ (by omega)]
    simp only [show i ≠ 0 by omega, show ¬(1 = i) by omega, show i ≠ 2 by omega,
      show i ≠ 3 by omega, if_false, mul_zero, add_zero]

/-- Separability survives `f ↦ u f(rX)` (`r, u ≠ 0`). -/
lemma squarefree_scale (f : ℚ[X]) (r u : ℚ) (hr : r ≠ 0) (hu : u ≠ 0) (hsq : Squarefree f) :
    Squarefree (C u * f.comp (C r * X)) := by
  have hsep : f.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
  have hsep' : IsCoprime f (derivative f) := hsep
  have h1 : IsCoprime (f.comp (C r * X)) ((derivative f).comp (C r * X)) :=
    hsep'.map (Polynomial.compRingHom (C r * X))
  have hru : IsUnit (C r) := isUnit_C.mpr (Ne.isUnit hr)
  have hcomp : (f.comp (C r * X)).Separable := by
    show IsCoprime (f.comp (C r * X)) (derivative (f.comp (C r * X)))
    have hL : derivative (C r * X) = C r := by
      rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one]
    rw [derivative_comp, hL]
    exact (isCoprime_mul_unit_left_right hru _ _).mpr h1
  rw [mul_comm]
  exact (hcomp.mul_unit (isUnit_C.mpr (Ne.isUnit hu))).squarefree

section Spec

open Differential IntermediateField

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ellDecideCubic`.** -/
theorem ellDecideCubic_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hsq : Squarefree (toPoly p)) (hy : y ^ 2 = aeval x (toPoly p))
    (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool)
    (h : ellDecideCubic p A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideCubic at h
  split at h
  swap
  · exact absurd h (by simp)
  rename_i a b c κ ν hABC
  unfold cubicABC at hABC
  simp only at hABC
  split_ifs at hABC with hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hABC
  obtain ⟨hlam, hlen, ha1, hb1, hc1⟩ := hcond
  obtain ⟨ha, hb, hc, hκ, hν⟩ := hABC
  set rho := p.getD 0 0
  set nu := p.getD 1 0
  set mu := p.getD 2 0
  set lam := p.getD 3 0
  set k : ℚ := (cubicK lam mu nu rho : ℚ) with hk
  have hk0 : k ≠ 0 := by
    simp only [hk, cubicK]; push_cast
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast Rat.den_nz mu)
      (by exact_mod_cast Rat.den_nz (nu * lam))) (by exact_mod_cast Rat.den_nz (rho * lam ^ (2 : ℕ)))
  have haQ : (a : ℚ) = mu * k ^ 2 := by rw [← ha]; exact Rat.coe_int_num_of_den_eq_one ha1
  have hbQ : (b : ℚ) = nu * lam * k ^ 4 := by rw [← hb]; exact Rat.coe_int_num_of_den_eq_one hb1
  have hcQ : (c : ℚ) = rho * lam ^ 2 * k ^ 6 := by
    rw [← hc]; exact Rat.coe_int_num_of_den_eq_one hc1
  subst hκ hν
  have hκ0 : lam * k ^ 2 ≠ 0 := mul_ne_zero hlam (pow_ne_zero _ hk0)
  have hν0 : lam * k ^ 3 ≠ 0 := mul_ne_zero hlam (pow_ne_zero _ hk0)
  have hp4 := toPoly_of_length_le_four p hlen
  -- the new variables
  set Xn : E := ((lam * k ^ 2 : ℚ) : E) * x
  set Zn : E := ((lam * k ^ 3 : ℚ) : E) * y
  have hκE : ((lam * k ^ 2 : ℚ) : E) ≠ 0 := by exact_mod_cast hκ0
  have hνE : ((lam * k ^ 3 : ℚ) : E) ≠ 0 := by exact_mod_cast hν0
  have hZ : Zn ^ 2 = Xn ^ 3 + a * Xn ^ 2 + b * Xn + c := by
    simp only [Zn, Xn, mul_pow, hy, hp4]
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
    have e1 : ((a : ℤ) : E) = ((mu * k ^ 2 : ℚ) : E) := by rw [← haQ]; push_cast; rfl
    have e2 : ((b : ℤ) : E) = ((nu * lam * k ^ 4 : ℚ) : E) := by rw [← hbQ]; push_cast; rfl
    have e3 : ((c : ℤ) : E) = ((rho * lam ^ 2 * k ^ 6 : ℚ) : E) := by rw [← hcQ]; push_cast; rfl
    rw [e1, e2, e3]
    push_cast
    ring
  -- the new curve is squarefree
  have hsq' : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)) := by
    have := squarefree_scale (toPoly p) (1 / (lam * k ^ 2)) ((lam * k ^ 2) ^ 3 / lam)
      (one_div_ne_zero hκ0) (div_ne_zero (pow_ne_zero _ hκ0) hlam) hsq
    convert this using 1
    rw [hp4]
    apply Polynomial.funext
    intro t
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_comp, haQ, hbQ, hcQ]
    field_simp
    ring
  -- the rescaled derivation
  set τ : E := ((lam * k ^ 2 : ℚ) : E) with hτ
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hconst : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ by
    rw [hd0, deriv_algebraMap, hC, map_zero]
  have hτ' : d0 τ = 0 := by rw [hd0, hτ]; exact deriv_ratCast_L _
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hX' : D'.deriv Xn = 1 := by
    show 1 / τ * d0 (τ * x) = 1
    rw [Derivation.leibniz, hτ', smul_zero, add_zero, smul_eq_mul, hd0, hx, mul_one,
      one_div_mul_cancel hκE]
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hconst, hC, map_zero, mul_zero])
  have hCall' : ∀ z : E, D'.deriv z = 0 → z ∈ Set.range (algebraMap Kc E) := by
    intro z hz
    apply hCall
    have : 1 / τ * d0 z = 0 := hz
    rw [mul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 (one_div_ne_zero hκE)
    · exact h0
  have hQmem : ∀ (w : E) (q : ℚ), ((q : ℚ) : E) ∈ Kc⟮w⟯ := fun w q ↦ by
    have := IntermediateField.algebraMap_mem Kc⟮w⟯ (q : Kc)
    rwa [map_ratCast] at this
  have hgen' : ∀ z : E, InHyp Kc Xn Zn z := by
    have hxX : Kc⟮x⟯ = Kc⟮Xn⟯ := by
      apply le_antisymm
      · rw [adjoin_simple_le_iff]
        have : x = ((1 / (lam * k ^ 2) : ℚ) : E) * Xn := by
          simp only [Xn]; push_cast; field_simp
        rw [this]
        exact mul_mem (hQmem _ _) (mem_adjoin_simple_self _ _)
      · rw [adjoin_simple_le_iff]
        exact mul_mem (hQmem _ _) (mem_adjoin_simple_self _ _)
    intro z
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
    refine ⟨α, β * ((1 / (lam * k ^ 3) : ℚ) : E), hxX ▸ hα, mul_mem (hxX ▸ hβ) (hQmem _ _), ?_⟩
    simp only [Zn]; push_cast; field_simp
  have hspec := @ellDecideEll_spec Kc E _ _ _ _ D' hDA' _ _ hC hCall' Xn Zn hX' a b c hsq' hZ
    hgen' _ _ fuel ans h
  rw [hspec]
  -- transfer back
  have hint : aeval Xn (toPoly (smul (lam * k ^ 3 / (lam * k ^ 2)) (compScale A (1 / (lam * k ^ 2))))) /
      (aeval Xn (toPoly (compScale D (1 / (lam * k ^ 2)))) * Zn) =
      1 / τ * (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
    simp only [toPoly_smul, toPoly_compScale, map_mul, aeval_C, eq_ratCast, aeval_comp]
    have hxx : ((1 / (lam * k ^ 2) : ℚ) : E) * aeval Xn (X : ℚ[X]) = x := by
      rw [aeval_X]; simp only [Xn]; push_cast; field_simp
    rw [hxx]
    simp only [Zn, hτ]
    push_cast
    field_simp
  rw [hint]
  exact hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hκE)

end Spec

end EllAlgo
