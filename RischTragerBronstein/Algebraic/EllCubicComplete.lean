import RischTragerBronstein.Algebraic.EllCubic
import RischTragerBronstein.Algebraic.EllGenMultiComplete

/-!
# Completeness of `ellDecideCubic`

For a squarefree cubic `p ∈ ℚ[x]` and a split denominator `D`, `ellDecideCubic` answers with
`fuelCubic p D` fuel: the normalization always succeeds and `D(X/κ)` still splits.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- Enough fuel for `ellDecideCubic`. -/
def fuelCubic (p D : CPoly ℚ) : ℕ :=
  match cubicABC p with
  | some (a, b, c, κ, _) => fuelAny a b c (compScale D (1 / κ))
  | none => 0

lemma den_mul_eq_one (q : ℚ) (n m : ℕ) (h : q.den ∣ n) : (q * n * m).den = 1 := by
  have e : q * n = (((q * n).num : ℤ) : ℚ) := (num_mul_of_den_dvd q n h).symm
  rw [e, show (((q * n).num : ℤ) : ℚ) * (m : ℚ) = (((q * n).num * m : ℤ) : ℚ) by push_cast; ring]
  exact Rat.den_intCast _

/-- The normalization of a genuine cubic always succeeds. -/
lemma cubicABC_isSome (p : CPoly ℚ) (hlen : p.length ≤ 4) (hlam : p.getD 3 0 ≠ 0) :
    ∃ a b c : ℤ, ∃ κ ν : ℚ, cubicABC p = some (a, b, c, κ, ν) := by
  unfold cubicABC
  simp only
  set rho := p.getD 0 0
  set nu := p.getD 1 0
  set mu := p.getD 2 0
  set lam := p.getD 3 0
  set k : ℚ := (cubicK lam mu nu rho : ℚ) with hk
  have hk' : k = ((mu.den * (nu * lam).den * (rho * lam ^ 2).den : ℕ) : ℚ) := by
    rw [hk, cubicK]
  rw [if_pos]
  · exact ⟨_, _, _, _, _, rfl⟩
  refine ⟨hlam, hlen, ?_, ?_, ?_⟩
  · have := den_mul_eq_one mu mu.den ((nu * lam).den * (rho * lam ^ 2).den *
      (mu.den * (nu * lam).den * (rho * lam ^ 2).den)) dvd_rfl
    convert this using 2
    rw [hk']; push_cast; ring
  · have := den_mul_eq_one (nu * lam) (nu * lam).den (mu.den * (rho * lam ^ 2).den *
      (mu.den * (nu * lam).den * (rho * lam ^ 2).den) ^ 3) dvd_rfl
    convert this using 2
    rw [hk']; push_cast; ring
  · have := den_mul_eq_one (rho * lam ^ 2) (rho * lam ^ 2).den (mu.den * (nu * lam).den *
      (mu.den * (nu * lam).den * (rho * lam ^ 2).den) ^ 5) dvd_rfl
    convert this using 2
    rw [hk']; push_cast; ring

/-- **Completeness of `ellDecideCubic`.** -/
theorem ellDecideCubic_ne_none (p A D : CPoly ℚ) (hsq : Squarefree (toPoly p))
    (hlen : p.length ≤ 4) (hlam : p.getD 3 0 ≠ 0) (hD : toPoly D ≠ 0)
    (hsplit : (toPoly D).Splits)
    (fuel : ℕ) (hfuel : fuelCubic p D ≤ fuel) :
    ellDecideCubic p A D fuel ≠ none := by
  obtain ⟨a, b, c, κ, ν, hABC⟩ := cubicABC_isSome p hlen hlam
  have hABC' := hABC
  unfold fuelCubic at hfuel
  rw [hABC] at hfuel
  unfold ellDecideCubic
  rw [hABC]
  dsimp only at hfuel ⊢
  unfold cubicABC at hABC'
  simp only at hABC'
  split_ifs at hABC' with hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hABC'
  obtain ⟨-, -, ha1, hb1, hc1⟩ := hcond
  obtain ⟨ha, hb, hc, hκ, hν⟩ := hABC'
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
  have hp4 := toPoly_of_length_le_four p hlen
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
  have hD' : toPoly (compScale D (1 / (lam * k ^ 2))) = (toPoly D).comp (C (1 / (lam * k ^ 2)) * X) :=
    toPoly_compScale _ D
  refine ellDecideEll_ne_none a b c hsq' _ _ ?_ ?_ fuel hfuel
  · rw [hD']
    intro h0
    have := congrArg (fun P ↦ P.comp (C (lam * k ^ 2) * X)) h0
    simp only [comp_assoc, mul_comp, C_comp, X_comp, zero_comp] at this
    rw [← mul_assoc, ← C_mul, one_div_mul_cancel hκ0, C_1, one_mul, comp_X] at this
    exact hD this
  · rw [hD']
    exact hsplit.comp_of_natDegree_le_one ((natDegree_C_mul_le _ _).trans (by simp))

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for `∫ A / (D √p)`, `p` any squarefree cubic over `ℚ`** (`D` split
over `ℚ`). -/
theorem ellDecideCubic_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hsq : Squarefree (toPoly p)) (hlen : p.length ≤ 4) (hlam : p.getD 3 0 ≠ 0)
    (hy : y ^ 2 = aeval x (toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly ℚ)
    (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits) :
    ∃ ans : Bool, ellDecideCubic p A D (fuelCubic p D) = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideCubic_ne_none p A D hsq hlen hlam hD hsplit _ le_rfl)
  exact ⟨ans, hans, ellDecideCubic_spec hC hCall x y hx p hsq hy hgen A D _ ans hans⟩

end Decision

end EllAlgo
