import RischTragerBronstein.Algebraic.HypLogField
import RischTragerBronstein.Algebraic.EllFunctional
import RischTragerBronstein.Computable.PrimNElem

/-!
# Both answers from certificates over a number field

`logCheckFB_decomp` writes `A/(Dy) = (W/V·y)′ + ∑ κₖ uₖ′/uₖ + B₀/y` with coefficients in a field `F`
embedded in the constants. If `B₀ = 0` the integral is elementary (`elem_of_logCheckFB`); if `B₀` is
a non-zero rational polynomial of degree `≤ deg p − 2` it is **not** elementary
(`not_elem_of_logCheckFB`: subtract the logarithms, then `hyp_no_elem`).
-/

open Polynomial Differential

namespace CPoly

variable {F : Type*} [Field F] [DecidableEq F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma hasElementaryIntegralIn_logSum {ι : Type*} (c u : ι → E) :
    ∀ l : List ι, (∀ i ∈ l, (c i)′ = 0 ∧ u i ≠ 0) →
      HasElementaryIntegralIn ((l.map fun i ↦ c i * logDeriv (u i)).sum)
  | [], _ => by
    simpa using hasElementaryIntegralIn_deriv (0 : E)
  | i :: l, h => by
    rw [List.map_cons, List.sum_cons]
    refine HasElementaryIntegralIn.add ?_ (hasElementaryIntegralIn_logSum c u l
      fun j hj ↦ h j (List.mem_cons_of_mem _ hj))
    have := hasElementaryIntegralIn_logDeriv₂ (c i) 0 (u i) 1 (h i List.mem_cons_self).1
      (by simp) (h i List.mem_cons_self).2 one_ne_zero
    simpa using this

/-- **Elementary when the remainder vanishes.** -/
theorem elem_of_logCheckFB (hC : ∀ c : Kc, c′ = 0) (ι : F →+* Kc) (x y : E) (hx : x′ = 1)
    (p A D W V B0 : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F))
    (hy : y ^ 2 = evF ι x p) (h : logCheckFB p A D W V B0 logs = true) (hB0 : toPoly B0 = 0) :
    HasElementaryIntegral (evF ι x A / (evF ι x D * y)) := by
  obtain ⟨hu, hdec⟩ := logCheckFB_decomp hC ι x y hx p A D W V B0 logs hy h
  rw [hdec, show evF ι x B0 = 0 by simp [evF, hB0], zero_div, add_zero]
  have := hasElementaryIntegral_of_liouville_form (evF ι x W / evF ι x V * y)
    (logs.map fun l ↦ (algebraMap Kc E (ι l.1),
      (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2)) (by
      intro q hq
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
      exact ⟨by rw [deriv_algebraMap, hC, map_zero], hu l hl⟩)
  rw [List.map_map] at this
  exact this

/-- **Not elementary when the remainder is a non-zero rational polynomial.** -/
theorem not_elem_of_logCheckFB (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (ι : F →+* Kc) (x y : E)
    (hx : x′ = 1) (pQ : CPoly ℚ) (hp : Squarefree (toPoly pQ)) (hodd : Odd (toPoly pQ).natDegree)
    (hyQ : y ^ 2 = aeval x (toPoly pQ)) (hgen : ∀ z : E, InHyp Kc x y z)
    (p A D W V B0 : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F))
    (hpQ : evF ι x p = aeval x (toPoly pQ)) (B0Q : ℚ[X]) (hB0Q : evF ι x B0 = aeval x B0Q)
    (hB0ne : B0Q ≠ 0) (hdeg : B0Q.natDegree + 2 ≤ (toPoly pQ).natDegree)
    (h : logCheckFB p A D W V B0 logs = true) :
    ¬HasElementaryIntegral (evF ι x A / (evF ι x D * y)) := by
  intro he
  obtain ⟨hu, hdec⟩ := logCheckFB_decomp hC ι x y hx p A D W V B0 logs (by rw [hpQ]; exact hyQ) h
  have hin := hasElementaryIntegralIn_logSum
    (fun l : F × CPoly F × CPoly F × CPoly F ↦ algebraMap Kc E (ι l.1))
    (fun l ↦ (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2) logs
    (fun l hl ↦ ⟨by rw [deriv_algebraMap, hC, map_zero], hu l hl⟩)
  have h2 := he.sub_in hin
  rw [hdec, hB0Q] at h2
  have h3 : HasElementaryIntegral ((evF ι x W / evF ι x V * y)′ + aeval x B0Q / y) := by
    convert h2 using 1; ring
  exact hB0ne (hyp_no_elem hC hCall x y hx pQ hp hodd hyQ hgen _ B0Q (Or.inr hdeg) h3)

/-- `not_elem_of_logCheckFB` with a remainder whose coefficients are arbitrary constants. -/
theorem not_elem_of_logCheckFBK (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (ι : F →+* Kc) (x y : E)
    (hx : x′ = 1) (pQ : CPoly ℚ) (hp : Squarefree (toPoly pQ)) (hodd : Odd (toPoly pQ).natDegree)
    (hyQ : y ^ 2 = aeval x (toPoly pQ)) (hgen : ∀ z : E, InHyp Kc x y z)
    (p A D W V B0 : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F))
    (hpQ : evF ι x p = aeval x (toPoly pQ)) (B0Q : Kc[X]) (hB0Q : evF ι x B0 = aeval x B0Q)
    (hB0ne : B0Q ≠ 0) (hdeg : B0Q.natDegree + 2 ≤ (toPoly pQ).natDegree)
    (h : logCheckFB p A D W V B0 logs = true) :
    ¬HasElementaryIntegral (evF ι x A / (evF ι x D * y)) := by
  intro he
  obtain ⟨hu, hdec⟩ := logCheckFB_decomp hC ι x y hx p A D W V B0 logs (by rw [hpQ]; exact hyQ) h
  have hin := hasElementaryIntegralIn_logSum
    (fun l : F × CPoly F × CPoly F × CPoly F ↦ algebraMap Kc E (ι l.1))
    (fun l ↦ (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2) logs
    (fun l hl ↦ ⟨by rw [deriv_algebraMap, hC, map_zero], hu l hl⟩)
  have h2 := he.sub_in hin
  rw [hdec, hB0Q] at h2
  have h3 : HasElementaryIntegral ((evF ι x W / evF ι x V * y)′ + aeval x B0Q / y) := by
    convert h2 using 1; ring
  exact hB0ne (hyp_no_elemK hC hCall x y hx pQ hp hodd hyQ hgen _ B0Q (Or.inr hdeg) h3)

end CPoly
