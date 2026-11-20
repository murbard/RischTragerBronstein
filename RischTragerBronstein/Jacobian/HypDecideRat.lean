import RischTragerBronstein.Jacobian.HypDecideQComplete
import RischTragerBronstein.Algebraic.EllQuartic
import RischTragerBronstein.Computable.RatRoots
import RischTragerBronstein.Computable.HermiteComplete

/-!
# Hyperelliptic curves with rational coefficients

`hypDecideOdd q A D B`: for `y² = q(x)`, `q ∈ ℚ[x]` squarefree of degree `2g + 1`, the integral
model `Y = m y`, `Y² = m² q(x)` (`m` a common denominator, `sqModel`) is passed to `hypDecideQ`.
`hypDecideOdd_spec`: every answer is correct; `hypDecideOdd_decides`: for all large `B` there is
an answer.
-/

open Polynomial CPoly

namespace Jac

/-- `m² q` with integer coefficients (`m = denProd q`). -/
def sqModel (q : CPoly ℚ) : List ℤ := q.map fun a ↦ ((denProd q : ℚ) ^ 2 * a).num

lemma sqModel_cast {q : CPoly ℚ} {a : ℚ} (ha : a ∈ q) :
    ((((denProd q : ℚ) ^ 2 * a).num : ℤ) : ℚ) = (denProd q : ℚ) ^ 2 * a := by
  have h := intCoeffs_cast ha
  have : (denProd q : ℚ) ^ 2 * a = (((denProd q : ℤ) * ((denProd q : ℚ) * a).num : ℤ) : ℚ) := by
    push_cast; rw [h]; ring
  rw [this, Rat.num_intCast]

lemma toPoly_sqModel (q : CPoly ℚ) :
    (toPoly (sqModel q)).map (Int.castRingHom ℚ) = C ((denProd q : ℚ) ^ 2) * toPoly q := by
  ext n
  rw [coeff_map, coeff_toPoly, coeff_C_mul, coeff_toPoly, sqModel]
  by_cases hn : n < q.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getElem_map,
      List.getD_eq_getElem _ _ hn]
    exact sqModel_cast (List.getElem_mem hn)
  · rw [List.getD_eq_default _ _ (by simpa using hn), List.getD_eq_default _ _ (by omega)]
    simp

lemma denProd_ne_zero (q : CPoly ℚ) : (denProd q : ℚ) ≠ 0 := by
  exact_mod_cast (denProd_pos q).ne'

lemma sqModel_getD (q : CPoly ℚ) (n : ℕ) (h : q.getD n 0 ≠ 0) : (sqModel q).getD n 0 ≠ 0 := by
  have hn : n < q.length := by
    by_contra hn; exact h (List.getD_eq_default _ _ (by omega))
  rw [sqModel, List.getD_eq_getElem _ _ (by simpa using hn), List.getElem_map]
  rw [List.getD_eq_getElem _ _ hn] at h
  exact Rat.num_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (denProd_ne_zero q)) h)

/-- **Odd degree over `ℚ`.** -/
noncomputable def hypDecideOdd (q A D : CPoly ℚ) (B : ℕ) : Option Bool :=
  let g := (q.length - 2) / 2
  if q.length = 2 * g + 2 ∧ q.getD (2 * g + 1) 0 ≠ 0 ∧ squarefreeCheck q = true then
    hypDecideQ (sqModel q) g (smul (denProd q : ℚ) A) D B
  else none

lemma sqModel_facts {q : CPoly ℚ} {g : ℕ} (hlen : q.length = 2 * g + 2)
    (hlc : q.getD (2 * g + 1) 0 ≠ 0) (hsq : Squarefree (toPoly q)) :
    Squarefree ((toPoly (sqModel q)).map (Int.castRingHom ℚ)) ∧
    ((toPoly (sqModel q)).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1 ∧
    (sqModel q).length = 2 * g + 2 ∧ (sqModel q).getD (2 * g + 1) 0 ≠ 0 := by
  have hm := denProd_ne_zero q
  have hlen' : (sqModel q).length = 2 * g + 2 := by simp [sqModel, hlen]
  have hlc' := sqModel_getD q _ hlc
  refine ⟨?_, ?_, hlen', hlc'⟩
  · rw [toPoly_sqModel]
    exact (Associated.squarefree_iff (associated_unit_mul_left _ _
      (isUnit_C.mpr (Ne.isUnit (pow_ne_zero 2 hm))))).mpr hsq
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ))]
    exact natDegree_of_list hlen' hlc'

/-- `hypDecideOdd` answers for all large bounds. -/
theorem hypDecideOdd_eventually (q : CPoly ℚ) {g : ℕ} (hlen : q.length = 2 * g + 2)
    (hlc : q.getD (2 * g + 1) 0 ≠ 0) (hsq : Squarefree (toPoly q)) (A D : CPoly ℚ)
    (hD : toPoly D ≠ 0) : ∃ B0, ∀ B, B0 ≤ B → hypDecideOdd q A D B ≠ none := by
  obtain ⟨hsq', hdeg', hlen', hlc'⟩ := sqModel_facts hlen hlc hsq
  obtain ⟨B0, hB0⟩ := hypDecideQ_eventually hlen' hlc' hsq' hdeg' (smul (denProd q : ℚ) A) D hD
  refine ⟨B0, fun B hB ↦ ?_⟩
  have hg : (q.length - 2) / 2 = g := by omega
  unfold hypDecideOdd
  simp only [hg]
  rw [if_pos ⟨hlen, hlc, CPoly.squarefreeCheck_complete hsq⟩]
  exact hB0 B hB

section Spec

open Differential IntermediateField

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] in
lemma ratCast_mem_adjoin (w : E) (r : ℚ) : ((r : ℚ) : E) ∈ Kc⟮w⟯ := by
  have := IntermediateField.algebraMap_mem Kc⟮w⟯ (r : Kc)
  rwa [map_ratCast] at this

set_option maxHeartbeats 800000 in
/-- **Correctness of `hypDecideOdd`.** -/
theorem hypDecideOdd_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (hy : y ^ 2 = aeval x (toPoly q)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (B : ℕ) (ans : Bool) (h : hypDecideOdd q A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypDecideOdd at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨hlen, hlc, hsqc⟩ := hc
  set g := (q.length - 2) / 2
  obtain ⟨hsq', hdeg', -, -⟩ := sqModel_facts hlen hlc (squarefreeCheck_sound hsqc)
  set m : ℚ := (denProd q : ℚ)
  have hm : (m : E) ≠ 0 := Rat.cast_ne_zero.mpr (denProd_ne_zero q)
  have hy' : ((m : E) * y) ^ 2 = aeval x ((toPoly (sqModel q)).map (Int.castRingHom ℚ)) := by
    rw [toPoly_sqModel, map_mul, aeval_C, mul_pow, hy]
    simp [m]
  have hgen' : ∀ z : E, InHyp Kc x ((m : E) * y) z := by
    intro z
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
    refine ⟨α, β / (m : E), hα, div_mem hβ (ratCast_mem_adjoin _ _), ?_⟩
    field_simp
  rw [hypDecideQ_spec hC hCall x ((m : E) * y) hx hsq' hdeg' hy' hgen' _ D B ans h]
  have : aeval x (toPoly (smul m A)) / (aeval x (toPoly D) * ((m : E) * y)) =
      aeval x (toPoly A) / (aeval x (toPoly D) * y) := by
    rw [toPoly_smul, map_mul, aeval_C, eq_ratCast]
    field_simp
  rw [this]

/-- **The odd-degree decision over `ℚ`**: for `q ∈ ℚ[x]` squarefree of degree `2g + 1` (given
without trailing zeros) and `D ≠ 0`, `hypDecideOdd` answers for all large bounds, correctly. -/
theorem hypDecideOdd_decides [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) {g : ℕ} (hlen : q.length = 2 * g + 2) (hlc : q.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree (toPoly q)) (hy : y ^ 2 = aeval x (toPoly q))
    (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → ∃ ans, hypDecideOdd q A D B = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨B0, hB0⟩ := hypDecideOdd_eventually q hlen hlc hsq A D hD
  refine ⟨B0, fun B hB ↦ ?_⟩
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (hB0 B hB)
  exact ⟨ans, h, hypDecideOdd_spec hC hCall x y hx q hy hgen A D B ans h⟩

end Spec

end Jac
