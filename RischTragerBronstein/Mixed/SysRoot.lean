import RischTragerBronstein.Computable.RootBound
import RischTragerBronstein.Mixed.MTRel

/-!
# Coupled Risch systems: a computable bound on the integer roots of a polynomial over `Fₘ`

For codes `c₀, …, c_d` of level `m`, the natural numbers `e` with `∑ eʲ cⱼ = 0` are bounded:
`(eʲ)ⱼ` is a `ℚ`-relation among the `cⱼ`, so it lies in the span `V` of `mrel`; any `w ⊥ V`
(`nullBasis` of the transpose) gives the rational polynomial `∑ wⱼ Xʲ` vanishing at `e`, bounded by
`rootBound` (`intRootBound_spec`).
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys

/-- The transpose of a list of rows of length `L`. -/
def transposeL (V : List (CPoly ℚ)) (L : ℕ) : List (CPoly ℚ) :=
  (List.range L).map fun j ↦ V.map fun v ↦ v.getD j 0

/-- The computable form of `rootBound`. -/
def rootBoundL (w : CPoly ℚ) : ℚ :=
  1 + (∑ i ∈ Finset.range ((CPoly.trim w).length - 1), |w.getD i 0|) /
    |w.getD ((CPoly.trim w).length - 1) 0|

lemma rootBoundL_eq (w : CPoly ℚ) (hw : toPoly w ≠ 0) : rootBoundL w = rootBound (toPoly w) := by
  have hne : CPoly.trim w ≠ [] := fun h ↦ hw (by
    rw [← toPoly_trim, h]; rfl)
  have hl := CPoly.length_trim hne
  have hd : (CPoly.trim w).length - 1 = (toPoly w).natDegree := by omega
  rw [rootBoundL, rootBound, hd, leadingCoeff, coeff_toPoly]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦ by rw [coeff_toPoly]

/-- **The integer-root bound** (`none` if no orthogonal vector exists, i.e. all `cⱼ = 0`). -/
def intRootBound (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (vs : List (LC m)) : Option ℕ :=
  match ((CPoly.nullBasis (transposeL (mrel Fc ks m vs) vs.length)).map (·.take vs.length)).find?
      (fun w ↦ w.any (· != 0)) with
  | some w => some (maxRootLE w ⌈rootBoundL w⌉₊)
  | none => none

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Every natural root is bounded.** -/
theorem intRootBound_spec (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (B : ℕ)
    (hB : intRootBound Fc ks m vs = some B) (e : ℕ)
    (he : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fun j ↦ algebraMap ℚ Cc ((e : ℚ) ^ j)) vs).sum = 0) :
    e ≤ B := by
  classical
  unfold intRootBound at hB
  split at hB
  swap
  · exact absurd hB (by simp)
  rename_i w hw
  obtain rfl := Option.some.inj hB
  have hwmem := List.mem_of_find?_eq_some hw
  have hwnz := List.find?_some hw
  simp only [List.any_eq_true, bne_iff_ne, ne_eq] at hwnz
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hwmem
  set Ln := vs.length with hLn
  set V := mrel Fc ks m vs with hV
  have hgw : ∀ j < Ln, (w0.take Ln).getD j 0 = w0.getD j 0 := fun j hj ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, hj]
  -- `w ⊥ V`
  have horth := CPoly.nullBasis_sound (transposeL V Ln) w0 hw0
  have hcol : ∀ j < Ln, ∀ k < V.length, ((transposeL V Ln).getD j []).getD k 0 = (V.getD k []).getD j 0 :=
    fun j hj k hk ↦ by
      rw [transposeL, Tower.NestP.NestTower.getD_range_map _ _ hj,
        Tower.NestP.NestTower.getD_map' _ _ [] 0 hk]
  have hwV : ∀ k < V.length, ∑ j ∈ Finset.range Ln, (w0.take Ln).getD j 0 * (V.getD k []).getD j 0 = 0 := by
    intro k hk
    have := congrArg (fun P : ℚ[X] ↦ P.coeff k) horth
    simp only [CPoly.lcomb, coeff_zero] at this
    rw [Tower.NestP.zipWith_sum_getD (fun (c : ℚ) (v : CPoly ℚ) ↦ Polynomial.C c * toPoly v) 0 []
      (fun v ↦ by simp), finset_sum_coeff] at this
    rw [show (transposeL V Ln).length = Ln by simp [transposeL]] at this
    refine (Finset.sum_congr rfl fun j hj ↦ ?_).trans this
    rw [coeff_C_mul, coeff_toPoly, hgw j (Finset.mem_range.mp hj), hcol j (Finset.mem_range.mp hj) k hk]
  -- the relation from the root
  obtain ⟨β, hβ⟩ := T.mrel_complete m h vs _ (by simp [hLn]) he
  have hrel : ∑ j ∈ Finset.range Ln, (w0.take Ln).getD j 0 * (e : ℚ) ^ j = 0 := by
    apply (algebraMap ℚ Cc).injective
    rw [map_zero, map_sum]
    have e1 : ∀ j ∈ Finset.range Ln, algebraMap ℚ Cc ((w0.take Ln).getD j 0 * (e : ℚ) ^ j) =
        ∑ k ∈ Finset.range V.length, β.getD k 0 * algebraMap ℚ Cc ((w0.take Ln).getD j 0 *
          (V.getD k []).getD j 0) := fun j hj ↦ by
      have := hβ j
      rw [Tower.NestP.NestTower.getD_range_map _ _ (Finset.mem_range.mp hj)] at this
      rw [map_mul, this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [← Finset.mul_sum, ← map_sum, hwV k (Finset.mem_range.mp hk), map_zero, mul_zero]
  -- the rational polynomial
  set P : ℚ[X] := toPoly (w0.take Ln) with hP
  have hP0 : P ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := hwnz
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    intro h0
    apply hx0
    have := congrArg (fun Q : ℚ[X] ↦ Q.coeff j) h0
    simp only [hP, coeff_toPoly, coeff_zero] at this
    rwa [List.getD_eq_getElem _ _ hj] at this
  have hdeg : P.natDegree < Ln + 1 := by
    rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hP, coeff_toPoly, List.getD_eq_default]
    have : (w0.take Ln).length ≤ Ln := List.length_take_le _ _
    exact_mod_cast (show (w0.take Ln).length ≤ i by
      have : Ln < i := by exact_mod_cast hi
      omega)
  have hroot : P.IsRoot (e : ℚ) := by
    rw [IsRoot.def, eval_eq_sum_range' hdeg, Finset.sum_range_succ]
    simp only [hP, coeff_toPoly]
    rw [hrel, zero_add, List.getD_eq_default _ _ (by
      have := List.length_take_le Ln w0; omega), zero_mul]
  have hb := abs_le_rootBound P hP0 _ hroot
  rw [← rootBoundL_eq _ hP0, abs_of_nonneg (by positivity)] at hb
  exact le_maxRootLE _ _ e (by exact_mod_cast hb.trans (Nat.le_ceil _)) hroot

end MTower

end Curves.MT
