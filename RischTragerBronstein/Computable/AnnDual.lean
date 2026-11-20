import RischTragerBronstein.Mixed.SysRoot
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duality for annihilators

The annihilator of a list of rational vectors `V` (truncated to `L` coordinates) is computed as
`nullBasis (transposeL V L)`. **A vector orthogonal to every annihilator vector is a rational
combination of the rows of `V`** (`ann_dual`): the rows, as linear functionals, have the kernel of
the matrix as common kernel, which the annihilator spans (`nullBasis_complete`), so the functional
`x · _` vanishes on it and lies in their span (`mem_span_of_iInf_ker_le_ker`).
-/

open Polynomial CPoly

namespace Curves.MT

lemma getD_unitL (i j : ℕ) : (CPoly.unitL i : CPoly ℚ).getD j 0 = if i = j then 1 else 0 := by
  unfold CPoly.unitL
  by_cases hij : j < i
  · rw [List.getD_append _ _ _ _ (by simpa using hij)]
    simp [List.getD_eq_getElem?_getD, hij.ne']
  · rw [List.getD_append_right _ _ _ _ (by simpa using hij)]
    simp only [List.length_replicate]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, List.getD_eq_default _ _ (by simp; omega)]

lemma getD_transposeL (V : List (CPoly ℚ)) (L j k : ℕ) (hj : j < L) :
    ((transposeL V L).getD j []).getD k 0 = (V.getD k []).getD j 0 := by
  rw [transposeL, Tower.NestP.NestTower.getD_range_map _ _ hj]
  by_cases hk : k < V.length
  · rw [Tower.NestP.NestTower.getD_map' _ _ [] 0 hk]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default V [] (by omega)]; rfl

/-- **Vectors orthogonal to the annihilator are combinations of the rows.** -/
theorem ann_dual (V : List (CPoly ℚ)) (L : ℕ) (x : ℕ → ℚ)
    (horth : ∀ w ∈ CPoly.nullBasis (transposeL V L),
      ∑ j ∈ Finset.range L, w.getD j 0 * x j = 0) :
    ∃ μ : ℕ → ℚ, ∀ j < L, x j = ∑ k ∈ Finset.range V.length, μ k * (V.getD k []).getD j 0 := by
  classical
  set φ : Fin V.length → ((Fin L → ℚ) →ₗ[ℚ] ℚ) := fun k ↦
    ∑ j : Fin L, (V.getD k []).getD j 0 • LinearMap.proj j with hφ
  set g : (Fin L → ℚ) →ₗ[ℚ] ℚ := ∑ j : Fin L, x j • LinearMap.proj j with hg
  have hφv : ∀ k v, φ k v = ∑ j : Fin L, (V.getD k []).getD j 0 * v j := fun k v ↦ by
    simp [hφ]
  have hgv : ∀ v, g v = ∑ j : Fin L, x j * v j := fun v ↦ by simp [hg]
  have hker : ⨅ k, LinearMap.ker (φ k) ≤ LinearMap.ker g := by
    intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [LinearMap.mem_ker, hgv]
    -- `v` is a relation among the columns
    set cs : List ℚ := List.ofFn v with hcs
    have hcl : cs.length = (transposeL V L).length := by simp [hcs, transposeL]
    have h0 : CPoly.lcombS (RingHom.id ℚ) cs (transposeL V L) = 0 := by
      refine Polynomial.ext fun k ↦ ?_
      rw [Tower.NestP.NestTower.coeff_lcombS, coeff_zero,
        Tower.NestP.zipWith_sum_getD (fun (b : ℚ) (w : CPoly ℚ) ↦ b * (RingHom.id ℚ) (w.getD k 0))
          0 [] (fun _ ↦ by simp)]
      rw [show (transposeL V L).length = L by simp [transposeL]]
      by_cases hk : k < V.length
      · have := LinearMap.mem_ker.mp (hv ⟨k, hk⟩)
        rw [hφv] at this
        rw [← Fin.sum_univ_eq_sum_range (fun j ↦ cs.getD j 0 * (RingHom.id ℚ)
          (((transposeL V L).getD j []).getD k 0))]
        refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) this
        rw [getD_transposeL V L j k j.2, hcs, List.getD_eq_getElem _ _ (by simp),
          List.getElem_ofFn, RingHom.id_apply, mul_comm]
      · refine Finset.sum_eq_zero fun j hj ↦ ?_
        rw [getD_transposeL V L j k (Finset.mem_range.mp hj),
          List.getD_eq_default V [] (by omega)]
        simp
    obtain ⟨β, -, hβ⟩ := CPoly.nullBasis_complete (RingHom.id ℚ) (transposeL V L) cs hcl h0
    -- the coordinates of `v`
    have hvj : ∀ j : Fin L, v j = ∑ b ∈ Finset.range (CPoly.nullBasis (transposeL V L)).length,
        β.getD b 0 * ((CPoly.nullBasis (transposeL V L)).getD b []).getD j 0 := by
      intro j
      have := congrArg (fun P : ℚ[X] ↦ P.coeff j) hβ
      rw [Tower.NestP.NestTower.coeff_lcombS, Tower.NestP.NestTower.coeff_lcombS,
        Tower.NestP.zipWith_sum_getD (fun (b : ℚ) (w : CPoly ℚ) ↦ b * (RingHom.id ℚ) (w.getD j 0))
          0 [] (fun _ ↦ by simp),
        Tower.NestP.zipWith_sum_getD (fun (b : ℚ) (w : CPoly ℚ) ↦ b * (RingHom.id ℚ) (w.getD j 0))
          0 [] (fun _ ↦ by simp)] at this
      simp only [RingHom.id_apply] at this
      rw [← this]
      have hlen : ((CPoly.nsItems (transposeL V L)).map Prod.snd).length = L := by
        simp [CPoly.nsItems, transposeL]
      rw [hlen, Finset.sum_eq_single (j : ℕ)]
      · rw [show ((CPoly.nsItems (transposeL V L)).map Prod.snd).getD j [] = CPoly.unitL j by
          simp [CPoly.nsItems, List.getD_eq_getElem?_getD, transposeL, j.2],
          getD_unitL, if_pos rfl, mul_one, hcs, List.getD_eq_getElem _ _ (by simp),
          List.getElem_ofFn]
      · intro b hb hbj
        rw [show ((CPoly.nsItems (transposeL V L)).map Prod.snd).getD b [] = CPoly.unitL b by
          simp [CPoly.nsItems, List.getD_eq_getElem?_getD, transposeL, Finset.mem_range.mp hb],
          getD_unitL, if_neg hbj, mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr j.2) h
    rw [Finset.sum_congr rfl fun j _ ↦ by rw [hvj j], ]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b hb ↦ ?_
    have ho := horth _ (List.getElem_mem (Finset.mem_range.mp hb))
    rw [← List.getD_eq_getElem _ [] (Finset.mem_range.mp hb)] at ho
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ ((CPoly.nullBasis (transposeL V L)).getD b []).getD j 0 *
      x j)] at ho
    calc ∑ j : Fin L, x j * (β.getD b 0 * ((CPoly.nullBasis (transposeL V L)).getD b []).getD j 0)
        = β.getD b 0 * ∑ j : Fin L, ((CPoly.nullBasis (transposeL V L)).getD b []).getD j 0 * x j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = 0 := by rw [ho, mul_zero]
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨fun k ↦ if h : k < V.length then μ ⟨k, h⟩ else 0, fun j hj ↦ ?_⟩
  have := congrArg (fun f : (Fin L → ℚ) →ₗ[ℚ] ℚ ↦ f (Pi.single ⟨j, hj⟩ 1)) hμ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hφv, hgv] at this
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  rw [← this, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [dif_pos k.2]
