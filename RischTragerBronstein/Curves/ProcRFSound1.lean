import RischTragerBronstein.Curves.ProcRFSem3

/-!
# Transferring local facts from the certified branch system to all branch systems

* `transfer_lb`, `transfer_diff`: "`φ(f) dX̂/dT − (φ v)′` has at most a simple pole" is invariant
  under reparametrization;
* `fin_rel_list`, `inf_rel_list`: every branch of every system (given as a list) is a
  reparametrization of a branch of a fixed system.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Generic

variable {K : Type*} [Field K] [CharZero K]

/-- A simple-pole bound transfers along a scaled `lsub` identity. -/
lemma transfer_lb (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (Z Z' : LaurentSeries K)
    (e' : HahnSeries.C (M : K) * (single ((M : ℤ) - 1) (1 : K) * lsub M hM Z') =
      HahnSeries.C (M' : K) * (single ((M' : ℤ) - 1) (1 : K) * lsub M' hM' Z))
    (h : LowerBd Z (-1)) : LowerBd Z' (-1) := by
  have hR : LowerBd (HahnSeries.C (M' : K) * (single ((M' : ℤ) - 1) (1 : K) *
      lsub M' hM' Z)) (-1) := by
    have h1 := (lowerBd_lsub_iff M' hM' _ (-1)).mpr h
    have := (lowerBd_C (M' : K)).mul ((lowerBd_single ((M' : ℤ) - 1) (1 : K)).mul h1)
    convert this using 1; ring
  rw [← e'] at hR
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM.ne'
  have key : HahnSeries.C (M : K)⁻¹ * single (1 - (M : ℤ)) (1 : K) *
      (HahnSeries.C (M : K) * single ((M : ℤ) - 1) (1 : K)) = 1 := by
    rw [show HahnSeries.C (M : K)⁻¹ * single (1 - (M : ℤ)) (1 : K) *
        (HahnSeries.C (M : K) * single ((M : ℤ) - 1) (1 : K)) =
        (HahnSeries.C (M : K)⁻¹ * HahnSeries.C (M : K)) *
          (single (1 - (M : ℤ)) (1 : K) * single ((M : ℤ) - 1) 1) by ring,
      ← map_mul, inv_mul_cancel₀ hMK, map_one, one_mul, single_mul_single, mul_one,
      show 1 - (M : ℤ) + ((M : ℤ) - 1) = 0 by ring]
    rfl
  have h2 : lsub M hM Z' =
      HahnSeries.C (M : K)⁻¹ * (single (1 - (M : ℤ)) (1 : K) * (HahnSeries.C (M : K) *
        (single ((M : ℤ) - 1) (1 : K) * lsub M hM Z'))) := by
    calc lsub M hM Z'
        = (HahnSeries.C (M : K)⁻¹ * single (1 - (M : ℤ)) (1 : K) *
            (HahnSeries.C (M : K) * single ((M : ℤ) - 1) (1 : K))) * lsub M hM Z' := by
          rw [key, one_mul]
      _ = _ := by ring
  have h3 : LowerBd (lsub M hM Z') (M * (-1)) := by
    rw [h2]
    have := (lowerBd_C (M : K)⁻¹).mul ((lowerBd_single (1 - (M : ℤ)) (1 : K)).mul hR)
    convert this using 1; ring
  exact (lowerBd_lsub_iff M hM _ (-1)).mp h3

/-- **`φ(f) dX̂ − d(φ v)` with at most simple poles transfers.** -/
lemma transfer_diff (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (u u' w w' Xh Xh' : LaurentSeries K)
    (hu : lsub M hM u' = lsub M' hM' u) (hw : lsub M hM w' = lsub M' hM' w)
    (hX : lsub M hM Xh' = lsub M' hM' Xh)
    (h : LowerBd (u * LaurentSeries.derivation Xh - LaurentSeries.derivation w) (-1)) :
    LowerBd (u' * LaurentSeries.derivation Xh' - LaurentSeries.derivation w') (-1) := by
  refine transfer_lb M M' hM hM' _ _ ?_ h
  have e := lsub_diff M M' hM hM' u u' Xh Xh' hu hX
  rw [derivation_lsub, derivation_lsub] at e
  have ew := congrArg LaurentSeries.derivation hw
  rw [derivation_lsub, derivation_lsub] at ew
  rw [map_sub, map_sub, map_mul, map_mul]
  linear_combination e - ew

/-- **Vanishing residues transfer.** -/
lemma transfer_res0 (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (u u' Xh Xh' : LaurentSeries K)
    (hu : lsub M hM u' = lsub M' hM' u) (hX : lsub M hM Xh' = lsub M' hM' Xh)
    (h : LaurentSeries.res (u * LaurentSeries.derivation Xh) = 0) :
    LaurentSeries.res (u' * LaurentSeries.derivation Xh') = 0 := by
  have e := transfer_res M M' hM hM' u u' Xh Xh' hu hX
  rw [h, mul_zero] at e
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM.ne'
  exact (mul_eq_zero.mp e).resolve_left hMK

end Generic

section Rel

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [CharZero K]

namespace CurveData

variable (S : CurveData C L)

/-- A list splitting as a `Fin`-indexed one containing a given root. -/
lemma split_fin_mem (g : C[X] →+* LaurentSeries K) (l : List (LaurentSeries K))
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) (x : LaurentSeries K)
    (hx : x ∈ l) :
    ∃ (r : Fin S.F.natDegree → LaurentSeries K) (k : Fin S.F.natDegree),
      S.F.map g = ∏ k, (X - Polynomial.C (r k)) ∧ r k = x := by
  have hlen : l.length = S.F.natDegree := by
    have := congrArg natDegree hl
    rw [S.monic.natDegree_map, (list_prod_X_sub_C l).2] at this
    exact this.symm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  refine ⟨fun k ↦ l[Fin.cast hlen.symm k], ⟨i, hlen ▸ hi⟩, ?_, rfl⟩
  rw [hl, ← Fin.prod_univ_fun_getElem]
  exact (Fintype.prod_equiv (finCongr hlen) _ _ (fun k ↦ rfl))

/-- Every finite branch is a reparametrization of a branch of a fixed system. -/
lemma fin_rel_list (a : K) (N0 : ℕ) (hN0 : 0 < N0) (r0 : Fin S.F.natDegree → LaurentSeries K)
    (hs0 : S.F.map (branchSub N0 a) = ∏ k, (X - Polynomial.C (r0 k)))
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    ∃ k, ∀ z, lsub N0 hN0 (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a)
        x (S.root_of_mem hl hx) z) =
      lsub N (Nat.pos_of_ne_zero hN) (S.embG (branchSub N0 a) (branchSub_injective N0 hN0 a) (r0 k)
        (S.root_of_split _ r0 hs0 k) z) := by
  obtain ⟨r, k0, hs, hk0⟩ := S.split_fin_mem _ l hl x hx
  obtain ⟨k, hk⟩ := S.fin_rel a N0 N hN0 (Nat.pos_of_ne_zero hN) r0 r hs0 hs k0
  refine ⟨k, fun z ↦ ?_⟩
  rw [← hk z]
  congr 2
  exact S.embG_congr rfl _ _ hk0.symm _ _

/-- Every branch above infinity is a reparametrization of a branch of a fixed system. -/
lemma inf_rel_list (N0 : ℕ) (hN0 : 0 < N0) (r0 : Fin S.F.natDegree → LaurentSeries K)
    (hs0 : S.F.map (infSub N0) = ∏ k, (X - Polynomial.C (r0 k)))
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    ∃ k, ∀ z, lsub N0 hN0 (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN))
        x (S.root_of_mem hl hx) z) =
      lsub N (Nat.pos_of_ne_zero hN) (S.embG (infSub N0) (infSub_injective N0 hN0) (r0 k)
        (S.root_of_split _ r0 hs0 k) z) := by
  obtain ⟨r, k0, hs, hk0⟩ := S.split_fin_mem _ l hl x hx
  obtain ⟨k, hk⟩ := S.inf_rel N0 N hN0 (Nat.pos_of_ne_zero hN) r0 r hs0 hs k0
  refine ⟨k, fun z ↦ ?_⟩
  rw [← hk z]
  congr 2
  exact S.embG_congr rfl _ _ hk0.symm _ _

end CurveData

end Rel

end Curves
