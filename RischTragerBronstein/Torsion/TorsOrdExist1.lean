import RischTragerBronstein.Torsion.TorsResExist5
import RischTragerBronstein.Torsion.Gcd

/-!
# Torsion data from principal divisors (1): changing the level of a branch

A root `r'` of `F(b + T^{N'}, Y)` and a complete branch system `l` at level `N` above the same point:
some `r ∈ l` has `lsub N (expansion along r') = lsub N' (expansion along r)` (`exists_lift_fin`); the
same above infinity (`exists_lift_inf`). Hence the relation `ord w = m Λ(res f dX)` transfers from
`l` to every root at every level (`good_transfer_fin`, `good_transfer_inf`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Lift

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma embG_lsub_inf (s : ℕ) (hs : 0 < s) (e : ℕ) (he : 0 < e)
    (ρ : LaurentSeries K) (hρ : (S.F.map (infSub e)).eval ρ = 0)
    (hρ' : (S.F.map (infSub (s * e))).eval (lsub s hs ρ) = 0) (f : C⟮S.x⟯⟮S.y⟯) :
    S.embG (infSub (s * e)) (infSub_injective (s * e) (Nat.mul_pos hs he)) (lsub s hs ρ) hρ' f =
      lsub s hs (S.embG (infSub e) (infSub_injective e he) ρ hρ f) := by
  have hc : (lsub s hs).comp (infSub (C := C) (K := K) e) = infSub (s * e) := by
    rw [lsub_comp_infSub, mul_comm]
  have hinj : Function.Injective ((lsub s hs).comp (infSub (C := C) (K := K) e)) := by
    rw [hc]; exact infSub_injective _ (Nat.mul_pos hs he)
  have h := S.embG_comp (lsub s hs) (infSub e) (infSub_injective e he) hinj ρ hρ
    (by rw [hc]; exact hρ')
  have := congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) h
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) (S.embG_congr' hc.symm _ _ rfl _ _)

/-- **Lifting a root to a complete system (finite points).** -/
lemma exists_lift_fin (b : K) (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r' : LaurentSeries K) (hr' : (S.F.map (branchSub N' b)).eval r' = 0) :
    ∃ r, ∃ hr : r ∈ l, ∀ u : C⟮S.x⟯⟮S.y⟯,
      lsub N hN (S.embG (branchSub N' b) (branchSub_injective N' hN' b) r' hr' u) =
      lsub N' hN' (S.embG (branchSub N b) (branchSub_injective N hN b) r (S.root_of_mem hl hr) u) := by
  have hc1 : (lsub N hN).comp (branchSub (C := C) N' b) = branchSub (N * N') b := by
    rw [lsub_comp_branchSub, mul_comm]
  have hc2 : (lsub N' hN').comp (branchSub (C := C) N b) = branchSub (N * N') b := by
    rw [lsub_comp_branchSub]
  have hroot : (S.F.map (branchSub (N * N') b)).eval (lsub N hN r') = 0 := by
    rw [← hc1, ← Polynomial.map_map, eval_map, eval₂_at_apply, hr', map_zero]
  have hsplit : S.F.map (branchSub (N * N') b) =
      ((l.map (lsub N' hN')).map fun r ↦ X - Polynomial.C r).prod := by
    rw [← hc2, ← Polynomial.map_map, hl, Polynomial.map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp
  rw [hsplit, eval_list_prod, List.prod_eq_zero_iff, List.map_map] at hroot
  obtain ⟨s, hs, hs0⟩ := List.mem_map.mp hroot
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hs0
  refine ⟨r, hr, fun u ↦ ?_⟩
  have e1 := S.embG_lsub_fin N hN N' hN' b r' hr' (by
      rw [hs0, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply, S.root_of_mem hl hr, map_zero]) u
  have e2 := S.embG_lsub_fin N' hN' N hN b r (S.root_of_mem hl hr) (by
    rw [mul_comm N' N, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply,
      S.root_of_mem hl hr, map_zero]) u
  have e3 : S.embG (branchSub (N * N') b) (branchSub_injective (N * N') (Nat.mul_pos hN hN') b)
      (lsub N hN r') (by rw [hs0, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply,
        S.root_of_mem hl hr, map_zero]) u =
      S.embG (branchSub (N' * N) b) (branchSub_injective (N' * N) (Nat.mul_pos hN' hN) b)
        (lsub N' hN' r) (by rw [mul_comm N' N, ← hc2, ← Polynomial.map_map, eval_map,
          eval₂_at_apply, S.root_of_mem hl hr, map_zero]) u :=
    congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ u)
      (S.embG_congr' (by rw [mul_comm]) _ _ hs0 _ _)
  exact e1.symm.trans (e3.trans e2)

/-- **Lifting a root to a complete system (infinity).** -/
lemma exists_lift_inf (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r' : LaurentSeries K) (hr' : (S.F.map (infSub N')).eval r' = 0) :
    ∃ r, ∃ hr : r ∈ l, ∀ u : C⟮S.x⟯⟮S.y⟯,
      lsub N hN (S.embG (infSub N') (infSub_injective N' hN') r' hr' u) =
      lsub N' hN' (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) u) := by
  have hc1 : (lsub N hN).comp (infSub (C := C) (K := K) N') = infSub (N * N') := by
    rw [lsub_comp_infSub, mul_comm]
  have hc2 : (lsub N' hN').comp (infSub (C := C) (K := K) N) = infSub (N * N') := by
    rw [lsub_comp_infSub]
  have hroot : (S.F.map (infSub (N * N'))).eval (lsub N hN r') = 0 := by
    rw [← hc1, ← Polynomial.map_map, eval_map, eval₂_at_apply, hr', map_zero]
  have hsplit : S.F.map (infSub (N * N')) =
      ((l.map (lsub N' hN')).map fun r ↦ X - Polynomial.C r).prod := by
    rw [← hc2, ← Polynomial.map_map, hl, Polynomial.map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp
  rw [hsplit, eval_list_prod, List.prod_eq_zero_iff, List.map_map] at hroot
  obtain ⟨s, hs, hs0⟩ := List.mem_map.mp hroot
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hs0
  refine ⟨r, hr, fun u ↦ ?_⟩
  have e1 := S.embG_lsub_inf N hN N' hN' r' hr' (by
      rw [hs0, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply, S.root_of_mem hl hr, map_zero]) u
  have e2 := S.embG_lsub_inf N' hN' N hN r (S.root_of_mem hl hr) (by
    rw [mul_comm N' N, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply,
      S.root_of_mem hl hr, map_zero]) u
  have e3 : S.embG (infSub (N * N')) (infSub_injective (N * N') (Nat.mul_pos hN hN'))
      (lsub N hN r') (by rw [hs0, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply,
        S.root_of_mem hl hr, map_zero]) u =
      S.embG (infSub (N' * N)) (infSub_injective (N' * N) (Nat.mul_pos hN' hN))
        (lsub N' hN' r) (by rw [mul_comm N' N, ← hc2, ← Polynomial.map_map, eval_map,
          eval₂_at_apply, S.root_of_mem hl hr, map_zero]) u :=
    congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ u)
      (S.embG_congr' (by rw [mul_comm]) _ _ hs0 _ _)
  exact e1.symm.trans (e3.trans e2)

section Good

variable [CharZero K]

/-- The torsion relation along a finite root. -/
def GoodFin (f w : C⟮S.x⟯⟮S.y⟯) (m : ℕ) (Λ : K →ₗ[ℚ] ℚ) (N : ℕ) (hN : 0 < N) (b : K)
    (r : LaurentSeries K) (hr : (S.F.map (branchSub N b)).eval r = 0) : Prop :=
  ((S.embG (branchSub N b) (branchSub_injective N hN b) r hr w).order : ℚ) =
    m * Λ (LaurentSeries.res (S.embG (branchSub N b) (branchSub_injective N hN b) r hr f *
      LaurentSeries.derivation (HahnSeries.C b + single (N : ℤ) (1 : K))))

/-- The torsion relation along a root above infinity. -/
def GoodInf (f w : C⟮S.x⟯⟮S.y⟯) (m : ℕ) (Λ : K →ₗ[ℚ] ℚ) (N : ℕ) (hN : 0 < N)
    (r : LaurentSeries K) (hr : (S.F.map (infSub N)).eval r = 0) : Prop :=
  ((S.embG (infSub N) (infSub_injective N hN) r hr w).order : ℚ) =
    m * Λ (LaurentSeries.res (S.embG (infSub N) (infSub_injective N hN) r hr f *
      LaurentSeries.derivation (single (-(N : ℤ)) (1 : K))))

lemma good_of_lsub (f w : C⟮S.x⟯⟮S.y⟯) (m : ℕ) (Λ : K →ₗ[ℚ] ℚ) (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (A A' : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) (X X' : LaurentSeries K)
    (hrel : ∀ u, lsub N hN (A' u) = lsub N' hN' (A u)) (hX : lsub N hN X' = lsub N' hN' X)
    (hgood : ((A w).order : ℚ) = m * Λ (LaurentSeries.res (A f * LaurentSeries.derivation X))) :
    ((A' w).order : ℚ) = m * Λ (LaurentSeries.res (A' f * LaurentSeries.derivation X')) := by
  have ho : (N : ℤ) * (A' w).order = N' * (A w).order := by
    rw [← order_lsub' N hN, ← order_lsub' N' hN', hrel]
  have hr : (N : K) * LaurentSeries.res (A' f * LaurentSeries.derivation X') =
      (N' : K) * LaurentSeries.res (A f * LaurentSeries.derivation X) := by
    rw [← res_lsub (M := N) (hM := hN), ← res_lsub (M := N') (hM := hN'), hrel, hX]
  have hΛ : (N : ℚ) * Λ (LaurentSeries.res (A' f * LaurentSeries.derivation X')) =
      (N' : ℚ) * Λ (LaurentSeries.res (A f * LaurentSeries.derivation X)) := by
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← map_nsmul, nsmul_eq_mul, nsmul_eq_mul, hr]
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hoq : (N : ℚ) * (A' w).order = N' * (A w).order := by exact_mod_cast ho
  apply mul_left_cancel₀ hNq
  rw [hoq, hgood, show (N : ℚ) * (m * Λ (LaurentSeries.res (A' f * LaurentSeries.derivation X'))) =
    m * ((N : ℚ) * Λ (LaurentSeries.res (A' f * LaurentSeries.derivation X'))) by ring, hΛ]
  ring

/-- **Transfer of the torsion relation between levels (finite points).** -/
lemma good_transfer_fin (f w : C⟮S.x⟯⟮S.y⟯) (m : ℕ) (Λ : K →ₗ[ℚ] ℚ) (b : K) (N : ℕ) (hN : 0 < N)
    (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hgood : ∀ r (hr : r ∈ l), S.GoodFin f w m Λ N hN b r (S.root_of_mem hl hr))
    (N' : ℕ) (hN' : 0 < N') (r' : LaurentSeries K) (hr' : (S.F.map (branchSub N' b)).eval r' = 0) :
    S.GoodFin f w m Λ N' hN' b r' hr' := by
  obtain ⟨r, hr, hrel⟩ := S.exists_lift_fin b N N' hN hN' l hl r' hr'
  refine S.good_of_lsub f w m Λ N N' hN hN' _ _ _ _ hrel ?_ (hgood r hr)
  rw [map_add, map_add, lsub_C, lsub_C, lsub_single, lsub_single]
  congr 2; push_cast; ring

/-- **Transfer of the torsion relation between levels (infinity).** -/
lemma good_transfer_inf (f w : C⟮S.x⟯⟮S.y⟯) (m : ℕ) (Λ : K →ₗ[ℚ] ℚ) (N : ℕ) (hN : 0 < N)
    (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hgood : ∀ r (hr : r ∈ l), S.GoodInf f w m Λ N hN r (S.root_of_mem hl hr))
    (N' : ℕ) (hN' : 0 < N') (r' : LaurentSeries K) (hr' : (S.F.map (infSub N')).eval r' = 0) :
    S.GoodInf f w m Λ N' hN' r' hr' := by
  obtain ⟨r, hr, hrel⟩ := S.exists_lift_inf N N' hN hN' l hl r' hr'
  refine S.good_of_lsub f w m Λ N N' hN hN' _ _ _ _ hrel ?_ (hgood r hr)
  rw [lsub_single, lsub_single]
  congr 1; push_cast; ring

end Good

end CurveData

end Lift

end Curves
