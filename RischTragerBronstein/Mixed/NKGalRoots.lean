import RischTragerBronstein.Mixed.NKInitForm
import RischTragerBronstein.Mixed.NKInf2

/-!
# Rational roots at infinity (Galois descent on Laurent series)

For `K` Galois over `C` (e.g. its algebraic closure in characteristic `0`), the automorphisms of
`K/C` act coefficientwise on `K⸨T⸩` (`lmap`), fix `infSub N` (`lmap_infSub`) and so permute the
roots above infinity (`lmap_root_mem`). A root whose order and leading coefficient are not shared
by another root, with leading coefficient in `C`, is fixed (`root_fixed`), hence has all its
coefficients in `C` (`coeff_mem_of_fixed`), and so do the expansions along it of all the functions
of the curve (`embG_coeff_mem`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma lmap_infSub (σ : K ≃ₐ[C] K) (N : ℕ) (P : C[X]) :
    lmap (σ : K →+* K) (infSub (K := K) N P) = infSub N P := by
  have h : (lmap (σ : K →+* K)).comp (infSub (C := C) (K := K) N) = infSub N := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · ext k
      simp only [RingHom.comp_apply, infSub, coe_eval₂RingHom, eval₂_C, lmap_coeff,
        HahnSeries.C_apply, HahnSeries.coeff_single]
      split_ifs <;> simp
    · ext k
      simp only [RingHom.comp_apply, lmap_coeff]
      rw [infSub, coe_eval₂RingHom, eval₂_X, HahnSeries.coeff_single]
      split_ifs <;> simp
  exact congrArg (fun φ : C[X] →+* LaurentSeries K ↦ φ P) h

lemma lmap_order (σ : K ≃ₐ[C] K) (r : LaurentSeries K) :
    (lmap (σ : K →+* K) r).order = r.order := by
  by_cases hr : r = 0
  · subst hr; simp
  have hr' : lmap (σ : K →+* K) r ≠ 0 := fun h ↦ hr (by
    ext k; have := congrArg (fun z ↦ z.coeff k) h
    simpa using this)
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by
      rw [lmap_coeff]; exact (_root_.map_ne_zero _).mpr (fun h ↦ hr (HahnSeries.coeff_order_eq_zero.mp h)))
  · exact HahnSeries.order_le_of_coeff_ne_zero (fun h ↦
      hr' (HahnSeries.coeff_order_eq_zero.mp (by rw [lmap_coeff, h, map_zero])))

/-- **The automorphisms permute the roots above infinity.** -/
lemma lmap_root_mem (σ : K ≃ₐ[C] K) (F : C[X][X]) (N : ℕ) (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) {r : LaurentSeries K}
    (hr : r ∈ l) : lmap (σ : K →+* K) r ∈ l := by
  have h0 : (F.map (infSub (K := K) N)).eval r = 0 := by
    rw [hl, eval_list_prod]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp⟩)
  have h1 : (F.map (infSub (K := K) N)).eval (lmap (σ : K →+* K) r) = 0 := by
    have e : F.map (infSub (K := K) N) = (F.map (infSub (K := K) N)).map (lmap (σ : K →+* K)) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext fun P ↦ (lmap_infSub σ N P).symm
    rw [e, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]
  rw [hl, eval_list_prod] at h1
  obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h1)
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hv
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hv0
  rw [hv0]; exact hr'

/-- **A root with a unique order and leading coefficient in `C` is fixed.** -/
lemma root_fixed (σ : K ≃ₐ[C] K) (F : C[X][X]) (N : ℕ) (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) {r : LaurentSeries K}
    (hr : r ∈ l) (huniq : ∀ r' ∈ l, r'.order = r.order → r'.coeff r'.order = r.coeff r.order →
      r' = r) (hc : r.coeff r.order ∈ Set.range (algebraMap C K)) :
    lmap (σ : K →+* K) r = r := by
  refine huniq _ (lmap_root_mem σ F N l hl hr) (lmap_order σ r) ?_
  rw [lmap_order, lmap_coeff]
  obtain ⟨c, hc⟩ := hc
  rw [← hc]
  exact σ.commutes c

/-- **Fixed Laurent series have coefficients in `C`.** -/
lemma coeff_mem_of_fixed [IsGalois C K] (r : LaurentSeries K)
    (hfix : ∀ σ : K ≃ₐ[C] K, lmap (σ : K →+* K) r = r) (k : ℤ) :
    r.coeff k ∈ Set.range (algebraMap C K) := by
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  have := congrArg (fun z ↦ z.coeff k) (hfix σ)
  simpa using this

namespace CurveData

variable {L : Type*} [Field L] [Algebra C L] (S : CurveData C L)

/-- **Expansions along a fixed root have coefficients in `C`.** -/
theorem embG_coeff_mem [IsGalois C K] (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K)
    (hY : (S.F.map (infSub N)).eval Y = 0)
    (hfix : ∀ σ : K ≃ₐ[C] K, lmap (σ : K →+* K) Y = Y) (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ) :
    (S.embG (infSub N) (infSub_injective N hN) Y hY z).coeff k ∈ Set.range (algebraMap C K) := by
  refine coeff_mem_of_fixed _ (fun σ ↦ ?_) k
  have hφ : (lmap (σ : K →+* K)).comp (S.embG (infSub N) (infSub_injective N hN) Y hY) =
      S.embG (infSub N) (infSub_injective N hN) Y hY := by
    refine S.embG_unique _ _ Y hY _ (fun Q ↦ ?_) ?_
    · rw [RingHom.comp_apply]
      letI := algebraAdjoinSimple (F := C) S.x
      rw [show S.polyF Q = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ Q) from rfl,
        S.embG_algebraMap, S.embXG_algebraMap, lmap_infSub]
    · rw [RingHom.comp_apply, S.embG_gen, hfix σ]
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ z) hφ

end CurveData

end Curves
