import RischTragerBronstein.Curves.ResIntegral
import RischTragerBronstein.Curves.ProcLogSem2
import RischTragerBronstein.Torsion.PrincipalG

/-!
# Functions with poles above a finite set

**`exists_repr_poles`**: if `w ∈ C(x, y)` has no pole along any branch above any finite point
outside a finite set `T ⊆ C`, then `w = W(x, y) / (Res(F, F_Y) · Q₀(x))` with `Q₀` vanishing only
on `T`. The part of the denominator of a representation `W₁/Q₁` (`exists_repr`) above `T` makes
`w Q₀` regular at all finite places, hence integral (`integral_of_regular`), and
`res_mul_integral` clears the remaining denominator.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential

section Poles

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]
  [CharZero C] [CharZero K]

namespace CurveData

variable (S : CurveData C L)

lemma lowerBd_zero_of_order {z : LaurentSeries K} (h : 0 ≤ z.order) : LowerBd z 0 :=
  fun k hk ↦ HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk h)

/-- **A function with poles only above `T`.** -/
theorem exists_repr_poles (w : C⟮S.x⟯⟮S.y⟯) (T : Finset C)
    (hreg : ∀ (a : K), (∀ t ∈ T, a ≠ algebraMap C K t) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries K)) (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      0 ≤ (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order) :
    ∃ (W : C[X][X]) (Q₀ : C[X]), Q₀ ≠ 0 ∧ (∀ c, Q₀.IsRoot c → c ∈ T) ∧
      (∃ e : C → ℕ, Q₀ = ∏ t ∈ T, (X - Polynomial.C t) ^ e t) ∧
      (w : L) * aeval S.x (resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1) * Q₀) =
        S.evXY W := by
  classical
  obtain ⟨W₁, Q₁, hQ₁, h₁⟩ := S.exists_repr w
  set Q₀ : C[X] := ∏ t : T, (X - Polynomial.C (t : C)) ^ Q₁.rootMultiplicity (t : C) with hQ₀
  have hQ₀0 : Q₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hQ₀r : ∀ c, Q₀.IsRoot c → c ∈ T := by
    intro c hc
    by_contra hcT
    have : Q₀.rootMultiplicity c = 0 := by
      rw [hQ₀, rootMultiplicity_prodPow]
      refine Finset.sum_eq_zero fun t _ ↦ ?_
      rw [if_neg]; intro h; exact hcT (h ▸ t.2)
    exact (rootMultiplicity_pos hQ₀0).mpr hc |>.ne' this
  set w₀ : C⟮S.x⟯⟮S.y⟯ := w * ⟨aeval S.x Q₀, S.aeval_mem Q₀⟩ with hw₀
  have hreg₀ : S.RegularFinite K w₀ := by
    intro a N hN l hl r hr
    set g := branchSub (C := C) (K := K) N a
    have hg := branchSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN) a
    have hemb : S.embG g hg r (S.root_of_mem hl hr) w₀ =
        S.embG g hg r (S.root_of_mem hl hr) w * g Q₀ := by
      rw [hw₀, map_mul, S.embG_polyX]
    rw [hemb]
    by_cases ha : ∀ t ∈ T, a ≠ algebraMap C K t
    · have h1 := hreg a ha N hN l hl r hr
      refine order_nonneg_of_lowerBd _ ?_
      have := (lowerBd_zero_of_order h1).mul (lowerBd_branchSub_nonneg N a Q₀)
      simpa using this
    · push Not at ha
      obtain ⟨t, htT, rfl⟩ := ha
      -- `W₁(r) = emb(w) · g(Q₁)`
      have hW₁ := S.eval_W_branch g hg r (S.root_of_mem hl hr) w W₁ Q₁ h₁
      have hWlb : 0 ≤ ((W₁.map g).eval r).order := order_nonneg_of_lowerBd _
        (CurveData.lowerBd_eval _ r 0 le_rfl (S.fin_root_lowerBd N _ r (S.root_of_mem hl hr)) 0
          fun i ↦ by rw [zero_mul, sub_zero, coeff_map]; exact CurveData.lowerBd_branchSub_nonneg N _ _)
      set e := S.embG g hg r (S.root_of_mem hl hr) w
      by_cases he : e = 0
      · rw [he, zero_mul, HahnSeries.order_zero]
      have hQ₁g : g Q₁ ≠ 0 := (map_ne_zero_iff _ hg).mpr hQ₁
      have hQ₀g : g Q₀ ≠ 0 := (map_ne_zero_iff _ hg).mpr hQ₀0
      -- equal multiplicities of `Q₀` and `Q₁` at `t`
      have hmult : (Q₀.map (algebraMap C K)).rootMultiplicity (algebraMap C K t) =
          (Q₁.map (algebraMap C K)).rootMultiplicity (algebraMap C K t) := by
        rw [← eq_rootMultiplicity_map (algebraMap C K).injective,
          ← eq_rootMultiplicity_map (algebraMap C K).injective, hQ₀]
        exact rootMultiplicity_prodPow_pt (fun t : T ↦ (t : C)) Subtype.val_injective _ ⟨t, htT⟩
      have hWr0 : (W₁.map g).eval r ≠ 0 := by rw [hW₁]; exact mul_ne_zero he hQ₁g
      have ho1 : ((W₁.map g).eval r).order = e.order + (g Q₁).order := by
        rw [hW₁, HahnSeries.order_mul he hQ₁g]
      have hoQ₁ : (g Q₁).order = (N * (Q₁.map (algebraMap C K)).rootMultiplicity
          (algebraMap C K t) : ℕ) := order_branchSub N (Nat.pos_of_ne_zero hN) _ Q₁ hQ₁
      have hoQ₀ : (g Q₀).order = (N * (Q₀.map (algebraMap C K)).rootMultiplicity
          (algebraMap C K t) : ℕ) := order_branchSub N (Nat.pos_of_ne_zero hN) _ Q₀ hQ₀0
      rw [HahnSeries.order_mul he hQ₀g, hoQ₀, hmult, ← hoQ₁]
      linarith
  obtain ⟨M, hM, hMz⟩ := S.integral_of_regular (K := K) w₀ hreg₀
  obtain ⟨W, hW⟩ := S.res_mul_integral w₀ M hM hMz
  refine ⟨W, Q₀, hQ₀0, hQ₀r, ⟨fun t ↦ Q₁.rootMultiplicity t,
    Finset.prod_coe_sort T (fun t ↦ (X - Polynomial.C t) ^ Q₁.rootMultiplicity t)⟩, ?_⟩
  rw [← hW, hw₀, IntermediateField.coe_mul, map_mul]
  ring

end CurveData

end Poles

end Curves
