import RischTragerBronstein.Torsion.IntegralHensel
import RischTragerBronstein.Curves.ProcLogSem2

/-!
# The degree theorem on a general curve

For `W ∈ C[x][Y]` with `W(x, y) ≠ 0` and its norm `N(W) = Res_Y(F, W)`:

* `branch_normW`: along a complete branch system, `N(W)(branch) = ∏ W(branch roots)`;
* `sum_order_fin`: above `a` (`x = a + Tᴺ`) the orders of `W(x, y)` add up to `N · mult_a N(W)`;
* `sum_order_inf`: above infinity (`x = T^{−N}`) they add up to `−N · deg N(W)`;
* `sum_rootMultiplicity`: `∑_a mult_a P = deg P` over an algebraically closed field.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Deg

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- The norm `Res_Y(F, W)` (with formal `Y`-degree `m`). -/
noncomputable def normW (W : C[X][X]) (m : ℕ) : C[X] := resultant S.F W S.F.natDegree m

lemma length_of_split {g : C[X] →+* LaurentSeries K} {l : List (LaurentSeries K)}
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) : l.length = S.F.natDegree := by
  have := congrArg natDegree hl
  rw [S.monic.natDegree_map, (list_prod_X_sub_C l).2] at this
  exact this.symm

/-- **The norm along a branch system.** -/
lemma branch_normW (W : C[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m) (g : C[X] →+* LaurentSeries K)
    (l : List (LaurentSeries K)) (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) :
    g (S.normW W m) = (l.map fun r ↦ (W.map g).eval r).prod := by
  rw [normW, ← resultant_map_map, hl, ← S.length_of_split hl]
  exact resultant_list_prod l _ m (natDegree_map_le.trans hWm)

lemma embG_wE_eq (ψ₀ : C →+* C) (W : C[X][X]) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (r : LaurentSeries K) (hr : (S.F.map g).eval r = 0) :
    S.embG g hg r hr ⟨S.evXY W, S.evXY_mem W⟩ = (W.map g).eval r := by
  have := S.eval_W_branch g hg r hr ⟨S.evXY W, S.evXY_mem W⟩ W 1 (by rw [map_one, mul_one])
  rw [this, map_one, mul_one]

/-- The norm does not vanish when `W(x, y) ≠ 0` (given one branch system). -/
lemma normW_ne_zero (W : C[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m) (hW : S.evXY W ≠ 0)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (l : List (LaurentSeries K))
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) : S.normW W m ≠ 0 := by
  intro h0
  have h1 := S.branch_normW W m hWm g l hl
  rw [h0, map_zero] at h1
  obtain ⟨r, hr, hr0⟩ : ∃ r ∈ l, (W.map g).eval r = 0 := by
    have := h1.symm
    rw [List.prod_eq_zero_iff] at this
    obtain ⟨z, hz, hz0⟩ := List.mem_map.mp this
    exact ⟨z, hz, hz0⟩
  have e := S.embG_wE_eq (RingHom.id C) W g hg r (S.root_of_mem hl hr)
  rw [hr0] at e
  apply hW
  have := congrArg Subtype.val ((map_eq_zero_iff _ (S.embG g hg r (S.root_of_mem hl hr)).injective).mp e)
  exact this

lemma order_list_prod (l : List (LaurentSeries K)) (h : ∀ z ∈ l, z ≠ 0) :
    l.prod.order = (l.map HahnSeries.order).sum := by
  induction l with
  | nil => simp
  | cons z l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    have hz := h z List.mem_cons_self
    have hl : l.prod ≠ 0 := List.prod_ne_zero fun h0 ↦ h 0 (List.mem_cons_of_mem _ h0) rfl
    rw [HahnSeries.order_mul hz hl, ih fun w hw ↦ h w (List.mem_cons_of_mem _ hw)]

lemma branch_values_ne_zero (W : C[X][X]) (hW : S.evXY W ≠ 0) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (l : List (LaurentSeries K))
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) :
    ∀ z ∈ l.map (fun r ↦ (W.map g).eval r), z ≠ 0 := by
  intro z hz
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
  rw [← S.embG_wE_eq (RingHom.id C) W g hg r (S.root_of_mem hl hr)]
  exact (map_ne_zero_iff _ (S.embG g hg r _).injective).mpr fun h ↦ hW (congrArg Subtype.val h)

/-- **Orders above a finite point.** -/
lemma sum_order_fin (W : C[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m) (hW : S.evXY W ≠ 0)
    (N : ℕ) (hN : 0 < N) (a : K) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (l.map fun r ↦ ((W.map (branchSub N a)).eval r).order).sum =
      N * (((S.normW W m).map (algebraMap C K)).rootMultiplicity a : ℤ) := by
  have hne := S.normW_ne_zero W m hWm hW _ (branchSub_injective N hN a) l hl
  have h := congrArg HahnSeries.order (S.branch_normW W m hWm _ l hl)
  rw [order_branchSub N hN a _ hne, order_list_prod _ (S.branch_values_ne_zero W hW _
    (branchSub_injective N hN a) l hl), List.map_map] at h
  exact h.symm

/-- **Orders above infinity.** -/
lemma sum_order_inf (W : C[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m) (hW : S.evXY W ≠ 0)
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (l.map fun r ↦ ((W.map (infSub N)).eval r).order).sum =
      -(N * ((S.normW W m).natDegree : ℤ)) := by
  have hne := S.normW_ne_zero W m hWm hW _ (infSub_injective N hN) l hl
  have h := congrArg HahnSeries.order (S.branch_normW W m hWm _ l hl)
  rw [order_infSub N hN _ hne, order_list_prod _ (S.branch_values_ne_zero W hW _
    (infSub_injective N hN) l hl), List.map_map] at h
  rw [show (l.map fun r ↦ ((W.map (infSub N)).eval r).order) =
    l.map (HahnSeries.order ∘ fun r ↦ (W.map (infSub N)).eval r) from rfl, ← h]

end CurveData

end Deg

end Curves
