import RischTragerBronstein.Curves.ProcLogSem1

/-!
# Norms on the curve

* `evXY_ne_zero_of_resultant`: `Res_Y(F, W) ≠ 0 ⇒ W(x, y) ≠ 0`;
* `order_wE_eq_zero`: above a point where `Res_Y(F, W)` does not vanish, `W(x, y)` has order `0`
  along every branch of every system;
* `order_qE_eq_zero`: the same for `Q(x)` at a non-root.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Norm

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma evXY_C (q : C[X]) : S.evXY (Polynomial.C q) = aeval S.x q := by simp [evXY]

/-- **Nonvanishing from the norm.** -/
lemma evXY_ne_zero_of_resultant (Wp : C[X][X]) (m : ℕ) (hWm : Wp.natDegree ≤ m)
    (hR : resultant S.F Wp S.F.natDegree m ≠ 0) : S.evXY Wp ≠ 0 := by
  intro h0
  obtain ⟨p, q, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant S.F Wp le_rfl hWm
    (Or.inl S.natDegree_F_ne_zero)
  have := congrArg S.evXY e
  rw [S.evXY_add, S.evXY_mul, S.evXY_mul, S.evXY_F, h0, S.evXY_C] at this
  simp only [zero_mul, add_zero] at this
  exact S.htr ⟨_, hR, this.symm⟩

/-- **Order zero away from the norm's roots.** -/
lemma order_wE_eq_zero (Wp : C[X][X]) (m : ℕ) (hWm : Wp.natDegree ≤ m) (a : K) (N : ℕ)
    (hN : 0 < N) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hRa : ((resultant S.F Wp S.F.natDegree m).map (algebraMap C K)).eval a ≠ 0)
    (x : LaurentSeries K) (hx : x ∈ l) (z : C⟮S.x⟯⟮S.y⟯) (hz : (z : L) = S.evXY Wp) :
    (S.embG (branchSub N a) (branchSub_injective N hN a) x (S.root_of_mem hl hx) z).order = 0 := by
  classical
  set g := branchSub (C := C) (K := K) N a with hg
  set R := resultant S.F Wp S.F.natDegree m with hR
  have hR0 : R ≠ 0 := fun h ↦ hRa (by rw [h, Polynomial.map_zero, eval_zero])
  have hlen : l.length = S.F.natDegree := by
    have := congrArg natDegree hl
    rw [S.monic.natDegree_map, (list_prod_X_sub_C l).2] at this
    exact this.symm
  set h : LaurentSeries K → LaurentSeries K := fun r ↦ (Wp.map g).eval r with hh
  have hmap : g R = (l.map h).prod := by
    rw [hR, ← resultant_map_map, hl, ← hlen]
    exact resultant_list_prod l _ m (natDegree_map_le.trans hWm)
  have hφ : S.embG g (branchSub_injective N hN a) x (S.root_of_mem hl hx) z = h x := by
    rw [hh]
    have := S.eval_W_branch g (branchSub_injective N hN a) x (S.root_of_mem hl hx) z Wp 1
      (by rw [map_one, mul_one, hz])
    show _ = (Wp.map g).eval x
    rw [this, map_one, mul_one]
  have hlb : ∀ r ∈ l, LowerBd (h r) 0 := fun r hr ↦ by
    refine CurveData.lowerBd_eval _ r 0 le_rfl (S.fin_root_lowerBd N a r (S.root_of_mem hl hr)) 0
      fun i ↦ ?_
    rw [zero_mul, sub_zero, coeff_map]; exact CurveData.lowerBd_branchSub_nonneg N a _
  have hgR : (g R).order = 0 := by
    rw [hg, order_branchSub N hN a R hR0, rootMultiplicity_eq_zero hRa, mul_zero, Nat.cast_zero]
  have hgR0 : g R ≠ 0 := (map_ne_zero_iff _ (branchSub_injective N hN a)).mpr hR0
  have hsplit := List.prod_map_erase h hx
  rw [← hmap] at hsplit
  have hx0 : h x ≠ 0 := fun h0 ↦ hgR0 (by rw [← hsplit, h0, zero_mul])
  have hr0 : ((l.erase x).map h).prod ≠ 0 := fun h0 ↦ hgR0 (by rw [← hsplit, h0, mul_zero])
  have hord := congrArg HahnSeries.order hsplit
  rw [HahnSeries.order_mul hx0 hr0, hgR] at hord
  have h1 := order_nonneg_of_lowerBd _ (hlb x hx)
  have h2 := order_nonneg_of_lowerBd _ (by
    have := lowerBd_list_prod ((l.erase x).map h) 0 fun y hy ↦ by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
      exact hlb r (List.mem_of_mem_erase hr)
    rwa [mul_zero] at this)
  rw [hφ]
  omega

omit [Field L] [Algebra C L] in
lemma order_branchSub_eq_zero (Q : C[X]) (a : K) (N : ℕ) (hN : 0 < N)
    (hQa : (Q.map (algebraMap C K)).eval a ≠ 0) : (branchSub N a Q).order = 0 := by
  have hQ0 : Q ≠ 0 := fun h ↦ hQa (by rw [h, Polynomial.map_zero, eval_zero])
  rw [order_branchSub N hN a Q hQ0, rootMultiplicity_eq_zero hQa, mul_zero, Nat.cast_zero]

end CurveData

end Norm

end Curves
