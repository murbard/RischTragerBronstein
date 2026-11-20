import RischTragerBronstein.Torsion.RootCheckComplete
import RischTragerBronstein.Curves.Puiseux

/-!
# Existence of branch certificates at a point

**`exists_branchCert`**: let `G(x, Y)` be monic of degree `n` in `Y` over an algebraically closed
field `K` of characteristic zero, separable (`R = A G + B G_Y` with `R ≠ 0`), and `a ∈ K`. Then
there are `N > 0`, a precision and truncated series `ys` over `K` such that **every** coefficient
field `F → K` reaching `a` and the coefficients of `ys` carries a branch certificate
`⟨N, ys', prec⟩` passing `certCheck`.

The roots are those of `G(a + Tᴺ, Y)` in `K⟦T⟧` (Newton–Puiseux, `puiseux_split`); they are simple
(the Bézout identity), so `rootCheck_of_root` applies, and pairwise distinct, so they separate
below the precision.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Roots

variable {K : Type*} [Field K]

lemma ex_comp_psSubR (N : ℕ) (hN : N ≠ 0) (a : K) :
    (Puiseux.ex N).comp (psSubR 1 a) = psSubR N a := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · simp [psSubR, Puiseux.ex_C]
  · simp [psSubR, Puiseux.ex_apply hN, PowerSeries.expand_X, PowerSeries.expand_C]

lemma psSubR_injective (N : ℕ) (hN : N ≠ 0) (a : K) : Function.Injective (psSubR N a) := by
  rw [injective_iff_map_eq_zero]
  intro R hR
  simp only [psSubR, RingHom.coe_comp, Function.comp_apply, coe_compRingHom,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_eq_zero_iff] at hR
  by_contra h0
  have hq : (Polynomial.C a + X ^ N : K[X]).natDegree = N := by
    rw [natDegree_add_eq_right_of_natDegree_lt (by simp; omega), natDegree_X_pow]
  have := congrArg natDegree hR
  rw [natDegree_comp, hq, natDegree_zero, mul_eq_zero] at this
  rcases this with h | h
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp h
    rw [C_comp, C_eq_zero] at hR
    exact h0 (by rw [hR, C_0])
  · exact hN h

variable [IsAlgClosed K] [CharZero K]

/-- The roots of `G(a + Tᴺ, Y)` (Newton–Puiseux). -/
lemma exists_roots (G : K[X][X]) (hmon : G.Monic) (n : ℕ) (hdeg : G.natDegree = n) (a : K) :
    ∃ N, N ≠ 0 ∧ ∃ l : List (PowerSeries K), l.length = n ∧
      G.map (psSubR N a) = (l.map fun r ↦ X - Polynomial.C r).prod := by
  have hHm : (G.map (psSubR 1 a)).Monic := hmon.map _
  have hHd : (G.map (psSubR 1 a)).natDegree = n := by rw [hmon.natDegree_map, hdeg]
  obtain ⟨N, hN, l, hl, h⟩ := Puiseux.puiseux_split n _ hHm hHd
  refine ⟨N, hN, l, hl, ?_⟩
  rw [← h, Polynomial.map_map, ex_comp_psSubR N hN]

end Roots

section Exist

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

omit [IsAlgClosed K] [CharZero K] in
lemma eval_prod_of_mem (l : List (PowerSeries K)) (r : PowerSeries K) (hr : r ∈ l) :
    ((l.map fun r ↦ X - Polynomial.C r).prod).eval r = 0 := by
  rw [eval_list_prod]
  refine List.prod_eq_zero ?_
  refine List.mem_map.mpr ⟨X - Polynomial.C r, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
  simp

omit [IsAlgClosed K] [CharZero K] in
open Classical in
/-- The derivative at a root `r` is the product of the other factors at `r`. -/
lemma derivative_eval_prod (l : List (PowerSeries K)) (r : PowerSeries K) (hr : r ∈ l) :
    (derivative (l.map fun r ↦ X - Polynomial.C r).prod).eval r =
      ((l.erase r).map fun r ↦ X - Polynomial.C r).prod.eval r := by
  have hp : (l.map fun r ↦ X - Polynomial.C r).prod =
      (X - Polynomial.C r) * ((l.erase r).map fun r ↦ X - Polynomial.C r).prod := by
    rw [← List.prod_cons]
    exact ((List.perm_cons_erase hr).map _).prod_eq
  rw [hp, derivative_mul]
  simp

omit [IsAlgClosed K] [CharZero K] in
open Classical in
/-- Simple roots are distinct. -/
lemma nodup_of_derivative (l : List (PowerSeries K))
    (h : ∀ r ∈ l, (derivative (l.map fun r ↦ X - Polynomial.C r).prod).eval r ≠ 0) : l.Nodup := by
  classical
  rw [List.nodup_iff_count_le_one]
  intro r
  by_contra hc
  push Not at hc
  have hr : r ∈ l := List.count_pos_iff.mp (by omega)
  have hr' : r ∈ l.erase r := by
    rw [← List.count_pos_iff, List.count_erase_self]; omega
  exact h r hr (by rw [derivative_eval_prod l r hr]; exact eval_prod_of_mem _ r hr')

/-- **Existence of branch certificates at a point.** -/
theorem exists_branchCert (G : K[X][X]) (n : ℕ) (hmon : G.Monic) (hdeg : G.natDegree = n)
    (R : K[X]) (hR : R ≠ 0) (A B : K[X][X]) (hAB : Polynomial.C R = A * G + B * derivative G)
    (a : K) :
    ∃ N prec₀ : ℕ, 0 < N ∧ ∀ prec, prec₀ ≤ prec → ∃ ys : List (CPoly K), ys.length = n ∧
      ∀ {F : Type*} [Field F] [DecidableEq F] (ψ : F →+* K) (Fc : BPoly F) (a' : F)
        (ys' : List (CPoly F)), (toB Fc).map (mapRingHom ψ) = G → ψ a' = a →
        ys'.map (·.map ψ) = ys → certCheck Fc n a' ⟨N, ys', prec⟩ = true := by
  classical
  obtain ⟨N, hN, l, hl, hsplit⟩ := exists_roots G hmon n hdeg a
  set Gs := G.map (psSubR N a) with hGs
  have hroot : ∀ r ∈ l, Gs.eval r = 0 := fun r hr ↦ by
    rw [hsplit]; exact eval_prod_of_mem l r hr
  have hRs : psSubR N a R ≠ 0 := fun h ↦
    hR (psSubR_injective N hN a (by rw [h, map_zero]))
  have hder : ∀ r ∈ l, (derivative Gs).eval r ≠ 0 := by
    intro r hr h0
    have := congrArg (fun P ↦ (P.map (psSubR N a)).eval r) hAB
    simp only [Polynomial.map_C, eval_C, Polynomial.map_add, Polynomial.map_mul, eval_add,
      eval_mul] at this
    rw [← hGs, hroot r hr, ← Polynomial.derivative_map, ← hGs, h0, mul_zero, mul_zero,
      add_zero] at this
    exact hRs this
  have hnd : l.Nodup := nodup_of_derivative l fun r hr ↦ by rw [← hsplit]; exact hder r hr
  -- the orders of the derivative and of the separations
  have hexd : ∀ r ∈ l, ∃ i, PowerSeries.coeff i ((derivative Gs).eval r) ≠ 0 := fun r hr ↦ by
    by_contra h
    push Not at h
    exact hder r hr (PowerSeries.ext fun i ↦ by rw [h i, map_zero])
  have hexs : ∀ r r' : PowerSeries K, r ≠ r' → ∃ i, PowerSeries.coeff i r ≠ PowerSeries.coeff i r' :=
    fun r r' h ↦ by
      by_contra h'
      push Not at h'
      exact h (PowerSeries.ext h')
  let d : PowerSeries K → ℕ := fun r ↦ if h : r ∈ l then Nat.find (hexd r h) else 0
  let sp : PowerSeries K → PowerSeries K → ℕ := fun r r' ↦
    if h : r ≠ r' then Nat.find (hexs r r' h) else 0
  set B0 := (l.map d).sum + (l.map fun r ↦ (l.map fun r' ↦ sp r r').sum).sum with hB0
  have hd_le : ∀ r ∈ l, d r ≤ B0 := fun r hr ↦
    le_trans (List.le_sum_of_mem (List.mem_map_of_mem hr)) (Nat.le_add_right _ _)
  have hs_le : ∀ r ∈ l, ∀ r' ∈ l, sp r r' ≤ B0 := fun r hr r' hr' ↦
    le_trans (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hr'))
      (List.le_sum_of_mem (List.mem_map_of_mem (f := fun r ↦ (l.map fun r' ↦ sp r r').sum) hr)))
      (Nat.le_add_left _ _)
  refine ⟨N, B0 + 1, Nat.pos_of_ne_zero hN, fun prec hprec ↦ ?_⟩
  set Lt := B0 + prec with hLt
  set ys : List (CPoly K) := l.map fun r ↦ (List.range Lt).map fun i ↦ PowerSeries.coeff i r
    with hys
  refine ⟨ys, by simp [ys, hl], ?_⟩
  intro F _ _ ψ Fc a' ys' hG ha hys'
  have hrep : repEq ψ Fc a' N = Gs := by rw [repEq, hG, ha]
  have hlen' : ys'.length = n := by
    have := congrArg List.length hys'
    rw [List.length_map] at this
    rw [this, hys, List.length_map, hl]
  have hget : ∀ k (hk : k < n), ∀ i < Lt,
      ψ ((ys'.getD k []).getD i 0) = PowerSeries.coeff i (l[k]'(by omega)) := by
    intro k hk i hi
    have h1 : (ys'.getD k []).map ψ = ys.getD k [] := by
      rw [← hys', List.getD_eq_getElem _ _ (by omega),
        List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map]
    have h2 := congrArg (fun y : CPoly K ↦ y.getD i 0) h1
    have e : ∀ (L : CPoly F) (i : ℕ), (L.map ψ).getD i 0 = ψ (L.getD i 0) := fun L i ↦ by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases L[i]? <;> simp
    rw [e] at h2
    rw [h2, hys, List.getD_eq_getElem (l := List.map _ l) _ (by rw [List.length_map]; omega),
      List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨Nat.pos_of_ne_zero hN, hlen'⟩, fun y hy ↦ ?_⟩, ?_⟩
  · -- the root checks
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    have hk' : k < n := by omega
    have hkl : k < l.length := by omega
    set r := l[k] with hr
    have hrl : r ∈ l := List.getElem_mem hkl
    have hdr : d r = Nat.find (hexd r hrl) := dif_pos hrl
    refine rootCheck_of_root ψ r (by rw [hrep]; exact hroot r hrl) (d r) (fun i hi ↦ ?_) ?_
      (by have := hd_le r hrl; omega) ?_
    · rw [hrep]
      rw [hdr] at hi
      by_contra h
      exact Nat.find_min (hexd r hrl) hi h
    · rw [hrep, hdr]; exact Nat.find_spec (hexd r hrl)
    · rw [PowerSeries.X_pow_dvd_iff]
      intro i hi
      rw [map_sub, coeff_thetaT, ← List.getD_eq_getElem ys' [] hk,
        hget k hk' i (by have := hd_le r hrl; omega), sub_self]
  · -- the separation
    simp only [sepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true]
    intro k hk k' hk'
    rw [hlen'] at hk hk'
    by_cases hkk : k = k'
    · exact Or.inl hkk
    right
    have hkl : k < l.length := by omega
    have hkl' : k' < l.length := by omega
    have hne : l[k] ≠ l[k'] := fun h ↦ hkk ((hnd.getElem_inj_iff).mp h)
    have hsp : sp l[k] l[k'] = Nat.find (hexs _ _ hne) := dif_pos hne
    refine ⟨sp l[k] l[k'], by have := hs_le _ (List.getElem_mem hkl) _ (List.getElem_mem hkl'); omega,
      fun heq ↦ ?_⟩
    have := congrArg ψ heq
    rw [hget k hk _ (by have := hs_le _ (List.getElem_mem hkl) _ (List.getElem_mem hkl'); omega),
      hget k' hk' _ (by have := hs_le _ (List.getElem_mem hkl) _ (List.getElem_mem hkl'); omega),
      hsp] at this
    exact Nat.find_spec (hexs _ _ hne) this

end Exist

end Curves
