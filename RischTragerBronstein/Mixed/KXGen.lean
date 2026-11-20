import RischTragerBronstein.Mixed.KQMMain

/-!
# The parametric Risch equation for `B θ` with several logarithmic columns

For a realization `T` of a certified tower, `θ² = A(t)` over the top level, an integrand code `rhs`
and a list of column codes `cols`:

* `prde_forward_gen`: if `rhs θ = (a θ)′ + ∑ e_i colᵢ θ` with `a ∈ Fₘ₊₁` and constant `e_i`, the
  parametric Risch equation has a solution with a non-zero coefficient of `rhs`;
* `prde_backward_gen`: if it has one and every `q colᵢ θ` (`q ∈ ℚ`) is elementary, so is `rhs θ`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Forward**: a representation `rhs θ = (a θ)′ + ∑ eᵢ colᵢ θ` gives a solution. -/
theorem prde_forward_gen (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m)) (hA0 : T.evP m A ≠ 0)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hspecA : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (rhs : LC (m + 1)) (cols : List (LC (m + 1))) (aa : L) (haa : aa ∈ T.F (m + 1))
    (e : Fin cols.length → L) (he : ∀ i, (e i)′ = 0)
    (hrep : T.ev (m + 1) rhs * θ = (aa * θ)′ + ∑ i, e i * T.ev (m + 1) cols[i] * θ) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: cols)).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
  have hconst' : ∀ i, ∃ c0 : Cc, algebraMap Cc L c0 = -e i := fun i ↦
    T.hconst _ (by rw [map_neg, he i, neg_zero])
  choose c0 hc0 using hconst'
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 aa 1
  simp only [pow_one] at h1
  rw [h1] at hrep
  have haaF : aa ∈ T.F (m + 1) := haa
  have hlen : (rhs :: cols).length = cols.length + 1 := by simp
  obtain ⟨βv, hβv, -⟩ := hspecA.complete (rhs :: cols) (1 :: List.ofFn c0) (fun i hi ↦ by
      rw [hlen] at hi
      rcases i with _ | i
      · simp at hi
      · simp only [List.getD_cons_succ]
        exact List.getD_eq_default _ _ (by simp; omega)) ⟨aa, haaF⟩ (by
    apply Subtype.ext
    simp only [sC, IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv]
    rw [hlen, Finset.sum_range_succ', IntermediateField.coe_add]
    simp only [List.getD_cons_zero, List.getD_cons_succ, map_one, one_mul]
    rw [T.sem_kpFr m hTr, T.sem_MP (m + 1) hTr]
    have hsum : ((∑ i ∈ Finset.range cols.length,
        algebraMap Cc (T.F (m + 1)) ((List.ofFn c0).getD i 0) *
          (T.MP (m + 1) hTr).sem (cols.getD i (MO Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        ∑ i : Fin cols.length, -e i * T.ev (m + 1) cols[i] := by
      rw [show ((∑ i ∈ Finset.range cols.length,
          algebraMap Cc (T.F (m + 1)) ((List.ofFn c0).getD i 0) *
            (T.MP (m + 1) hTr).sem (cols.getD i (MO Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
          ∑ i ∈ Finset.range cols.length,
            ((algebraMap Cc (T.F (m + 1)) ((List.ofFn c0).getD i 0) *
              (T.MP (m + 1) hTr).sem (cols.getD i (MO Fc ks (m + 1)).zero) : T.F (m + 1)) : L) from
          map_sum (T.F (m + 1)).val _ _, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [IntermediateField.coe_mul, List.getD_eq_getElem _ _ (by simp),
        List.getD_eq_getElem _ _ i.2, List.getElem_ofFn]
      rw [T.sem_MP (m + 1) hTr]
      change algebraMap Cc L (c0 i) * _ = _
      rw [hc0 i]
      rfl
    rw [hsum]
    change aa′ + _ * aa = _
    rw [show (((1 : ℕ) : ℚ) / (2 : ℕ) : L) = (1 / 2 : L) by push_cast; ring]
    apply mul_right_cancel₀ hθ0
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [add_mul, add_mul, hrep, neg_mul, Finset.sum_mul]
    push_cast
    ring)
  have h0 := hβv 0
  simp only [List.getD_cons_zero] at h0
  by_contra hno
  simp only [List.any_eq_true, not_exists, not_and, decide_eq_true_eq, not_not] at hno
  apply one_ne_zero (α := Cc)
  rw [h0]
  refine Finset.sum_eq_zero fun kk hkk ↦ ?_
  have hmem : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: cols)).getD kk
      ([], (MO Fc ks (m + 1)).zero) ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: cols) := by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hkk)]
    exact List.getElem_mem _
  rw [hno _ hmem, map_zero, mul_zero]

/-- `prde_forward_gen` for a list of columns given by a function. -/
theorem prde_forward_ofFn (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m)) (hA0 : T.evP m A ≠ 0)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hspecA : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (rhs : LC (m + 1)) {n : ℕ} (f : Fin n → LC (m + 1)) (aa : L) (haa : aa ∈ T.F (m + 1))
    (e : Fin n → L) (he : ∀ i, (e i)′ = 0)
    (hrep : T.ev (m + 1) rhs * θ = (aa * θ)′ + ∑ i, e i * T.ev (m + 1) (f i) * θ) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: List.ofFn f)).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
  have hl : (List.ofFn f).length = n := List.length_ofFn
  refine T.prde_forward_gen m hTr A hA0 θ hθ hspecA rhs (List.ofFn f) aa haa
    (fun i ↦ e (Fin.cast hl i)) (fun i ↦ he _) ?_
  rw [hrep]
  congr 1
  rw [← Fin.sum_congr' (fun i ↦ e i * T.ev (m + 1) (f i) * θ) hl]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.getElem_fin, List.getElem_ofFn]
  rfl

/-- **Backward**: a solution gives an antiderivative, when every column is elementary. -/
theorem prde_backward_gen (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (rhs : LC (m + 1)) (cols : List (LC (m + 1)))
    (hcol : ∀ c ∈ cols, ∀ q : ℚ, HasElementaryIntegralIn ((q : L) * (T.ev (m + 1) c * θ)))
    (h : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: cols)).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true) :
    HasElementaryIntegralIn (T.ev (m + 1) rhs * θ) := by
  obtain ⟨r, hr, hr0⟩ := List.any_eq_true.mp h
  have hq0 : r.1.getD 0 0 ≠ 0 := of_decide_eq_true hr0
  have hs := hspec.sound (rhs :: cols) r hr
  have hlen : (rhs :: cols).length = cols.length + 1 := by simp
  have hsQ : sQ (T.MP (m + 1) hTr) r.1 (rhs :: cols) =
      ((r.1.getD 0 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem rhs +
        ∑ k : Fin cols.length, ((r.1.getD (k + 1) 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) hTr).sem cols[k] := by
    unfold sQ
    rw [hlen, Finset.sum_range_succ']
    refine (add_comm _ _).trans ?_
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [List.getD_eq_getElem _ _ k.2]
    rfl
  rw [hsQ] at hs
  have hsL := congrArg Subtype.val hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv,
    IntermediateField.coe_sum] at hsL
  rw [T.sem_kpFr m hTr] at hsL
  simp only [T.sem_MP (m + 1) hTr] at hsL
  set a : L := T.ev (m + 1) r.2
  set q0 : ℚ := r.1.getD 0 0
  have hq0L : (q0 : L) ≠ 0 := by exact_mod_cast hq0
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (a / q0) 1
  simp only [pow_one] at h1
  have hf : T.ev (m + 1) rhs * θ = ((a / q0) * θ)′ + ∑ k : Fin cols.length,
      ((-(r.1.getD (k + 1) 0) / q0 : ℚ) : L) * (T.ev (m + 1) cols[k] * θ) := by
    rw [h1]
    have hq0d : ((q0 : L))′ = 0 := Tower.NestP.deriv_ratCastK (K := L) q0
    have hd : (a / (q0 : L))′ = a′ / q0 := by
      rw [div_eq_mul_inv a, Derivation.leibniz, Derivation.leibniz_inv, hq0d, div_eq_mul_inv]
      simp only [smul_zero, smul_eq_mul, mul_zero, zero_add, neg_zero]
      ring
    rw [hd]
    have hsum : ∑ k : Fin cols.length, ((-(r.1.getD (k + 1) 0) / q0 : ℚ) : L) *
        (T.ev (m + 1) cols[k] * θ) =
        -(∑ k : Fin cols.length, ((r.1.getD (k + 1) 0 : ℚ) : L) * T.ev (m + 1) cols[k]) * θ / q0 := by
      rw [div_eq_mul_inv, neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast; field_simp
    rw [hsum]
    generalize T.ev (m + 1) rhs = R at hsL ⊢
    push_cast at hsL ⊢
    field_simp
    linear_combination (-2 * θ : L) * hsL
  rw [hf]
  exact (hasElementaryIntegralIn_deriv _).add (hei_sum _ fun k ↦ hcol _ (List.getElem_mem _) _)

end MTower

end Curves.MT
