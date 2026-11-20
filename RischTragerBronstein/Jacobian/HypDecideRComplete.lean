import RischTragerBronstein.Jacobian.HypDecideR
import RischTragerBronstein.Jacobian.ScaleInt
import RischTragerBronstein.Algebraic.EllGenComplete

/-!
# `hypDecideR` always answers on well-formed data

`hypDecideR_ne_none`: for `f` squarefree of degree `2g + 1` and residues at distinct rational
non-branch points, `wfR` holds and every check of `torsionDecideR` passes (the rescaled points
are integral, `den_scale_x`, `den_scale_y`; rescaling keeps `f` squarefree), so `hypDecideR`
answers.
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

lemma isCoprime_derivative_scaleF {f : ℚ[X]} (h : IsCoprime f (derivative f)) {t e : ℚ}
    (ht : t ≠ 0) (he : e ≠ 0) :
    IsCoprime (scaleF t e f) (derivative (scaleF t e f)) := by
  obtain ⟨a, b, hab⟩ := h
  set L : ℚ[X] := C t⁻¹ * X
  have hdL : derivative (f.comp (C t⁻¹ * X)) = C t⁻¹ * (derivative f).comp L := by
    rw [derivative_comp]; simp [L]
  have hcomp := congrArg (fun P ↦ P.comp L) hab
  simp only [add_comp, mul_comp, one_comp] at hcomp
  refine ⟨C (e ^ 2)⁻¹ * a.comp L, C (e ^ 2)⁻¹ * C t * b.comp L, ?_⟩
  have h1 : C (e ^ 2)⁻¹ * C (e ^ 2) = (1 : ℚ[X]) := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ (pow_ne_zero 2 he), C_1]
  have h2 : C t * C t⁻¹ = (1 : ℚ[X]) := by rw [← Polynomial.C_mul, mul_inv_cancel₀ ht, C_1]
  simp only [scaleF, derivative_mul, derivative_C, zero_mul, zero_add, hdL]
  linear_combination hcomp + (a.comp L * f.comp L + b.comp L * (derivative f).comp L) * h1 +
    (b.comp L * (derivative f).comp L * (C (e ^ 2)⁻¹ * C (e ^ 2))) * h2

lemma cast_evalC (F : List ℤ) (n : ℤ) :
    ((evalC F n : ℤ) : ℚ) = ((toPoly F).map (Int.castRingHom ℚ)).eval (n : ℚ) := by
  rw [evalC_eq, eval_map, show (n : ℚ) = Int.castRingHom ℚ n from rfl, eval₂_at_apply]; rfl

lemma eval_scaleF (f : ℚ[X]) {t e : ℚ} (ht : t ≠ 0) (α : ℚ) :
    (scaleF t e f).eval (t * α) = e ^ 2 * f.eval α := by
  simp [scaleF, eval_comp, ← mul_assoc, inv_mul_cancel₀ ht]

/-- **All checks of `torsionDecideR` pass on well-formed data.** -/
theorem torsionDecideR_ne_none {f : List ℤ} {g : ℕ} {Γ : EDiv ℚ} (hlen : f.length = 2 * g + 2)
    (hlc : f.getD (2 * g + 1) 0 ≠ 0) (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hΓ : ∀ q ∈ Γ, q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = ((toPoly f).map (Int.castRingHom ℚ)).eval q.1)
    (hnd : Γ.Pairwise fun u v ↦ u.1 ≠ v.1) : torsionDecideR f g Γ ≠ none := by
  unfold torsionDecideR
  dsimp only
  set d : ℕ := (Γ.map fun q ↦ q.1.den).foldr Nat.lcm 1 with hd
  set t : ℚ := (d : ℚ) ^ 2
  set e : ℚ := (d : ℚ) ^ (2 * g + 1)
  have hd0 : d ≠ 0 := foldr_lcm_ne_zero _ fun a ha ↦ by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; exact Rat.den_ne_zero _
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have ht : t ≠ 0 := pow_ne_zero _ hdq
  have he : e ≠ 0 := pow_ne_zero _ hdq
  have hdv : ∀ q ∈ Γ, q.1.den ∣ d := fun q hq ↦
    dvd_foldr_lcm (List.mem_map_of_mem (f := fun q : ℚ × ℚ × ℕ ↦ q.1.den) hq)
  have hev : ∀ α : ℚ, evalC (f.map (Int.castRingHom ℚ)) α =
      ((toPoly f).map (Int.castRingHom ℚ)).eval α := fun α ↦ by rw [evalC_eq, toPoly_map_list]
  have hint : ∀ q ∈ Γ, (t * q.1).den = 1 ∧ (e * q.2.1).den = 1 := fun q hq ↦
    ⟨den_scale_x (hdv q hq), den_scale_y hlen (hdv q hq) (by rw [hev]; exact (hΓ q hq).2)⟩
  have hF : (toPoly (scaleList f g d)).map (Int.castRingHom ℚ) =
      scaleF t e ((toPoly f).map (Int.castRingHom ℚ)) := toPoly_scaleList hlen hd0
  rw [dif_pos]
  · simp
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨fun q hq ↦ hint q hq, hlen⟩, hd0⟩, by simp [scaleList]⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by simp [scaleList])]
    simp only [scaleList, List.getElem_map, List.getElem_range, Nat.sub_self, mul_zero, pow_zero,
      mul_one]
    exact hlc
  · apply squarefreeCheck_complete
    rw [toPoly_map_list, hF]
    exact isCoprime_derivative_scaleF (PerfectField.separable_iff_squarefree.mpr hsq) ht he
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hx, hy⟩ := hint r hr
    have eX : (((t * r.1).num : ℤ) : ℚ) = t * r.1 := Rat.coe_int_num_of_den_eq_one hx
    have eY : (((e * r.2.1).num : ℤ) : ℚ) = e * r.2.1 := Rat.coe_int_num_of_den_eq_one hy
    refine ⟨fun h0 ↦ ?_, ?_⟩
    · have h0' : (e * r.2.1).num = 0 := h0
      have : e * r.2.1 = 0 := by rw [← eY, h0', Int.cast_zero]
      exact mul_ne_zero he (hΓ r hr).1 this
    · show (e * r.2.1).num ^ 2 = evalC (scaleList f g d) (t * r.1).num
      apply Int.cast_injective (α := ℚ)
      rw [cast_evalC, Int.cast_pow, eY, eX, hF, eval_scaleF _ ht, mul_pow, (hΓ r hr).2]
  · unfold scaleΓInt
    rw [List.pairwise_map]
    refine hnd.imp_of_mem fun {u v} hu hv huv he' ↦ huv ?_
    have eu : (((t * u.1).num : ℤ) : ℚ) = t * u.1 := Rat.coe_int_num_of_den_eq_one (hint u hu).1
    have ev : (((t * v.1).num : ℤ) : ℚ) = t * v.1 := Rat.coe_int_num_of_den_eq_one (hint v hv).1
    have he'' : (t * u.1).num = (t * v.1).num := he'
    have : t * u.1 = t * v.1 := by rw [← eu, ← ev, he'']
    exact mul_left_cancel₀ ht this

/-- **`hypDecideR` answers on well-formed data.** -/
theorem hypDecideR_ne_none {f : List ℤ} {g : ℕ} {pts : List (ℚ × ℚ × ℤ)} (B : CPoly ℚ) (D : ℕ)
    (hlen : f.length = 2 * g + 2) (hlc : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hon : ∀ q ∈ pts, ((toPoly f).map (Int.castRingHom ℚ)).eval q.1 = q.2.1 ^ 2 ∧
      q.2.1 ≠ 0 ∧ q.2.2 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) : hypDecideR f g pts B D ≠ none := by
  have hev : ∀ α : ℚ, evalC (f.map (Int.castRingHom ℚ)) α =
      ((toPoly f).map (Int.castRingHom ℚ)).eval α := fun α ↦ by rw [evalC_eq, toPoly_map_list]
  have hw : wfR f g pts = true := by
    simp only [wfR, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨hlen, hlc⟩, ?_⟩, fun q hq ↦ ?_⟩, hnd⟩
    · apply squarefreeCheck_complete
      rw [toPoly_map_list]; exact PerfectField.separable_iff_squarefree.mpr hsq
    · obtain ⟨h1, h2, h3⟩ := hon q hq
      exact ⟨by rw [hev, h1], h2, h3⟩
  have hT : torsionDecideR f g (ptsDivR (ptsNorm pts)) ≠ none := by
    apply torsionDecideR_ne_none hlen hlc hsq
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq'
      obtain ⟨h1, h2, h3⟩ := hon r hr
      have hpos := zgcd_pos hr h3
      obtain ⟨k, hk⟩ := zgcd_dvd hr
      have hq0 : r.2.2 / (zgcd pts : ℤ) ≠ 0 := by
        rw [hk, Int.mul_ediv_cancel_left _ (by exact_mod_cast hpos.ne')]
        rintro rfl; simp at hk; exact h3 hk
      have hs : (((r.2.2 / (zgcd pts : ℤ)).sign : ℤ) : ℚ) ^ 2 = 1 := by
        rcases lt_trichotomy (r.2.2 / (zgcd pts : ℤ)) 0 with h | h | h
        · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
        · exact absurd h hq0
        · rw [Int.sign_eq_one_of_pos h]; norm_num
      refine ⟨mul_ne_zero (fun h0 ↦ by rw [h0] at hs; norm_num at hs) h2, ?_⟩
      simp only
      rw [mul_pow, hs, one_mul, h1]
    · unfold ptsDivR ptsNorm
      rw [List.map_map, List.pairwise_map]
      have := hnd
      rw [List.Nodup, List.pairwise_map] at this
      exact this
  unfold hypDecideR
  rw [dif_pos hw]
  split
  · exact absurd ‹_› hT
  · simp
  · dsimp only
    split <;> simp

end Jac
