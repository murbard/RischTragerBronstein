import RischTragerBronstein.Algebraic.EllTwist
import RischTragerBronstein.Algebraic.EllComplete

/-!
# The decision procedure for residues at twisted points `(α, γ√d)`

`ellDecideTw a b c d B pts D fuel` for `∫ (B(x) + ∑ (zᵢ/D) γᵢ d / (x − αᵢ)) dx / √p(x)`,
`dγᵢ² = p(αᵢ)` (residues `±(zᵢ/D)√d` at `(αᵢ, ±γᵢ√d)`), in a differential field whose constants
contain `√d`:

1. the Nagell–Lutz test on `∑ zᵢ (dαᵢ, d²γᵢ)` on the twist `Y² = X³ + adX² + bd²X + cd³`;
   infinite order ⇒ not elementary (`ell_torsion_twist`);
2. torsion ⇒ the certificate search of `ellCert` on the curve `Ỹ² = p/d` (the function
   `u = A + √d (B̃/d) y`), the kernel check, `ell_log_reduce_twist`, and `hypRed` on `p`.

`ellDecideTw_spec`: every answer is correct.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace EllAlgo

open CPoly

/-- The twisted point `(dα, d²γ)`. -/
def ptTw (a b c d : ℤ) (q : ℚ × ℚ × ℤ) : (EllNL.W (a * d) (b * d ^ 2) (c * d ^ 3)).toAffine.Point :=
  ptOf (a * d) (b * d ^ 2) (c * d ^ 3) (d * q.1, d ^ 2 * q.2.1, q.2.2)

/-- The certificate step on `Ỹ² = p/d`. -/
def ellCertTw (a b c d : ℤ) (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ)) (D n : ℕ) : Option Bool :=
  match ellSolve (smul (1 / (d : ℚ)) (pOf a b c)) (ptsQ pts n) with
  | none => none
  | some AB =>
    if certCheck (smul (1 / (d : ℚ)) (pOf a b c)) AB (fracG (smul (1 / (d : ℚ)) B) D pts)
        (1 / ((n : ℚ) * D)) then
      some (isZero (hypRed (pOf a b c) (certR (smul (1 / (d : ℚ)) (pOf a b c)) AB
        (fracG (smul (1 / (d : ℚ)) B) D pts) (1 / ((n : ℚ) * D)))).2)
    else none

/-- **The twisted decision procedure.** -/
def ellDecideTw (a b c d : ℤ) (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ)) (D fuel : ℕ) : Option Bool :=
  if decide (d ≠ 0) && pts.all (fun q ↦ decide ((d : ℚ) * q.2.1 ^ 2 =
      q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)) &&
      decide (pts.map Prod.fst).Nodup && decide (D ≠ 0) then
    let S := (pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum
    match EllNL.torsionTest (a * d) (b * d ^ 2) (c * d ^ 3) S fuel with
    | some false => some false
    | some true => ellCertTw a b c d B pts D (ordOf S fuel)
    | none => none
  else none

/-! ### Correctness -/

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma twist_nonsingular (a b c d : ℤ) (hd : d ≠ 0) {α γ : ℚ}
    (h : (d : ℚ) * γ ^ 2 = α ^ 3 + a * α ^ 2 + b * α + c ∧ γ ≠ 0) :
    ((d * α : ℚ)) = (d : ℚ) * α ∧ (((d ^ 2 * γ : ℚ)) ^ 2 = (d * α) ^ 3 + ((a * d : ℤ) : ℚ) * (d * α) ^ 2 +
      ((b * d ^ 2 : ℤ) : ℚ) * (d * α) + ((c * d ^ 3 : ℤ) : ℚ) ∧ ((d : ℚ) ^ 2 * γ) ≠ 0) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  refine ⟨rfl, ?_, mul_ne_zero (pow_ne_zero _ hdq) h.2⟩
  push_cast
  linear_combination (d : ℚ) ^ 3 * h.1

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ellDecideTw`.** -/
theorem ellDecideTw_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (d : ℤ) (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ)) (D fuel : ℕ) (ans : Bool)
    (h : ellDecideTw a b c d B pts D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral ((aeval x (toPoly B) + (pts.map fun q ↦
      (((q.2.2 : ℚ) / D * q.2.1 * d : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hp : toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) :=
    toPoly_pOf a b c
  have hy' : y ^ 2 = aeval x (toPoly (pOf a b c)) := by rw [hp, hy]; simp
  unfold ellDecideTw at h
  split_ifs at h with hval
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hval
  obtain ⟨⟨⟨hd, hon⟩, hnd⟩, hD⟩ := hval
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  dsimp only at h
  split at h
  · -- infinite order
    rename_i hT
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    intro hf
    have hns := EllNL.torsionTest_spec _ _ _ _ fuel false hT
    simp only [Bool.false_eq_true, false_iff] at hns
    apply hns
    have hP : ∀ i : Fin pts.length, (EllNL.W (a * d) (b * d ^ 2) (c * d ^ 3)).toAffine.Nonsingular
        (d * pts[i].1) (d ^ 2 * pts[i].2.1) := fun i ↦ by
      have := twist_nonsingular a b c d hd (hon _ (List.getElem_mem i.2))
      exact nonsingular_of _ _ _ ⟨by exact_mod_cast this.2.1, this.2.2⟩
    have hinj : Set.InjOn (fun i : Fin pts.length ↦ pts[i].1)
        ((Finset.univ : Finset (Fin pts.length)) : Set (Fin pts.length)) := by
      intro i _ j _ hij
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
        (hj := by rw [List.length_map]; exact j.2)).mp (by simp only [List.getElem_map]; exact hij))
    have key := ell_torsion_twist hC hCall x y hx a b c hsq hy hgen (toPoly B)
      (Finset.univ : Finset (Fin pts.length)) (fun i ↦ pts[i].1) (fun i ↦ pts[i].2.1) d hd hP
      (fun i _ ↦ (hon _ (List.getElem_mem _)).2) hinj (fun i ↦ pts[i].2.2) D hD (by
        rw [sum_map_eq_fin] at hf; exact hf)
    rw [sum_map_eq_fin]
    convert key using 2 with i
    rw [ptTw, ptOf]
    split_ifs with hh
    · rfl
    · exact absurd ⟨by exact_mod_cast (twist_nonsingular a b c d hd
        (hon _ (List.getElem_mem _))).2.1, (twist_nonsingular a b c d hd
          (hon _ (List.getElem_mem _))).2.2⟩ hh
  · -- torsion: the certificate
    rename_i hT
    unfold ellCertTw at h
    split at h
    · exact absurd h (by simp)
    rename_i AB hAB
    split_ifs at h with hchk
    simp only [Option.some.injEq] at h
    subst h
    set pt := smul (1 / (d : ℚ)) (pOf a b c)
    set cc : ℚ := 1 / ((ordOf ((pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum) fuel : ℚ) * D)
    unfold certCheck at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, certN, certM] at hchk
    obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
    have hpt : toPoly pt = C (1 / (d : ℚ)) * toPoly (pOf a b c) := toPoly_smul _ _
    have hN' : toPoly AB.1 ^ 2 - C (d : ℚ) * (C (1 / (d : ℚ)) * toPoly AB.2) ^ 2 *
        toPoly (pOf a b c) ≠ 0 := by
      intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
      simp only [toPoly_sub, toPoly_mul, hpt]
      have hdd : C (d : ℚ) * C (1 / (d : ℚ)) = 1 := by rw [← C_mul, mul_one_div_cancel hdq, C_1]
      linear_combination h0 + C (1 / (d : ℚ)) * toPoly AB.2 ^ 2 * toPoly (pOf a b c) * hdd
    have hG' : toPoly (fracG (smul (1 / (d : ℚ)) B) D pts).2 ≠ 0 := by
      intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
    have hid := (beq_iff _ _).mp hbeq
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2, hpt] at hid
    have hp0 : toPoly (pOf a b c) ≠ 0 := by rw [hp]; exact hsq.ne_zero
    have hred := ell_log_reduce_twist' hC x y hx (toPoly (pOf a b c)) hp0 hy' (d : ℚ) hdq
      (toPoly (fracG (smul (1 / (d : ℚ)) B) D pts).1) (toPoly (fracG (smul (1 / (d : ℚ)) B) D pts).2)
      (toPoly AB.1) (C (1 / (d : ℚ)) * toPoly AB.2)
      (toPoly (certR pt AB (fracG (smul (1 / (d : ℚ)) B) D pts) cc)) cc hG' hN' (by
        have hdd : C (d : ℚ) * C (1 / (d : ℚ)) = 1 := by rw [← C_mul, mul_one_div_cancel hdq, C_1]
        simp only [derivative_mul, derivative_C, zero_mul, zero_add] at hid ⊢
        linear_combination hid + C (1 / (d : ℚ)) * toPoly AB.2 ^ 2 * toPoly (pOf a b c) *
          (toPoly (fracG (smul (1 / (d : ℚ)) B) D pts).2 *
            toPoly (certR pt AB (fracG (smul (1 / (d : ℚ)) B) D pts) cc) -
            toPoly (fracG (smul (1 / (d : ℚ)) B) D pts).1) * hdd)
    have hdeg3 : (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) : ℚ[X]).natDegree = 3 := by
      compute_degree!
    have hdec := hyp_decides hC hCall x y hx (pOf a b c) (by rw [hp]; exact hsq)
      (by rw [hp, hdeg3]; decide) hy' hgen (certR pt AB (fracG (smul (1 / (d : ℚ)) B) D pts) cc)
    obtain ⟨_, hfr⟩ := fracG_spec x hne (smul (1 / (d : ℚ)) B) D pts
    have hint : (aeval x (toPoly B) + (pts.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 * d : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y =
        ((d : ℚ) : E) * (aeval x (toPoly (fracG (smul (1 / (d : ℚ)) B) D pts).1) /
          (aeval x (toPoly (fracG (smul (1 / (d : ℚ)) B) D pts).2) * y)) := by
      rw [← div_div, hfr, toPoly_smul, map_mul, aeval_C, eq_ratCast]
      have hdE : ((d : ℚ) : E) ≠ 0 := by exact_mod_cast hdq
      have hl : (pts.map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 * d : ℚ) : E) /
          (x - ((q.1 : ℚ) : E))).sum = ((d : ℚ) : E) * (pts.map fun q ↦
            (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun q _ ↦ ?_
        push_cast; ring
      rw [hl]
      push_cast
      field_simp
    rw [hint, hasElementaryIntegral_const_mul_iff _ _ (deriv_ratCast_L _)
      (by exact_mod_cast hdq), hred, hdec]
  · exact absurd h (by simp)

end Spec

end EllAlgo
