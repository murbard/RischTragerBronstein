import RischTragerBronstein.Algebraic.EllMixed
import RischTragerBronstein.Algebraic.EllCompleteTw
import RischTragerBronstein.Algebraic.EllGenComplete

/-!
# The decision procedure for residues in two quadratic classes

`ellDecideMix a b c d₁ d₂ B pts₁ pts₂ D fuel` for
`∫ (B(x) + ∑_{pts₁} (zᵢ/D) γᵢ d₁ / (x − αᵢ) + ∑_{pts₂} (zᵢ/D) γᵢ d₂ / (x − αᵢ)) dx / √p(x)`
(`d₁d₂` not a square):

1. the Nagell–Lutz test on the class-`d₂` divisor on the twist by `d₂`; infinite order ⇒ not
   elementary (`ell_torsion_mixed`);
2. torsion ⇒ the class-`d₂` certificate `u₂` (`ellCertTwR`): its logarithm absorbs the class-`d₂`
   residues and leaves a polynomial `R₂` (`ell_log_reduce_twist'_add`), and `ellDecideTw` decides the
   rest `∫ (B + d₂ R₂ + ∑_{pts₁} …) / y`.

`ellDecideMix_spec`: every answer is correct; `ellDecideMix_decides`: with enough fuel it always
answers.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace EllAlgo

open CPoly

/-- The class-`d` certificate remainder (the certificate for the residues alone). -/
def ellCertTwR (a b c d : ℤ) (pts : List (ℚ × ℚ × ℤ)) (D n : ℕ) : Option (CPoly ℚ) :=
  match ellSolve (smul (1 / (d : ℚ)) (pOf a b c)) (ptsQ pts n) with
  | none => none
  | some AB =>
    if certCheck (smul (1 / (d : ℚ)) (pOf a b c)) AB (fracG (smul (1 / (d : ℚ)) []) D pts)
        (1 / ((n : ℚ) * D)) then
      some (certR (smul (1 / (d : ℚ)) (pOf a b c)) AB (fracG (smul (1 / (d : ℚ)) []) D pts)
        (1 / ((n : ℚ) * D)))
    else none

lemma ellCertTwR_ne_none {a b c d : ℤ} {pts : List (ℚ × ℚ × ℤ)} {D n : ℕ}
    (h : ellCertTw a b c d [] pts D n ≠ none) : ellCertTwR a b c d pts D n ≠ none := by
  unfold ellCertTw at h
  unfold ellCertTwR
  split
  · rename_i hs; rw [hs] at h; exact absurd rfl h
  · rename_i AB hs
    rw [hs] at h
    dsimp only at h ⊢
    split_ifs at h ⊢ with hc
    · simp
    · exact absurd rfl h

/-- Validity of the data of one class. -/
def classValid (a b c d : ℤ) (pts : List (ℚ × ℚ × ℤ)) : Bool :=
  decide (d ≠ 0) && pts.all (fun q ↦ decide ((d : ℚ) * q.2.1 ^ 2 =
    q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)) && decide (pts.map Prod.fst).Nodup

/-- **The decision procedure for two quadratic classes.** -/
def ellDecideMix (a b c d₁ d₂ : ℤ) (B : CPoly ℚ) (pts₁ pts₂ : List (ℚ × ℚ × ℤ)) (D fuel : ℕ) :
    Option Bool :=
  if classValid a b c d₁ pts₁ && classValid a b c d₂ pts₂ && decide (D ≠ 0) &&
      (qsqrt ((d₁ * d₂ : ℤ) : ℚ)).isNone then
    let S := (pts₂.map fun q ↦ q.2.2 • ptTw a b c d₂ q).sum
    match EllNL.torsionTest (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3) S fuel with
    | some false => some false
    | some true =>
      match ellCertTwR a b c d₂ pts₂ D (ordOf S fuel) with
      | some R => ellDecideTw a b c d₁ (add B (smul (d₂ : ℚ) R)) pts₁ D fuel
      | none => none
    | none => none
  else none

lemma classValid_iff {a b c d : ℤ} {pts : List (ℚ × ℚ × ℤ)} :
    classValid a b c d pts = true ↔ d ≠ 0 ∧ (∀ q ∈ pts, (d : ℚ) * q.2.1 ^ 2 =
      q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0) ∧ (pts.map Prod.fst).Nodup := by
  simp only [classValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

lemma not_sq_of_qsqrt_none {v : ℚ} (h : qsqrt v = none) : ∀ q : ℚ, v ≠ q ^ 2 := by
  intro q hq
  have := qsqrt_sq q
  rw [← hq, h] at this
  exact Bool.false_ne_true this

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ellDecideMix`.** -/
theorem ellDecideMix_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (d₁ d₂ : ℤ) (B : CPoly ℚ) (pts₁ pts₂ : List (ℚ × ℚ × ℤ)) (D fuel : ℕ) (ans : Bool)
    (h : ellDecideMix a b c d₁ d₂ B pts₁ pts₂ D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral ((aeval x (toPoly B) + (pts₁.map fun q ↦
      (((q.2.2 : ℚ) / D * q.2.1 * d₁ : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum + (pts₂.map fun q ↦
      (((q.2.2 : ℚ) / D * q.2.1 * d₂ : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hp : toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) :=
    toPoly_pOf a b c
  have hy' : y ^ 2 = aeval x (toPoly (pOf a b c)) := by rw [hp, hy]; simp
  have hp0 : toPoly (pOf a b c) ≠ 0 := by rw [hp]; exact hsq.ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl; apply hne _ hp0; rw [← hy']; ring
  unfold ellDecideMix at h
  split_ifs at h with hval
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hval
  obtain ⟨⟨⟨hv₁, hv₂⟩, hD⟩, hqs⟩ := hval
  obtain ⟨hd₁, hon₁, hnd₁⟩ := classValid_iff.mp hv₁
  obtain ⟨hd₂, hon₂, hnd₂⟩ := classValid_iff.mp hv₂
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂
  have hns := not_sq_of_qsqrt_none hqs
  dsimp only at h
  split at h
  · -- infinite order of the class-`d₂` divisor
    rename_i hT
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    intro hf
    have hnt := EllNL.torsionTest_spec _ _ _ _ fuel false hT
    simp only [Bool.false_eq_true, false_iff] at hnt
    apply hnt
    have hP : ∀ i : Fin pts₂.length, (EllNL.W (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3)).toAffine.Nonsingular
        (d₂ * pts₂[i].1) (d₂ ^ 2 * pts₂[i].2.1) := fun i ↦ by
      have := twist_nonsingular a b c d₂ hd₂ (hon₂ _ (List.getElem_mem i.2))
      exact nonsingular_of _ _ _ ⟨by exact_mod_cast this.2.1, this.2.2⟩
    have hinj : ∀ (l : List (ℚ × ℚ × ℤ)), (l.map Prod.fst).Nodup →
        Set.InjOn (fun i : Fin l.length ↦ l[i].1)
          ((Finset.univ : Finset (Fin l.length)) : Set (Fin l.length)) := by
      intro l hnd i _ j _ hij
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
        (hj := by rw [List.length_map]; exact j.2)).mp (by simp only [List.getElem_map]; exact hij))
    have key := ell_torsion_mixed hC hCall x y hx a b c hsq hy hgen (toPoly B) d₁ d₂ hd₁ hd₂ hns
      (Finset.univ : Finset (Fin pts₁.length)) (Finset.univ : Finset (Fin pts₂.length))
      (fun i ↦ pts₁[i].1) (fun i ↦ pts₁[i].2.1) (fun i ↦ pts₂[i].1) (fun i ↦ pts₂[i].2.1)
      (fun i ↦ (hon₁ _ (List.getElem_mem i.2)).1) hP
      (fun i _ ↦ (hon₁ _ (List.getElem_mem _)).2) (fun i _ ↦ (hon₂ _ (List.getElem_mem _)).2)
      (hinj pts₁ hnd₁) (hinj pts₂ hnd₂) (fun i ↦ pts₁[i].2.2) (fun i ↦ pts₂[i].2.2) D hD (by
        rw [sum_map_eq_fin, sum_map_eq_fin] at hf; exact hf)
    rw [sum_map_eq_fin]
    convert key using 2 with i
    rw [ptTw, ptOf]
    split_ifs with hh
    · rfl
    · exact absurd ⟨by exact_mod_cast (twist_nonsingular a b c d₂ hd₂
        (hon₂ _ (List.getElem_mem _))).2.1, (twist_nonsingular a b c d₂ hd₂
          (hon₂ _ (List.getElem_mem _))).2.2⟩ hh
  · -- torsion: absorb the class-`d₂` residues
    rename_i hT
    split at h
    · rename_i R hR
      have hans := ellDecideTw_spec hC hCall x y hx a b c hsq hy hgen d₁ _ pts₁ D fuel ans h
      rw [hans]
      unfold ellCertTwR at hR
      split at hR
      · exact absurd hR (by simp)
      rename_i AB hAB
      split_ifs at hR with hchk
      simp only [Option.some.injEq] at hR
      subst hR
      set pt := smul (1 / (d₂ : ℚ)) (pOf a b c)
      set cc : ℚ := 1 / ((ordOf ((pts₂.map fun q ↦ q.2.2 • ptTw a b c d₂ q).sum) fuel : ℚ) * D)
      set G := fracG (smul (1 / (d₂ : ℚ)) []) D pts₂
      unfold certCheck at hchk
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, certN, certM] at hchk
      obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
      have hpt : toPoly pt = C (1 / (d₂ : ℚ)) * toPoly (pOf a b c) := toPoly_smul _ _
      have hN' : toPoly AB.1 ^ 2 - C (d₂ : ℚ) * (C (1 / (d₂ : ℚ)) * toPoly AB.2) ^ 2 *
          toPoly (pOf a b c) ≠ 0 := by
        intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
        simp only [toPoly_sub, toPoly_mul, hpt]
        have hdd : C (d₂ : ℚ) * C (1 / (d₂ : ℚ)) = 1 := by
          rw [← C_mul, mul_one_div_cancel hd₂q, C_1]
        linear_combination h0 + C (1 / (d₂ : ℚ)) * toPoly AB.2 ^ 2 * toPoly (pOf a b c) * hdd
      have hG' : toPoly G.2 ≠ 0 := by
        intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
      have hid := (beq_iff _ _).mp hbeq
      have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
        rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
      simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2, hpt] at hid
      set L₁ : E := (pts₁.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 * d₁ : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum
      set f₀ : E := ((d₂ : ℚ) : E)⁻¹ * ((aeval x (toPoly B) + L₁) / y)
      have hred := ell_log_reduce_twist'_add hC x y hx (toPoly (pOf a b c)) hp0 hy' (d₂ : ℚ) hd₂q
        (toPoly G.1) (toPoly G.2) (toPoly AB.1) (C (1 / (d₂ : ℚ)) * toPoly AB.2)
        (toPoly (certR pt AB G cc)) cc hG' hN' (by
          have hdd : C (d₂ : ℚ) * C (1 / (d₂ : ℚ)) = 1 := by
            rw [← C_mul, mul_one_div_cancel hd₂q, C_1]
          simp only [derivative_mul, derivative_C, zero_mul, zero_add] at hid ⊢
          linear_combination hid + C (1 / (d₂ : ℚ)) * toPoly AB.2 ^ 2 * toPoly (pOf a b c) *
            (toPoly G.2 * toPoly (certR pt AB G cc) - toPoly G.1) * hdd) f₀
      obtain ⟨_, hfr⟩ := fracG_spec x hne (smul (1 / (d₂ : ℚ)) []) D pts₂
      have hdE : ((d₂ : ℚ) : E) ≠ 0 := by exact_mod_cast hd₂q
      have hsum₂ : (pts₂.map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 * d₂ : ℚ) : E) /
          (x - ((q.1 : ℚ) : E))).sum = ((d₂ : ℚ) : E) * (pts₂.map fun q ↦
            (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun q _ ↦ ?_
        push_cast; ring
      have hG0 : aeval x (toPoly (smul (1 / (d₂ : ℚ)) ([] : CPoly ℚ))) = 0 := by
        simp [toPoly_smul]
      rw [hG0, zero_add] at hfr
      have e1 : (aeval x (toPoly B) + L₁ + (pts₂.map fun q ↦
          (((q.2.2 : ℚ) / D * q.2.1 * d₂ : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y =
          ((d₂ : ℚ) : E) * (f₀ + aeval x (toPoly G.1) / (aeval x (toPoly G.2) * y)) := by
        rw [hsum₂, ← div_div, hfr]
        simp only [f₀]
        field_simp
      have e2 : (aeval x (toPoly (add B (smul (d₂ : ℚ) (certR pt AB G cc)))) + L₁) / y =
          ((d₂ : ℚ) : E) * (f₀ + aeval x (toPoly (certR pt AB G cc)) / y) := by
        simp only [f₀, toPoly_add, toPoly_smul, map_add, map_mul, aeval_C, eq_ratCast]
        field_simp
        ring
      rw [e1, e2, hasElementaryIntegral_const_mul_iff _ _ (deriv_ratCast_L _) hdE,
        hasElementaryIntegral_const_mul_iff _ _ (deriv_ratCast_L _) hdE, hred]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end Spec

/-! ### Completeness -/

/-- **Completeness of `ellDecideMix`**: with the fuel bounds of both twists it always answers on
valid input. -/
theorem ellDecideMix_ne_none (a b c d₁ d₂ : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly ℚ) (pts₁ pts₂ : List (ℚ × ℚ × ℤ))
    (hv₁ : classValid a b c d₁ pts₁ = true) (hv₂ : classValid a b c d₂ pts₂ = true)
    (D : ℕ) (hD : D ≠ 0) (hns : qsqrt ((d₁ * d₂ : ℤ) : ℚ) = none) (fuel : ℕ)
    (hf₁ : EllNL.fuelBound (a * d₁) (b * d₁ ^ 2) (c * d₁ ^ 3) ≤ fuel)
    (hf₂ : EllNL.fuelBound (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3) ≤ fuel) :
    ellDecideMix a b c d₁ d₂ B pts₁ pts₂ D fuel ≠ none := by
  obtain ⟨hd₁, hon₁, hnd₁⟩ := classValid_iff.mp hv₁
  obtain ⟨hd₂, hon₂, hnd₂⟩ := classValid_iff.mp hv₂
  have hdisc : EllNL.disc (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3) ≠ 0 := by
    rw [disc_twist]
    exact mul_ne_zero (pow_ne_zero _ hd₂) (disc_ne_zero_of_squarefree a b c hsq)
  unfold ellDecideMix
  have hns' : qsqrt ((d₁ : ℚ) * d₂) = none := by exact_mod_cast hns
  rw [if_pos (by simp [hv₁, hv₂, hD, hns'])]
  dsimp only
  have hT := EllNL.torsionTest_isSome' _ _ _ hdisc
    ((pts₂.map fun q ↦ q.2.2 • ptTw a b c d₂ q).sum) fuel hf₂
  split
  · simp
  · rename_i hT'
    obtain ⟨hn, hnS⟩ := ordOf_spec _ fuel (torsionTest_true _ _ _ hT')
    obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp (ellCertTwR_ne_none
      (ellCertTw_ne_none a b c d₂ hd₂ hsq [] pts₂ hon₂ hnd₂ D hD _ hn hnS))
    rw [hR]
    exact ellDecideTw_ne_none a b c d₁ hd₁ hsq _ pts₁ hon₁ hnd₁ D hD fuel hf₁
  · rename_i hT'
    exact absurd hT' hT

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for residues in two quadratic classes** (`d₁ d₂` not a square; points
`(αᵢ, γᵢ√dₖ)` with `dₖγᵢ² = p(αᵢ)`): `ellDecideMix` with the larger of the two twists' fuel bounds
returns `some b`, and `b = true` iff the integral is elementary. -/
theorem ellDecideMix_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (d₁ d₂ : ℤ) (B : CPoly ℚ) (pts₁ pts₂ : List (ℚ × ℚ × ℤ))
    (hv₁ : classValid a b c d₁ pts₁ = true) (hv₂ : classValid a b c d₂ pts₂ = true)
    (D : ℕ) (hD : D ≠ 0) (hns : qsqrt ((d₁ * d₂ : ℤ) : ℚ) = none) :
    ∃ ans : Bool, ellDecideMix a b c d₁ d₂ B pts₁ pts₂ D
        (max (EllNL.fuelBound (a * d₁) (b * d₁ ^ 2) (c * d₁ ^ 3))
          (EllNL.fuelBound (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3))) = some ans ∧
      (ans = true ↔ HasElementaryIntegral ((aeval x (toPoly B) + (pts₁.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 * d₁ : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum + (pts₂.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 * d₂ : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y)) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp (ellDecideMix_ne_none a b c d₁ d₂ hsq B
    pts₁ pts₂ hv₁ hv₂ D hD hns _ (le_max_left _ _) (le_max_right _ _))
  exact ⟨ans, hans, ellDecideMix_spec hC hCall x y hx a b c hsq hy hgen d₁ d₂ B pts₁ pts₂ D _ ans
    hans⟩

end Decision

end EllAlgo
