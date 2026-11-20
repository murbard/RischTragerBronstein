import RischTragerBronstein.Algebraic.EllMulti
import RischTragerBronstein.Algebraic.EllAlgoMix

/-!
# The decision procedure for residues in any number of quadratic classes

`ellDecideMulti a b c B ((d₁, pts₁) :: rest) D fuel`: for every class `(d, pts)` of `rest`, the
Nagell–Lutz test on the twist by `d` (infinite order ⇒ not elementary, `ell_torsion_multi`), else
its certificate remainder `R` is folded into `B ← B + d R` (`ellCertTwR_fold`); finally
`ellDecideTw` decides the class `d₁`. `ellDecideMulti_spec`: every answer is correct;
`ellDecideMulti_ne_none`: with enough fuel it always answers.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace EllAlgo

open CPoly

/-- The residue sum of one class. -/
noncomputable def classSum {E : Type*} [Field E] (x : E) (D : ℕ) (d : ℤ)
    (pts : List (ℚ × ℚ × ℤ)) : E :=
  (pts.map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 * d : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum

section Fold

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Folding one class**: its certificate remainder `R` replaces its residues. -/
theorem ellCertTwR_fold (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (d : ℤ) (hd : d ≠ 0)
    (pts : List (ℚ × ℚ × ℤ)) (D n : ℕ) (R : CPoly ℚ) (hR : ellCertTwR a b c d pts D n = some R)
    (B : CPoly ℚ) (other : E) :
    HasElementaryIntegral ((aeval x (toPoly B) + other + classSum x D d pts) / y) ↔
      HasElementaryIntegral ((aeval x (toPoly (add B (smul (d : ℚ) R))) + other) / y) := by
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
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  unfold ellCertTwR at hR
  split at hR
  · exact absurd hR (by simp)
  rename_i AB hAB
  split_ifs at hR with hchk
  simp only [Option.some.injEq] at hR
  subst hR
  set pt := smul (1 / (d : ℚ)) (pOf a b c)
  set cc : ℚ := 1 / ((n : ℚ) * D)
  set G := fracG (smul (1 / (d : ℚ)) []) D pts
  unfold certCheck at hchk
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, certN, certM] at hchk
  obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
  have hpt : toPoly pt = C (1 / (d : ℚ)) * toPoly (pOf a b c) := toPoly_smul _ _
  have hN' : toPoly AB.1 ^ 2 - C (d : ℚ) * (C (1 / (d : ℚ)) * toPoly AB.2) ^ 2 *
      toPoly (pOf a b c) ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
    simp only [toPoly_sub, toPoly_mul, hpt]
    have hdd : C (d : ℚ) * C (1 / (d : ℚ)) = 1 := by
      rw [← C_mul, mul_one_div_cancel hdq, C_1]
    linear_combination h0 + C (1 / (d : ℚ)) * toPoly AB.2 ^ 2 * toPoly (pOf a b c) * hdd
  have hG' : toPoly G.2 ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
  have hid := (beq_iff _ _).mp hbeq
  have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2, hpt] at hid
  set f₀ : E := ((d : ℚ) : E)⁻¹ * ((aeval x (toPoly B) + other) / y)
  have hred := ell_log_reduce_twist'_add hC x y hx (toPoly (pOf a b c)) hp0 hy' (d : ℚ) hdq
    (toPoly G.1) (toPoly G.2) (toPoly AB.1) (C (1 / (d : ℚ)) * toPoly AB.2)
    (toPoly (certR pt AB G cc)) cc hG' hN' (by
      have hdd : C (d : ℚ) * C (1 / (d : ℚ)) = 1 := by
        rw [← C_mul, mul_one_div_cancel hdq, C_1]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add] at hid ⊢
      linear_combination hid + C (1 / (d : ℚ)) * toPoly AB.2 ^ 2 * toPoly (pOf a b c) *
        (toPoly G.2 * toPoly (certR pt AB G cc) - toPoly G.1) * hdd) f₀
  obtain ⟨_, hfr⟩ := fracG_spec x hne (smul (1 / (d : ℚ)) []) D pts
  have hdE : ((d : ℚ) : E) ≠ 0 := by exact_mod_cast hdq
  have hsum : classSum x D d pts = ((d : ℚ) : E) * (pts.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum := by
    unfold classSum
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun q _ ↦ ?_
    push_cast; ring
  have hG0 : aeval x (toPoly (smul (1 / (d : ℚ)) ([] : CPoly ℚ))) = 0 := by
    simp [toPoly_smul]
  rw [hG0, zero_add] at hfr
  have e1 : (aeval x (toPoly B) + other + classSum x D d pts) / y =
      ((d : ℚ) : E) * (f₀ + aeval x (toPoly G.1) / (aeval x (toPoly G.2) * y)) := by
    rw [hsum, ← div_div, hfr]
    simp only [f₀]
    field_simp
  have e2 : (aeval x (toPoly (add B (smul (d : ℚ) (certR pt AB G cc)))) + other) / y =
      ((d : ℚ) : E) * (f₀ + aeval x (toPoly (certR pt AB G cc)) / y) := by
    simp only [f₀, toPoly_add, toPoly_smul, map_add, map_mul, aeval_C, eq_ratCast]
    field_simp
    ring
  rw [e1, e2, hasElementaryIntegral_const_mul_iff _ _ (deriv_ratCast_L _) hdE,
    hasElementaryIntegral_const_mul_iff _ _ (deriv_ratCast_L _) hdE, hred]

end Fold

/-! ### The procedure -/

/-- Fold the classes of `rest` into `B`: `some none` = not elementary, `some (some B′)` = the
reduced polynomial part, `none` = out of fuel / failure. -/
def multiStep (a b c : ℤ) (D fuel : ℕ) :
    CPoly ℚ → List (ℤ × List (ℚ × ℚ × ℤ)) → Option (Option (CPoly ℚ))
  | B, [] => some (some B)
  | B, (d, pts) :: rest =>
    match EllNL.torsionTest (a * d) (b * d ^ 2) (c * d ^ 3)
        ((pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum) fuel with
    | some false => some none
    | some true =>
      match ellCertTwR a b c d pts D (ordOf ((pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum) fuel) with
      | some R => multiStep a b c D fuel (add B (smul (d : ℚ) R)) rest
      | none => none
    | none => none

/-- All the points, tagged with their class. -/
def flatPts (cls : List (ℤ × List (ℚ × ℚ × ℤ))) : List (ℤ × ℚ × ℚ × ℤ) :=
  cls.flatMap fun q ↦ q.2.map fun r ↦ (q.1, r)

/-- Validity of a list of classes. -/
def classesOk (a b c : ℤ) (cls : List (ℤ × List (ℚ × ℚ × ℤ))) : Bool :=
  cls.all (fun q ↦ classValid a b c q.1 q.2) &&
    decide (cls.Pairwise fun q q' ↦ qsqrt ((q.1 * q'.1 : ℤ) : ℚ) = none) &&
    decide ((flatPts cls).map fun r ↦ r.2.1).Nodup

/-- **The decision procedure for residues in any number of quadratic classes.** -/
def ellDecideMulti (a b c : ℤ) (B : CPoly ℚ) (cls : List (ℤ × List (ℚ × ℚ × ℤ))) (D fuel : ℕ) :
    Option Bool :=
  match cls with
  | [] => none
  | (d₁, pts₁) :: rest =>
    if classesOk a b c ((d₁, pts₁) :: rest) && decide (D ≠ 0) then
      match multiStep a b c D fuel B rest with
      | some none => some false
      | some (some B') => ellDecideTw a b c d₁ B' pts₁ D fuel
      | none => none
    else none

lemma sum_classSum {E : Type*} [Field E] (x : E) (D : ℕ) :
    ∀ cls : List (ℤ × List (ℚ × ℚ × ℤ)), (cls.map fun q ↦ classSum x D q.1 q.2).sum =
      ((flatPts cls).map fun r ↦ (((r.2.2.2 : ℚ) / D * r.2.2.1 * r.1 : ℚ) : E) /
        (x - ((r.2.1 : ℚ) : E))).sum
  | [] => by simp [flatPts]
  | q :: t => by
    rw [List.map_cons, List.sum_cons, sum_classSum x D t]
    simp only [flatPts, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, classSum]

/-! ### Completeness -/

lemma multiStep_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (D : ℕ) (hD : D ≠ 0) (fuel : ℕ) :
    ∀ (rest : List (ℤ × List (ℚ × ℚ × ℤ))) (B : CPoly ℚ),
      (∀ q ∈ rest, classValid a b c q.1 q.2 = true) →
      (∀ q ∈ rest, EllNL.fuelBound (a * q.1) (b * q.1 ^ 2) (c * q.1 ^ 3) ≤ fuel) →
      multiStep a b c D fuel B rest ≠ none
  | [], B, _, _ => by simp [multiStep]
  | (d, pts) :: rest, B, hv, hf => by
    obtain ⟨hd, hon, hnd⟩ := classValid_iff.mp (hv (d, pts) List.mem_cons_self)
    have hdisc : EllNL.disc (a * d) (b * d ^ 2) (c * d ^ 3) ≠ 0 := by
      rw [disc_twist]
      exact mul_ne_zero (pow_ne_zero _ hd) (disc_ne_zero_of_squarefree a b c hsq)
    have hT := EllNL.torsionTest_isSome' _ _ _ hdisc
      ((pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum) fuel
      (by simpa only using hf (d, pts) List.mem_cons_self)
    unfold multiStep
    split
    · simp
    · rename_i hT'
      obtain ⟨hn, hnS⟩ := ordOf_spec _ fuel (torsionTest_true _ _ _ hT')
      obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp (ellCertTwR_ne_none
        (ellCertTw_ne_none a b c d hd hsq [] pts hon hnd D hD _ hn hnS))
      rw [hR]
      exact multiStep_ne_none a b c hsq D hD fuel rest _
        (fun q hq ↦ hv q (List.mem_cons_of_mem _ hq)) (fun q hq ↦ hf q (List.mem_cons_of_mem _ hq))
    · rename_i hT'
      exact absurd hT' hT

/-- **Completeness of `ellDecideMulti`.** -/
theorem ellDecideMulti_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly ℚ) (cls : List (ℤ × List (ℚ × ℚ × ℤ))) (hne : cls ≠ [])
    (hok : classesOk a b c cls = true) (D : ℕ) (hD : D ≠ 0) (fuel : ℕ)
    (hf : ∀ q ∈ cls, EllNL.fuelBound (a * q.1) (b * q.1 ^ 2) (c * q.1 ^ 3) ≤ fuel) :
    ellDecideMulti a b c B cls D fuel ≠ none := by
  obtain ⟨⟨d₁, pts₁⟩, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hv : ∀ q ∈ (d₁, pts₁) :: rest, classValid a b c q.1 q.2 = true := by
    unfold classesOk at hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.1.1
  obtain ⟨hd₁, hon₁, hnd₁⟩ := classValid_iff.mp (hv _ List.mem_cons_self)
  unfold ellDecideMulti
  dsimp only
  rw [if_pos (by simp [hok, hD])]
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (multiStep_ne_none a b c hsq D hD fuel rest B
    (fun q hq ↦ hv q (List.mem_cons_of_mem _ hq)) (fun q hq ↦ hf q (List.mem_cons_of_mem _ hq)))
  rw [hr]
  rcases r with _ | B'
  · simp
  · have hf1 : EllNL.fuelBound (a * d₁) (b * d₁ ^ 2) (c * d₁ ^ 3) ≤ fuel := by
      simpa only using hf (d₁, pts₁) List.mem_cons_self
    exact ellDecideTw_ne_none a b c d₁ hd₁ hsq B' pts₁ hon₁ hnd₁ D hD fuel hf1

/-! ### Correctness -/

lemma classesOk_iff {a b c : ℤ} {cls : List (ℤ × List (ℚ × ℚ × ℤ))} :
    classesOk a b c cls = true ↔ (∀ q ∈ cls, classValid a b c q.1 q.2 = true) ∧
      cls.Pairwise (fun q q' ↦ qsqrt ((q.1 * q'.1 : ℤ) : ℚ) = none) ∧
      ((flatPts cls).map fun r ↦ r.2.1).Nodup := by
  simp only [classesOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

lemma qsqrt_sq_ne_none (d : ℤ) : qsqrt ((d * d : ℤ) : ℚ) ≠ none := by
  intro h
  have := qsqrt_sq (d : ℚ)
  rw [show ((d : ℚ) ^ 2) = ((d * d : ℤ) : ℚ) by push_cast; ring, h] at this
  exact Bool.false_ne_true this

lemma classesOk_drop {a b c : ℤ} {c₁ x : ℤ × List (ℚ × ℚ × ℤ)} {rest : List (ℤ × List (ℚ × ℚ × ℤ))}
    (h : classesOk a b c (c₁ :: x :: rest) = true) : classesOk a b c (c₁ :: rest) = true := by
  rw [classesOk_iff] at h ⊢
  obtain ⟨hv, hp, hn⟩ := h
  refine ⟨fun q hq ↦ hv q ?_, ?_, ?_⟩
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  · exact hp.sublist ((List.sublist_cons_self x rest).cons₂ c₁)
  · refine hn.sublist ?_
    apply List.Sublist.map
    simp only [flatPts, List.flatMap_cons]
    exact List.Sublist.append_left (List.sublist_append_right _ _) _

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- The integrand of a list of classes. -/
noncomputable def integrandM (x y : E) (D : ℕ) (B : CPoly ℚ)
    (cls : List (ℤ × List (ℚ × ℚ × ℤ))) : E :=
  (aeval x (toPoly B) + (cls.map fun q ↦ classSum x D q.1 q.2).sum) / y

set_option maxHeartbeats 3200000 in
/-- **A class of infinite order forbids an elementary integral.** -/
lemma not_elem_of_class (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (D : ℕ) (hD : D ≠ 0) (B : CPoly ℚ) (c₁ : ℤ × List (ℚ × ℚ × ℤ)) (d : ℤ)
    (pts : List (ℚ × ℚ × ℤ)) (rest : List (ℤ × List (ℚ × ℚ × ℤ)))
    (hok : classesOk a b c (c₁ :: (d, pts) :: rest) = true)
    (hnt : ¬IsOfFinAddOrder (pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum) :
    ¬HasElementaryIntegral (integrandM x y D B (c₁ :: (d, pts) :: rest)) := by
  classical
  intro hf
  obtain ⟨hv, hp, hn⟩ := classesOk_iff.mp hok
  set cls := c₁ :: (d, pts) :: rest with hcls
  set others := c₁ :: rest with hothers
  set flat := flatPts others with hflat
  obtain ⟨hd, hon, hnd⟩ := classValid_iff.mp (hv (d, pts) (List.mem_cons_of_mem _ List.mem_cons_self))
  -- the relation `R` is symmetric, and separates all the classes from `d`
  have hsymm : Symmetric (fun q q' : ℤ × List (ℚ × ℚ × ℤ) ↦ qsqrt ((q.1 * q'.1 : ℤ) : ℚ) = none) :=
    fun q q' h ↦ by simpa only [mul_comm] using h
  have hsepd : ∀ q ∈ others, qsqrt ((q.1 * d : ℤ) : ℚ) = none := by
    intro q hq
    rw [List.pairwise_cons, List.pairwise_cons] at hp
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp.1 (d, pts) List.mem_cons_self
    · exact hsymm (hp.2.1 q hq)
  have hne_d : ∀ q ∈ others, q.1 ≠ d := fun q hq h ↦ by
    have := hsepd q hq; rw [h] at this; exact qsqrt_sq_ne_none d this
  have hmemflat : ∀ r ∈ flat, ∃ q ∈ others, r.1 = q.1 ∧ r.2 ∈ q.2 := by
    intro r hr
    simp only [hflat, flatPts, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨q, hq, r', hr', rfl⟩ := hr
    exact ⟨q, hq, rfl, hr'⟩
  have hothers_sub : ∀ q ∈ others, q ∈ cls := fun q hq ↦ by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  set Kl : Finset ℤ := (cls.map Prod.fst).toFinset with hKl
  have hKl_mem : ∀ q ∈ cls, q.1 ∈ Kl := fun q hq ↦
    List.mem_toFinset.mpr (List.mem_map_of_mem hq)
  have hdk : ∀ k ∈ Kl, k ≠ 0 := fun k hk ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact (classValid_iff.mp (hv q hq)).1
  have hclsK : ∀ k ∈ Kl, ∀ k' ∈ Kl, k ≠ k' → ∀ q : ℚ, ((id k * id k' : ℤ) : ℚ) ≠ q ^ 2 := by
    intro k hk k' hk' hkk'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk')
    haveI : Std.Symm (fun q q' : ℤ × List (ℚ × ℚ × ℤ) ↦ qsqrt ((q.1 * q'.1 : ℤ) : ℚ) = none) :=
      ⟨fun _ _ h ↦ hsymm h⟩
    exact not_sq_of_qsqrt_none (hp.forall hq hq' (fun h ↦ hkk' (by rw [h])))
  have hP : ∀ i : Fin pts.length, (EllNL.W (a * d) (b * d ^ 2) (c * d ^ 3)).toAffine.Nonsingular
      (d * pts[i].1) (d ^ 2 * pts[i].2.1) := fun i ↦ by
    have := twist_nonsingular a b c d hd (hon _ (List.getElem_mem i.2))
    exact nonsingular_of _ _ _ ⟨by exact_mod_cast this.2.1, this.2.2⟩
  have hflat_i : ∀ i : Fin flat.length, ∃ q ∈ others, flat[i].1 = q.1 ∧ flat[i].2 ∈ q.2 :=
    fun i ↦ hmemflat _ (List.getElem_mem i.2)
  have hnd_flat : (flat.map fun r ↦ r.2.1).Nodup := by
    refine hn.sublist (List.Sublist.map _ ?_)
    simp only [hflat, flatPts, List.flatMap_cons]
    exact List.Sublist.append_left (List.sublist_append_right _ _) _
  have hinj : ∀ (l : List (ℚ × ℚ × ℤ)), (l.map Prod.fst).Nodup →
      Set.InjOn (fun i : Fin l.length ↦ l[i].1)
        ((Finset.univ : Finset (Fin l.length)) : Set (Fin l.length)) := by
    intro l hnd i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
      (hj := by rw [List.length_map]; exact j.2)).mp (by simp only [List.getElem_map]; exact hij))
  have hinj₁ : Set.InjOn (fun i : Fin flat.length ↦ flat[i].2.1)
      ((Finset.univ : Finset (Fin flat.length)) : Set (Fin flat.length)) := by
    intro i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd_flat (hi := by rw [List.length_map]; exact i.2)
      (hj := by rw [List.length_map]; exact j.2)).mp (by simp only [List.getElem_map]; exact hij))
  have key := ell_torsion_multi hC hCall x y hx a b c hsq hy hgen (toPoly B) Kl id hdk hclsK d
    (hKl_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (Finset.univ : Finset (Fin flat.length)) (Finset.univ : Finset (Fin pts.length))
    (fun i ↦ flat[i].1)
    (fun i ↦ by
      obtain ⟨q, hq, h1, -⟩ := hflat_i i
      exact ⟨by rw [h1]; exact hKl_mem q (hothers_sub q hq), by rw [h1]; exact hne_d q hq⟩)
    (fun i ↦ flat[i].2.1) (fun i ↦ flat[i].2.2.1) (fun i ↦ pts[i].1) (fun i ↦ pts[i].2.1)
    (fun i ↦ by
      obtain ⟨q, hq, h1, h2⟩ := hflat_i i
      have := ((classValid_iff.mp (hv q (hothers_sub q hq))).2.1 _ h2).1
      simp only [id, h1]; exact this)
    hP
    (fun i _ ↦ by
      obtain ⟨q, hq, h1, h2⟩ := hflat_i i
      exact ((classValid_iff.mp (hv q (hothers_sub q hq))).2.1 _ h2).2)
    (fun i _ ↦ (hon _ (List.getElem_mem _)).2) hinj₁ (hinj pts hnd)
    (fun i ↦ flat[i].2.2.2) (fun i ↦ pts[i].2.2) D hD (by
      have h1 : (others.map fun q ↦ classSum x D q.1 q.2).sum = ∑ i : Fin flat.length,
          (((flat[i].2.2.2 : ℚ) / D * flat[i].2.2.1 * flat[i].1 : ℚ) : E) /
            (x - ((flat[i].2.1 : ℚ) : E)) := by
        rw [sum_classSum, sum_map_eq_fin]
      have h2 : classSum x D d pts = ∑ i : Fin pts.length,
          (((pts[i].2.2 : ℚ) / D * pts[i].2.1 * d : ℚ) : E) / (x - ((pts[i].1 : ℚ) : E)) := by
        unfold classSum; rw [sum_map_eq_fin]
      have h3 : (cls.map fun q ↦ classSum x D q.1 q.2).sum =
          (others.map fun q ↦ classSum x D q.1 q.2).sum + classSum x D d pts := by
        simp only [hcls, hothers, List.map_cons, List.sum_cons]; ring
      have e : integrandM x y D B cls = (aeval x (toPoly B) + ∑ i : Fin flat.length,
          (((flat[i].2.2.2 : ℚ) / D * flat[i].2.2.1 * flat[i].1 : ℚ) : E) /
            (x - ((flat[i].2.1 : ℚ) : E)) + ∑ i : Fin pts.length,
          (((pts[i].2.2 : ℚ) / D * pts[i].2.1 * d : ℚ) : E) /
            (x - ((pts[i].1 : ℚ) : E))) / y := by
        unfold integrandM
        rw [h3, h1, h2, add_assoc]
      simp only [id]; rw [← e]; exact hf)
  dsimp only [id] at key
  apply hnt
  rw [sum_map_eq_fin]
  convert key using 2 with i
  rw [ptTw, ptOf]
  split_ifs with hh
  · rfl
  · exact absurd ⟨by exact_mod_cast (twist_nonsingular a b c d hd
      (hon _ (List.getElem_mem _))).2.1, (twist_nonsingular a b c d hd
        (hon _ (List.getElem_mem _))).2.2⟩ hh

/-- **What `multiStep` means.** -/
theorem multiStep_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (D : ℕ) (hD : D ≠ 0) (fuel : ℕ) (c₁ : ℤ × List (ℚ × ℚ × ℤ)) :
    ∀ (rest : List (ℤ × List (ℚ × ℚ × ℤ))) (B : CPoly ℚ) (r : Option (CPoly ℚ)),
      multiStep a b c D fuel B rest = some r → classesOk a b c (c₁ :: rest) = true →
      (r = none → ¬HasElementaryIntegral (integrandM x y D B (c₁ :: rest))) ∧
      (∀ B', r = some B' → (HasElementaryIntegral (integrandM x y D B (c₁ :: rest)) ↔
        HasElementaryIntegral (integrandM x y D B' [c₁])))
  | [], B, r, h, _ => by
    simp only [multiStep, Option.some.injEq] at h
    subst h
    exact ⟨fun h ↦ by simp at h, fun B' hB' ↦ by simp only [Option.some.injEq] at hB'; subst hB'; rfl⟩
  | (d, pts) :: rest, B, r, h, hok => by
    have hok' := classesOk_drop hok
    obtain ⟨hv, -, -⟩ := classesOk_iff.mp hok
    obtain ⟨hd, -, -⟩ := classValid_iff.mp (hv (d, pts) (List.mem_cons_of_mem _ List.mem_cons_self))
    unfold multiStep at h
    split at h
    · rename_i hT
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨fun _ ↦ ?_, fun B' h ↦ by simp at h⟩
      have hnt := EllNL.torsionTest_spec _ _ _ _ fuel false hT
      simp only [Bool.false_eq_true, false_iff] at hnt
      exact not_elem_of_class hC hCall x y hx a b c hsq hy hgen D hD B c₁ d pts rest hok hnt
    · split at h
      · rename_i R hR
        have ih := multiStep_spec hC hCall x y hx a b c hsq hy hgen D hD fuel c₁ rest _ r h hok'
        have hfold := ellCertTwR_fold hC x y hx a b c hsq hy d hd pts D _ R hR B
          ((c₁ :: rest).map fun q ↦ classSum x D q.1 q.2).sum
        have e1 : integrandM x y D B (c₁ :: (d, pts) :: rest) =
            (aeval x (toPoly B) + ((c₁ :: rest).map fun q ↦ classSum x D q.1 q.2).sum +
              classSum x D d pts) / y := by
          unfold integrandM
          simp only [List.map_cons, List.sum_cons]
          ring
        have e2 : integrandM x y D (add B (smul (d : ℚ) R)) (c₁ :: rest) =
            (aeval x (toPoly (add B (smul (d : ℚ) R))) +
              ((c₁ :: rest).map fun q ↦ classSum x D q.1 q.2).sum) / y := rfl
        rw [e1, hfold, ← e2]
        exact ih
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **Correctness of `ellDecideMulti`.** -/
theorem ellDecideMulti_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (B : CPoly ℚ) (cls : List (ℤ × List (ℚ × ℚ × ℤ))) (D fuel : ℕ) (ans : Bool)
    (h : ellDecideMulti a b c B cls D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (integrandM x y D B cls) := by
  unfold ellDecideMulti at h
  split at h
  · exact absurd h (by simp)
  rename_i d₁ pts₁ rest
  split_ifs at h with hval
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hval
  obtain ⟨hok, hD⟩ := hval
  split at h
  · rename_i hm
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    exact (multiStep_spec hC hCall x y hx a b c hsq hy hgen D hD fuel (d₁, pts₁) rest B none hm
      hok).1 rfl
  · rename_i B' hm
    rw [((multiStep_spec hC hCall x y hx a b c hsq hy hgen D hD fuel (d₁, pts₁) rest B _ hm
      hok).2 B' rfl)]
    have := ellDecideTw_spec hC hCall x y hx a b c hsq hy hgen d₁ B' pts₁ D fuel ans h
    rw [this]
    unfold integrandM classSum
    simp
  · exact absurd h (by simp)

end Spec

end EllAlgo
