import RischTragerBronstein.Mixed.NKExactWit

/-!
# Explicit exact parts in a rescaled basis

`exactWRSLW` mirrors `exactWRSL` (`exactWRSLW_isSome`): the witness `(c, Ỹ)` of `exactWLEW` in
the basis `t^{−rᵢ} wᵢ` becomes `(c, Ỹᵢ t^{−rᵢ})` in the basis `w` (`exactWRSLW_valid`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX CPoly

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- Coordinates `Ỹᵢ` in the basis `t^{−rᵢ} wᵢ` as coordinates `Ỹᵢ t^{−rᵢ}` in the basis `w`. -/
def unscaleY (m N : ℕ) (r : ℕ → ℤ) (Y : List (LC (m + 1))) : List (LC (m + 1)) :=
  (List.range N).map fun i ↦ tpowL Fc ks m (-r i) (Y.getD i (MOr Fc ks (m + 1)).zero)

/-- **`exactWRSL` with the witness.** -/
def exactWRSLW (m : ℕ) (η : LC m) (solve : SysSolver m) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) : Option (Option (List ℚ × List (LC (m + 1)))) :=
  let O1 := MOr Fc ks (m + 1)
  let O := MO Fc ks m
  if N = 0 then none else
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O ((f ++ gs.flatten).map Prod.snd)
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst &&
        ((f ++ gs.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst &&
        isMonicC O q && isMonicC O hq) then none
    else
    let A0 : Fin N → Fin N → GPoly (LC m) := matFn (matData fun (j i : Fin N) ↦
      GPoly.mul O ((M.getD i []).getD j O1.zero).1 (cofC O q ((M.getD i []).getD j O1.zero).2).2) []
    match indBound2 Fc ks m (degG O q) N q (DzLC O η O.zero q) A0 with
    | none => none
    | some B =>
      let R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0
      let E := GPoly.mul O (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R)
      (exactWLEW Fc ks m solve N (rescaleM Fc ks m η N Mc r) (rescaleF Fc ks m N f r)
        (gs.map fun g ↦ rescaleF Fc ks m N g r) E).map
          (Option.map fun w ↦ (w.1, unscaleY Fc ks m N r w.2))

lemma map_map_isSome {α β : Type*} (x : Option (Option α)) (g : α → β) :
    (x.map (Option.map g)).map Option.isSome = x.map Option.isSome := by
  cases x with
  | none => rfl
  | some y => cases y <;> rfl

/-- **`exactWRSLW` answers as `exactWRSL`.** -/
theorem exactWRSLW_isSome (m : ℕ) (η : LC m) (solve : SysSolver m) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) :
    (exactWRSLW Fc ks m η solve N Mc f gs r).map Option.isSome =
      exactWRSL Fc ks m η solve N Mc f gs r := by
  unfold exactWRSLW exactWRSL
  dsimp only
  split_ifs
  all_goals try rfl
  split
  · rename_i heq; rw [heq]; rfl
  · rename_i B heq
    rw [heq]
    dsimp only
    rw [map_map_isSome, exactWLEW_isSome]

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ) (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **Every witness returned by `exactWRSLW` is an explicit exact part.** -/
theorem exactWRSLW_valid (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (solve : SysSolver m)
    (hspec : T.SolverSpecB m h1.of_succ ((T.MP m h1.of_succ).sem η) 0 solve)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (w : List ℚ × List (LC (m + 1)))
    (hdec : exactWRSLW Fc ks m η solve N Mc f gs r = some (some w)) :
    T.ExW m h1 N θw f gs w := by
  classical
  unfold exactWRSLW at hdec
  simp only [matFn_matData] at hdec
  split_ifs at hdec with hN0 hcof
  split at hdec
  · exact absurd hdec (by simp)
  rename_i B hB
  obtain ⟨w', hw', hww⟩ := Option.map_eq_some_iff.mp hdec
  obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.mp hww
  rw [hw0] at hw'
  set O1 := MOr Fc ks (m + 1) with hO1
  set O := MO Fc ks m with hO
  set M1 := T.MPr (m + 1) h1 with hM1
  set h0 := h1.of_succ with hh0
  set M := T.MP m h0 with hM
  set Ml : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMl
  set Mw : ℕ → ℕ → T.F (m + 1) := fun i j ↦ M1.sem ((Mc.getD i []).getD j O1.zero) with hMw
  set ent : List (LC (m + 1)) := Ml.flatten with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set hq := lcmGL O ((f ++ gs.flatten).map Prod.snd) with hhq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  set numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2 with hnumF
  have hcof2 : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true ∧
      ((f ++ gs.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst = true ∧ isMonicC O q = true ∧
      isMonicC O hq = true := by
    revert hcof
    cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;>
      cases ((f ++ gs.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst <;> cases isMonicC O q <;>
      cases isMonicC O hq <;> simp
  have hqM := isMonicC_spec M q hcof2.2.2.1
  have hhM := isMonicC_spec M hq hcof2.2.2.2
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hq with hhs
  have hqs0 : qs ≠ 0 := hqM.ne_zero
  have hhs0 : hs ≠ 0 := hhM.ne_zero
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hcofsF : ∀ c ∈ f ++ gs.flatten, (cofC O hq c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hvalF : ∀ c ∈ f ++ gs.flatten,
      (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (numF c)) / T.phi m hs :=
    fun c hc ↦ T.sem_cof m h1 htr hq hhs0 c (hcofsF c hc)
  have hMe : ∀ i < N, ∀ j < N, (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent, List.mem_flatten]
    refine ⟨Ml.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMl] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Ml.getD i []).length := by
        rw [hMl, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Ml.getD i []) _ hlen]; exact List.getElem_mem _
  have hMlij : ∀ i < N, ∀ j < N, (Ml.getD i []).getD j O1.zero = (Mc.getD i []).getD j O1.zero :=
    fun i hi j hj ↦ by rw [hMl, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
  have hMθ : ∀ i < N, ∀ j < N, Mw i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), hMlij i hi j hj]
  have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
  have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
  -- the denominators of the matrix entries
  have hden : ∀ i < N, ∀ j < N,
      T.phi m (GPoly.toPoly M ((Mc.getD i []).getD j O1.zero).2) ≠ 0 := by
    intro i hi j hj h0'
    have hc := hcofs _ (hMe i hi j hj)
    rw [hMlij i hi j hj] at hc
    have hd0 : GPoly.toPoly M ((Mc.getD i []).getD j O1.zero).2 = 0 :=
      T.phi_injective htr (by rw [h0', map_zero])
    have hs' := GPoly.divMod_spec M q ((Mc.getD i []).getD j O1.zero).2
    have hr0 := (GPoly.isZero_iff M _).mp hc
    rw [hr0, add_zero, hd0, mul_zero] at hs'
    exact hqs0 hs'
  -- the rescaled basis
  set θt : ℕ → L := fun i ↦ ((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i with hθt
  have hwt := T.rescale_deriv h1 hm hk htr N Mc r θw hw hden
  have hindt := T.rescale_ind htr N r θw hind
  have hv := T.exactWLEW_valid m h1 htr _ ((T.MP m h0).sem η) 0 hspec N
    (rescaleM Fc ks m η N Mc r) (rescaleF Fc ks m N f r) θt hwt hindt
    (gs.map fun g ↦ rescaleF Fc ks m N g r) _ w0 hw'
  have hcast : ∀ x : ℚ, ((x : ℚ) : L) = algebraMap Cc L ((x : ℚ) : Cc) := fun x ↦
    (map_ratCast _ x).symm
  unfold ExW at hv ⊢
  simp only [hcast] at hv ⊢
  rw [T.rescale_rhsL m h1 htr N f gs r θw] at hv
  rw [← hv]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  simp only [unscaleY]
  rw [NestTower.getD_range_map _ _ hi', T.sem_tpowL m h1 htr, hθt]
  push_cast
  ring

end MTower

end Curves.MT
