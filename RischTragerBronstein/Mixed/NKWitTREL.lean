import RischTragerBronstein.Mixed.NKWitTRE
import RischTragerBronstein.Mixed.NKWitRNTR

/-!
# Exponential level, several places at infinity over `ℚ(α)`: the antiderivative

`exactWRELW`, `exactTRELW`: `exactWREW`, `exactTREW` with parameters `gs`; every witness is an
explicit exact part (`exactWRELW_valid`, `exactTRELW_valid`). `nk_integrateETRNTRE` makes
`nk_decidesETRNTRE` constructive, with the explicit form `NKExplRN` (`rn_explicit`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM CPoly NCodes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **`exactWREL` with the witness.** -/
def exactWRELW (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) (N0 : ℕ)
    (C Ci : List (List ℚ)) : Option (Option (List ℚ × List (LC (m + 1)))) :=
  let O1 := MOr Fc ks (m + 1)
  let O := MO Fc ks m
  let bc := O.deriv a
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
    if O.isZero (q.getD 0 O.zero) then none else
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
      GPoly.mul O ((M.getD i []).getD j O1.zero).1 (cofC O q ((M.getD i []).getD j O1.zero).2).2
    if !(zeroOKE Fc ks m bc N N0 q A0 C Ci) then none
    else
    match indBound2 Fc ks m (degG O q) N q (DzLC O O.zero bc q) A0 with
    | none => none
    | some B =>
      let R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0
      let E := GPoly.mul O (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R)
      (exactWLEW Fc ks m (fun n A0 q hh G0 ↦ expSysB Fc ks m a rdeD n A0 q hh G0 0) N
        ((conjM Fc ks m N C (rescaleME Fc ks m bc N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m))
        ((vecCi Fc ks m N (rescaleF Fc ks m N f r) Ci).map (redC Fc ks m))
        (gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map (redC Fc ks m)) E).map
          (Option.map fun w ↦ (w.1, unconjY Fc ks m N r C w.2))

theorem exactWRELW_isSome (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) (N0 : ℕ)
    (C Ci : List (List ℚ)) :
    (exactWRELW Fc ks m a rdeD N Mc f gs r N0 C Ci).map Option.isSome =
      exactWREL Fc ks m a rdeD N Mc f gs r N0 C Ci := by
  unfold exactWRELW exactWREL
  dsimp only
  split_ifs
  all_goals try rfl
  rcases indBound2 Fc ks m (degG (MO Fc ks m) _) N _ _ _ with _ | B
  · rfl
  · dsimp only
    rw [map_map_isSome, exactWLEW_isSome, exactWEL_eq]

/-- **`exactTREL` with the witness.** -/
def exactTRELW (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (r : ℕ → ℤ)
    (N0 : ℕ) (C Ci : List (List ℚ)) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  let O1 := MOr Fc ks (m + 1)
  let N := P.length - 1
  let tm : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Tc.getD i []).getD j O1.zero
  let ti : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Ti.getD i []).getD j O1.zero
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 ||
    !(prodIdC Fc ks m N tm ti && prodIdC Fc ks m N ti tm) then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let mθ : ℕ → ℕ → LC (m + 1) := fun i j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let Mw := (List.range N).map fun i ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv (tm i l))
        (lsumC O1 ((List.range N).map fun k ↦ O1.mul (tm i k) (mθ k l)))) (ti l j))
    let cw : List (LC (m + 1)) → List (LC (m + 1)) := fun g ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun k ↦ O1.mul (g.getD k O1.zero) (ti k j))
    (exactWRELW Fc ks m a rdeD N (Mw.map fun l ↦ l.map (redC Fc ks m))
      ((cw f).map (redC Fc ks m)) (gs.map fun g ↦ (cw g).map (redC Fc ks m)) r N0 C Ci).map
        (Option.map fun w ↦ (w.1, thetaY Fc ks m N Tc w.2))


theorem exactTRELW_isSome (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    (exactTRELW Fc ks m a rdeD r N0 C Ci P Tc Ti f gs).map Option.isSome =
      exactTREL Fc ks m a rdeD r N0 C Ci P Tc Ti f gs := by
  unfold exactTRELW exactTREL exactTGL
  dsimp only
  split_ifs
  all_goals try rfl
  rcases dThetaC (MOr Fc ks (m + 1)) P with _ | dθ
  · rfl
  · dsimp only
    rw [map_map_isSome, exactWRELW_isSome]
    simp only [List.map_map, Function.comp_def]

/-- The exact part of a candidate with parameters, with the witness. -/
def trelExW (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (c : CandTRE) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTRELW Fc ks m a rdeD (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.1 c.2.2.2.2.1
    c.2.2.2.2.2 P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f gs

lemma searchTREL_eq (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (B : ℕ) :
    searchTREL Fc ks m a rdeD P f gs B = searchPS (fun _ ↦ true)
      (fun c : CandTRE ↦ exactTREL Fc ks m a rdeD (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.1
        c.2.2.2.2.1 c.2.2.2.2.2 P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f gs) [] B := by
  unfold searchTREL searchPS searchS
  simp only [List.findSome?_nil]
  congr 1
  funext k
  cases (Encodable.decode k : Option CandTRE) with
  | none => rfl
  | some c => rfl

/-- **The constructive decision** (constant curves, several places at infinity over `ℚ(α)`,
exponential level). -/
def nkETRNTRW (lv : (m : ℕ) → LC m) (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m)))
    (gss : List (List (GPoly (LC (m + 1))))) (s : List (LC (m + 1))) (fp : List (GPoly (LC m)))
    (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (fun _ ↦ true) (trelExW Fc ks m a (rdeE Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
      gss.flatten) [] N)

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ) (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **Every witness returned by `exactWRELW` is an explicit exact part.** -/
theorem exactWRELW_valid (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
      ((T.MP m h1.of_succ).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) (N0 : ℕ)
    (C Ci : List (List ℚ)) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (wt : List ℚ × List (LC (m + 1)))
    (hres : exactWRELW Fc ks m a rdeD N Mc f gs r N0 C Ci = some (some wt)) :
    T.ExW m h1 N θw f gs wt := by
  classical
  unfold exactWRELW at hres
  simp only at hres
  split_ifs at hres with hN0 hcof hq0c hzc
  split at hres
  · exact absurd hres (by simp)
  rename_i B hB
  obtain ⟨w', hw', hww⟩ := Option.map_eq_some_iff.mp hres
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
  have hcofsF : ∀ c ∈ f, (cofC O hq c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.2.1 _ (List.mem_map.mpr ⟨c, List.mem_append_left _ hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hvalF : ∀ c ∈ f, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (numF c)) / T.phi m hs :=
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
  have hfv : ∀ j, (M1.sem (f.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (numF (f.getD j O1.zero))) / T.phi m hs := by
    intro j
    by_cases hj : j < f.length
    · refine hvalF _ ?_
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnumF]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
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
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  -- the checks at `t = 0`
  set b := (T.MP m h0).sem ((MO Fc ks m).deriv a) with hb
  have hq0 : qs.coeff 0 ≠ 0 := by
    rw [hqs, coeff_toPoly_sem]
    intro h0'
    exact hq0c ((M.isZero_iff _).mpr h0')
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hzc
  obtain ⟨hA0z, hN0pos, hP, hCCi, hCiC⟩ := T.zeroOKE_spec m h0 _ N N0 q _ C Ci hzc
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  -- the rescaled and conjugated basis
  set θt : ℕ → L := fun i ↦ ((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i with hθt
  have hwt := T.rescale_derivE h1 hm hk htr N Mc r θw hw hden
  have hindt := T.rescale_ind htr N r θw hind
  set θc : ℕ → L := fun l ↦ ∑ i ∈ Finset.range N, (qget C l i : L) * θt i with hθc
  have hwc0 := T.conj_deriv h1 N C Ci hCiC _ θt hwt
  have hwc : ∀ k < N, (θc k)′ = ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
      ((((conjM Fc ks m N C (rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r) Ci).map fun l ↦
        l.map (redC Fc ks m)).getD k []).getD l (MOr Fc ks (m + 1)).zero) : L) * θc l := by
    intro k hk
    rw [hwc0 k hk]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have hindc := T.conj_ind N C Ci hCCi θt hindt
  have hspec := T.expSpecB hm h0 hk rdeD hrdeD hom
  have hv := T.exactWLEW_valid m h1 htr _ 0 b hspec N _ _ θc hwc hindc
    (gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map (redC Fc ks m)) _ w0 hw'
  have hrhsV : ∀ v : List (LC (m + 1)), ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
      (((vecCi Fc ks m N (rescaleF Fc ks m N v r) Ci).map (redC Fc ks m)).getD l
        (MOr Fc ks (m + 1)).zero) : L) * θc l =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (v.getD j (MOr Fc ks (m + 1)).zero) : L) *
        θw j := by
    intro v
    simp only [T.sem_getD_map_redC m h1 htr]
    rw [T.conj_rhs h1 N C Ci hCiC _ θt, T.rescale_rhs h1 htr N v r θw]
  have hsplit : ∀ (v : List (LC (m + 1))) (us : List (List (LC (m + 1)))) (θx : ℕ → L)
      (cq : ℕ → L), ∑ j ∈ Finset.range N, (((T.MPr (m + 1) h1).sem (v.getD j O1.zero) : L) -
        ∑ i ∈ Finset.range us.length, cq i *
          ((T.MPr (m + 1) h1).sem ((us.getD i []).getD j O1.zero) : L)) * θx j =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (v.getD j O1.zero) : L) * θx j -
        ∑ i ∈ Finset.range us.length, cq i * ∑ j ∈ Finset.range N,
          ((T.MPr (m + 1) h1).sem ((us.getD i []).getD j O1.zero) : L) * θx j := by
    intro v us θx cq
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hsumY : ∀ Y : ℕ → T.F (m + 1), ∑ l ∈ Finset.range N, (Y l : L) * θc l =
      ∑ i ∈ Finset.range N, ((∑ l ∈ Finset.range N, Y l * (qget C l i : T.F (m + 1)) *
        T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i := fun Y ↦ by
    simp only [hθc, hθt, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  unfold ExW at hv ⊢
  dsimp only
  rw [hsplit] at hv ⊢
  rw [hrhsV] at hv
  have hgs' : ∀ i ∈ Finset.range (gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map
      (redC Fc ks m)).length, ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
        (((gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map
          (redC Fc ks m)).getD i []).getD j O1.zero) : L) * θc j =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j O1.zero) : L) *
        θw j := by
    intro i hi
    have hi' : i < gs.length := by simpa using hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
      ← List.getD_eq_getElem gs [] hi']
    exact hrhsV _
  have hsum2 : ∑ i ∈ Finset.range (gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map
      (redC Fc ks m)).length, ((w0.1.getD i 0 : ℚ) : L) * ∑ j ∈ Finset.range N,
        ((T.MPr (m + 1) h1).sem (((gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r)
          Ci).map (redC Fc ks m)).getD i []).getD j O1.zero) : L) * θc j =
      ∑ i ∈ Finset.range gs.length, ((w0.1.getD i 0 : ℚ) : L) * ∑ j ∈ Finset.range N,
        ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j O1.zero) : L) * θw j := by
    rw [List.length_map]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hgs' i (by simpa using hi)]
  rw [hsum2] at hv
  rw [← hv, hsumY]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  simp only [unconjY]
  rw [NestTower.getD_range_map _ _ hi', T.sem_tpowL m h1 htr, T.sem_lsum_range m h1]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [(T.MPr (m + 1) h1).sem_mul]
  push_cast
  rw [T.sem_mcst_L m h1]

set_option maxHeartbeats 3200000 in
/-- **Every witness returned by `exactTRELW` is an explicit exact part in the power basis.** -/
theorem exactTRELW_valid (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
      ((T.MP m h1.of_succ).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (gs : List (List (LC (m + 1))))
    (wt : List ℚ × List (LC (m + 1)))
    (hres : exactTRELW Fc ks m a rdeD r N0 C Ci P Tc Ti f gs = some (some wt)) :
    T.ExW m h1 (P.length - 1) (fun k ↦ θ ^ k) f gs wt := by
  classical
  unfold exactTRELW at hres
  simp only at hres
  split_ifs at hres with hPc0
  split at hres
  · exact absurd hres (by simp)
  rename_i dθ hd
  have hPc : ¬((!(MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero) ((MOr Fc ks (m + 1)).neg
        (MOr Fc ks (m + 1)).one)) || decide (P.length - 1 = 0)) = true) := by
    intro h; apply hPc0; simp only [Bool.or_eq_true] at h ⊢; exact Or.inl h
  have hok : ((prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) &&
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)) = true) := by
    by_contra h; apply hPc0; simp only [Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
    right; simpa using h
  set O1 := MOr Fc ks (m + 1) with hO1
  set M1 := T.MPr (m + 1) h1 with hM1
  -- `P` is monic of degree `(P.length - 1)`
  have hPc' : O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) = true ∧ (P.length - 1) ≠ 0 := by
    revert hPc
    cases O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) <;> simp
  have hlead : M1.sem (P.getD (P.length - 1) O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc'.1
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPlen : P.length = (P.length - 1) + 1 := by
    have : P ≠ [] := fun h0' ↦ by rw [h0'] at hPc'; exact hPc'.2 rfl
    have := List.length_pos_of_ne_nil this
    omega
  have hPdeg : (GPoly.toPoly M1 P).natDegree = (P.length - 1) := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : (P.length - 1) < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  set N := P.length - 1 with hN
  have hN0 : N ≠ 0 := hPc'.2
  have hok' : prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
      (fun i j ↦ (Ti.getD i []).getD j O1.zero) = true ∧
      prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
      (fun i j ↦ (Tc.getD i []).getD j O1.zero) = true := by
    revert hok
    cases prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
      (fun i j ↦ (Ti.getD i []).getD j O1.zero) <;>
    cases prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
      (fun i j ↦ (Tc.getD i []).getD j O1.zero) <;> simp
  -- the values
  set t : ℕ → ℕ → L := fun i j ↦ (M1.sem ((Tc.getD i []).getD j O1.zero) : L) with ht
  set s : ℕ → ℕ → L := fun i j ↦ (M1.sem ((Ti.getD i []).getD j O1.zero) : L) with hs
  have hts := T.prodIdC_sound m h1 N _ _ hok'.1
  have hst := T.prodIdC_sound m h1 N _ _ hok'.2
  set w : ℕ → L := fun i ↦ ∑ k ∈ Finset.range N, t i k * θ ^ k with hw
  have hθw : ∀ l < N, θ ^ l = ∑ j ∈ Finset.range N, s l j * w j := fun l hl ↦
    (sum_inv_basis N t s (fun k ↦ θ ^ k) hst l hl).symm
  have hθd := fun i ↦ T.deriv_θ_pow_sum m h1 θ P hP hPm dθ hd i
  rw [hPdeg] at hθd
  -- the derivation matrix of `w`
  have hwd : ∀ i < N, (w i)′ = ∑ j ∈ Finset.range N,
      ((M1.sem ((((List.range N).map fun i ↦ (List.range N).map fun j ↦
        lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv ((Tc.getD i []).getD l O1.zero))
          (lsumC O1 ((List.range N).map fun k ↦ O1.mul ((Tc.getD i []).getD k O1.zero)
            ((dPowC O1 P dθ k).getD l O1.zero)))) ((Ti.getD l []).getD j O1.zero))).getD i []).getD
              j O1.zero) : T.F (m + 1)) : L) * w j := by
    intro i hi
    have hA : (w i)′ = ∑ l ∈ Finset.range N, (((M1.sem ((Tc.getD i []).getD l O1.zero))′ : T.F (m + 1)) +
        ∑ k ∈ Finset.range N, t i k * (T.Mθ m h1 P dθ k l : L)) * θ ^ l := by
      rw [hw, map_sum]
      simp only [Derivation.leibniz, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_comm]; rfl
      · rw [Finset.sum_congr rfl fun k hk ↦ by rw [hθd k, Finset.mul_sum], Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hA]
    refine (Finset.sum_congr rfl fun l hl ↦ by rw [hθw l (Finset.mem_range.mp hl)]).trans ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ (Finset.mem_range.mp hj),
      T.sem_lsum_range m h1]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [hO1, (T.MPr (m + 1) h1).sem_mul, (T.MPr (m + 1) h1).sem_add,
      (T.MPr (m + 1) h1).sem_deriv, T.sem_lsum_range m h1,
      IntermediateField.coe_mul, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum,
      MTower.coe_deriv, Mθ, ht, hs, Finset.sum_mul]
    ring
  -- independence of `w`
  have hindw : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * w j = 0 →
      ∀ j < N, a j = 0 := by
    intro a ha j hj
    have h0 : ∑ k ∈ Finset.range N, ((∑ i ∈ Finset.range N, a i * M1.sem ((Tc.getD i []).getD k O1.zero) :
        T.F (m + 1)) : L) * θ ^ k = 0 := by
      rw [← ha, hw]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hz := hind _ h0
    have := coords_inv N t s (fun i ↦ (a i : L)) hts j hj
    apply Subtype.ext
    change (a j : L) = 0
    rw [← this]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have := congrArg (fun z : T.F (m + 1) ↦ (z : L)) (hz k (Finset.mem_range.mp hk))
    push_cast at this
    simp only [ht]
    rw [this, zero_mul]
  -- the coordinates in the basis `w`
  have ecoords : ∀ l : List (LC (m + 1)), ∑ j ∈ Finset.range N,
        ((M1.sem ((((List.range N).map fun j ↦ lsumC O1 ((List.range N).map fun k ↦
          O1.mul (l.getD k O1.zero) ((Ti.getD k []).getD j O1.zero)))).getD j O1.zero) :
            T.F (m + 1)) : L) * w j = ∑ k ∈ Finset.range N,
        ((M1.sem (l.getD k O1.zero) : T.F (m + 1)) : L) * θ ^ k := by
    intro l
    refine (Finset.sum_congr rfl fun j hj ↦ by
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hj), T.sem_lsum_range m h1]).trans ?_
    symm
    refine (Finset.sum_congr rfl fun k hk ↦ by rw [hθw k (Finset.mem_range.mp hk)]).trans ?_
    push_cast
    simp only [hO1, (T.MPr (m + 1) h1).sem_mul, IntermediateField.coe_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  set cw : List (LC (m + 1)) → List (LC (m + 1)) := fun g ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun k ↦
        O1.mul (g.getD k O1.zero) ((Ti.getD k []).getD j O1.zero)) with hcw
  have hfw : ∀ c : ℕ → Cc, ∑ j ∈ Finset.range N,
      (((M1.sem ((cw f).getD j O1.zero) : T.F (m + 1)) : L) -
        ∑ i ∈ Finset.range (gs.map cw).length, algebraMap Cc L (c i) *
          ((M1.sem (((gs.map cw).getD i []).getD j O1.zero) : T.F (m + 1)) : L)) * w j =
      ∑ k ∈ Finset.range N, (((M1.sem (f.getD k O1.zero) : T.F (m + 1)) : L) -
        ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
          ((M1.sem ((gs.getD i []).getD k O1.zero) : T.F (m + 1)) : L)) * θ ^ k := by
    intro c
    simp only [List.length_map, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · exact ecoords f
    · simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [mul_assoc, ← Finset.mul_sum]
      congr 1
      have hgi : (gs.map cw).getD i [] = cw (gs.getD i []) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
          List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]
      rw [hgi]
      exact (ecoords _).symm
  have hwd' : ∀ i < N, (w i)′ = ∑ j ∈ Finset.range N,
      ((M1.sem (((((List.range N).map fun i ↦ (List.range N).map fun j ↦
        lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv ((Tc.getD i []).getD l O1.zero))
          (lsumC O1 ((List.range N).map fun k ↦ O1.mul ((Tc.getD i []).getD k O1.zero)
            ((dPowC O1 P dθ k).getD l O1.zero)))) ((Ti.getD l []).getD j O1.zero))).map
              fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero) : T.F (m + 1)) : L) * w j := by
    intro i hi
    rw [hwd i hi]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have hfw' : ∀ c : ℕ → Cc, ∑ j ∈ Finset.range N,
      (((M1.sem (((cw f).map (redC Fc ks m)).getD j O1.zero) : T.F (m + 1)) : L) -
        ∑ i ∈ Finset.range (gs.map fun g ↦ (cw g).map (redC Fc ks m)).length,
          algebraMap Cc L (c i) * ((M1.sem (((gs.map fun g ↦ (cw g).map (redC Fc ks m)).getD i
            []).getD j O1.zero) : T.F (m + 1)) : L)) * w j =
      ∑ k ∈ Finset.range N, (((M1.sem (f.getD k O1.zero) : T.F (m + 1)) : L) -
        ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
          ((M1.sem ((gs.getD i []).getD k O1.zero) : T.F (m + 1)) : L)) * θ ^ k := by
    intro c
    rw [← hfw c]
    simp only [List.length_map]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 2
    · rw [T.sem_getD_map_redC m h1 htr]
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have h1' : (gs.map fun g ↦ (cw g).map (redC Fc ks m)).getD i [] =
          (cw (gs.getD i [])).map (redC Fc ks m) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
          List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]
      have h2' : (gs.map cw).getD i [] = cw (gs.getD i []) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
          List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]
      rw [h1', h2', T.sem_getD_map_redC m h1 htr]
  obtain ⟨w', hw', hww⟩ := Option.map_eq_some_iff.mp hres
  obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.mp hww
  rw [hw0] at hw'
  have hv0 := T.exactWRELW_valid m h1 hm hk htr rdeD hrdeD hom N _ _ _ r N0 C Ci w hwd' hindw w0 hw'
  have hv : T.ExW m h1 N w ((cw f).map (redC Fc ks m))
      (gs.map fun g ↦ (cw g).map (redC Fc ks m)) w0 := by
    exact hv0
  have hcast : ∀ x : ℚ, ((x : ℚ) : L) = algebraMap Cc L ((x : ℚ) : Cc) := fun x ↦
    (map_ratCast _ x).symm
  unfold ExW at hv ⊢
  simp only [hcast] at hv ⊢
  rw [hfw'] at hv
  rw [← hv]
  congr 1
  rw [hw]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp only [thetaY]
  rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hk), T.sem_lsum_range m h1]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [hO1, (T.MPr (m + 1) h1).sem_mul, IntermediateField.coe_mul, ht]
  ring


end MTower

section Integrate

variable {lv : (m : ℕ) → LC m}

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 8000000 in
/-- **The integral with several places at infinity over `ℚ(α)` (constant curves, exponential
level, a single place above `t = 0`), decided and computed.** -/
theorem nk_integrateETRNTRE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (hsh0 : nkShape0 Fc ks m Pp = true) (ha0Q : (toB Fq).coeff 0 ≠ 0)
    (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true) (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkETRNTRW Fc ks lv m a Pp gss s fp N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplRN m θ Pp fp s μ.length gss.length
          (fun p i ↦ nVal (T.evθ m h1 θ) (algebraMap Cc L (αs i)) ((Ass.getD p []).map (nkFl Fc ks m)))
          (fun p i ↦ ∑ k : Fin μ.length,
            ((b.2.1.getD (p * μ.length + k) 0 : ℚ) : Cc) * (Matrix.vandermonde αs)⁻¹ k i) b.2 := by
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (fun c ↦ exactTRELW_isSome Fc ks m a _ _ _ _ _ _ _ _ _ _) [] N).trans
        (searchTREL_eq Fc ks m a _ _ _ _ N).symm)
    _ (T.nk_decidesETRNTRE hmon hdeg hshF m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo hsh0 ha0Q θ ιC
      k0 M hinv hGm hGn μ Ass Bss gss hpd dθ wθ s hU J H hJH hθ hgen αs hαinj hαμ hs fp F0 hF0 hlen
      hcoef) _ fun N w hw h1 ↦ ?_
  obtain ⟨-, hex⟩ := searchPW_src _ _ [] N w hw
  obtain ⟨hrde, hom⟩ := T.expTRE_specs hmon hdeg m hn hc hk
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveG_ind m h1 Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  have hY := T.exactTRELW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ gss.flatten w.2 hex
  exact T.rn_explicit m h1 Pp hn0 θ hP μ Ass Bss gss dθ wθ s hU αs hαinj hαμ fp w.2 hY

end MTower

end Integrate

end Curves.MT

