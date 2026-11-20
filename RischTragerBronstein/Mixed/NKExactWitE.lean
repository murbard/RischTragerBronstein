import RischTragerBronstein.Mixed.NKExactWitTL
import RischTragerBronstein.Mixed.NKExactTLEVG

/-!
# Explicit exact parts over an exponential level

`exactWREVLSW`, `exactTLEVSW`, `exactTLEVGW` mirror `exactWREVLS`, `exactTLEVS`, `exactTLEVG`
(`_isSome`) and return, with a `true` answer, an explicit exact part `(c, Y)` (`ExW`) in the
rescaled basis, then in the power basis `θᵏ` (`_valid`), exactly as at a logarithmic level.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX CPoly

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **`exactWREVLS` with the witness.** -/
def exactWREVLSW (m : ℕ) (a : LC m) (solve : SysSolver m)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m)) : Option (Option (List ℚ × List (LC (m + 1)))) :=
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
    if !(zeroOKV Fc ks m a N q A0 C Ci dg0) then none
    else
    match indBound2 Fc ks m (degG O q) N q (DzLC O O.zero bc q) A0 with
    | none => none
    | some B =>
      let R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0
      let E := GPoly.mul O (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R)
      (exactWLEW Fc ks m solve N
        ((rescaleME Fc ks m bc N Mc r).map fun l ↦ l.map (redC Fc ks m))
        ((rescaleF Fc ks m N f r).map (redC Fc ks m))
        (gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m)) E).map
          (Option.map fun w ↦ (w.1, unscaleY Fc ks m N r w.2))

theorem exactWREVLSW_isSome (m : ℕ) (a : LC m) (solve : SysSolver m)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m)) :
    (exactWREVLSW Fc ks m a solve N Mc f gs r C Ci dg0).map Option.isSome =
      exactWREVLS Fc ks m a solve N Mc f gs r C Ci dg0 := by
  unfold exactWREVLSW exactWREVLS
  dsimp only
  split_ifs
  all_goals try rfl
  split
  · rename_i heq; rw [heq]; rfl
  · rename_i B heq
    rw [heq]
    dsimp only
    rw [map_map_isSome, exactWLEW_isSome]

/-- **`exactTLEVS` with the witness.** -/
def exactTLEVSW (m : ℕ) (a : LC m) (solve : SysSolver m) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
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
    (exactWREVLSW Fc ks m a solve N (Mw.map fun l ↦ l.map (redC Fc ks m))
      ((cw f).map (redC Fc ks m)) (gs.map fun g ↦ (cw g).map (redC Fc ks m)) r C Ci dg0).map
        (Option.map fun w ↦ (w.1, thetaY Fc ks m N Tc w.2))

theorem exactTLEVSW_isSome (m : ℕ) (a : LC m) (solve : SysSolver m) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    (exactTLEVSW Fc ks m a solve r C Ci dg0 P Tc Ti f gs).map Option.isSome =
      exactTLEVS Fc ks m a solve r C Ci dg0 P Tc Ti f gs := by
  unfold exactTLEVSW exactTLEVS
  dsimp only
  split_ifs
  all_goals try rfl
  split
  · rename_i heq; rw [heq]; rfl
  · rename_i dθ heq
    rw [heq]
    dsimp only
    rw [map_map_isSome]
    exact exactWREVLSW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **`exactTLEVG` with the witness.** -/
def exactTLEVGW (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLEVSW Fc ks m a (expSysVG Fc ks m a rde dg Cg Cgi) r C Ci dg0 P Tc Ti f gs

theorem exactTLEVGW_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    (exactTLEVGW Fc ks m a rde dg Cg Cgi r C Ci dg0 P Tc Ti f gs).map Option.isSome =
      exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 P Tc Ti f gs :=
  exactTLEVSW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ) (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **Every witness returned by `exactWREVLSW` is an explicit exact part.** -/
theorem exactWREVLSW_valid (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m)
    (hspec : T.SolverSpecB m h1.of_succ 0 ((T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a)) solve)
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (wt : List ℚ × List (LC (m + 1)))
    (hres : exactWREVLSW Fc ks m a solve N Mc f gs r C Ci dg0 = some (some wt)) :
    T.ExW m h1 N θw f gs wt := by
  classical
  unfold exactWREVLSW at hres
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
  -- the right-hand sides
  set fl : List (List (LC (m + 1))) := f :: gs with hfl
  set R : ℕ → ℕ → T.F (m + 1) := fun l j ↦ M1.sem ((fl.getD l []).getD j O1.zero) with hR
  have hzF : GPoly.toPoly M (numF O1.zero) = 0 := by
    have hz : O1.zero.1 = [] := rfl
    rw [hnumF]
    simp only [hz, GPoly.mul, GPoly.toPoly_nil]
  have hvG : ∀ l j, R l j = T.phi m (GPoly.toPoly M (numF ((fl.getD l []).getD j O1.zero))) /
      T.phi m hs := by
    intro l j
    have hgl : fl.getD l [] = [] ∨ fl.getD l [] ∈ fl := by
      by_cases hl : l < fl.length
      · right; rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
      · left; exact List.getD_eq_default _ _ (by omega)
    have hgj : ∀ g : List (LC (m + 1)), g.getD j O1.zero ∈ g ∨ g.getD j O1.zero = O1.zero := by
      intro g
      by_cases hj : j < g.length
      · left; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
      · right; exact List.getD_eq_default _ _ (by omega)
    have hz : ∀ c, c = O1.zero → (M1.sem c : T.F (m + 1)) =
        T.phi m (GPoly.toPoly M (numF c)) / T.phi m hs := by
      rintro c rfl
      rw [M1.sem_zero, hzF, map_zero, zero_div]
    rcases hgj (fl.getD l []) with hm | hm
    · rcases hgl with he | he
      · rw [he] at hm; simp at hm
      · refine hvalF _ ?_
        rcases List.mem_cons.mp he with he | he
        · exact List.mem_append_left _ (he ▸ hm)
        · exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, he, hm⟩)
    · exact hz _ hm
  set G0 : List (Fin N → GPoly (LC m)) := fl.map fun g j ↦ numF (g.getD j O1.zero) with hG0
  have hG0len : G0.length = gs.length + 1 := by simp [hG0, hfl]
  have hRG : ∀ l (j : Fin N), T.phi m (GPoly.toPoly M ((G0.getD l fun _ ↦ []) j)) =
      T.phi m hs * R l j := by
    intro l j
    have e : GPoly.toPoly M ((G0.getD l fun _ ↦ []) j) =
        GPoly.toPoly M (numF ((fl.getD l []).getD j O1.zero)) := by
      simp only [hG0, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases fl[l]? with
      | none =>
        simp only [Option.map_none, Option.getD_none, List.getElem?_nil]
        rw [hzF]; rfl
      | some g => rfl
    rw [e, hvG, mul_div_cancel₀ _ hphih]
  have hsplit : ∀ (a : ℕ → T.F (m + 1)) j, ∑ l ∈ Finset.range G0.length, a l * (T.phi m hs * R l j) =
      T.phi m hs * (a 0 * R 0 j + ∑ i ∈ Finset.range gs.length, a (i + 1) * R (i + 1) j) := by
    intro a j
    rw [hG0len, Finset.sum_range_succ' (fun l ↦ a l * (T.phi m hs * R l j)) gs.length, mul_add,
      Finset.mul_sum]
    have e : ∑ i ∈ Finset.range gs.length, a (i + 1) * (T.phi m hs * R (i + 1) j) =
        ∑ i ∈ Finset.range gs.length, T.phi m hs * (a (i + 1) * R (i + 1) j) :=
      Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e]
    ring
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Rc : (ℕ → Cc) → ℕ → T.F (m + 1) := fun c j ↦
    R 0 j - ∑ i ∈ Finset.range gs.length, algebraMap Cc (T.F (m + 1)) (c i) * R (i + 1) j with hRc'
  have hRc : ∀ c : ℕ → Cc, ∑ j ∈ Finset.range N,
      (((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) -
        ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
          ((M1.sem ((gs.getD i []).getD j O1.zero) : T.F (m + 1)) : L)) * θw j =
      ∑ j ∈ Finset.range N, ((Rc c j : T.F (m + 1)) : L) * θw j := by
    intro c
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hRc', hR, hfl, List.getD_cons_zero, List.getD_cons_succ]
    push_cast
    rfl
  -- the checks at `t = 0`
  set b := (T.MP m h0).sem ((MO Fc ks m).deriv a) with hb
  have hq0 : qs.coeff 0 ≠ 0 := by
    rw [hqs, coeff_toPoly_sem]
    intro h0'
    exact hq0c ((M.isZero_iff _).mpr h0')
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hzc
  obtain ⟨hA0z, hCiC, hTg, htriT, hdiagT, hpT⟩ := T.zeroOKV_spec h0 a N q _ C Ci dg0 hzc hq0
  -- the rescaled basis
  set θt : ℕ → L := fun i ↦ ((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i with hθt
  have hwt0 := T.rescale_derivE h1 hm hk htr N Mc r θw hw hden
  have hwt : ∀ k < N, (θt k)′ = ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
      ((((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r).map fun l ↦
        l.map (redC Fc ks m)).getD k []).getD l (MOr Fc ks (m + 1)).zero) : L) * θt l := by
    intro k hk
    rw [hwt0 k hk]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have hindt := T.rescale_ind htr N r θw hind
  have hv := T.exactWLEW_valid m h1 htr _ 0 b hspec N _ _ θt hwt hindt _ _ w0 hw'
  have hcast : ∀ x : ℚ, ((x : ℚ) : L) = algebraMap Cc L ((x : ℚ) : Cc) := fun x ↦
    (map_ratCast _ x).symm
  unfold ExW at hv ⊢
  simp only [hcast] at hv ⊢
  rw [T.rescale_rhsLE m h1 htr N f gs r θw] at hv
  rw [← hv]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  simp only [unscaleY]
  rw [NestTower.getD_range_map _ _ hi', T.sem_tpowL m h1 htr, hθt]
  push_cast
  ring

set_option maxHeartbeats 3200000 in
/-- **Every witness returned by `exactTLEVSW` is an explicit exact part in the power basis.** -/
theorem exactTLEVSW_valid (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m)
    (hspec : T.SolverSpecB m h1.of_succ 0 ((T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a)) solve)
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (gs : List (List (LC (m + 1))))
    (wt : List ℚ × List (LC (m + 1)))
    (hres : exactTLEVSW Fc ks m a solve r C Ci dg0 P Tc Ti f gs = some (some wt)) :
    T.ExW m h1 (P.length - 1) (fun k ↦ θ ^ k) f gs wt := by
  classical
  unfold exactTLEVSW at hres
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
  have hv := T.exactWREVLSW_valid m h1 hm hk htr solve hspec hom N _ _ _ r C Ci dg0 w hwd' hindw w0
    hw'
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

/-- **Every witness returned by `exactTLEVGW` is an explicit exact part in the power basis.** -/
theorem exactTLEVGW_valid (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (gs : List (List (LC (m + 1))))
    (wt : List ℚ × List (LC (m + 1)))
    (hres : exactTLEVGW Fc ks m a rde dg Cg Cgi r C Ci dg0 P Tc Ti f gs = some (some wt)) :
    T.ExW m h1 (P.length - 1) (fun k ↦ θ ^ k) f gs wt :=
  T.exactTLEVSW_valid m h1 hm hk htr _ (T.expSpecVG m hm h1.of_succ hk rde hrde hom dg Cg Cgi) hom
    r C Ci dg0 P f θ hP hind Tc Ti gs wt hres

end MTower

end Curves.MT
