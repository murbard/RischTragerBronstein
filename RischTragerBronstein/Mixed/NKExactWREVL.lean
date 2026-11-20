import RischTragerBronstein.Mixed.NKExactWREV
import RischTragerBronstein.Mixed.NKExactWRVL

/-!
# The exact part over an exponential level with several parameters (non-constant curves)

`exactWREVL … f gs`: as `exactWREV` (gauge at `t = 0`, rescaled basis, solver `expSysV`), testing
whether `f − ∑ cᵢ gᵢ` is exact for some constants `cᵢ` (`exactWREVL_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test with several parameters over an exponential level**, for any system
solver `solve` one level down. -/
def exactWREVLS (m : ℕ) (a : LC m) (solve : SysSolver m)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m)) : Option Bool :=
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
      exactWLE Fc ks m solve N
        ((rescaleME Fc ks m bc N Mc r).map fun l ↦ l.map (redC Fc ks m))
        ((rescaleF Fc ks m N f r).map (redC Fc ks m))
        (gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m)) E

/-- **The exact-part test with several parameters over an exponential level** (solver
`expSysV`). -/
def exactWREVL (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m)) : Option Bool :=
  exactWREVLS Fc ks m a (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) N Mc f gs r
    C Ci dg0

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ) (h1 : T.Tr (m + 1))

/-- The combined right-hand side is rescaled termwise (reduced codes). -/
lemma rescale_rhsLE (htr : Transcendental (T.F m) (T.ts m)) (N : ℕ) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ) (θw : ℕ → L) (c : ℕ → Cc) :
    ∑ j ∈ Finset.range N,
      (((T.MPr (m + 1) h1).sem (((rescaleF Fc ks m N f r).map (redC Fc ks m)).getD j
          (MOr Fc ks (m + 1)).zero) : L) -
        ∑ i ∈ Finset.range (gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m)).length,
          algebraMap Cc L (c i) * ((T.MPr (m + 1) h1).sem
            (((gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m)).getD i []).getD j
              (MOr Fc ks (m + 1)).zero) : L)) *
        (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j) =
    ∑ j ∈ Finset.range N,
      (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
        ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
          ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) * θw j := by
  have hgi : ∀ i ∈ Finset.range gs.length,
      (gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m)).getD i [] =
        (rescaleF Fc ks m N (gs.getD i []) r).map (redC Fc ks m) := fun i hi ↦ by
    have hi' := Finset.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
      List.getD_eq_getElem _ _ hi']
  rw [List.length_map]
  rw [Finset.sum_congr rfl fun j _ ↦ by
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [hgi i hi]]]
  simp only [T.sem_getD_map_redC m h1 htr]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [T.rescale_rhs h1 htr N f r θw]
  congr 1
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range N)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  exact T.rescale_rhs h1 htr N (gs.getD i []) r θw

set_option maxHeartbeats 6400000 in
/-- **Correctness of `exactWREVLS`** for a solver meeting the specification. -/
theorem exactWREVLS_correct (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
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
    (res : Bool) (hres : exactWREVLS Fc ks m a solve N Mc f gs r C Ci dg0 = some res) :
    res = true ↔ ∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θw j := by
  classical
  unfold exactWREVLS at hres
  simp only at hres
  split_ifs at hres with hN0 hcof hq0c hzc
  split at hres
  · exact absurd hres (by simp)
  rename_i B hB
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
  obtain ⟨ha, hb'⟩ := T.exactWLE_correct m h1 htr _ 0 b hspec N _ _ θt hwt hindt _ _ res hres
  have hsumY : ∀ Y : ℕ → T.F (m + 1), ∑ i ∈ Finset.range N, (Y i : L) * θt i =
      ∑ i ∈ Finset.range N, ((Y i * T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i := fun Y ↦
    Finset.sum_congr rfl fun i _ ↦ by simp only [hθt]; push_cast; ring
  constructor
  · intro hrt
    obtain ⟨c, Y, hY⟩ := ha hrt
    refine ⟨c, fun i ↦ Y i * T.tau m ^ (-r i), ?_⟩
    rw [← hsumY, ← T.rescale_rhsLE m h1 htr N f gs r θw c]
    exact hY
  · rintro ⟨c, Y, hY⟩
    rw [hRc] at hY
    -- the coordinate equations
    have hcoord : ∀ j < N, (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i = Rc c j := by
      have hdc := T.deriv_coordsW m N θw Mw hw Y
      rw [hdc] at hY
      intro j hj
      have h0' := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i - Rc c j) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hY]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0'
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin N ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin N, Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    set cl : List Cc := 1 :: (List.range gs.length).map fun i ↦ -c i with hcl
    set Gc : Fin N → (T.F m)[X] := fun j ↦ ∑ l ∈ Finset.range G0.length,
      Polynomial.C (algebraMap Cc (T.F m) (cl.getD l 0)) *
        GPoly.toPoly M ((G0.getD l fun _ ↦ []) j) with hGc
    have hsol : SysSol 0 b qs hs (semMat M A0f) Gc Z d := by
      refine T.sysSol_of_phiG m htr 0 b (T.phi_DzL_exp m hm hk h0) qs hs (semMat M A0f) _ Z d
        fun j ↦ ?_
      have hj := hcoord j j.2
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)] at hj
      have hMθ' : ∀ i : Fin N, Mw i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi] at hj
      have hphiC : ∀ a : Cc, T.phi m (Polynomial.C (algebraMap Cc (T.F m) a)) =
          algebraMap Cc (T.F (m + 1)) a :=
        fun a ↦ by rw [T.phi_C]; rfl
      simp only [hGc, map_sum, map_mul, hphiC, hRG, semMat, Matrix.of_apply]
      rw [hsplit (fun l ↦ algebraMap Cc (T.F (m + 1)) (cl.getD l 0)) j]
      have key : Rc c j = T.phi m hs * (algebraMap Cc (T.F (m + 1)) (cl.getD 0 0) * R 0 j +
          ∑ i ∈ Finset.range gs.length, algebraMap Cc (T.F (m + 1)) (cl.getD (i + 1) 0) *
            R (i + 1) j) / T.phi m hs := by
        rw [mul_div_cancel_left₀ _ hphih, hRc']
        simp only [hcl, List.getD_cons_zero, List.getD_cons_succ, map_one, one_mul, sub_eq_add_neg,
          ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        simp
      rw [key] at hj
      exact cleared_of_solW _ _ _ _ _ _ _ hphiq hphih hphid hj
    have hindB : ∀ (p : (T.F m)[X]) (e : ℕ), Irreducible p → p ∣ qs →
        p ∣ (Matrix.of fun i j ↦ semMat M A0f i j - if i = j then
          Polynomial.C (e : T.F m) * DzL 0 b qs else 0).det → e ≤ B :=
      fun p e hp hpq hdet ↦ T.indBound2_spec m h0 (degG O q) N q
        (DzLC O O.zero ((MO Fc ks m).deriv a) q)
        A0f hqM (degG_eq M q).symm B hB e p hp hpq (by rwa [toPoly_DzLC, M.sem_zero])
    have hbval : b = (T.val m a)′ := by
      rw [hb, M.sem_deriv, T.sem_MP_F m h0]
    have hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ DzL 0 b p → X ∣ p := by
      intro p hp hpd
      by_contra hX
      apply T.normal_exp m htr hk p hp hX
      rw [T.wPoly_exp hm hk, ← hbval]
      simpa [DzL] using hpd
    have hspecP := sys_den_special_gauge b qs hq0 (semMat M A0f)
      (fun i j ↦ M.sem (m0E Fc ks m N q A0f i j)) (fun i j ↦ hA0z i j) _ _ hCiC
      (fun i j ↦ M.sem (gaugeT Fc ks m N q A0f C Ci i j)) hTg htriT
      (fun i ↦ (dgEAt Fc ks m dg0 (i : ℕ)).1) (fun i ↦ (dgEAt Fc ks m dg0 (i : ℕ)).2.1)
      (fun i ↦ M.sem (dgEAt Fc ks m dg0 (i : ℕ)).2.2) hdiagT hpT Gc hom hnormal
    have hdvd := fun i ↦ sys_den_bound' 0 b qs hs hhs0 (semMat M A0f) _ B hindB
      Z d hd0 hsol hspecP i
    choose u hu using hdvd
    -- the bound for the rescaled coordinates
    set Rm := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hRm
    have hRi : ∀ i < N, (-r i).toNat ≤ Rm := fun i hi ↦
      Tower.Sys.le_foldr_max _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hterm : ∀ i (hi : i < N), Y i * T.tau m ^ r i * T.phi m (GPoly.toPoly M (GPoly.mul O
        (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) Rm))) =
        T.phi m (u ⟨i, hi⟩ * X ^ (Rm - (-r i).toNat + (r i).toNat)) := by
      intro i hi
      have hE : GPoly.toPoly M (GPoly.mul O (GPoly.mul O hq (sysPowC O q B))
          (sysPowC O (tX Fc ks m) Rm)) = hs * qs ^ B * X ^ Rm := by
        rw [GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
      rw [hE, map_mul, map_mul, map_pow, map_mul, map_pow, map_pow]
      have hui := hu ⟨i, hi⟩
      have hX : T.phi m X = T.tau m := rfl
      rw [hX, hYi ⟨i, hi⟩]
      have e1 : T.phi m (Z ⟨i, hi⟩) * (T.phi m hs * T.phi m qs ^ B) =
          T.phi m d * T.phi m (u ⟨i, hi⟩) := by
        rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, ← hui]; ring_nf
      have ht := T.tau_ne_zero m htr
      have e2 : T.tau m ^ r i * T.tau m ^ Rm = T.tau m ^ (Rm - (-r i).toNat + (r i).toNat) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ht]
        congr 1
        have := hRi i hi
        omega
      calc T.phi m (Z ⟨i, hi⟩) / T.phi m d * T.tau m ^ r i *
            (T.phi m hs * T.phi m qs ^ B * T.tau m ^ Rm)
          = (T.phi m (Z ⟨i, hi⟩) * (T.phi m hs * T.phi m qs ^ B)) / T.phi m d *
            (T.tau m ^ r i * T.tau m ^ Rm) := by ring
        _ = T.phi m (u ⟨i, hi⟩) * T.tau m ^ (Rm - (-r i).toNat + (r i).toNat) := by
          rw [e1, e2]; field_simp
    refine hb' ⟨c, fun i ↦ Y i * T.tau m ^ r i, fun i ↦ if hi : i < N then
      u ⟨i, hi⟩ * X ^ (Rm - (-r i).toNat + (r i).toNat) else 0, fun i hi ↦ ?_, ?_⟩
    · show Y i * T.tau m ^ r i * _ = T.phi m (if hi : i < N then _ else 0)
      rw [dif_pos hi]
      exact hterm i hi
    · rw [hsumY, T.rescale_rhsLE m h1 htr N f gs r θw c, hRc]
      convert hY using 2
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_assoc, ← zpow_add₀ (T.tau_ne_zero m htr), add_neg_cancel, zpow_zero, mul_one]

/-- **Correctness of `exactWREVL`.** -/
theorem exactWREVL_correct (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (ℚ × ℚ × LC m))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (res : Bool) (hres : exactWREVL Fc ks m a rde dg N Mc f gs r C Ci dg0 = some res) :
    res = true ↔ ∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θw j :=
  T.exactWREVLS_correct m h1 hm hk htr _ (T.expSpecV hm h1.of_succ hk rde hrde hom dg) hom N Mc f gs r
    C Ci dg0 θw hw hind res hres

end MTower

end Curves.MT
