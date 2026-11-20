import RischTragerBronstein.Mixed.NKExactWRESome
import RischTragerBronstein.Mixed.NKExactWRL

/-!
# The rescaled exact-part test with several parameters (exponential level)

`exactWREL f gs r N₀ C C⁻¹`: is `f − ∑ cᵢ gᵢ` exact for some constants `cᵢ` (`exactWRE` with
`exactWEL`)? Correct for every basis and parameters (`exactWREL_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test with several parameters at an exponential level, rescaled at infinity.** -/
def exactWREL (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) : Option Bool :=
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
      exactWEL Fc ks m (fun n A0 q hh G0 ↦ expSysB Fc ks m a rdeD n A0 q hh G0 0) N
        ((conjM Fc ks m N C (rescaleME Fc ks m bc N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m))
        ((vecCi Fc ks m N (rescaleF Fc ks m N f r) Ci).map (redC Fc ks m))
        (gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map (redC Fc ks m)) E

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) {m : ℕ} (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **Correctness of `exactWREL`**: for any basis `w` with derivation matrix `Mc`, shifts `r`,
`N₀` and constant `C`, an answer `res` says whether `∑ fⱼ wⱼ` has an antiderivative `∑ Yᵢ wᵢ`. -/
theorem exactWREL_correct (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
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
    (res : Bool) (hres : exactWREL Fc ks m a rdeD N Mc f gs r N0 C Ci = some res) :
    res = true ↔ ∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θw j := by
  classical
  unfold exactWREL at hres
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
  have hzF : GPoly.toPoly M (numF O1.zero) = 0 := by
    have hz : O1.zero.1 = [] := rfl
    rw [hnumF]
    simp only [hz, GPoly.mul, GPoly.toPoly_nil]
  have hgv : ∀ g, (g = f ∨ g ∈ gs ∨ g = []) → ∀ j, (M1.sem (g.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (numF (g.getD j O1.zero))) / T.phi m hs := by
    intro g hg j
    by_cases hj : j < g.length
    · refine hvalF _ ?_
      have hm : g.getD j O1.zero ∈ g := by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
      rcases hg with rfl | hg | rfl
      · exact List.mem_append_left _ hm
      · exact List.mem_append_right _ (List.mem_flatten.mpr ⟨g, hg, hm⟩)
      · simp at hm
    · rw [List.getD_eq_default _ _ (by omega), M1.sem_zero, hzF, map_zero, zero_div]
  have hgi : ∀ i, (gs.getD i [] = [] ∨ gs.getD i [] ∈ gs) := fun i ↦ by
    by_cases hi : i < gs.length
    · right; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    · left; exact List.getD_eq_default _ _ (by omega)
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
  -- the checks at `t = 0`
  set b := (T.MP m h0).sem ((MO Fc ks m).deriv a) with hb
  have hq0 : qs.coeff 0 ≠ 0 := by
    rw [hqs, coeff_toPoly_sem]
    intro h0'
    exact hq0c ((M.isZero_iff _).mpr h0')
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hzc
  obtain ⟨hA0z, hN0pos, hP, hCCi, hCiC⟩ := T.zeroOKE_spec m h0 _ N N0 q _ C Ci hzc
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gc : (ℕ → Cc) → Fin N → (T.F m)[X] := fun c j ↦ GPoly.toPoly M (numF (f.getD j O1.zero)) -
    ∑ i ∈ Finset.range gs.length, Polynomial.C (algebraMap Cc (T.F m) (c i)) *
      GPoly.toPoly M (numF ((gs.getD i []).getD j O1.zero)) with hGc
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
  set gs' : List (List (LC (m + 1))) :=
    gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map (redC Fc ks m) with hgs'
  obtain ⟨ha, hb'⟩ := T.exactWEL_correct m h1 htr _ 0 b hspec N _ _ θc hwc hindc gs' _ res hres
  have hrhs1 : ∀ g : List (LC (m + 1)), ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
      (((vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map (redC Fc ks m)).getD l
        (MOr Fc ks (m + 1)).zero) : L) * θc l =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (g.getD j (MOr Fc ks (m + 1)).zero) : L) *
        θw j := by
    intro g
    simp only [T.sem_getD_map_redC m h1 htr]
    rw [T.conj_rhs h1 N C Ci hCiC _ θt, T.rescale_rhs h1 htr N g r θw]
  have hrhs : ∀ c : ℕ → Cc, ∑ l ∈ Finset.range N,
      (((T.MPr (m + 1) h1).sem (((vecCi Fc ks m N (rescaleF Fc ks m N f r) Ci).map
        (redC Fc ks m)).getD l (MOr Fc ks (m + 1)).zero) : L) -
        ∑ i ∈ Finset.range gs'.length, algebraMap Cc L (c i) *
          ((T.MPr (m + 1) h1).sem ((gs'.getD i []).getD l (MOr Fc ks (m + 1)).zero) : L)) * θc l =
      ∑ j ∈ Finset.range N,
        (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
          ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
            ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
          θw j := by
    intro c
    simp only [sub_mul, Finset.sum_sub_distrib, hgs', List.length_map]
    congr 1
    · exact hrhs1 f
    · simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := Finset.mem_range.mp hi
      have hgl : (gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map
          (redC Fc ks m)).getD i [] =
          (vecCi Fc ks m N (rescaleF Fc ks m N (gs.getD i []) r) Ci).map (redC Fc ks m) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
          List.getD_eq_getElem _ _ hi']
      rw [hgl]
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hrhs1]
  have hsumY : ∀ Y : ℕ → T.F (m + 1), ∑ l ∈ Finset.range N, (Y l : L) * θc l =
      ∑ i ∈ Finset.range N, ((∑ l ∈ Finset.range N, Y l * (qget C l i : T.F (m + 1)) *
        T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i := fun Y ↦ by
    simp only [hθc, hθt, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  constructor
  · intro hrt
    obtain ⟨c, Y, hY⟩ := ha hrt
    refine ⟨c, fun i ↦ ∑ l ∈ Finset.range N, Y l * (qget C l i : T.F (m + 1)) * T.tau m ^ (-r i),
      ?_⟩
    rw [← hsumY, ← hrhs c]
    exact hY
  · rintro ⟨c, Y, hY⟩
    set Rc : ℕ → T.F (m + 1) := fun j ↦ M1.sem (f.getD j O1.zero) -
      ∑ i ∈ Finset.range gs.length, algebraMap Cc (T.F (m + 1)) (c i) *
        M1.sem ((gs.getD i []).getD j O1.zero) with hRc
    have hY' : (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N, ((Rc j : T.F (m + 1)) : L) * θw j := by
      rw [hY]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hRc]
      push_cast
      rfl
    -- the denominator bound in the basis `w`
    have hcoord : ∀ j < N, (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i = Rc j := by
      have hdc := T.deriv_coordsW m N θw Mw hw Y
      rw [hdc] at hY'
      intro j hj
      have h0' := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i - Rc j) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hY']
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0'
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin N ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin N, Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hphiC : ∀ a : Cc, T.phi m (Polynomial.C (algebraMap Cc (T.F m) a)) = algebraMap Cc (T.F (m + 1)) a :=
      fun a ↦ by rw [T.phi_C]; rfl
    have hRcv : ∀ j : Fin N, Rc j = T.phi m (Gc c j) / T.phi m hs := by
      intro j
      simp only [hRc, hGc]
      rw [hgv f (Or.inl rfl)]
      rw [Finset.sum_congr rfl fun i _ ↦ by
        rw [hgv (gs.getD i []) (by
          rcases hgi i with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h))]]
      simp only [map_sub, map_sum, map_mul, hphiC]
      rw [sub_div, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hsol : SysSol 0 b qs hs (semMat M A0f) (Gc c) Z d := by
      refine T.sysSol_of_phiG m htr 0 b (T.phi_DzL_exp m hm hk h0) qs hs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := hcoord j j.2
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)] at hj
      have hMθ' : ∀ i : Fin N, Mw i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi] at hj
      rw [hRcv j] at hj
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul] at hj
      simp only [semMat, Matrix.of_apply]
      have hsum : ∑ x, T.phi m (GPoly.toPoly M (A0f j x)) / T.phi m qs *
          (T.phi m (Z x) / T.phi m d) =
          (∑ x, T.phi m (GPoly.toPoly M (A0f j x)) * T.phi m (Z x)) / (T.phi m qs * T.phi m d) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ ↦ by field_simp
      rw [hsum, smul_eq_mul] at hj
      field_simp at hj
      linear_combination hj
    have hindB : ∀ (p : (T.F m)[X]) (e : ℕ), Irreducible p → p ∣ qs →
        p ∣ (Matrix.of fun i j ↦ semMat M A0f i j - if i = j then
          Polynomial.C (e : T.F m) * DzL 0 b qs else 0).det → e ≤ B :=
      fun p e hp hpq hdet ↦ T.indBound2_spec m h0 (degG O q) N q (DzLC O O.zero ((MO Fc ks m).deriv a) q)
        A0f hqM (degG_eq M q).symm B hB e p hp hpq (by rwa [toPoly_DzLC, M.sem_zero])
    have hbval : b = (T.val m a)′ := by
      rw [hb, M.sem_deriv, T.sem_MP_F m h0]
    have hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ DzL 0 b p → X ∣ p := by
      intro p hp hpd
      by_contra hX
      apply T.normal_exp m htr hk p hp hX
      rw [T.wPoly_exp hm hk, ← hbval]
      simpa [DzL] using hpd
    have hspecP := sys_den_special_ann b qs hq0 (semMat M A0f) _
      (fun i j ↦ hA0z i j) N0 hN0pos hP
      (Gc c) hom hnormal
    have hdvd := fun i ↦ sys_den_bound' 0 b qs hs hhs0 (semMat M A0f) _ B hindB
      Z d hd0 hsol hspecP i
    choose u hu using hdvd
    -- the bound for the rescaled coordinates
    set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
    have hRi : ∀ i < N, (-r i).toNat ≤ R := fun i hi ↦
      Tower.Sys.le_foldr_max _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    -- each coordinate in the rescaled basis has denominator dividing `E`
    have hterm : ∀ i (hi : i < N), Y i * T.tau m ^ r i * T.phi m (GPoly.toPoly M (GPoly.mul O
        (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R))) =
        T.phi m (u ⟨i, hi⟩ * X ^ (R - (-r i).toNat + (r i).toNat)) := by
      intro i hi
      have hE : GPoly.toPoly M (GPoly.mul O (GPoly.mul O hq (sysPowC O q B))
          (sysPowC O (tX Fc ks m) R)) = hs * qs ^ B * X ^ R := by
        rw [GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
      rw [hE, map_mul, map_mul, map_pow, map_mul, map_pow, map_pow]
      have hui := hu ⟨i, hi⟩
      have hX : T.phi m X = T.tau m := rfl
      rw [hX, hYi ⟨i, hi⟩]
      have e1 : T.phi m (Z ⟨i, hi⟩) * (T.phi m hs * T.phi m qs ^ B) = T.phi m d * T.phi m (u ⟨i, hi⟩) := by
        rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, ← hui]; ring_nf
      have ht := T.tau_ne_zero m htr
      have e2 : T.tau m ^ r i * T.tau m ^ R = T.tau m ^ (R - (-r i).toNat + (r i).toNat) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ht]
        congr 1
        have := hRi i hi
        omega
      calc T.phi m (Z ⟨i, hi⟩) / T.phi m d * T.tau m ^ r i * (T.phi m hs * T.phi m qs ^ B * T.tau m ^ R)
          = (T.phi m (Z ⟨i, hi⟩) * (T.phi m hs * T.phi m qs ^ B)) / T.phi m d *
            (T.tau m ^ r i * T.tau m ^ R) := by ring
        _ = T.phi m (u ⟨i, hi⟩) * T.tau m ^ (R - (-r i).toNat + (r i).toNat) := by
          rw [e1, e2]; field_simp
    refine hb' ⟨c, fun l ↦ ∑ i ∈ Finset.range N, (qget Ci i l : T.F (m + 1)) * (Y i * T.tau m ^ r i),
      fun l ↦ ∑ i ∈ Finset.range N, Polynomial.C ((qget Ci i l : ℚ) : T.F m) *
        (if hi : i < N then u ⟨i, hi⟩ * X ^ (R - (-r i).toNat + (r i).toNat) else 0),
      fun l hl ↦ ?_, ?_⟩
    · push_cast
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := Finset.mem_range.mp hi
      rw [dif_pos hi', map_mul, ← hterm i hi']
      have hc : T.phi m (Polynomial.C ((qget Ci i l : ℚ) : T.F m)) = ((qget Ci i l : ℚ) : T.F (m + 1)) := by
        rw [show ((qget Ci i l : ℚ) : T.F m) = algebraMap ℚ (T.F m) (qget Ci i l) from rfl,
          ← Polynomial.algebraMap_apply, ← RingHom.comp_apply]
        simp
      rw [hc]
      push_cast
      ring
    · -- the coordinates represent the same element
      have hsame : ∑ l ∈ Finset.range N, ((∑ i ∈ Finset.range N, (qget Ci i l : T.F (m + 1)) *
          (Y i * T.tau m ^ r i) : T.F (m + 1)) : L) * θc l =
          ∑ i ∈ Finset.range N, (Y i : L) * θw i := by
        have hθw : ∀ i < N, θw i = ((T.tau m ^ r i : T.F (m + 1)) : L) * θt i := fun i hi ↦ by
          simp only [hθt]
          rw [← mul_assoc, ← IntermediateField.coe_mul, ← zpow_add₀ (T.tau_ne_zero m htr),
            add_neg_cancel, zpow_zero, OneMemClass.coe_one, one_mul]
        have hR : ∑ i ∈ Finset.range N, (Y i : L) * θw i = ∑ i ∈ Finset.range N, (Y i : L) *
            (((T.tau m ^ r i : T.F (m + 1)) : L) * ∑ l ∈ Finset.range N, (qget Ci i l : L) * θc l) :=
          Finset.sum_congr rfl fun i hi ↦ by
            rw [hθw i (Finset.mem_range.mp hi), conj_inv N C Ci hCiC θt i (Finset.mem_range.mp hi)]
        rw [hR]
        push_cast
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
        ring
      rw [hsame, hrhs c]
      exact hY

section Lim

set_option maxHeartbeats 1600000 in
/-- **`exactWREL` answers** for squarefree matrix denominators prime to `t`, a rational limit
`a′ Λ₀` at `t = 0` annihilated by `∏_{k<N₀} (X − k/N₀)`, an invertible constant `C`, and a
conjugated rescaled matrix with an upper triangular rational limit `a′ Λ∞` at infinity. -/
theorem exactWREL_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hb0 : (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) ≠ 0)
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (N0 : ℕ) (C Ci : List (List ℚ))
    (hent : ∀ i < N, ∀ j < N,
      Squarefree (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2) ∧
      (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).coeff 0 ≠ 0)
    (lam0 : ℕ → ℕ → ℚ)
    (hz : ∀ i < N, ∀ j < N,
      (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).coeff 0 =
        (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * (lam0 j i : T.F m) *
          (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).coeff 0)
    (hN0 : 0 < N0) (hP : aeval (Matrix.of fun i j : Fin N ↦ lam0 i j)
      (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0)
    (hC1 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0)
    (hC2 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0)
    (lamI : ℕ → ℕ → ℚ)
    (hlim : ∀ i < N, ∀ j < N, ∃ A B : (T.F m)[X], B ≠ 0 ∧ A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree = (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * (lamI j i : T.F m) *
        B.leadingCoeff ∧
      (T.MPr (m + 1) h1).sem (((conjM Fc ks m N C (rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r)
        Ci).getD i []).getD j (MOr Fc ks (m + 1)).zero) = T.phi m A / T.phi m B)
    (htri : ∀ i < N, ∀ j < N, j < i → lamI i j = 0)
    (hf : ∀ c ∈ f ++ gs.flatten, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWREL Fc ks m a rdeD N Mc f gs r N0 C Ci).isSome := by
  set h0 := h1.of_succ with hh0
  set O := MO Fc ks m with hO
  set P := T.MP m h0 with hP'
  set O1 := MOr Fc ks (m + 1) with hO1
  set Mm : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMm
  have hmem : ∀ c ∈ Mm.flatten, ∃ i < N, ∃ j < N, c = (Mc.getD i []).getD j O1.zero := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcl
    exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, rfl⟩
  have hent' : ∀ c ∈ Mm.flatten, GPoly.toPoly P c.2 ≠ 0 ∧ Squarefree (GPoly.toPoly P c.2) ∧
      (GPoly.toPoly P c.2).coeff 0 ≠ 0 := by
    intro c hc
    obtain ⟨i, hi, j, hj, rfl⟩ := hmem c hc
    exact ⟨(hent i hi j hj).1.ne_zero, hent i hi j hj⟩
  have hMmij : ∀ i < N, ∀ j < N, (Mm.getD i []).getD j O1.zero = (Mc.getD i []).getD j O1.zero :=
    fun i hi j hj ↦ by rw [hMm, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
  have hMme : ∀ i < N, ∀ j < N, (Mm.getD i []).getD j O1.zero ∈ Mm.flatten := fun i hi j hj ↦ by
    rw [List.mem_flatten]
    refine ⟨Mm.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMm] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Mm.getD i []).length := by
        rw [hMm, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Mm.getD i []) _ hlen]; exact List.getElem_mem _
  set q := lcmGL O (Mm.flatten.map Prod.snd) with hq
  set hh := lcmGL O ((f ++ gs.flatten).map Prod.snd) with hhh
  have hdens : ∀ d ∈ Mm.flatten.map Prod.snd, GPoly.toPoly P d ≠ 0 := by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1
  obtain ⟨hqm, hqd, hqs⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) hdens
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P ((f ++ gs.flatten).map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc)
  have hsq : Squarefree (GPoly.toPoly P q) := hqs (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).2.1)
  have hq0 : (GPoly.toPoly P q).coeff 0 ≠ 0 := by
    intro h0'
    rw [← X_dvd_iff] at h0'
    obtain ⟨d, hd, hXd⟩ := lcmGL_prime P _ hdens X prime_X h0'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact (hent' c hc).2.2 (X_dvd_iff.mp hXd)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      ((f ++ gs.flatten).map fun c ↦ cofC O hh c.2).all Prod.fst && isMonicC O q &&
        isMonicC O hh) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨⟨?_, ?_⟩, isMonicC_of_monic P q hqm⟩, isMonicC_of_monic P hh hhm⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_map_of_mem hc))
  have hq0c : O.isZero (q.getD 0 O.zero) = false := by
    cases hz' : O.isZero (q.getD 0 O.zero)
    · rfl
    · exact absurd (by rw [coeff_toPoly_sem]; exact (P.isZero_iff _).mp hz') hq0
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  have hzc : zeroOKE Fc ks m (O.deriv a) N N0 q A0 C Ci = true := by
    refine T.zeroOKE_of m h0 _ N N0 q A0 C Ci lam0 hq0 hb0 (fun i j ↦ ?_) hN0 hP hC1 hC2
    have he := hMmij j j.2 i i.2
    have hqe := cofC_snd P q _ (hent' _ (hMme j j.2 i i.2)).1 (hqd _ (List.mem_map_of_mem (hMme j j.2 i i.2)))
    simp only [hA0]
    rw [GPoly.toPoly_mul, mul_coeff_zero, hqe, mul_coeff_zero, he, hz j j.2 i i.2]
    ring
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp
    (T.indBound2_isSome m h0 (degG O q) N q (DzLC O O.zero (O.deriv a) q) A0 hqm (degG_eq P q).symm
      (T.hpd_exp m h0 hm hk htr q hsq hq0))
  set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
  set E := GPoly.mul O (GPoly.mul O hh (sysPowC O q B)) (sysPowC O (tX Fc ks m) R) with hE
  have hE0 : GPoly.toPoly P E ≠ 0 := by
    rw [hE, GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
    exact mul_ne_zero (mul_ne_zero hhm.ne_zero (pow_ne_zero _ hqm.ne_zero))
      (pow_ne_zero _ X_ne_zero)
  have hlim' : ∀ i < N, ∀ j < N, (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).1).natDegree ≤
      (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).2).natDegree ∧
      (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).1).coeff
      (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).2).natDegree =
      P.sem (O.deriv a) * (lamI j i : T.F m) * (GPoly.toPoly P ((((conjM Fc ks m N C
      (rescaleME Fc ks m (O.deriv a) N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
      O1.zero).2).leadingCoeff := by
    intro i hi j hj
    obtain ⟨A, B', hB', hAB, hc, hv⟩ := hlim i hi j hj
    rw [conjRed_entry N C _ Ci i j hi hj]
    exact T.limit_of_sem h1 htr _ (T.redC_den_ne_zero m h1 _) A B' hB' hAB _ hc
      (by rw [T.sem_redC m h1 htr]; exact hv)
  have hWE : (exactWEL Fc ks m (fun n A0 q hh G0 ↦ expSysB Fc ks m a rdeD n A0 q hh G0 0) N
      ((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a) N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m))
      ((vecCi Fc ks m N (rescaleF Fc ks m N f r) Ci).map (redC Fc ks m))
      (gs.map fun g ↦ (vecCi Fc ks m N (rescaleF Fc ks m N g r) Ci).map (redC Fc ks m)) E).isSome :=
    T.exactWEL_isSome_exp m h0 a rdeD hb0 N hN _ _ _
      (fun i hi j hj ↦ ⟨by rw [conjRed_entry N C _ Ci i j hi hj]; exact T.redC_den_ne_zero m h1 _,
        (hlim' i hi j hj).1⟩)
      lamI (fun i hi j hj ↦ (hlim' i hi j hj).2) htri
      (by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
          exact T.redC_den_ne_zero m h1 _
        · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
          obtain ⟨g, -, rfl⟩ := List.mem_map.mp hl
          obtain ⟨c', -, rfl⟩ := List.mem_map.mp hcl
          exact T.redC_den_ne_zero m h1 _)
      E hE0
  unfold exactWREL
  simp only [hN, ↓reduceIte]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hq0c]
  rw [← hA0]
  simp only [hzc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hB]
  exact hWE

end Lim

end MTower

end Curves.MT
