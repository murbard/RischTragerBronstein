import RischTragerBronstein.Mixed.NKExactWR
import RischTragerBronstein.Mixed.NKExactWEL

/-!
# The rescaled exact-part test with several parameters (primitive level)

`exactWRL f gs r`: is `f − ∑ cᵢ gᵢ` exact for some constants `cᵢ`, in a basis `w` rescaled by
`t^{−r}` (`exactWR` with `exactWEL`)? Correct for every basis and shifts (`exactWRL_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test with several parameters in the basis `w` rescaled by `t^{−r}`.** -/
def exactWRL (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) : Option Bool :=
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
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
      GPoly.mul O ((M.getD i []).getD j O1.zero).1 (cofC O q ((M.getD i []).getD j O1.zero).2).2
    match indBound2 Fc ks m (degG O q) N q (DzLC O η O.zero q) A0 with
    | none => none
    | some B =>
      let R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0
      let E := GPoly.mul O (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R)
      exactWEL Fc ks m (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) N
        (rescaleM Fc ks m η N Mc r) (rescaleF Fc ks m N f r)
        (gs.map fun g ↦ rescaleF Fc ks m N g r) E

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) {m : ℕ} (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **Correctness of `exactWR`**: for any basis `w` with derivation matrix `Mc` and any shifts `r`,
an answer `res` says whether `∑ fⱼ wⱼ` has an antiderivative `∑ Yᵢ wᵢ`. -/
theorem exactWRL_correct (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (res : Bool) (hres : exactWRL Fc ks m η lim N Mc f gs r = some res) :
    res = true ↔ ∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θw j := by
  classical
  unfold exactWRL at hres
  simp only at hres
  split_ifs at hres with hN0 hcof
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
  set Gc : (ℕ → Cc) → Fin N → (T.F m)[X] := fun c j ↦ GPoly.toPoly M (numF (f.getD j O1.zero)) -
    ∑ i ∈ Finset.range gs.length, C (algebraMap Cc (T.F m) (c i)) *
      GPoly.toPoly M (numF ((gs.getD i []).getD j O1.zero)) with hGc
  -- the rescaled basis
  set θt : ℕ → L := fun i ↦ ((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i with hθt
  have hwt := T.rescale_deriv h1 hm hk htr N Mc r θw hw hden
  have hindt := T.rescale_ind htr N r θw hind
  have hspec := T.primSpecB hm h0 hk lim hlim
  obtain ⟨ha, hb⟩ := T.exactWEL_correct m h1 htr _ ((T.MP m h0).sem η) 0 hspec N
    (rescaleM Fc ks m η N Mc r) (rescaleF Fc ks m N f r) θt hwt hindt
    (gs.map fun g ↦ rescaleF Fc ks m N g r) _ res hres
  have hrhs : ∀ c : ℕ → Cc, ∑ j ∈ Finset.range N,
      (((T.MPr (m + 1) h1).sem ((rescaleF Fc ks m N f r).getD j (MOr Fc ks (m + 1)).zero) : L) -
        ∑ i ∈ Finset.range (gs.map fun g ↦ rescaleF Fc ks m N g r).length, algebraMap Cc L (c i) *
          ((T.MPr (m + 1) h1).sem (((gs.map fun g ↦ rescaleF Fc ks m N g r).getD i []).getD j
            (MOr Fc ks (m + 1)).zero) : L)) * θt j =
      ∑ j ∈ Finset.range N,
        (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
          ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
            ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
          θw j := by
    intro c
    simp only [sub_mul, Finset.sum_sub_distrib, List.length_map]
    congr 1
    · exact T.rescale_rhs h1 htr N f r θw
    · simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hgl : (gs.map fun g ↦ rescaleF Fc ks m N g r).getD i [] =
          rescaleF Fc ks m N (gs.getD i []) r := by
        have hi' := Finset.mem_range.mp hi
        rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
          List.getD_eq_getElem _ _ hi']
      rw [hgl]
      have := T.rescale_rhs h1 htr N (gs.getD i []) r θw
      calc ∑ j ∈ Finset.range N, algebraMap Cc L (c i) * ((T.MPr (m + 1) h1).sem
            ((rescaleF Fc ks m N (gs.getD i []) r).getD j (MOr Fc ks (m + 1)).zero) : L) * θt j
          = algebraMap Cc L (c i) * ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
            ((rescaleF Fc ks m N (gs.getD i []) r).getD j (MOr Fc ks (m + 1)).zero) : L) *
              (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by simp only [hθt]; ring
        _ = ∑ j ∈ Finset.range N, algebraMap Cc L (c i) * ((T.MPr (m + 1) h1).sem
            ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j := by
            rw [this, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hsumY : ∀ Y : ℕ → T.F (m + 1), ∑ i ∈ Finset.range N, (Y i : L) * θt i =
      ∑ i ∈ Finset.range N, ((Y i * T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i := fun Y ↦
    Finset.sum_congr rfl fun i _ ↦ by simp only [hθt]; push_cast; ring
  constructor
  · intro hrt
    obtain ⟨c, Y, hY⟩ := ha hrt
    refine ⟨c, fun i ↦ Y i * T.tau m ^ (-r i), ?_⟩
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
    have hphiC : ∀ a : Cc, T.phi m (C (algebraMap Cc (T.F m) a)) = algebraMap Cc (T.F (m + 1)) a :=
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
    have hsol : SysSol ((T.MP m h0).sem η) 0 qs hs (semMat M A0f) (Gc c) Z d := by
      refine T.sysSol_of_phiG m htr _ 0 (T.phi_DzL m hm hk h0) qs hs (semMat M A0f) _ Z d fun j ↦ ?_
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
          C (e : T.F m) * DzL ((T.MP m h0).sem η) 0 qs else 0).det → e ≤ B :=
      fun p e hp hpq hdet ↦ T.indBound2_spec m h0 (degG O q) N q (DzLC O η O.zero q) A0f hqM
        (degG_eq M q).symm B hB e p hp hpq (by rwa [toPoly_DzLC, M.sem_zero])
    have hdvd := fun i ↦ sys_den_bound ((T.MP m h0).sem η) 0 qs hs hhs0 (semMat M A0f) _ B hindB
      Z d hd0 hsol 1 (fun p e hp hpd _ ↦ absurd hpd (T.not_dvd_DzL m h0 η hm htr hk p hp)) i
    choose u hu using hdvd
    -- the bound for the rescaled coordinates
    set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
    have hRi : ∀ i < N, (-r i).toNat ≤ R := fun i hi ↦
      Tower.Sys.le_foldr_max _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    refine hb ⟨c, fun i ↦ Y i * T.tau m ^ r i, fun i ↦ if hi : i < N then
      u ⟨i, hi⟩ * X ^ (R - (-r i).toNat + (r i).toNat) else 0, fun i hi ↦ ?_, ?_⟩
    · simp only [dif_pos hi]
      have hE : GPoly.toPoly M (GPoly.mul O (GPoly.mul O hq (sysPowC O q B))
          (sysPowC O (tX Fc ks m) R)) = hs * qs ^ B * X ^ R := by
        rw [GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
      rw [hE, map_mul, map_mul, map_pow, map_mul, map_pow, map_pow]
      have hui := hu ⟨i, hi⟩
      rw [mul_one] at hui
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
    · rw [hsumY, hrhs c]
      convert hY using 2
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_assoc, ← zpow_add₀ (T.tau_ne_zero m htr), add_neg_cancel, zpow_zero, mul_one]

/-- **`exactWRL` answers** when the denominators of the matrix of `w` are squarefree, the rescaled
matrix vanishes at infinity and `η` is not a derivative (an integral basis normal at infinity). -/
theorem exactWRL_isSome (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      Squarefree (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2))
    (hprop : ∀ i < N, ∀ j < N,
      (GPoly.toPoly (T.MP m h1.of_succ)
        (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero).1).degree <
      (GPoly.toPoly (T.MP m h1.of_succ)
        (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero).2).degree)
    (hf : ∀ c ∈ f ++ gs.flatten, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWRL Fc ks m η lim N Mc f gs r).isSome := by
  set h0 := h1.of_succ with hh0
  set O := MO Fc ks m with hO
  set P := T.MP m h0 with hP
  set O1 := MOr Fc ks (m + 1) with hO1
  set Mm : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMm
  have hent' : ∀ c ∈ Mm.flatten, GPoly.toPoly P c.2 ≠ 0 ∧ Squarefree (GPoly.toPoly P c.2) := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcl
    exact hent i (List.mem_range.mp hi) j (List.mem_range.mp hj)
  set q := lcmGL O (Mm.flatten.map Prod.snd) with hq
  set hh := lcmGL O ((f ++ gs.flatten).map Prod.snd) with hhh
  obtain ⟨hqm, hqd, hqs⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1)
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P ((f ++ gs.flatten).map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc)
  have hsq : Squarefree (GPoly.toPoly P q) := hqs (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).2)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      ((f ++ gs.flatten).map fun c ↦ cofC O hh c.2).all Prod.fst && isMonicC O q &&
        isMonicC O hh) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨⟨?_, ?_⟩, isMonicC_of_monic P q hqm⟩, isMonicC_of_monic P hh hhm⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_map_of_mem hc))
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp
    (T.indBound2_isSome m h0 (degG O q) N q (DzLC O η O.zero q) A0 hqm (degG_eq P q).symm
      (T.not_dvd_DzLC_of_squarefree m h0 η hm htr hk q hsq))
  set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
  set E := GPoly.mul O (GPoly.mul O hh (sysPowC O q B)) (sysPowC O (tX Fc ks m) R) with hE
  have hE0 : GPoly.toPoly P E ≠ 0 := by
    rw [hE, GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
    exact mul_ne_zero (mul_ne_zero hhm.ne_zero (pow_ne_zero _ hqm.ne_zero))
      (pow_ne_zero _ X_ne_zero)
  have hresc : ∀ g, (∀ c ∈ g, GPoly.toPoly P c.2 ≠ 0) →
      ∀ c ∈ rescaleF Fc ks m N g r, GPoly.toPoly P c.2 ≠ 0 := by
    intro g hg c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    refine T.tpowL_snd_ne_zero h1 _ _ ?_
    by_cases hjf : j < g.length
    · exact hg _ (by rw [List.getD_eq_getElem _ _ hjf]; exact List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      show GPoly.toPoly P [O.one] ≠ 0
      simp only [GPoly.toPoly, hO, P.sem_one]; simp
  have hWE := T.exactWEL_isSome m h0 η lim hlim hη N hN (rescaleM Fc ks m η N Mc r)
    (rescaleF Fc ks m N f r) (gs.map fun g ↦ rescaleF Fc ks m N g r)
    (fun i hi j hj ↦ ⟨fun h0' ↦ by
        have := hprop i hi j hj
        rw [h0', degree_zero] at this
        exact absurd this (not_lt_bot), hprop i hi j hj⟩)
    (by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hresc f (fun c hc ↦ hf c (List.mem_append_left _ hc)) c hc
      · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
        exact hresc g (fun c hc ↦ hf c (List.mem_append_right _ (List.mem_flatten.mpr ⟨g, hg, hc⟩)))
          c hcl)
    E hE0
  unfold exactWRL
  simp only [hN, ↓reduceIte]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← hA0, hB]
  exact hWE


end MTower

end Curves.MT
