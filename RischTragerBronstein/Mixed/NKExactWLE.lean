import RischTragerBronstein.Mixed.NKExactWL
import RischTragerBronstein.Mixed.NKExactWE

/-!
# The exact-part test with several parameters and a denominator bound

`exactWLE f gs E`: as `exactWL` (is `f − ∑ cᵢ gᵢ` exact for some constants?) for a solver that is
complete only for solutions whose denominators divide `E` (`SolverSpecB`): an answer `true` gives
an antiderivative, and an antiderivative with denominators dividing `E` forces `true`
(`exactWLE_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM CPoly

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test in any basis, with several parameters and a denominator bound `E`.** -/
def exactWLE (m : ℕ) (solve : SysSolver m) (N : ℕ) (Mc : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (E : GPoly (LC m)) : Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  if N = 0 then none else
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O ((f ++ gs.flatten).map Prod.snd ++ [E])
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst &&
        ((f ++ gs.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst && (cofC O hq E).1) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2
    let A0 : Fin N → Fin N → GPoly (LC m) :=
      matFn (matData fun (j i : Fin N) ↦ num ((M.getD i []).getD j O1.zero)) []
    let G0 : List (Fin N → GPoly (LC m)) := (f :: gs).map fun g j ↦ numF (g.getD j O1.zero)
    match solve N A0 q hq G0 with
    | none => none
    | some r => some (r.2.any fun b ↦ b.1.getD 0 0 != 0)

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ)

set_option maxHeartbeats 3200000 in
/-- **Correctness of the exact-part test with several parameters and a denominator bound.** -/
theorem exactWLE_correct (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m) (wD bD : T.F m) (S : T.SolverSpecB m h1.of_succ wD bD solve)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (gs : List (List (LC (m + 1)))) (E : GPoly (LC m)) (res : Bool)
    (hres : exactWLE Fc ks m solve N Mc f gs E = some res) :
    (res = true → ∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θw j) ∧
    ((∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)) (z : ℕ → (T.F m)[X]),
      (∀ i < N, Y i * T.phi m (GPoly.toPoly (T.MP m h1.of_succ) E) = T.phi m (z i)) ∧
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θw j) → res = true) := by
  classical
  unfold exactWLE at hres
  simp only [matFn_matData] at hres
  split_ifs at hres with hN0 hcof
  split at hres
  · exact absurd hres (by simp)
  rename_i r hr
  obtain rfl := Option.some.inj hres
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
  set hq := lcmGL O ((f ++ gs.flatten).map Prod.snd ++ [E]) with hhq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  set numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2 with hnumF
  obtain ⟨hDs, hqs0, hhs0⟩ := S.den _ _ _ _ _ r hr
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hq with hhs
  have hcof3 : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true ∧
      ((f ++ gs.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst = true ∧ (cofC O hq E).1 = true := by
    revert hcof
    cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;>
      cases ((f ++ gs.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst <;> cases (cofC O hq E).1 <;>
      simp
  have hcof2 : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true ∧
      ((f ++ gs.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst = true := ⟨hcof3.1, hcof3.2.1⟩
  -- `E` divides `h`
  have hEh : GPoly.toPoly M hq = GPoly.toPoly M (cofC O hq E).2 * GPoly.toPoly M E := by
    have hs := GPoly.divMod_spec M hq E
    have hr0 := (GPoly.isZero_iff M _).mp hcof3.2.2
    rw [hs]; simp only [cofC] at hr0 ⊢; rw [hr0, add_zero]
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hcofsF : ∀ c ∈ f ++ gs.flatten, (cofC O hq c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
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
  have hMθ : ∀ i < N, ∀ j < N, Mw i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), hMl, NestTower.getD_range_map _ _ hi,
      NestTower.getD_range_map _ _ hj]
  have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
  have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
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
  -- the coordinate equations
  have hcoord : ∀ Y R : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range N, (Y i : L) * θw i)′ = ∑ j ∈ Finset.range N,
        ((R j : T.F (m + 1)) : L) * θw j) ↔
      ∀ j < N, (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i = R j := by
    intro Y R
    have hdc := T.deriv_coordsW m N θw Mw hw Y
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i -
        R j) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hE]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0
    · intro hE
      exact Finset.sum_congr rfl fun j hj ↦ by rw [hE j (Finset.mem_range.mp hj)]
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
  refine ⟨fun hany ↦ ?_, ?_⟩
  · obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hany
    simp only [bne_iff_ne, ne_eq] at he
    set e : ℕ → ℚ := fun l ↦ b.1.getD l 0 with he_
    have hsS := S.sound _ _ _ _ _ r.1 r.2 (by simpa using hr) b hb
    have hphiD : T.phi m (GPoly.toPoly M r.1) ≠ 0 := fun h0' ↦ hDs (T.phi_injective htr
      (by rw [h0', map_zero]))
    have hE : ((e 0 : ℚ) : T.F (m + 1)) ≠ 0 := by exact_mod_cast he
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < N then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e 0 : T.F (m + 1))) else 0
      with hY
    set c : ℕ → Cc := fun i ↦ algebraMap ℚ Cc (-(e (i + 1) / e 0)) with hc
    refine ⟨c, Y, ?_⟩
    rw [hRc]
    refine (hcoord Y _).mpr fun j hj ↦ ?_
    have hcF : ∀ x : ℚ, algebraMap Cc (T.F (m + 1)) (algebraMap ℚ Cc x) = (x : T.F (m + 1)) :=
      fun x ↦ by rw [← IsScalarTower.algebraMap_apply]; exact eq_ratCast _ _
    have hphi := T.sysSol_phiG m wD bD S.hD qs hs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hsS
    rw [← hM] at hphi
    simp only [map_sum, map_mul, T.phi_C_ratCast, hRG, semMat, Matrix.of_apply] at hphi
    have hsp := hsplit (fun l ↦ ((b.1.getD l 0 : ℚ) : T.F (m + 1))) j
    rw [hsp] at hphi
    have key : Rc c j = T.phi m hs * ((e 0 : T.F (m + 1)) * R 0 j +
        ∑ i ∈ Finset.range gs.length, (e (i + 1) : T.F (m + 1)) * R (i + 1) j) /
        (T.phi m hs * (e 0 : T.F (m + 1))) := by
      have hsumc : ∑ i ∈ Finset.range gs.length, algebraMap Cc (T.F (m + 1)) (c i) * R (i + 1) j =
          -(∑ i ∈ Finset.range gs.length, (e (i + 1) : T.F (m + 1)) * R (i + 1) j) / e 0 := by
        rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hc, hcF]
        push_cast
        field_simp
      rw [hRc']
      simp only
      rw [hsumc]
      field_simp
      ring
    rw [key]
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)]
    have hMθ' : ∀ i : Fin N,
        Mw i j = T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ i)) / T.phi m qs :=
      fun i ↦ hMθ i i.2 j hj
    have hYi : ∀ i : Fin N, Y i = T.phi m (semV M b.2 i) /
        (T.phi m (GPoly.toPoly M r.1) * (e 0 : T.F (m + 1))) := fun i ↦ by
      rw [hY]; simp only [dif_pos i.2]
    have hYj : Y j = T.phi m (semV M b.2 ⟨j, hj⟩) /
        (T.phi m (GPoly.toPoly M r.1) * (e 0 : T.F (m + 1))) := by
      rw [hY]; simp only [dif_pos hj]
    simp only [hMθ', hYi]
    rw [hYj]
    exact solW_of_cleared _ _ _ _ _ _ _ _ hphiq hphih hphiD hE (T.deriv_ratCast _) hphi
  · rintro ⟨c, Y, z, hYz, hY⟩
    rw [hRc] at hY
    have heq := (hcoord Y _).mp hY
    set d := GPoly.toPoly M E with hdE
    set Z : Fin N → (T.F m)[X] := fun i ↦ z i with hZdef
    have hd0 : d ≠ 0 := fun h0' ↦ hhs0 (by rw [hhs, hEh, h0', mul_zero])
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin N, Y i = T.phi m (Z i) / T.phi m d := fun i ↦
      (eq_div_iff hphid).mpr (hYz i i.2)
    have hdvd : ∀ i, d ∣ hs * Z i := fun i ↦
      Dvd.dvd.mul_right ⟨_, by rw [hhs, hEh, mul_comm]⟩ _
    set cl : List Cc := 1 :: (List.range gs.length).map fun i ↦ -c i with hcl
    have hsol : SysSol wD bD qs hs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range G0.length,
          C (algebraMap Cc (T.F m) (cl.getD l 0)) *
          GPoly.toPoly M ((G0.getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phiG m htr wD bD S.hD qs hs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)] at hj
      have hMθ' : ∀ i : Fin N, Mw i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi] at hj
      have hphiC : ∀ a : Cc, T.phi m (C (algebraMap Cc (T.F m) a)) = algebraMap Cc (T.F (m + 1)) a :=
        fun a ↦ by rw [T.phi_C]; rfl
      simp only [map_sum, map_mul, hphiC, hRG, semMat, Matrix.of_apply]
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
    obtain ⟨β, hβc, -⟩ := S.complete _ _ _ _ _ r.1 r.2 (by simpa using hr) cl (fun l hl ↦ by
        rw [hG0len] at hl
        exact List.getD_eq_default _ _ (by simpa [hcl] using hl)) Z d hd0 hsol hdvd
    have h1' := hβc 0
    simp only [hcl, List.getD_cons_zero] at h1'
    by_contra hcon
    rw [Bool.not_eq_true, List.any_eq_false] at hcon
    have hz : ∀ k ∈ Finset.range r.2.length,
        β.getD k 0 * algebraMap ℚ Cc (((r.2.getD k ([], fun _ ↦ [])).1).getD 0 0) = 0 := by
      intro k hk
      have hmem : r.2.getD k ([], fun _ ↦ []) ∈ r.2 := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
      have := hcon _ hmem
      simp only [bne_iff_ne, ne_eq, not_not] at this
      rw [this, map_zero, mul_zero]
    rw [Finset.sum_eq_zero hz] at h1'
    exact one_ne_zero h1'

end MTower

end Curves.MT
