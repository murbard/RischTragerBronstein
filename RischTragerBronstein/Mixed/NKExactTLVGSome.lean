import RischTragerBronstein.Mixed.NKExactTLVG
import RischTragerBronstein.Mixed.SysPrimVGSome
import RischTragerBronstein.Mixed.NKExactWRVSome
import RischTragerBronstein.Mixed.NKExactTVSome

/-!
# When the gauged parametric exact-part tests answer

`exactWLEVG_isSome`, `exactWRVLG_isSome`: the tests with several right-hand sides and the solver
`primSysVG` answer when the (rescaled) derivation matrix is bounded at infinity, its limit becomes
triangular after the gauge `C`, the limit system is non-degenerate and (for the rescaled
version) the denominators are squarefree.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`exactWLE` answers** with the gauged solver `primSysVG` when the derivation matrix is bounded
at infinity and its limit becomes triangular after the gauge, with a non-degenerate limit
system. -/
theorem exactWLEVG_isSome (m : ℕ) (h : T.Tr m) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m)))
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1))))
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).natDegree ≤
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).natDegree)
    (hinv : invOKG Fc ks m N C Ci = true)
    (htri : ∀ a b : Fin N, b < a → gaugeM (fun i j : Fin N ↦ (T.MP m h).sem (cgV Fc ks m C i j))
      (fun i j : Fin N ↦ (T.MP m h).sem (cgV Fc ks m Ci i j))
      (fun a b : Fin N ↦ T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
        a b = 0)
    (hdiag : ∀ a : Fin N, gaugeM (fun i j : Fin N ↦ (T.MP m h).sem (cgV Fc ks m C i j))
      (fun i j : Fin N ↦ (T.MP m h).sem (cgV Fc ks m Ci i j))
      (fun a b : Fin N ↦ T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
        a a = (T.MP m h).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg a)))
    (hok : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin N → T.F m, c ≠ 0 →
      (∀ a : Fin N, (c a)′ + ∑ b : Fin N,
        T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) * c b = 0) →
      ¬ ∃ y : Fin N → T.F m, ∀ a : Fin N, (y a)′ + ∑ b : Fin N,
        T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) * y b =
          (T.MP m h).sem η * c a)
    (hf : ∀ c ∈ f ++ gs.flatten, GPoly.toPoly (T.MP m h) c.2 ≠ 0) (E : GPoly (LC m))
    (hE : GPoly.toPoly (T.MP m h) E ≠ 0) :
    (exactWLE Fc ks m (fun n A0 q hh G0 ↦ primSysVG Fc ks m η rde dg C Ci n A0 q hh G0) N Mc f gs
      E).isSome := by
  set O := MO Fc ks m with hO
  set P := T.MP m h with hP
  set O1 := MOr Fc ks (m + 1) with hO1
  set Mm : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMm
  have hmem : ∀ c ∈ Mm.flatten, ∃ i < N, ∃ j < N, c = (Mc.getD i []).getD j O1.zero := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcl
    exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, rfl⟩
  have hent' : ∀ c ∈ Mm.flatten, GPoly.toPoly P c.2 ≠ 0 ∧
      (GPoly.toPoly P c.1).natDegree ≤ (GPoly.toPoly P c.2).natDegree := by
    intro c hc
    obtain ⟨i, hi, j, hj, rfl⟩ := hmem c hc
    exact hent i hi j hj
  set q := lcmGL O (Mm.flatten.map Prod.snd) with hq
  set hh := lcmGL O ((f ++ gs.flatten).map Prod.snd ++ [E]) with hhh
  obtain ⟨hqm, hqd, -⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1)
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P ((f ++ gs.flatten).map Prod.snd ++ [E]) (by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc
    · rw [List.mem_singleton.mp hd]; exact hE)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      ((f ++ gs.flatten).map fun c ↦ cofC O hh c.2).all Prod.fst && (cofC O hh E).1) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨?_, ?_⟩, cofC_fst P hh E hE (hhd _ (List.mem_append_right _ (List.mem_singleton_self _)))⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_append_left _ (List.mem_map_of_mem hc)))
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  have hAe : ∀ i j, (GPoly.toPoly P (A0 i j)).natDegree ≤ (GPoly.toPoly P q).natDegree ∧
      (GPoly.toPoly P (A0 i j)).coeff (GPoly.toPoly P q).natDegree =
        T.limE m h ((Mc.getD j []).getD i (MOr Fc ks (m + 1)).zero) := by
    intro j i
    set c := (Mm.getD i []).getD j O1.zero with hc
    have hcm : c ∈ Mm.flatten := by
      rw [hc, hMm, NestTower.getD_range_map _ _ i.2, NestTower.getD_range_map _ _ j.2]
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩,
        List.mem_map.mpr ⟨j, List.mem_range.mpr j.2, rfl⟩⟩
    have hcM : c = (Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero := by
      rw [hc, hMm, NestTower.getD_range_map _ _ i.2, NestTower.getD_range_map _ _ j.2]
    obtain ⟨h0, hdeg⟩ := hent' c hcm
    have := T.entry_lim m h q c hqm h0 (hqd _ (List.mem_map_of_mem hcm)) hdeg
    rw [← hcM]
    exact this
  have hmon : (isMonicC O q && isMonicC O hh) = true := by
    rw [isMonicC_of_monic P q hqm, isMonicC_of_monic P hh hhm]; rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (T.primSysVG_isSome h η rde hrde dg C Ci N A0 q hh _ hmon (fun a b ↦ (hAe a b).1)
      (fun a b ↦ T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
      (fun a b ↦ (hAe a b).2) hinv htri hdiag hok hnd)
  unfold exactWLE
  simp only [matFn_matData]
  simp only [hN, ↓reduceIte]
  split_ifs with hc
  · rw [Bool.not_eq_true'] at hc
    exact absurd (hc.symm.trans hcheck) (by decide)
  split
  · rename_i heq
    exact absurd (heq.symm.trans hr) (by simp)
  · rfl



variable {m : ℕ} (h1 : T.Tr (m + 1))

/-- **`exactWRVLG` answers** when the denominators of the matrix of `w` are squarefree and the
limit of the rescaled matrix becomes triangular after the gauge `C`, with a non-degenerate limit
system. -/
theorem exactWRVLG_isSome (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m)))
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      Squarefree (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2))
    (hprop : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h1.of_succ)
        (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      (GPoly.toPoly (T.MP m h1.of_succ)
        (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero).1).natDegree ≤
      (GPoly.toPoly (T.MP m h1.of_succ)
        (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero).2).natDegree)
    (hinv : invOKG Fc ks m N C Ci = true)
    (htri : ∀ a b : Fin N, b < a → gaugeM
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m C i j))
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Ci i j))
      (fun a b : Fin N ↦ T.limE m h1.of_succ
        (((rescaleM Fc ks m η N Mc r).getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
        a b = 0)
    (hdiag : ∀ a : Fin N, gaugeM
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m C i j))
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Ci i j))
      (fun a b : Fin N ↦ T.limE m h1.of_succ
        (((rescaleM Fc ks m η N Mc r).getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
        a a = (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg a)))
    (hok : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h1.of_succ).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin N → T.F m, c ≠ 0 →
      (∀ a : Fin N, (c a)′ + ∑ b : Fin N, T.limE m h1.of_succ
        (((rescaleM Fc ks m η N Mc r).getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) *
          c b = 0) →
      ¬ ∃ y : Fin N → T.F m, ∀ a : Fin N, (y a)′ + ∑ b : Fin N, T.limE m h1.of_succ
        (((rescaleM Fc ks m η N Mc r).getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) *
          y b = (T.MP m h1.of_succ).sem η * c a)
    (hf : ∀ c ∈ f ++ gs.flatten, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWRVLG Fc ks m η rde dg C Ci N Mc f gs r).isSome := by
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
  have hres_ne : ∀ g : List (LC (m + 1)), (∀ c ∈ g, GPoly.toPoly P c.2 ≠ 0) →
      ∀ c ∈ rescaleF Fc ks m N g r, GPoly.toPoly P c.2 ≠ 0 := by
    intro g hg c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    refine T.tpowL_snd_ne_zero h1 _ _ ?_
    by_cases hjf : j < g.length
    · exact hg _ (by rw [List.getD_eq_getElem _ _ hjf]; exact List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      show GPoly.toPoly P [O.one] ≠ 0
      simp only [GPoly.toPoly, hO, P.sem_one]; simp
  have hWE := T.exactWLEVG_isSome m h0 η rde hrde dg C Ci N hN (rescaleM Fc ks m η N Mc r)
    (rescaleF Fc ks m N f r) (gs.map fun g ↦ rescaleF Fc ks m N g r) hprop hinv htri hdiag hok hnd
    (by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hres_ne f (fun c hc ↦ hf c (List.mem_append_left _ hc)) c hc
      · obtain ⟨g', hg', hcg⟩ := List.mem_flatten.mp hc
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
        exact hres_ne g (fun c hc ↦ hf c (List.mem_append_right _
          (List.mem_flatten.mpr ⟨g, hg, hc⟩))) c hcg)
    E hE0
  unfold exactWRVLG exactWRSL
  simp only [hN, ↓reduceIte, matFn_matData]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← hA0, hB]
  exact hWE


variable (m : ℕ)

variable {m} in
set_option maxHeartbeats 1600000 in
/-- **`exactTLVG` answers** (non-constant curves: a limit `Λ` triangular after a gauge `C`). -/
theorem exactTLVG_isSome (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hPc : (MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero)
      ((MOr Fc ks (m + 1)).neg (MOr Fc ks (m + 1)).one)) = true)
    (hN : P.length - 1 ≠ 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (dθ : GPoly (LC (m + 1))) (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ)
    (Tc Ti : List (List (LC (m + 1))))
    (hok : prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true ∧
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true)
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (Mval : ℕ → ℕ → T.F (m + 1))
    (hMval : ∀ i < P.length - 1, (∑ k ∈ Finset.range (P.length - 1), ((T.MPr (m + 1) h1).sem
        ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range (P.length - 1), (Mval i j : L) *
        ∑ k ∈ Finset.range (P.length - 1), ((T.MPr (m + 1) h1).sem
          ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k)
    (hsq : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      Mval i j = T.phi m A / T.phi m S)
    (Λ : ℕ → ℕ → T.F m)
    (hprop : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.natDegree ≤ B.natDegree ∧ A.coeff B.natDegree / B.leadingCoeff = Λ i j ∧
      Mval i j * T.tau m ^ (r j - r i) - (if i = j then (r i : T.F (m + 1)) *
        T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) / T.tau m else 0) =
        T.phi m A / T.phi m B)
    (hinv : invOKG Fc ks m (P.length - 1) C Ci = true)
    (htri : ∀ a b : Fin (P.length - 1), b < a → gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m C i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Ci i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a b = 0)
    (hdiag : ∀ a : Fin (P.length - 1), gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m C i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Ci i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a a =
        (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg a)))
    (hokd : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h1.of_succ).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin (P.length - 1) → T.F m, c ≠ 0 →
      (∀ a : Fin (P.length - 1), (c a)′ + ∑ b : Fin (P.length - 1), Λ b a * c b = 0) →
      ¬ ∃ y : Fin (P.length - 1) → T.F m, ∀ a : Fin (P.length - 1),
        (y a)′ + ∑ b : Fin (P.length - 1), Λ b a * y b = (T.MP m h1.of_succ).sem η * c a) :
    (exactTLVG Fc ks m η rde dg C Ci r P Tc Ti f gs).isSome := by
  classical
  set O1 := MOr Fc ks (m + 1) with hO1
  set M1 := T.MPr (m + 1) h1 with hM1
  set N := P.length - 1 with hNdef
  -- `P` is monic of degree `N`
  have hlead : M1.sem (P.getD N O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPdeg : (GPoly.toPoly M1 P).natDegree = N := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : N < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  obtain ⟨hwd, hindw⟩ := T.basisW_facts m h1 P θ hP N hPm hPdeg hind dθ hd Tc Ti hok
  -- the computed matrix is `Mval`
  have hsem : ∀ i < N, ∀ j < N,
      M1.sem (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero) = Mval i j := by
    intro i hi
    have h0 := hindw (fun j ↦ M1.sem (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero) -
      Mval i j) (by
        have := (hwd i hi).symm.trans (hMval i hi)
        push_cast
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]; exact this)
    intro j hj
    exact sub_eq_zero.mp (h0 j hj)
  set MW := matW Fc ks m P dθ Tc Ti N with hMW
  set Mc' := MW.map fun l ↦ l.map (redC Fc ks m) with hMc'
  set M := T.MP m h1.of_succ
  have hent : ∀ i < N, ∀ j < N, GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2 ≠ 0 ∧
      Squarefree (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2) := by
    intro i hi j hj
    rw [hMc', redMat_entry (Fc := Fc) (ks := ks) m P dθ Tc Ti N i j hi hj]
    refine ⟨T.redC_den_ne_zero m h1 _, ?_⟩
    obtain ⟨A, S, hS, hAS⟩ := hsq i hi j hj
    exact T.redC_den_squarefree m h1 htr _ A S hS (by rw [hsem i hi j hj]; exact hAS)
  have hprop' : ∀ i < N, ∀ j < N,
      GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).2 ≠ 0 ∧
      (GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).1).natDegree ≤
      (GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).2).natDegree ∧
      T.limE m h1.of_succ (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero) = Λ i j := by
    intro i hi j hj
    obtain ⟨A, B, hB, hAB, hΛ, hval⟩ := hprop i hi j hj
    have hc := redMat_entry (Fc := Fc) (ks := ks) m P dθ Tc Ti N i j hi hj
    have hcd := T.redC_den_ne_zero m h1 (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero)
    have hcs := T.sem_redC m h1 htr (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero)
    rw [hsem i hi j hj] at hcs
    rw [rescaleM, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
    rw [← hMc'] at hc
    split_ifs with hij
    · subst hij
      rw [hc]
      have hden : GPoly.toPoly M (addOverT Fc ks m (tpowL Fc ks m 0 (redC Fc ks m
          (((matW Fc ks m P dθ Tc Ti N).getD i []).getD i O1.zero)))
          ((MO Fc ks m).mul (mcst Fc ks m (-(r i : ℚ))) η)).2 ≠ 0 := by
        simp only [addOverT, GPoly.toPoly_mul, tpowL_zero_snd]
        exact mul_ne_zero hcd (by rw [T.toPoly_tX]; exact X_ne_zero)
      refine T.limE_of_sem h1 htr _ hden A B hB hAB hΛ ?_
      rw [T.sem_addOverT m h1 htr _ _ (by
        rw [tpowL_zero_snd]
        exact fun h0 ↦ hcd (T.phi_injective htr (by rw [h0, map_zero]))),
        T.sem_tpowL m h1 htr, hcs, (T.MP m h1.of_succ).sem_mul, T.sem_mcst m h1.of_succ, ← hval,
        if_pos rfl, sub_self, zpow_zero]
      have : T.phi m (Polynomial.C (((-(r i : ℚ) : ℚ) : T.F m) * (T.MP m h1.of_succ).sem η)) =
          (-(r i : T.F (m + 1))) * T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) := by
        rw [Polynomial.C_mul, map_mul]; congr 1; simp
      rw [this]; ring
    · rw [hc]
      refine T.limE_of_sem h1 htr _ (T.tpowL_snd_ne_zero h1 _ _ hcd) A B hB hAB hΛ ?_
      rw [T.sem_tpowL m h1 htr, hcs, ← hval, if_neg hij, sub_zero]
  have hf' : ∀ c ∈ (vecF Fc ks m f Ti N).map (redC Fc ks m) ++
      (gs.map fun g ↦ (vecF Fc ks m g Ti N).map (redC Fc ks m)).flatten,
      GPoly.toPoly M c.2 ≠ 0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hc
      exact T.redC_den_ne_zero m h1 c0
    · obtain ⟨g', hg', hcg⟩ := List.mem_flatten.mp hc
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hg'
      obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hcg
      exact T.redC_den_ne_zero m h1 c0
  have e : ∀ a b : Fin N, T.limE m h1.of_succ
      (((rescaleM Fc ks m η N Mc' r).getD (b : ℕ) []).getD (a : ℕ) O1.zero) = Λ b a :=
    fun a b ↦ (hprop' b b.2 a a.2).2.2
  have he : (fun a b : Fin N ↦ T.limE m h1.of_succ
      (((rescaleM Fc ks m η N Mc' r).getD (b : ℕ) []).getD (a : ℕ) O1.zero)) =
      fun a b : Fin N ↦ Λ b a := funext fun a ↦ funext fun b ↦ e a b
  have hWR := T.exactWRVLG_isSome h1 hm hk htr rde hrde dg C Ci N hN Mc'
    ((vecF Fc ks m f Ti N).map (redC Fc ks m))
    (gs.map fun g ↦ (vecF Fc ks m g Ti N).map (redC Fc ks m)) r hent
    (fun i hi j hj ↦ ⟨(hprop' i hi j hj).1, (hprop' i hi j hj).2.1⟩) hinv
    (fun a b hba ↦ by rw [he]; exact htri a b hba)
    (fun a ↦ by rw [he]; exact hdiag a) hokd
    (by
      intro c hc hhom hy
      refine hnd c hc (fun a ↦ by
        rw [← hhom a]; congr 1; exact Finset.sum_congr rfl fun b _ ↦ by rw [e a b]) ?_
      obtain ⟨y, hy⟩ := hy
      exact ⟨y, fun a ↦ by
        rw [← hy a]; congr 1; exact Finset.sum_congr rfl fun b _ ↦ by rw [e a b]⟩) hf'
  -- unfold `exactTR`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTLVG
  simp only
  rw [if_neg hcheck, hd]
  exact hWR

end MTower

end Curves.MT
