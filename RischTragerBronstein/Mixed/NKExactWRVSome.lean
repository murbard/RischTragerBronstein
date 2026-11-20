import RischTragerBronstein.Mixed.NKExactWRV
import RischTragerBronstein.Mixed.SysPrimVSome

/-!
# When the exact-part test with a triangular limit answers

`exactWEV_isSome`, `exactWRV_isSome`: the tests with the solver `primSysV` answer for a basis
whose (rescaled) derivation matrix is bounded at infinity, with a lower triangular limit
`limE Mᵢⱼ` of diagonal `fCode dgᵢ` and a non-degenerate limit system (and squarefree
denominators, for the rescaled version).
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

/-- The value at infinity of a fraction code `num/den` with `deg num ≤ deg den`. -/
noncomputable def limE (m : ℕ) (h : T.Tr m) (c : LC (m + 1)) : T.F m :=
  (GPoly.toPoly (T.MP m h) c.1).coeff (GPoly.toPoly (T.MP m h) c.2).natDegree /
    (GPoly.toPoly (T.MP m h) c.2).leadingCoeff

/-- `num · (q/den)` has degree `≤ deg q` and top coefficient `lim num/den` (monic `q`). -/
lemma entry_lim (m : ℕ) (h : T.Tr m) (q : GPoly (LC m)) (c : LC (m + 1))
    (hqm : (GPoly.toPoly (T.MP m h) q).Monic) (h0 : GPoly.toPoly (T.MP m h) c.2 ≠ 0)
    (hdq : GPoly.toPoly (T.MP m h) c.2 ∣ GPoly.toPoly (T.MP m h) q)
    (hdeg : (GPoly.toPoly (T.MP m h) c.1).natDegree ≤ (GPoly.toPoly (T.MP m h) c.2).natDegree) :
    (GPoly.toPoly (T.MP m h) (GPoly.mul (MO Fc ks m) c.1 (cofC (MO Fc ks m) q c.2).2)).natDegree ≤
        (GPoly.toPoly (T.MP m h) q).natDegree ∧
      (GPoly.toPoly (T.MP m h) (GPoly.mul (MO Fc ks m) c.1 (cofC (MO Fc ks m) q c.2).2)).coeff
        (GPoly.toPoly (T.MP m h) q).natDegree = T.limE m h c := by
  have hqc := cofC_snd (T.MP m h) q c.2 h0 hdq
  have hcof0 : GPoly.toPoly (T.MP m h) (cofC (MO Fc ks m) q c.2).2 ≠ 0 := fun hz ↦
    hqm.ne_zero (by rw [hqc, hz, zero_mul])
  have hdq' : (GPoly.toPoly (T.MP m h) q).natDegree = (GPoly.toPoly (T.MP m h) c.2).natDegree +
      (GPoly.toPoly (T.MP m h) (cofC (MO Fc ks m) q c.2).2).natDegree := by
    rw [hqc, natDegree_mul hcof0 h0]; ring
  rw [GPoly.toPoly_mul, hdq']
  refine ⟨natDegree_mul_le.trans (by omega), ?_⟩
  rw [MTower.coeff_mul_of_natDegree_le' hdeg le_rfl, limE]
  have hlc : (GPoly.toPoly (T.MP m h) (cofC (MO Fc ks m) q c.2).2).leadingCoeff *
      (GPoly.toPoly (T.MP m h) c.2).leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hqc]; exact hqm.leadingCoeff
  have hden : (GPoly.toPoly (T.MP m h) c.2).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
  rw [eq_div_iff hden, mul_assoc]
  simp only [Polynomial.leadingCoeff] at hlc ⊢
  rw [hlc, mul_one]

/-- **`exactWE` answers** with the solver `primSysV` for a basis whose derivation matrix is bounded
at infinity with a lower triangular limit of diagonal `fCode dgᵢ` and a non-degenerate limit
system. -/
theorem exactWEV_isSome (m : ℕ) (h : T.Tr m) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (dg : List (FRep (LC m)))
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).natDegree ≤
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).natDegree)
    (htri : ∀ i < N, ∀ j < N, i < j →
      T.limE m h ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = 0)
    (hdiag : ∀ i < N, T.limE m h ((Mc.getD i []).getD i (MOr Fc ks (m + 1)).zero) =
      (T.MP m h).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg i)))
    (hok : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin N → T.F m, c ≠ 0 →
      (∀ a : Fin N, (c a)′ + ∑ b : Fin N,
        T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) * c b = 0) →
      ¬ ∃ y : Fin N → T.F m, ∀ a : Fin N, (y a)′ + ∑ b : Fin N,
        T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) * y b =
          (T.MP m h).sem η * c a)
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h) c.2 ≠ 0) (E : GPoly (LC m))
    (hE : GPoly.toPoly (T.MP m h) E ≠ 0) :
    (exactWE Fc ks m (fun n A0 q hh G0 ↦ primSysV Fc ks m η rde dg n A0 q hh G0) N Mc f E).isSome := by
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
  set hh := lcmGL O (f.map Prod.snd ++ [E]) with hhh
  obtain ⟨hqm, hqd, -⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1)
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P (f.map Prod.snd ++ [E]) (by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc
    · rw [List.mem_singleton.mp hd]; exact hE)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      (f.map fun c ↦ cofC O hh c.2).all Prod.fst && (cofC O hh E).1) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨?_, ?_⟩, cofC_fst P hh E hE (hhd _ (List.mem_append_right _ (List.mem_singleton_self _)))⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_append_left _ (List.mem_map_of_mem hc)))
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  set G : Fin N → GPoly (LC m) := fun j ↦
    GPoly.mul O (f.getD j O1.zero).1 (cofC O hh (f.getD j O1.zero).2).2 with hG
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
    (T.primSysV_isSome h η rde hrde dg N A0 q hh [G] hmon (fun a b ↦ (hAe a b).1)
      (fun a b ↦ T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
      (fun a b ↦ (hAe a b).2)
      (fun a b hba ↦ htri b b.2 a a.2 hba) (fun a ↦ hdiag a a.2) hok hnd)
  unfold exactWE
  simp only
  simp only [hN, ↓reduceIte]
  split_ifs with hc
  · rw [Bool.not_eq_true'] at hc
    exact absurd (hc.symm.trans hcheck) (by decide)
  split
  · rename_i heq
    exact absurd (heq.symm.trans hr) (by simp)
  · rfl


variable {m : ℕ} (h1 : T.Tr (m + 1))

/-- **`exactWRV` answers** (triangular limit version of `exactWR_isSome`) when the denominators of the matrix of `w` are squarefree, the rescaled
matrix vanishes at infinity and `η` is not a derivative (an integral basis normal at infinity). -/
theorem exactWRV_isSome (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m)))
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ)
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
    (htri : ∀ i < N, ∀ j < N, i < j → T.limE m h1.of_succ
      (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero) = 0)
    (hdiag : ∀ i < N, T.limE m h1.of_succ
      (((rescaleM Fc ks m η N Mc r).getD i []).getD i (MOr Fc ks (m + 1)).zero) =
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg i)))
    (hok : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h1.of_succ).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin N → T.F m, c ≠ 0 →
      (∀ a : Fin N, (c a)′ + ∑ b : Fin N, T.limE m h1.of_succ
        (((rescaleM Fc ks m η N Mc r).getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) *
          c b = 0) →
      ¬ ∃ y : Fin N → T.F m, ∀ a : Fin N, (y a)′ + ∑ b : Fin N, T.limE m h1.of_succ
        (((rescaleM Fc ks m η N Mc r).getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero) *
          y b = (T.MP m h1.of_succ).sem η * c a)
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWRV Fc ks m η rde dg N Mc f r).isSome := by
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
  set hh := lcmGL O (f.map Prod.snd) with hhh
  obtain ⟨hqm, hqd, hqs⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1)
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P (f.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc)
  have hsq : Squarefree (GPoly.toPoly P q) := hqs (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).2)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      (f.map fun c ↦ cofC O hh c.2).all Prod.fst && isMonicC O q && isMonicC O hh) = true := by
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
  have hWE := T.exactWEV_isSome m h0 η rde hrde dg N hN (rescaleM Fc ks m η N Mc r)
    (rescaleF Fc ks m N f r) hprop htri hdiag hok hnd
    (by
      intro c hc
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      refine T.tpowL_snd_ne_zero h1 _ _ ?_
      by_cases hjf : j < f.length
      · exact hf _ (by rw [List.getD_eq_getElem _ _ hjf]; exact List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)]
        show GPoly.toPoly P [O.one] ≠ 0
        simp only [GPoly.toPoly, hO, P.sem_one]; simp)
    E hE0
  unfold exactWRV exactWRS
  simp only [hN, ↓reduceIte]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← hA0, hB]
  exact hWE


end MTower

end Curves.MT
