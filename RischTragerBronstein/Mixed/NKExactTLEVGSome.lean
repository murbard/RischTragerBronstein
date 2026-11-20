import RischTragerBronstein.Mixed.NKExactTLEVG
import RischTragerBronstein.Mixed.NKExactTEVSome
import RischTragerBronstein.Mixed.NKExactTLVGSome

/-!
# When the gauged exponential exact-part tests answer

`exactWLEVG_isSome_exp`, `exactWREVLG_isSome`, `exactTLEVG_isSome`: the tests with several
right-hand sides and the gauged solver `expSysVG` answer for a basis whose matrix is regular at
`t = 0` after the gauge `C` (as in `exactTEV_isSome`) and whose rescaled matrix has a limit at
infinity that the gauge `Cg` makes upper triangular with diagonal `pᵢ a′ + qᵢ cᵢ′/cᵢ`.
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

/-- **`exactWLE` answers** with the gauged solver `expSysVG` when the derivation matrix is bounded
at infinity and its limit becomes triangular after the gauge, with diagonal given by `dg`. -/
theorem exactWLEVG_isSome_exp (m : ℕ) (h : T.Tr m) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (C Ci : List (List (LC m)))
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
    (hdiag : ∀ i : Fin N, gaugeM (fun i j : Fin N ↦ (T.MP m h).sem (cgV Fc ks m C i j))
      (fun i j : Fin N ↦ (T.MP m h).sem (cgV Fc ks m Ci i j))
      (fun a b : Fin N ↦ T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
        i i = (T.MP m h).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg i))))
    (hf : ∀ c ∈ f ++ gs.flatten, GPoly.toPoly (T.MP m h) c.2 ≠ 0) (E : GPoly (LC m))
    (hE : GPoly.toPoly (T.MP m h) E ≠ 0) :
    (exactWLE Fc ks m (expSysVG Fc ks m a rde dg C Ci) N Mc f gs
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
    (T.expSysVG_isSome m h a rde dg C Ci N A0 q hh _ hmon (fun a b ↦ (hAe a b).1)
      (fun a b ↦ T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
      (fun a b ↦ (hAe a b).2) hinv htri hdiag)
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

variable {m : ℕ}

variable (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **`exactWREVLS` with `expSysVG` answers** (gauge `C` at `t = 0`, gauge `Cg` at infinity). -/
theorem exactWREVLG_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m))
    (Cg Cgi : List (List (LC m)))
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (hent : ∀ i < N, ∀ j < N,
      Squarefree (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2) ∧
      (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).coeff 0 ≠ 0)
    (M0v : ℕ → ℕ → T.F m)
    (hz : ∀ i < N, ∀ j < N,
      (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).coeff 0 =
        M0v j i *
          (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).coeff 0)
    (hC1 : ∀ i j : Fin N, ∑ k : Fin N, (T.MP m h1.of_succ).sem (cget Fc ks m C (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m Ci (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (hC2 : ∀ i j : Fin N, ∑ k : Fin N, (T.MP m h1.of_succ).sem (cget Fc ks m Ci (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m C (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (hgtri : ∀ i j : Fin N, j < i →
      ((Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)) *
        Matrix.of (fun i j : Fin N ↦ M0v i j) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j))) i j = 0)
    (hgdiag : ∀ i : Fin N,
      ((Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)) *
        Matrix.of (fun i j : Fin N ↦ M0v i j) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j))) i i =
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg0 (i : ℕ)))))
    (hgp : ∀ i : Fin N, (dgEAt Fc ks m dg0 (i : ℕ)).1.den ≠ 1 ∨ (dgEAt Fc ks m dg0 (i : ℕ)).1 ≤ 0)
    (Λ : ℕ → ℕ → T.F m)
    (hlim : ∀ i < N, ∀ j < N, ∃ A B : (T.F m)[X], B ≠ 0 ∧ A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree / B.leadingCoeff = Λ i j ∧
      (T.MPr (m + 1) h1).sem (((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) = T.phi m A / T.phi m B)
    (hinvg : invOKG Fc ks m N Cg Cgi = true)
    (htri : ∀ a b : Fin N, b < a → gaugeM
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cg i j))
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cgi i j))
      (fun a b : Fin N ↦ Λ b a) a b = 0)
    (hdiag : ∀ i : Fin N, gaugeM
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cg i j))
      (fun i j : Fin N ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cgi i j))
      (fun a b : Fin N ↦ Λ b a) i i =
        (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg i))))
    (hf : ∀ c ∈ f ++ gs.flatten, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWREVLS Fc ks m a (expSysVG Fc ks m a rde dg Cg Cgi) N Mc f gs r C Ci dg0).isSome := by
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
  have hzc : zeroOKV Fc ks m a N q A0 C Ci dg0 = true := by
    refine T.zeroOKV_of h0 a N q A0 C Ci dg0 (fun i j ↦ M0v i j) hq0 (fun i j ↦ ?_) hC1 hC2 hgtri hgdiag hgp
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
  have hlim' : ∀ i < N, ∀ j < N,
      GPoly.toPoly P ((((rescaleME Fc ks m (O.deriv a) N Mc r).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).2 ≠ 0 ∧
      (GPoly.toPoly P ((((rescaleME Fc ks m (O.deriv a) N Mc r).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).1).natDegree ≤
      (GPoly.toPoly P ((((rescaleME Fc ks m (O.deriv a) N Mc r).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).2).natDegree ∧
      T.limE m h0 ((((rescaleME Fc ks m (O.deriv a) N Mc r).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero) = Λ i j := by
    intro i hi j hj
    obtain ⟨A, B', hB', hAB, hc, hv⟩ := hlim i hi j hj
    have hrow : ((rescaleME Fc ks m (O.deriv a) N Mc r).getD i []).length = N := by
      rw [rescaleME, NestTower.getD_range_map _ _ hi, List.length_map, List.length_range]
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m,
      getD_map_redC_of_lt _ _ (by rw [hrow]; exact hj)]
    exact T.limE_of_sem h1 htr _ (T.redC_den_ne_zero m h1 _) A B' hB' hAB hc
      (by rw [T.sem_redC m h1 htr]; exact hv)
  have he : (fun x y : Fin N ↦ T.limE m h0 ((((rescaleME Fc ks m (O.deriv a) N Mc r).map
      fun l ↦ l.map (redC Fc ks m)).getD (y : ℕ) []).getD (x : ℕ) O1.zero)) =
      fun x y : Fin N ↦ Λ y x :=
    funext fun x ↦ funext fun y ↦ (hlim' y y.2 x x.2).2.2
  set Mr := (rescaleME Fc ks m (O.deriv a) N Mc r).map fun l ↦ l.map (redC Fc ks m) with hMr
  have htri' : ∀ x y : Fin N, y < x → gaugeM (fun i j : Fin N ↦ P.sem (cgV Fc ks m Cg i j))
      (fun i j : Fin N ↦ P.sem (cgV Fc ks m Cgi i j))
      (fun x y : Fin N ↦ T.limE m h0 ((Mr.getD (y : ℕ) []).getD (x : ℕ) O1.zero)) x y = 0 := by
    intro x y hyx
    rw [he]; exact htri x y hyx
  have hdiag' : ∀ x : Fin N, gaugeM (fun i j : Fin N ↦ P.sem (cgV Fc ks m Cg i j))
      (fun i j : Fin N ↦ P.sem (cgV Fc ks m Cgi i j))
      (fun x y : Fin N ↦ T.limE m h0 ((Mr.getD (y : ℕ) []).getD (x : ℕ) O1.zero)) x x =
        P.sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg x))) := by
    intro x
    rw [he]; exact hdiag x
  have hfr : ∀ c ∈ (rescaleF Fc ks m N f r).map (redC Fc ks m) ++
      (gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m)).flatten,
      GPoly.toPoly P c.2 ≠ 0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
      exact T.redC_den_ne_zero m h1 _
    · obtain ⟨g', hg', hcg⟩ := List.mem_flatten.mp hc
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hg'
      obtain ⟨c', -, rfl⟩ := List.mem_map.mp hcg
      exact T.redC_den_ne_zero m h1 _
  have hWE := T.exactWLEVG_isSome_exp m h0 a rde dg Cg Cgi N hN Mr
    ((rescaleF Fc ks m N f r).map (redC Fc ks m))
    (gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m))
    (fun i hi j hj ↦ ⟨(hlim' i hi j hj).1, (hlim' i hi j hj).2.1⟩) hinvg htri' hdiag' hfr E hE0
  unfold exactWREVLS
  simp only [hN, ↓reduceIte]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hq0c]
  rw [← hA0]
  simp only [hzc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hB]
  exact hWE


set_option maxHeartbeats 3200000 in
/-- **`exactTLEVG` answers in its regime** (non-constant curves over an exponential, several
places at infinity: a gauge `Cg` at infinity). -/
theorem exactTLEVG_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
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
    (M0v : ℕ → ℕ → T.F m)
    (hsq : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      S.coeff 0 ≠ 0 ∧ A.coeff 0 = M0v j i * S.coeff 0 ∧ Mval i j = T.phi m A / T.phi m S)
    (hC1 : ∀ i j : Fin (P.length - 1), ∑ k : Fin (P.length - 1),
      (T.MP m h1.of_succ).sem (cget Fc ks m C (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m Ci (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (hC2 : ∀ i j : Fin (P.length - 1), ∑ k : Fin (P.length - 1),
      (T.MP m h1.of_succ).sem (cget Fc ks m Ci (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m C (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (hgtri : ∀ i j : Fin (P.length - 1), j < i →
      ((Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)) *
        Matrix.of (fun i j : Fin (P.length - 1) ↦ M0v i j) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin (P.length - 1) ↦
          (T.MP m h1.of_succ).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)))
          i j = 0)
    (hgdiag : ∀ i : Fin (P.length - 1),
      ((Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)) *
        Matrix.of (fun i j : Fin (P.length - 1) ↦ M0v i j) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin (P.length - 1) ↦
          (T.MP m h1.of_succ).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)))
          i i =
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg0 (i : ℕ)))))
    (hgp : ∀ i : Fin (P.length - 1),
      (dgEAt Fc ks m dg0 (i : ℕ)).1.den ≠ 1 ∨ (dgEAt Fc ks m dg0 (i : ℕ)).1 ≤ 0)
    (Λ : ℕ → ℕ → T.F m)
    (hlim : ∀ k < P.length - 1, ∀ l < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.natDegree ≤ B.natDegree ∧ A.coeff B.natDegree / B.leadingCoeff = Λ k l ∧
      T.tau m ^ (r l - r k) * Mval k l -
          (if k = l then (r k : T.F (m + 1)) *
            T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a))) else 0) =
        T.phi m A / T.phi m B)
    (hinvg : invOKG Fc ks m (P.length - 1) Cg Cgi = true)
    (htri : ∀ a b : Fin (P.length - 1), b < a → gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cg i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cgi i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a b = 0)
    (hdiag : ∀ i : Fin (P.length - 1), gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cg i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cgi i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) i i =
        (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg i)))) :
    (exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 P Tc Ti f gs).isSome := by
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
  have hc : ∀ i < N, ∀ j < N, (Mc'.getD i []).getD j O1.zero =
      redC Fc ks m ((MW.getD i []).getD j O1.zero) := fun i hi j hj ↦
    redMat_entry (Fc := Fc) (ks := ks) m P dθ Tc Ti N i j hi hj
  have hcs : ∀ i < N, ∀ j < N, M1.sem ((Mc'.getD i []).getD j O1.zero) = Mval i j :=
    fun i hi j hj ↦ by rw [hc i hi j hj, T.sem_redC m h1 htr, hsem i hi j hj]
  have hent : ∀ i < N, ∀ j < N, Squarefree (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2) ∧
      (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2).coeff 0 ≠ 0 := by
    intro i hi j hj
    obtain ⟨A, S, hS, hS0, -, hAS⟩ := hsq i hi j hj
    rw [hc i hi j hj]
    refine ⟨T.redC_den_squarefree m h1 htr _ A S hS (by rw [hsem i hi j hj]; exact hAS), ?_⟩
    intro h0
    have hdv := T.redC_den_dvd h1 htr _ A S hS.ne_zero (by rw [hsem i hi j hj]; exact hAS)
    rw [← X_dvd_iff] at h0
    exact hS0 (X_dvd_iff.mp (h0.trans hdv))
  have hz : ∀ i < N, ∀ j < N, (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).1).coeff 0 =
      M0v j i * (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2).coeff 0 := by
    intro i hi j hj
    obtain ⟨A, S, -, hS0, hA0, hAS⟩ := hsq i hi j hj
    exact T.zero_of_sem h1 htr _ (by rw [hc i hi j hj]; exact T.redC_den_ne_zero m h1 _) A S hS0 _
      hA0 (by rw [hcs i hi j hj]; exact hAS)
  have hlim' : ∀ k < N, ∀ l < N, ∃ A B : (T.F m)[X], B ≠ 0 ∧ A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree / B.leadingCoeff = Λ k l ∧
      M1.sem (((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc' r).getD k []).getD l O1.zero) =
        T.phi m A / T.phi m B := by
    intro k hk l hl
    obtain ⟨A, B, hB, hAB, hcB, hv⟩ := hlim k hk l hl
    refine ⟨A, B, hB, hAB, hcB, ?_⟩
    rw [T.sem_rescaleME h1 htr _ N Mc' r k l hk hl (by
      rw [hc k hk k hk]
      exact fun h0 ↦ T.redC_den_ne_zero m h1 _ (T.phi_injective htr (by rw [h0, map_zero]))),
      hcs k hk l hl, ← hv]
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
  have hWRE := T.exactWREVLG_isSome h1 hm hk htr rde dg Cg Cgi N hN Mc'
    ((vecF Fc ks m f Ti N).map (redC Fc ks m))
    (gs.map fun g ↦ (vecF Fc ks m g Ti N).map (redC Fc ks m)) r C Ci dg0 hent M0v hz hC1 hC2
    hgtri hgdiag hgp Λ hlim' hinvg htri hdiag hf'
  -- unfold `exactTRE`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTLEVG exactTLEVS
  simp only
  rw [if_neg hcheck, hd]
  exact hWRE

end MTower

end Curves.MT
