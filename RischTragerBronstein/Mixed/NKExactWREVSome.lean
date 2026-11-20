import RischTragerBronstein.Mixed.NKExactWREV
import RischTragerBronstein.Mixed.NKExactWRVSome
import RischTragerBronstein.Mixed.NKExactTVSome
import RischTragerBronstein.Mixed.NKExactWRESome

/-!
# When the exact-part test over an exponential answers (non-constant curves)

`exactWEV_isSome_exp`: `exactWE` with the solver `expSysV` answers for a basis whose derivation
matrix is bounded at infinity with a lower triangular limit of diagonal `pᵢ a′ + qᵢ cᵢ′/cᵢ`.
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

/-- **`exactWE` answers** with the solver `expSysV` at an exponential level for a basis whose
derivation matrix is bounded at infinity with a lower triangular limit of diagonal
`pᵢ a′ + qᵢ cᵢ′/cᵢ` (given by `dg`). -/
theorem exactWEV_isSome_exp (m : ℕ) (h : T.Tr m) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (dg : List (ℚ × ℚ × LC m))
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).natDegree ≤
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).natDegree)
    (htri : ∀ i < N, ∀ j < N, i < j →
      T.limE m h ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = 0)
    (hdiag : ∀ i < N, T.limE m h ((Mc.getD i []).getD i (MOr Fc ks (m + 1)).zero) =
      (T.MP m h).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg i))))
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h) c.2 ≠ 0) (E : GPoly (LC m))
    (hE : GPoly.toPoly (T.MP m h) E ≠ 0) :
    (exactWE Fc ks m (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) N Mc f E).isSome := by
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
    (T.expSysV_isSome m h N A0 q hh [G] 0 a rde dg hmon (fun a b ↦ (hAe a b).1)
      (fun a b ↦ T.limE m h ((Mc.getD (b : ℕ) []).getD (a : ℕ) (MOr Fc ks (m + 1)).zero))
      (fun a b ↦ (hAe a b).2)
      (fun a b hba ↦ htri b b.2 a a.2 hba) (fun a ↦ hdiag a a.2))
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


variable {m : ℕ}

/-- **The checks at `t = 0` pass** for a value `M₀` at `0` and a gauge `C` with the semantic
properties. -/
lemma zeroOKV_of (h0 : T.Tr m) (a : LC m) (N : ℕ) (q : GPoly (LC m))
    (A0 : Fin N → Fin N → GPoly (LC m)) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (M0 : Fin N → Fin N → T.F m)
    (hq0 : (GPoly.toPoly (T.MP m h0) q).coeff 0 ≠ 0)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).coeff 0 =
      (GPoly.toPoly (T.MP m h0) q).coeff 0 * M0 i j)
    (hC1 : ∀ i j : Fin N, ∑ k : Fin N, (T.MP m h0).sem (cget Fc ks m C (i : ℕ) (k : ℕ)) *
      (T.MP m h0).sem (cget Fc ks m Ci (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (hC2 : ∀ i j : Fin N, ∑ k : Fin N, (T.MP m h0).sem (cget Fc ks m Ci (i : ℕ) (k : ℕ)) *
      (T.MP m h0).sem (cget Fc ks m C (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (htri : ∀ i j : Fin N, j < i →
      ((Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)) * Matrix.of M0 *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j))) i j = 0)
    (hdiag : ∀ i : Fin N,
      ((Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)) * Matrix.of M0 *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j))) i i =
      (T.MP m h0).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg0 (i : ℕ)))))
    (hp : ∀ i : Fin N, (dgEAt Fc ks m dg0 (i : ℕ)).1.den ≠ 1 ∨ (dgEAt Fc ks m dg0 (i : ℕ)).1 ≤ 0) :
    zeroOKV Fc ks m a N q A0 C Ci dg0 = true := by
  classical
  have hm0 : ∀ i j, (T.MP m h0).sem (m0E Fc ks m N q A0 i j) = M0 i j := by
    intro i j
    rw [m0E, CField.sem_mul, CField.sem_inv, ← coeff_toPoly_sem, ← coeff_toPoly_sem, hA]
    field_simp
  have hg : ∀ i j, (T.MP m h0).sem (gaugeT Fc ks m N q A0 C Ci i j) =
      ((Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)) * Matrix.of M0 *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j))) i j := by
    intro i j
    rw [gaugeT, CField.sem_add, CField.sem_neg, T.sem_lsumC_finRange h0, T.sem_lsumC_finRange h0]
    simp only [T.sem_lsumC_finRange h0, CField.sem_mul, CField.sem_deriv, hm0, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.sum_comm]
  unfold zeroOKV cmatOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq]
  refine ⟨fun i j ↦ ⟨?_, ?_⟩, fun i j ↦ ⟨⟨fun hji ↦ ?_, fun hij ↦ ?_⟩, hp i⟩⟩
  · rw [(T.MP m h0).isZero_iff, CField.sem_add, CField.sem_neg, T.sem_lsumC_finRange h0]
    simp only [CField.sem_mul]
    rw [hC1 i j]
    split_ifs <;> simp [CField.sem_one, CField.sem_zero]
  · rw [(T.MP m h0).isZero_iff, CField.sem_add, CField.sem_neg, T.sem_lsumC_finRange h0]
    simp only [CField.sem_mul]
    rw [hC2 i j]
    split_ifs <;> simp [CField.sem_one, CField.sem_zero]
  · rw [(T.MP m h0).isZero_iff, hg]; exact htri i j hji
  · subst hij
    rw [(T.MP m h0).isZero_iff, CField.sem_add, CField.sem_neg, hg, hdiag, add_neg_cancel]

variable (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **`exactWRE` answers** for squarefree matrix denominators prime to `t`, a rational limit
`a′ Λ₀` at `t = 0` annihilated by `∏_{k<N₀} (X − k/N₀)`, an invertible constant `C`, and a
conjugated rescaled matrix with an upper triangular rational limit `a′ Λ∞` at infinity. -/
theorem exactWREV_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (ℚ × ℚ × LC m))
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ)
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
    (htri : ∀ i < N, ∀ j < N, i < j → Λ i j = 0)
    (hdiag : ∀ i < N, Λ i i = (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg i))))
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWREV Fc ks m a rde dg N Mc f r C Ci dg0).isSome := by
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
  set hh := lcmGL O (f.map Prod.snd) with hhh
  have hdens : ∀ d ∈ Mm.flatten.map Prod.snd, GPoly.toPoly P d ≠ 0 := by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1
  obtain ⟨hqm, hqd, hqs⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) hdens
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P (f.map Prod.snd) (by
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
      (f.map fun c ↦ cofC O hh c.2).all Prod.fst && isMonicC O q && isMonicC O hh) = true := by
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
  have hWE : (exactWE Fc ks m (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) N
      ((rescaleME Fc ks m (O.deriv a) N Mc r).map fun l ↦ l.map (redC Fc ks m))
      ((rescaleF Fc ks m N f r).map (redC Fc ks m)) E).isSome :=
    T.exactWEV_isSome_exp m h0 a rde hrde dg N hN _ _
      (fun i hi j hj ↦ ⟨(hlim' i hi j hj).1, (hlim' i hi j hj).2.1⟩)
      (fun i hi j hj hij ↦ by rw [(hlim' i hi j hj).2.2]; exact htri i hi j hj hij)
      (fun i hi ↦ by rw [(hlim' i hi i hi).2.2]; exact hdiag i hi)
      (by
        intro c hc
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
        exact T.redC_den_ne_zero m h1 _)
      E hE0
  unfold exactWREV
  simp only [hN, ↓reduceIte]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hq0c]
  rw [← hA0]
  simp only [hzc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hB]
  exact hWE


end MTower

end Curves.MT
