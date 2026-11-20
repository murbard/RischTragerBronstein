import RischTragerBronstein.Mixed.NKExactWE
import RischTragerBronstein.Mixed.SysExpB

/-!
# The exact-part test with a known denominator at an exponential level

`expSpecB`: `expSysB … 0` meets the solver specification with known denominators;
`exactWE_isSome_exp`: `exactWE` with this solver answers when the matrix entries are bounded at
infinity with a rational upper triangular limit `a′ Λ` (any non-zero denominators, `a′ ≠ 0`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- A successful `expSysB` has monic `q`, `h`. -/
lemma expSysB_monic {m : ℕ} {a : LC m} {rdeD : LC m → List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {B : ℕ} {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : expSysB Fc ks m a rdeD n A0 q hq G0 B = some r) :
    isMonicC (MO Fc ks m) q = true ∧ isMonicC (MO Fc ks m) hq = true := by
  unfold expSysB at hres
  simp only at hres
  split_ifs at hres with hmon
  have : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) = true := by
    revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) <;> simp
  exact Bool.and_eq_true_iff.mp this

/-- A successful `expSysB` returns the `W`-system denominator. -/
lemma expSysB_den {m : ℕ} {a : LC m} {rdeD : LC m → List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {B : ℕ} {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : expSysB Fc ks m a rdeD n A0 q hq G0 B = some r) :
    r.1 = (wSysE Fc ks m ((MO Fc ks m).deriv a) n A0 q hq G0 B).Den := by
  unfold expSysB at hres
  simp only at hres
  split_ifs at hres
  rw [← Option.some.inj hres]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable {m : ℕ} in
/-- `expSysB … 0` meets the solver specification with known denominators. -/
theorem expSpecB (hm : m < T.n) (h0 : T.Tr m) {a : LC m} (hk : ks m = .exp a)
    (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h0).sem ((MO Fc ks m).deriv a) * z ≠ 0) :
    T.SolverSpecB m h0 0 ((T.MP m h0).sem ((MO Fc ks m).deriv a))
      (fun n A0 q hh G0 ↦ expSysB Fc ks m a rdeD n A0 q hh G0 0) where
  hD := T.phi_DzL_exp m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦
    T.expSysB_sound m h0 n A0 q hh G0 0 a rdeD Den out hres
  den := fun n A0 q hh G0 r hres ↦ by
    have hB := expSysB_den hres
    have hmo := expSysB_monic hres
    have hq := (isMonicC_spec (T.MP m h0) q hmo.1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh hmo.2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [hB, T.wSysE_Den m h0 ((MO Fc ks m).deriv a) n A0 q hh G0 0]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol hdvd ↦
    T.expSysB_complete m h0 n A0 q hh G0 0 a rdeD hrdeD hom Den out hres c hc Z d hd hsol
      (fun i ↦ by rw [pow_zero, mul_one]; exact hdvd i)

/-- **`exactWE` answers** with the solver `expSysB … 0` at an exponential level when the matrix
is bounded at infinity with a rational upper triangular limit `a′ Λ`. -/
theorem exactWE_isSome_exp (m : ℕ) (h : T.Tr m) (a : LC m)
    (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hb0 : (T.MP m h).sem ((MO Fc ks m).deriv a) ≠ 0)
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).natDegree ≤
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).natDegree)
    (lam : ℕ → ℕ → ℚ)
    (hlam : ∀ i < N, ∀ j < N,
      (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).coeff
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).natDegree =
      (T.MP m h).sem ((MO Fc ks m).deriv a) * (lam j i : T.F m) *
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).leadingCoeff)
    (htri : ∀ i < N, ∀ j < N, j < i → lam i j = 0)
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h) c.2 ≠ 0) (E : GPoly (LC m))
    (hE : GPoly.toPoly (T.MP m h) E ≠ 0) :
    (exactWE Fc ks m (fun n A0 q hh G0 ↦ expSysB Fc ks m a rdeD n A0 q hh G0 0) N Mc f E).isSome := by
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
  have hentry : ∀ (i j : Fin N), ∃ c ∈ Mm.flatten, (Mm.getD i []).getD j O1.zero = c ∧
      c = (Mc.getD i []).getD j O1.zero := by
    intro i j
    refine ⟨_, ?_, rfl, ?_⟩
    · rw [hMm, NestTower.getD_range_map _ _ i.2, NestTower.getD_range_map _ _ j.2]
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩,
        List.mem_map.mpr ⟨j, List.mem_range.mpr j.2, rfl⟩⟩
    · rw [hMm, NestTower.getD_range_map _ _ i.2, NestTower.getD_range_map _ _ j.2]
  have hA : ∀ i j, (GPoly.toPoly P (A0 i j)).natDegree ≤ (GPoly.toPoly P q).natDegree ∧
      (GPoly.toPoly P (A0 i j)).coeff (GPoly.toPoly P q).natDegree =
        (T.MP m h).sem ((MO Fc ks m).deriv a) * (lam i j : T.F m) := by
    intro j i
    obtain ⟨c, hcm, hc, hcMc⟩ := hentry i j
    obtain ⟨h0, hdeg⟩ := hent' c hcm
    have hqc := cofC_snd P q c.2 h0 (hqd _ (List.mem_map_of_mem hcm))
    have hcof0 : GPoly.toPoly P (cofC O q c.2).2 ≠ 0 := fun hz ↦
      hqm.ne_zero (by rw [hqc, hz, zero_mul])
    have hqdeg : (GPoly.toPoly P q).natDegree =
        (GPoly.toPoly P c.2).natDegree + (GPoly.toPoly P (cofC O q c.2).2).natDegree := by
      rw [hqc, natDegree_mul hcof0 h0, add_comm]
    have hlc : (GPoly.toPoly P c.2).leadingCoeff * (GPoly.toPoly P (cofC O q c.2).2).leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, mul_comm, ← hqc]; exact hqm.leadingCoeff
    show (GPoly.toPoly P (GPoly.mul O ((Mm.getD i []).getD j O1.zero).1
      (cofC O q ((Mm.getD i []).getD j O1.zero).2).2)).natDegree ≤ _ ∧
      (GPoly.toPoly P (GPoly.mul O ((Mm.getD i []).getD j O1.zero).1
      (cofC O q ((Mm.getD i []).getD j O1.zero).2).2)).coeff _ = _
    rw [hc, GPoly.toPoly_mul, hqdeg]
    refine ⟨natDegree_mul_le.trans (by omega), ?_⟩
    rw [coeff_mul_of_natDegree_le' hdeg le_rfl]
    have hl := hlam i i.2 j j.2
    rw [← hcMc] at hl
    rw [hl, ← leadingCoeff, mul_assoc, hlc, mul_one]
  have hmon : (isMonicC O q && isMonicC O hh) = true := by
    rw [isMonicC_of_monic P q hqm, isMonicC_of_monic P hh hhm]; rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (T.expSysB_isSome m h N A0 q hh [G] 0 a rdeD hmon (fun i j ↦ (hA i j).1)
      (fun i j ↦ lam i j) (fun i j ↦ (hA i j).2) (fun i j hji ↦ htri i i.2 j j.2 hji) hb0)
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

end MTower

end Curves.MT
