import RischTragerBronstein.Mixed.LcmGL
import RischTragerBronstein.Mixed.NKExactW
import RischTragerBronstein.Mixed.SysPrimSome

/-!
# The exact-part test in a basis always answers in its regime

**`exactW_isSome`**: over a certified primitive level `m` (`t′ = η`, `η` not a derivative), the
exact-part test `exactW` with the solver `primSysC` answers whenever the derivation matrix of the
basis has entries vanishing at infinity (`deg num < deg den`) with squarefree denominators and the
integrand coordinates have non-zero denominators:

* the common denominators `q`, `h` are monic lcms, the `cofC` checks pass (`lcmGL_spec`,
  `cofC_fst`);
* `q` is squarefree and the cleared matrix `A₀ = num · (q / den)` has `deg A₀ < deg q`
  (`cofC_snd`);
* `primSysC` answers (`primSysC_isSome_sq`).

With `exactW_correct` the test is then a decision procedure for the exact part in such a basis.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`exactW` answers** with the solver `primSysC` for a basis whose derivation matrix vanishes at
infinity and has squarefree denominators. -/
theorem exactW_isSome (m : ℕ) (h : T.Tr m) (η : LC m) (hm : m < T.n)
    (htr : Transcendental (T.F m) (T.ts m)) (hk : ks m = .prim η)
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim)
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h).sem η)
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      Squarefree (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2) ∧
      (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).degree <
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).degree)
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h) c.2 ≠ 0) :
    (exactW Fc ks m (fun n A0 q hh G0 ↦ primSysC Fc ks m η lim n A0 q hh G0) N Mc f).isSome := by
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
  have hent' : ∀ c ∈ Mm.flatten, GPoly.toPoly P c.2 ≠ 0 ∧ Squarefree (GPoly.toPoly P c.2) ∧
      (GPoly.toPoly P c.1).degree < (GPoly.toPoly P c.2).degree := by
    intro c hc
    obtain ⟨i, hi, j, hj, rfl⟩ := hmem c hc
    exact hent i hi j hj
  set q := lcmGL O (Mm.flatten.map Prod.snd) with hq
  set hh := lcmGL O (f.map Prod.snd) with hhh
  obtain ⟨hqm, hqd, hqs⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1)
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P (f.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      (f.map fun c ↦ cofC O hh c.2).all Prod.fst) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_map_of_mem hc))
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  set G : Fin N → GPoly (LC m) := fun j ↦
    GPoly.mul O (f.getD j O1.zero).1 (cofC O hh (f.getD j O1.zero).2).2 with hG
  have hA : ∀ i j, (GPoly.toPoly P (A0 i j)).degree < (GPoly.toPoly P q).degree := by
    intro j i
    set c := (Mm.getD i []).getD j O1.zero with hc
    have hcm : c ∈ Mm.flatten := by
      rw [hc, hMm, NestTower.getD_range_map _ _ i.2, NestTower.getD_range_map _ _ j.2]
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩,
        List.mem_map.mpr ⟨j, List.mem_range.mpr j.2, rfl⟩⟩
    obtain ⟨h0, -, hdeg⟩ := hent' c hcm
    have hqc := cofC_snd P q c.2 h0 (hqd _ (List.mem_map_of_mem hcm))
    have hcof0 : GPoly.toPoly P (cofC O q c.2).2 ≠ 0 := fun hz ↦
      hqm.ne_zero (by rw [hqc, hz, zero_mul])
    show (GPoly.toPoly P (GPoly.mul O c.1 (cofC O q c.2).2)).degree < _
    rw [GPoly.toPoly_mul, hqc, degree_mul, degree_mul, add_comm]
    exact WithBot.add_lt_add_left (by rw [Ne, degree_eq_bot]; exact hcof0) hdeg
  have hmon : (isMonicC O q && isMonicC O hh) = true := by
    rw [isMonicC_of_monic P q hqm, isMonicC_of_monic P hh hhm]; rfl
  have hsq : Squarefree (GPoly.toPoly P q) := hqs (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).2.1)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (T.primSysC_isSome_sq m h η hm htr hk lim hlim N A0 q hh [G] hmon hA hsq hη)
  unfold exactW
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
