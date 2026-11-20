import RischTragerBronstein.Mixed.MTChain
import RischTragerBronstein.Mixed.LTElem
import RischTragerBronstein.Mixed.ExpCurveMain

/-!
# Mixed towers over a curve: elementary integration, the algorithm

`elM Fc ks lv m q N` decides whether the level-`m` code `q` has an elementary integral:

* level `0`: the total decision on the curve (`decideTotal`, search bound `N`);
* a logarithmic level `m + 1` (`tₘ′ = η`): Hermite reduction in `t`, the residue test, the chain of
  limited integration problems at level `m` (`mchain`), and the constant term `a₀ − η Q₁`
  decided at level `m`;
* an exponential level `m + 1` (`tₘ = exp a`): the powers of `t` split off the denominator,
  Hermite reduction, the residue test, the Risch equations `y′ + (j − k) a′ y = Λⱼ` (`j ≠ k`) at
  level `m` (`prdeC`), and the constant term `Λₖ` decided at level `m`.

This file: the algorithm and the Risch-equation check `rdeOKM_iff`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The Risch equation `y′ + h′ y = f` at level `m` has a solution (non-zero parameter). -/
def rdeOKM (m : ℕ) (h f : LC m) : Bool :=
  (prdeC Fc ks lv m ⟨h, []⟩ [f]).any fun r ↦ decide (r.1.getD 0 0 ≠ 0)

/-- **Elementary integration in mixed towers over a curve**, with search bound `N`. -/
def elM : (m : ℕ) → LC m → ℕ → Option Bool
  | 0, q, N => decideTotal Fc ((codeW (cvNorm Fc q)).map trim) (codeQ (cvNorm Fc q)) N
  | m + 1, q, N =>
    let O := MO Fc ks m
    let q' : GFrac (LC m) := q
    if GPoly.isZero O q'.2 then some true
    else match ks m with
    | .prim η =>
      let w := wKC O (.prim η)
      let h := GPoly.hermite O w q'.1 q'.2
      let qr := GPoly.divMod O h.b h.s
      if !(GPoly.residueCheck O w qr.2 h.s) then some false
      else match mchain Fc ks lv m η qr.1 qr.1.length O.zero with
        | none => some false
        | some Q1 => elM m (mconst Fc ks m η qr.1 Q1) N
    | .exp a =>
      let w := wKC O (.exp a)
      let sp := GPoly.expSplit O q'.1 q'.2
      let k := sp.2.2.1
      let h := GPoly.hermite O w sp.1 sp.2.2.2
      let qr := GPoly.divMod O h.b h.s
      let Λ := GPoly.add O (GPoly.mul O qr.1 (GPoly.monomial O k O.one)) sp.2.1
      if !(GPoly.residueCheck O w qr.2 h.s) then some false
      else if !((List.range (Λ.length + k + 1)).all fun j ↦
          decide (j = k) || rdeOKM Fc ks lv m (O.mul (mcst Fc ks m ((j : ℚ) - k)) a)
            (Λ.getD j O.zero)) then some false
      else elM m (Λ.getD k O.zero) N

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The Risch-equation check**, given the specification of `prdeC m`. -/
theorem rdeOKM_iff (m : ℕ) (h : T.Tr m)
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
        (prdeC Fc ks lv m fr))
    (hc f : LC m) :
    (∃ y : T.F m, y′ + ((T.MP m h).sem hc)′ * y = (T.MP m h).sem f) ↔
      rdeOKM Fc ks lv m hc f = true := by
  classical
  set M := T.MP m h
  have hs : RdeSpecK (algebraMap Cc (T.F m)) M (M.sem hc)′ (prdeC Fc ks lv m ⟨hc, []⟩) := by
    have := hrde ⟨hc, []⟩ (fun cw hcw ↦ by simp at hcw)
    rwa [sem_fCode, logSumV, List.map_nil, List.sum_nil, add_zero] at this
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨β, hβ, -⟩ := hs.complete [f] [1] (fun i hi ↦ by
      rcases i with _ | i
      · simp at hi
      · rfl) y (by
        rw [hy, sC]
        simp)
    have h1 := hβ 0
    rw [List.getD_cons_zero] at h1
    unfold rdeOKM
    rw [List.any_eq_true]
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      have : ((prdeC Fc ks lv m ⟨hc, []⟩ [f]).getD k ([], (MO Fc ks m).zero)).1.getD 0 0 = 0 := by
        have hmem : (prdeC Fc ks lv m ⟨hc, []⟩ [f]).getD k ([], (MO Fc ks m).zero) ∈
            prdeC Fc ks lv m ⟨hc, []⟩ [f] := by
          rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
        simpa using hall _ hmem
      rw [this, map_zero, mul_zero]] at h1
    exact one_ne_zero h1
  · intro hok
    unfold rdeOKM at hok
    obtain ⟨r, hr, hr0⟩ := List.any_eq_true.mp hok
    simp only [decide_eq_true_eq] at hr0
    have hsd := hs.sound [f] r hr
    rw [sQ] at hsd
    simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one,
      Finset.sum_singleton, List.getD_cons_zero] at hsd
    have hq : ((r.1.getD 0 0 : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hr0
    refine ⟨M.sem r.2 / ((r.1.getD 0 0 : ℚ) : T.F m), ?_⟩
    rw [Derivation.leibniz_div, T.deriv_ratCast]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp
    linear_combination hsd

end MTower

end Curves.MT
