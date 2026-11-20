import RischTragerBronstein.Mixed.SysRoot2
import RischTragerBronstein.Mixed.SysIndM
import RischTragerBronstein.Computable.VandTrue
import RischTragerBronstein.Computable.SysNormNZ

/-!
# A complete bound on the indicial roots

`indBound2`: as `indBound`, with the complete root bound `intRootBound2`. Its answers bound every
natural indicial root (`indBound2_spec`), and **it always answers** when no irreducible factor of
the monic `q` divides `dq` (`indBound2_isSome`): the interpolation check holds
(`vandCheck_true`), the indicial norm is not identically zero (`indNorm'_ne_zero`), so one of its
coefficients — the semantics of the interpolated codes (`sem_indCoeffsC`) — is non-zero, and
`intRootBound2` answers (`intRootBound2_isSome`).
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys

/-- **The bound on the natural indicial roots** (complete version). -/
def indBound2 (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m d n : ℕ) (q dq : GPoly (LC m))
    (A0 : Fin n → Fin n → GPoly (LC m)) : Option ℕ :=
  if vandCheck (d * n) then
    intRootBound2 Fc ks m (indCoeffsC (MO Fc ks m) (mcst Fc ks m) d n q dq A0)
  else none

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Every natural indicial root at a factor of `q` is bounded by `indBound2`.** -/
theorem indBound2_spec (m : ℕ) (h : T.Tr m) (d n : ℕ) (q dq : GPoly (LC m))
    (A0 : Fin n → Fin n → GPoly (LC m)) (hq : (GPoly.toPoly (T.MP m h) q).Monic)
    (hd : (GPoly.toPoly (T.MP m h) q).natDegree = d) (B : ℕ)
    (hB : indBound2 Fc ks m d n q dq A0 = some B) (e : ℕ) (p : (T.F m)[X]) (hp : Irreducible p)
    (hpq : p ∣ GPoly.toPoly (T.MP m h) q)
    (hdet : p ∣ (Matrix.of fun i j ↦ semMat (T.MP m h) A0 i j -
      if i = j then C (e : T.F m) * GPoly.toPoly (T.MP m h) dq else 0).det) :
    e ≤ B := by
  unfold indBound2 at hB
  split_ifs at hB with hv
  set cs := indCoeffsC (MO Fc ks m) (mcst Fc ks m) d n q dq A0 with hcs
  have hρ := indNorm'_eval_eq_zero _ _ hq _ _ p hp hpq hdet
  have hr := indCoeffsC_root (T.MP m h) (mcst Fc ks m) (T.sem_mcst m h) d q dq A0 hq hd hv _ hρ
  refine T.intRootBound2_spec m h cs B hB e ?_
  rw [Tower.NestP.zipWith_sum_getD (fun (c : Cc) (v : LC m) ↦ algebraMap Cc (T.F m) c *
    (T.MP m h).sem v) 0 (MO Fc ks m).zero (fun _ ↦ by simp), ← hr]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Tower.NestP.NestTower.getD_range_map _ _ (Finset.mem_range.mp hj), T.algebraMap_ratCast]
  push_cast
  rfl

/-- **`indBound2` answers** when no irreducible factor of the monic `q` divides `dq`. -/
theorem indBound2_isSome (m : ℕ) (h : T.Tr m) (d n : ℕ) (q dq : GPoly (LC m))
    (A0 : Fin n → Fin n → GPoly (LC m)) (hq : (GPoly.toPoly (T.MP m h) q).Monic)
    (hd : (GPoly.toPoly (T.MP m h) q).natDegree = d)
    (hpd : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m h) q →
      ¬ p ∣ GPoly.toPoly (T.MP m h) dq) :
    (indBound2 Fc ks m d n q dq A0).isSome := by
  unfold indBound2
  rw [if_pos (vandCheck_true _)]
  have hne := indNorm'_ne_zero (GPoly.toPoly (T.MP m h) q) (GPoly.toPoly (T.MP m h) dq) hq
    (semMat (T.MP m h) A0) hpd
  obtain ⟨j, hj⟩ : ∃ j, (indNorm' (GPoly.toPoly (T.MP m h) q) (GPoly.toPoly (T.MP m h) dq)
      (semMat (T.MP m h) A0)).coeff j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (Polynomial.ext fun j ↦ by rw [hc j, coeff_zero])
  have hdeg := natDegree_indNorm' (GPoly.toPoly (T.MP m h) q) (GPoly.toPoly (T.MP m h) dq)
    (semMat (T.MP m h) A0)
  rw [hd] at hdeg
  have hjle : j ≤ d * n := by
    by_contra hlt
    exact hj (coeff_eq_zero_of_natDegree_lt (by omega))
  have hsem := sem_indCoeffsC (T.MP m h) (mcst Fc ks m) (T.sem_mcst m h) d q dq A0 hq hd
    (vandCheck_true _) j
  refine T.intRootBound2_isSome m h _ j (by rw [length_indCoeffsC]; omega) ?_
  rw [hsem]; exact hj

end MTower

end Curves.MT
