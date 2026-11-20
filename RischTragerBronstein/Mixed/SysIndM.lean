import RischTragerBronstein.Computable.SysIndC
import RischTragerBronstein.Mixed.SysRoot
import RischTragerBronstein.Mixed.MTBasics

/-!
# Coupled Risch systems over a tower: the bound on the indicial roots

`indBound` computes the coefficients of the indicial norm of `(q, dq, A₀)` over the code field of
level `m` and bounds its natural roots (`intRootBound`). By `indBound_spec`, every natural `e`
with `p ∣ det(A₀ − e dq I)` for an irreducible factor `p` of `q` satisfies `e ≤ B`.
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys

/-- **The bound on the natural indicial roots** (`none` if the interpolation check fails or the
norm vanishes identically). -/
def indBound (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m d n : ℕ) (q dq : GPoly (LC m))
    (A0 : Fin n → Fin n → GPoly (LC m)) : Option ℕ :=
  if vandCheck (d * n) then
    intRootBound Fc ks m (indCoeffsC (MO Fc ks m) (mcst Fc ks m) d n q dq A0)
  else none

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Every natural indicial root at a factor of `q` is bounded by `indBound`.** -/
theorem indBound_spec (m : ℕ) (h : T.Tr m) (d n : ℕ) (q dq : GPoly (LC m))
    (A0 : Fin n → Fin n → GPoly (LC m)) (hq : (GPoly.toPoly (T.MP m h) q).Monic)
    (hd : (GPoly.toPoly (T.MP m h) q).natDegree = d) (B : ℕ)
    (hB : indBound Fc ks m d n q dq A0 = some B) (e : ℕ) (p : (T.F m)[X]) (hp : Irreducible p)
    (hpq : p ∣ GPoly.toPoly (T.MP m h) q)
    (hdet : p ∣ (Matrix.of fun i j ↦ semMat (T.MP m h) A0 i j -
      if i = j then C (e : T.F m) * GPoly.toPoly (T.MP m h) dq else 0).det) :
    e ≤ B := by
  unfold indBound at hB
  split_ifs at hB with hv
  set cs := indCoeffsC (MO Fc ks m) (mcst Fc ks m) d n q dq A0 with hcs
  have hρ := indNorm'_eval_eq_zero _ _ hq _ _ p hp hpq hdet
  have hr := indCoeffsC_root (T.MP m h) (mcst Fc ks m) (T.sem_mcst m h) d q dq A0 hq hd hv _ hρ
  refine T.intRootBound_spec m h cs B hB e ?_
  rw [Tower.NestP.zipWith_sum_getD (fun (c : Cc) (v : LC m) ↦ algebraMap Cc (T.F m) c *
    (T.MP m h).sem v) 0 (MO Fc ks m).zero (fun _ ↦ by simp), ← hr]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Tower.NestP.NestTower.getD_range_map _ _ (Finset.mem_range.mp hj), T.algebraMap_ratCast]
  push_cast
  rfl

end MTower

end Curves.MT
