import RischTragerBronstein.Mixed.NKExactTR
import RischTragerBronstein.Mixed.NKExactWRV

/-!
# The exact part in the basis `w = T θ` with a triangular limit matrix

`exactTV … rde dg r`: as `exactTR`, with the solver `primSysV` (a limit matrix at infinity that is
upper triangular with diagonal `fCode dgᵢ`, checked), the case of non-constant curves. Correct for
any `T`, `T⁻¹` and shifts (`exactTV_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test in the basis `w = T θ` rescaled by `t^{−r}`, triangular limit.** -/
def exactTV (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) :
    Option Bool :=
  exactTG Fc ks m (fun N Mw fw ↦ exactWRV Fc ks m η rde dg N (Mw.map fun l ↦ l.map (redC Fc ks m))
    (fw.map (redC Fc ks m)) r) P Tc Ti f

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) {m : ℕ} (h1 : T.Tr (m + 1))

/-- `exactWRV` on reduced codes meets the specification of an exact test in a basis. -/
lemma wexSpec_exactWRV (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (r : ℕ → ℤ) :
    T.WexSpec m h1 (fun N Mw fw ↦ exactWRV Fc ks m η rde dg N (Mw.map fun l ↦ l.map (redC Fc ks m))
      (fw.map (redC Fc ks m)) r) := by
  intro N Mc f θw hw hind res hres
  have hw' : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (((Mc.map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) * θw j := by
    intro i hi
    rw [hw i hi]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have := T.exactWRV_correct m h1 hm hk htr rde hrde dg N _ _ r θw hw' hind res hres
  rw [this]
  simp only [T.sem_getD_map_redC m h1 htr]

/-- **Correctness of `exactTV`**: for any `T`, `T⁻¹` (checked), shifts `r` and diagonal
representations `dg`, an answer decides the existence of an antiderivative in `Fₘ₊₁(θ)`. -/
theorem exactTV_correct (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTV Fc ks m η rde dg r P Tc Ti f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j :=
  T.exactTG_correct m h1 _ (T.wexSpec_exactWRV h1 hm hk htr rde hrde dg r) P f θ hP hind Tc Ti res
    hres

end MTower

end Curves.MT
