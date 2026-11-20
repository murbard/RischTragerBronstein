import RischTragerBronstein.Mixed.NKExactWREV

/-!
# The exact part in a basis `w = T θ` at an exponential level

`exactTEV … dg r C C⁻¹ dg0`: the exact test in the basis `w = T θ` (`exactTG`) with `exactWREV`
(shifts `r`, zero-place bound `N₀`, constant conjugation `C`) on the reduced matrix and
coordinates (non-constant curves over an exponential). Correct for every parameter (`exactTEV_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test in the basis `w = T θ` at an exponential level.** -/
def exactTEV (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) :
    Option Bool :=
  exactTG Fc ks m (fun N Mw fw ↦ exactWREV Fc ks m a rde dg N (Mw.map fun l ↦ l.map (redC Fc ks m))
    (fw.map (redC Fc ks m)) r C Ci dg0) P Tc Ti f

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable {m : ℕ} (h1 : T.Tr (m + 1))

lemma wexSpec_exactWREV (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (dg : List (ℚ × ℚ × LC m)) (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) :
    T.WexSpec m h1 (fun N Mw fw ↦ exactWREV Fc ks m a rde dg N (Mw.map fun l ↦ l.map (redC Fc ks m))
      (fw.map (redC Fc ks m)) r C Ci dg0) := by
  intro N Mc f θw hw hind res hres
  have hw' : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (((Mc.map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) * θw j := by
    intro i hi
    rw [hw i hi]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have := T.exactWREV_correct h1 hm hk htr rde hrde dg hom N _ _ r C Ci dg0 θw hw' hind res hres
  rw [this]
  simp only [T.sem_getD_map_redC m h1 htr]

/-- **Correctness of `exactTEV`**: for any `T`, `T⁻¹` (checked), shifts `r`, `N₀` and `C`, `C⁻¹`
(checked), an answer decides the existence of an antiderivative in `Fₘ₊₁(θ)`. -/
theorem exactTEV_correct (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (dg : List (ℚ × ℚ × LC m)) (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTEV Fc ks m a rde dg r C Ci dg0 P Tc Ti f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j :=
  T.exactTG_correct m h1 _ (T.wexSpec_exactWREV h1 hm hk htr rde hrde hom dg r C Ci dg0) P f θ hP hind
    Tc Ti res hres

end MTower

end Curves.MT
