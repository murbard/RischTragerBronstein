import RischTragerBronstein.Mixed.NKExactWRE

/-!
# The exact part in a basis `w = T θ` at an exponential level

`exactTRE … r N₀ C C⁻¹`: the exact test in the basis `w = T θ` (`exactTG`) with `exactWRE`
(shifts `r`, zero-place bound `N₀`, constant conjugation `C`) on the reduced matrix and
coordinates. Correct for every `T`, `T⁻¹`, `r`, `N₀`, `C`, `C⁻¹` (`exactTRE_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test in the basis `w = T θ` at an exponential level.** -/
def exactTRE (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (r : ℕ → ℤ)
    (N0 : ℕ) (C Ci : List (List ℚ)) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) : Option Bool :=
  exactTG Fc ks m (fun N Mw fw ↦ exactWRE Fc ks m a rdeD N (Mw.map fun l ↦ l.map (redC Fc ks m))
    (fw.map (redC Fc ks m)) r N0 C Ci) P Tc Ti f

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable {m : ℕ} (h1 : T.Tr (m + 1))

lemma wexSpec_exactWRE (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
      ((T.MP m h1.of_succ).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) :
    T.WexSpec m h1 (fun N Mw fw ↦ exactWRE Fc ks m a rdeD N (Mw.map fun l ↦ l.map (redC Fc ks m))
      (fw.map (redC Fc ks m)) r N0 C Ci) := by
  intro N Mc f θw hw hind res hres
  have hw' : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (((Mc.map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) * θw j := by
    intro i hi
    rw [hw i hi]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have := T.exactWRE_correct h1 hm hk htr rdeD hrdeD hom N _ _ r N0 C Ci θw hw' hind res hres
  rw [this]
  simp only [T.sem_getD_map_redC m h1 htr]

/-- **Correctness of `exactTRE`**: for any `T`, `T⁻¹` (checked), shifts `r`, `N₀` and `C`, `C⁻¹`
(checked), an answer decides the existence of an antiderivative in `Fₘ₊₁(θ)`. -/
theorem exactTRE_correct (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
      ((T.MP m h1.of_succ).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTRE Fc ks m a rdeD r N0 C Ci P Tc Ti f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j :=
  T.exactTG_correct m h1 _ (T.wexSpec_exactWRE h1 hm hk htr rdeD hrdeD hom r N0 C Ci) P f θ hP hind
    Tc Ti res hres

end MTower

end Curves.MT
