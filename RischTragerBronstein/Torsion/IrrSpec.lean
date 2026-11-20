import RischTragerBronstein.Torsion.Eisenstein
import RischTragerBronstein.Torsion.ZpLift
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Irreducibility by specialization

`irreducible_ratFunc_of_map`: a monic `F ∈ k[x][Y]` whose image under some ring homomorphism
`k[x] → K` (e.g. `x ↦ a`) is irreducible is irreducible over `k(x)`. With a specialization
modulo `p` without roots (degree `≤ 3`), this certifies irreducibility over `𝔽_p(x)`, over
`ℚ_p(x)` (the fibre over `ℤ_p` is irreducible, Gauss) and over any field mapping to `ℚ_p`.
-/

open Polynomial

namespace Curves

section Spec

/-- **Irreducibility over `k(x)` from an irreducible image.** -/
theorem irreducible_ratFunc_of_map {k K : Type*} [Field k] [CommRing K] [IsDomain K]
    (F : k[X][X]) (hF : F.Monic) (θ : k[X] →+* K) (h : Irreducible (F.map θ)) :
    Irreducible (F.map (algebraMap k[X] (RatFunc k))) :=
  (hF.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := RatFunc k)).mp
    (Polynomial.Monic.irreducible_of_irreducible_map θ F hF h)

/-- A polynomial of degree `1, 2, 3` without roots is irreducible. -/
lemma irreducible_of_no_roots {K : Type*} [Field K] (f : K[X]) (h1 : 1 ≤ f.natDegree)
    (h3 : f.natDegree ≤ 3) (h : ∀ y, f.eval y ≠ 0) : Irreducible f :=
  irreducible_of_degree_le_three_of_not_isRoot (Finset.mem_Icc.mpr ⟨h1, h3⟩) fun y hy ↦ h y hy

end Spec

section SmallFactor

open CPoly

variable {K : Type*} [Field K] [DecidableEq K]

/-- All lists of length `d` over `els`. -/
def tuplesL (els : List K) : ℕ → List (List K)
  | 0 => [[]]
  | d + 1 => (tuplesL els d).flatMap fun l ↦ els.map (· :: l)

lemma mem_tuplesL (els : List K) (hels : ∀ x, x ∈ els) :
    ∀ (d : ℕ) (l : List K), l.length = d → l ∈ tuplesL els d
  | 0, l, h => by rw [List.length_eq_zero_iff.mp h]; simp [tuplesL]
  | d + 1, [], h => by simp at h
  | d + 1, a :: l, h => by
    rw [tuplesL, List.mem_flatMap]
    exact ⟨l, mem_tuplesL els hels d l (by simpa using h), List.mem_map.mpr ⟨a, hels a, rfl⟩⟩

/-- **No monic factor of degree `1, …, n/2`** (the monic polynomials enumerated over `els`). -/
def noSmallFactor (els : List K) (f : CPoly K) (n : ℕ) : Bool :=
  (List.range (n / 2)).all fun d ↦ (tuplesL els (d + 1)).all fun l ↦
    !isZero (divMod f (l ++ [1])).2

lemma toPoly_monic_list (g : K[X]) (hg : g.Monic) :
    toPoly ((List.range g.natDegree).map g.coeff ++ [1]) = g := by
  ext i
  rw [coeff_toPoly]
  rcases lt_trichotomy i g.natDegree with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map, List.getElem_range]
  · rw [List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range, Nat.sub_self,
      List.getD_cons_zero, hg.coeff_natDegree]
  · rw [List.getD_eq_default _ _ (by simp; omega), coeff_eq_zero_of_natDegree_lt hi]

/-- **Irreducibility from the absence of small monic factors.** -/
theorem irreducible_of_noSmallFactor (els : List K) (hels : ∀ x, x ∈ els) (f : CPoly K) (n : ℕ)
    (hm : (toPoly f).Monic) (hn : (toPoly f).natDegree = n) (h1 : 1 ≤ n)
    (h : noSmallFactor els f n = true) : Irreducible (toPoly f) := by
  have hne1 : toPoly f ≠ 1 := fun he ↦ by rw [he, natDegree_one] at hn; omega
  rw [hm.irreducible_iff_lt_natDegree_lt hne1]
  intro q hq hdeg hdvd
  rw [Finset.mem_Ioc, hn] at hdeg
  simp only [noSmallFactor, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    Bool.eq_false_iff] at h
  set l := (List.range (q.natDegree - 1 + 1)).map q.coeff with hl
  have hq' : q.natDegree - 1 + 1 = q.natDegree := by omega
  have hmem : (List.range q.natDegree).map q.coeff ∈ tuplesL els (q.natDegree - 1 + 1) :=
    mem_tuplesL els hels _ _ (by simp [hq'])
  have h0 := h (q.natDegree - 1) (by omega) _ hmem
  apply h0
  have ht := toPoly_monic_list q hq
  rw [isZero_iff]
  exact divMod_exact f _ (by rw [ht]; exact hq.ne_zero) (by rw [ht]; exact hdvd)

end SmallFactor

end Curves
