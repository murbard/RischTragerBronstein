import RischTragerBronstein.Mixed.KXAllLevels

/-!
# Checking the input conditions of cubic completeness

`kxInputCheck` checks the degree, residue classes, and well-formed codes required by the
cubic completeness theorem. Squarefreeness and the tower certificate are checked separately
by the expression parser. A passing check does not assert elementary integrability.
-/

open Polynomial

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (c0 : CPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The executable well-formedness check at each level. -/
def kxWFb : (m : ℕ) → LC m → Bool
  | 0 => codeOKb
  | m + 1 => fun q ↦ !GPoly.isZero (MO [c0, [1]] ks m) q.2

theorem kxWFb_spec (m : ℕ) (q : LC m) :
    kxWFb c0 ks m q = true ↔ kxWF c0 ks m q := by
  cases m <;> simp only [kxWFb, kxWF, WFm, Bool.not_eq_true']

variable [Fact (Irreducible (toPoly (fKc [c0, [1]])))]

/-- The additional input checks for eventual completeness of the cubic solver. -/
def kxInputCheck (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) : Bool :=
  decide (degG (MO [c0, [1]] ks m) A = 3) && decide (cs.length ≠ 0) &&
    kxOK [c0, [1]] ks m A B kt l cs &&
    decide (kxConst [c0, [1]] ks m g A B kt l cs = true →
      kxRepOK [c0, [1]] ks m g A B kt l cs = true) &&
    A.all (kxWFb c0 ks m) && B.all (kxWFb c0 ks m) &&
    cs.all (kxWFb c0 ks m) && kxWFb c0 ks m g

/-- The check is exactly the additional hypotheses of `kxDecideNC_decides`. -/
theorem kxInputCheck_spec (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) :
    kxInputCheck c0 ks m g A B kt l cs = true ↔
      degG (MO [c0, [1]] ks m) A = 3 ∧ cs.length ≠ 0 ∧
      kxOK [c0, [1]] ks m A B kt l cs = true ∧
      (kxConst [c0, [1]] ks m g A B kt l cs = true →
        kxRepOK [c0, [1]] ks m g A B kt l cs = true) ∧
      (∀ a ∈ A, kxWF c0 ks m a) ∧ (∀ b ∈ B, kxWF c0 ks m b) ∧
      (∀ c ∈ cs, kxWF c0 ks m c) ∧ kxWF c0 ks m g := by
  simp only [kxInputCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    kxWFb_spec, and_assoc]

end Curves.MT
