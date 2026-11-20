import RischTragerBronstein.Torsion.AutoLog
import RischTragerBronstein.Torsion.NullTest

/-!
# Completeness of the kernel search

`testKernel` looks for a relation among the columns of the principality test with `nullBasis`.
If it finds none, the null space of `kerCols` is empty (`nullBasis_of_testKernel`), so the test
fails over every extension of the coefficient field (`not_princTest_of_nullN`) and the failed-test
certificate `nonPrincOK` passes (`nonPrincOK_of_testKernel`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section TK

variable {F : Type*} [Field F] [DecidableEq F]

/-- `testKernel` fails exactly when the null basis of the test columns is empty. -/
lemma nullBasis_of_testKernel {n : ℕ} {δL : List ℕ} {Bc : List (BPoly F)} {Dc : CPoly F}
    {Pc : PlaceCert F} {M m : ℕ} (h : testKernel n δL Bc Dc Pc M m = none) :
    nullBasis (kerCols n M δL Bc Dc Pc.αs (Pc.fcerts n) (Pc.bL n m) Pc.fib.length) = [] := by
  unfold testKernel at h
  simpa [kernelL, kerCols] using h

/-- **The failed-test certificate always passes when the kernel search fails** (given the side
conditions). -/
lemma nonPrincOK_of_testKernel {n : ℕ} {δL : List ℕ} {Bc : List (BPoly F)} {Dc : CPoly F}
    {Pc : PlaceCert F} {M m : ℕ} (h : testKernel n δL Bc Dc Pc M m = none)
    (hside : testSideN n Dc Pc.αs (Pc.fcerts n) (Pc.bL n m) = true) (P : ℕ) (Lm : List (List F)) :
    nonPrincOK n M P δL Bc Dc Pc.αs (Pc.fcerts n) (Pc.bL n m) Lm = true := by
  have h1 := nullBasis_of_testKernel h
  have hl : Pc.αs.length = Pc.fib.length := by simp [PlaceCert.αs]
  simp only [nonPrincOK, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff]
  exact Or.inr ⟨hside, by rw [hl]; exact h1⟩

end TK

end Curves
