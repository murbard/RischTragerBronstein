import RischTragerBronstein.Mixed.KPLiouville

/-!
# Kummer radicals over a logarithmic level: the decision

Let `T` be a certified mixed tower over a curve, of height `m + 1`, whose top level
`t = tₘ` is logarithmic (`t′ = η`), realized in `E`, and `θ ∈ E` with `θⁿ = a(t)`, where
`a ∈ Fₘ[t]` is squarefree of degree prime to `n`, `E = F_{m+1}(θ)`. For `0 < j < n` and
`B ∈ Fₘ[t]`:

**`kp_decides`**: `B(t) θʲ` has an elementary integral over `E` iff the Risch equation
`y′ + (j/n)(a′/a) y = B` has a solution in `F_{m+1}` — decided by the parametric solver
(`rdeOKFr`, with the logarithmic potential `(j/n, a)`).

`⇐`: `(y θʲ)′ = B θʲ`. `⇒`: a Liouville form lives in the elementary extension over its
constants, where the tower is realized again (`exists_lift`; the certificate proves the
transcendence of `t` and that `η` is not a derivative, hence not one of an algebraic element,
`not_deriv_of_integral`); there `θ` generates a superelliptic curve over the base `Fₘ` and
`kp_liouville` gives `B θʲ = (y θʲ)′`; completeness of `prdeC` there turns `y` into a returned
solution.

Example: `∫ √(x + log x) dx`, `∫ (log x)² √(x + log x) dx`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The potential `(j/n) a′/a` of the Risch equation, at level `m + 1`. -/
def kpFr (m : ℕ) (j n : ℕ) (a : GPoly (LC m)) : FRep (LC (m + 1)) :=
  ⟨(MO Fc ks (m + 1)).zero, [(mcst Fc ks (m + 1) ((j : ℚ) / n), ((a, [(MO Fc ks m).one]) : LC (m + 1)))]⟩

/-- **The decision** for `∫ B(t) a(t)^{j/n}` over a logarithmic level `t = tₘ`. -/
def kpDecide (m : ℕ) (j n : ℕ) (a B : GPoly (LC m)) : Bool :=
  rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m j n a) ((B, [(MO Fc ks m).one]) : LC (m + 1))

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The value of a polynomial code `(a, 1)` of level `m + 1`. -/
lemma sem_poly_code (m : ℕ) (h : T.Tr (m + 1)) (a : GPoly (LC m)) :
    (((T.MP (m + 1) h).sem ((a, [(MO Fc ks m).one]) : LC (m + 1)) : T.F (m + 1)) : L) =
      T.evP m a := by
  refine (T.sem_MP (m + 1) h _).trans ?_
  change T.evP m a / T.evP m [(MO Fc ks m).one] = T.evP m a
  have h1 : T.evP m [(MO Fc ks m).one] = 1 := by
    simp only [evP, evPL, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
    have h2 : T.ev m (MO Fc ks m).one = 1 := by
      rw [← T.sem_MP m h.of_succ, (T.MP m h.of_succ).sem_one]; rfl
    exact h2
  rw [h1, div_one]

/-- The potential is a constant multiple of a logarithmic derivative. -/
lemma kpFr_ok (m : ℕ) (h : T.Tr (m + 1)) (j n : ℕ) (a : GPoly (LC m)) :
    FRepOK (T.MP (m + 1) h) (kpFr Fc ks m j n a) := by
  intro cw hcw
  simp only [kpFr, List.mem_singleton] at hcw
  subst hcw
  rw [T.sem_mcst, T.deriv_ratCast]

lemma sem_kpFr (m : ℕ) (h : T.Tr (m + 1)) (j n : ℕ) (a : GPoly (LC m)) :
    (((T.MP (m + 1) h).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n a)) : T.F (m + 1)) : L) =
      ((j : ℚ) / n : L) * logDeriv (T.evP m a) := by
  rw [sem_fCode, logSumV]
  simp only [kpFr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    (T.MP (m + 1) h).sem_zero, Derivation.map_zero, zero_add]
  rw [IntermediateField.coe_mul, T.coe_logDeriv_FX, T.sem_poly_code m h, T.sem_mcst, coe_ratCast]
  push_cast
  ring

end MTower

end Curves.MT
