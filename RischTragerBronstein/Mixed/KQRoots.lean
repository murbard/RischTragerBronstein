import RischTragerBronstein.Mixed.KQMMain

/-!
# A realization containing constant square roots

`kq_roots`: for any realization `T` and non-zero rationals `κs`, there is a realization `TE` of the
same codes in an algebraic extension `E ⊇ L` containing constant square roots of the `κs`, with
`θ ↦ θE`, `θE² = A`. (As `kqm_lift`, without an antiderivative.)
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **A realization with constant square roots.** -/
theorem kq_roots (m : ℕ) (hn : T.n = m + 1) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (κs : List ℚ) (hκ : ∀ κ ∈ κs, κ ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Differential E) (_ : CharZero E)
      (TE : MTower Fc ks (constants E) E) (θE : E) (rts : List E),
      TE.n = m + 1 ∧ θE ^ 2 = TE.evP m A ∧ rts.length = κs.length ∧
      (∀ i (hi : i < rts.length) (hi' : i < κs.length), rts[i] ^ 2 = (κs[i] : E) ∧ rts[i]′ = 0) := by
  classical
  obtain ⟨E₂, _, _, _, _, -, -, rts, hrl, hrts⟩ := sqrts_ext L κs hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap L E₂).injective
  obtain ⟨TE, hTEn, hTEts, hTEev, -⟩ := T.exists_lift E₂
  set ψ := algebraMap L E₂ with hψ
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    induction P with
    | nil => simp [evP, evPL]
    | cons a P ih =>
      simp only [evP, evPL, List.foldr_cons] at ih ⊢
      rw [ih, map_add, map_mul, hTEts m, ← hTEev m a]
  exact ⟨E₂, inferInstance, inferInstance, inferInstance, TE, ψ θ, rts, by rw [hTEn, hn],
    by rw [hPE, ← map_pow, hθ], hrl, hrts⟩

end MTower

end Curves.MT
