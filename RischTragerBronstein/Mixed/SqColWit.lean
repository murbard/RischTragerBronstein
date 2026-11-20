import RischTragerBronstein.Mixed.ColWit

/-!
# Square-root logarithmic columns as data

A column of the square-root deciders (`KQ`, `KQM`, `KX`, `KE`) is `logCol Â W₀ W₁ z` for a
twist `Â` of `A` with `Â ρ² = z² A`, `ρ² = ρsq ∈ ℚ` (`SqCol`, `SqCol.Good`). With `θ² = A`,
`Y = z θ / ρ` is a square root of `Â`, and the column times `θ` is
`ρ ((W₀ + W₁ Y)′/(W₀ + W₁ Y) − ½ N′/N)` (`SqCol.logs`). With a solution of the parametric
equation, `∫ rhs θ = (y/q₀) θ + ∑ₖ (−qₖ/q₀) ρₖ (log(W₀ₖ + W₁ₖ Yₖ) − ½ log Nₖ)`
(`sqcols_antiderivative`, columns with `Nₖ = 0` contribute nothing).
-/

open Polynomial CPoly Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- **A square-root logarithmic column**: `logCol Â W₀ W₁ z` with `Â ρsq = z² A`. -/
structure SqCol (m : ℕ) where
  Ahat : GPoly (LC m)
  W0 : GPoly (LC m)
  W1 : GPoly (LC m)
  z : LC m
  ρsq : ℚ

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)

/-- The code of the column. -/
def SqCol.code {m : ℕ} (c : SqCol m) : LC (m + 1) :=
  normC Fc (m + 1) (logCol Fc ks m c.Ahat c.W0 c.W1 c.z)

universe u

variable {Fc ks} {lv : (m : ℕ) → LC m} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L]
  [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The column is a twist of `A`: `Â ρsq = z² A`, `ρsq ≠ 0`, `z ≠ 0`. -/
def SqCol.Good {m : ℕ} (A : GPoly (LC m)) (c : SqCol m) : Prop :=
  c.ρsq ≠ 0 ∧ T.ev m c.z ≠ 0 ∧ T.evP m c.Ahat * (c.ρsq : L) = T.ev m c.z ^ 2 * T.evP m A

/-- The norm `N = W₀² − W₁² Â`. -/
noncomputable def SqCol.norm {m : ℕ} (c : SqCol m) : L :=
  T.evP m c.W0 ^ 2 - T.evP m c.W1 ^ 2 * T.evP m c.Ahat

/-- **The column times `θ`, explicitly**: with `ρ² = ρsq`, `Y = z θ/ρ`. -/
theorem SqCol.logs {m : ℕ} (h : T.Tr (m + 1)) (A : GPoly (LC m)) (c : SqCol m)
    (hc : SqCol.Good T A c) (θ : L) (hθ : θ ^ 2 = T.evP m A) (hθ0 : θ ≠ 0)
    (E : Type*) [Field E] [CharZero E] [Differential E] [Algebra L E] [DifferentialAlgebra L E]
    (ρ : E) (hρ : ρ ^ 2 = c.ρsq) :
    let ψ := algebraMap L E
    let Y := ψ (T.ev m c.z * θ) / ρ
    (SqCol.norm T c = 0 → T.ev (m + 1) (c.code Fc ks) * θ = 0) ∧
    (SqCol.norm T c ≠ 0 → ψ (T.ev (m + 1) (c.code Fc ks) * θ) =
      ρ * (logDeriv (ψ (T.evP m c.W0) + ψ (T.evP m c.W1) * Y) -
        (1 / 2 : E) * logDeriv (ψ (SqCol.norm T c)))) := by
  intro ψ Y
  obtain ⟨hρsq, hz0, hrel⟩ := hc
  rw [SqCol.code, T.ev_normC (m + 1) h]
  refine ⟨fun hN ↦ by rw [T.logCol_zero_of_norm m h _ _ _ _ hN, zero_mul], fun hN ↦ ?_⟩
  have hρ0 : ρ ≠ 0 := fun h0 ↦ hρsq (by
    have : ((c.ρsq : ℚ) : E) = 0 := by rw [← hρ, h0]; ring
    exact_mod_cast this)
  have hY0 : Y ≠ 0 := div_ne_zero ((map_ne_zero ψ).mpr (mul_ne_zero hz0 hθ0)) hρ0
  have hY2 : Y ^ 2 = ψ (T.evP m c.Ahat) := by
    show (ψ (T.ev m c.z * θ) / ρ) ^ 2 = _
    have hA : T.evP m c.Ahat = T.ev m c.z ^ 2 * T.evP m A / (c.ρsq : L) := by
      rw [← hrel]; field_simp
    rw [div_pow, hρ, ← map_pow, mul_pow, hθ, hA, map_div₀, map_ratCast]
  have := T.logCol_theta_logs m h c.Ahat c.W0 c.W1 c.z θ hN E Y ρ hY2 hY0 (by
    show ψ (T.ev m c.z * θ) = ρ * (ψ (T.ev m c.z * θ) / ρ)
    field_simp)
  exact this

/-- **The antiderivative of a parametric solution with square-root columns.** -/
theorem sqcols_antiderivative (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (rhs : LC (m + 1)) (cols : List (SqCol m)) (r : List ℚ × LC (m + 1))
    (hr : r ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: cols.map (SqCol.code Fc ks)))
    (hq0 : r.1.getD 0 0 ≠ 0) :
    T.ev (m + 1) rhs * θ = ((T.ev (m + 1) r.2 / (r.1.getD 0 0 : L)) * θ)′ +
      ∑ k : Fin cols.length, ((-(r.1.getD (k + 1) 0) / r.1.getD 0 0 : ℚ) : L) *
        (T.ev (m + 1) (cols[k].code Fc ks) * θ) := by
  have := T.prde_param_eqN m 2 1 two_pos hTr A θ hθ hA0 hspec rhs (cols.map (SqCol.code Fc ks)) r hr
    hq0
  simp only [pow_one] at this
  rw [this]
  congr 1
  have hl : (cols.map (SqCol.code Fc ks)).length = cols.length := List.length_map _
  rw [← Fin.sum_congr' (M := L) (fun k : Fin cols.length ↦
    ((-(r.1.getD (k + 1) 0) / r.1.getD 0 0 : ℚ) : L) * (T.ev (m + 1) (cols[k].code Fc ks) * θ)) hl]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Fin.getElem_fin, List.getElem_map, Fin.val_cast]

end MTower

end Curves.MT
