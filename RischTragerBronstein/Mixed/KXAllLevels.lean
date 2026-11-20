import RischTragerBronstein.Mixed.KXNonConstDecide4
import RischTragerBronstein.Mixed.KX0NonConstDecide

/-!
# One cubic decider at every exponential level over a linear base

`kxDecideNC` dispatches to the level-zero procedure or to the recursive tower procedure.
Every answer is correct without Manin's kernel theorem. Eventual completeness assumes `MKT`
over `ℚ` and the code fields strictly below the input level, with the same input conditions
as the two underlying procedures.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]
  (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The cubic decider at any level of a tower over a linear base. -/
def kxDecideNC : (m : ℕ) → LC m → GPoly (LC m) → GPoly (LC m) → ℕ → ℕ →
    List (LC m) → List ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ → Option Bool
  | 0 => kxDecideNC0 [c0, [1]] ks lv
  | m + 1 => kxDecideNCS3 [c0, [1]] ks lv m (recKF c0 m) (recKF1 c0 m)

/-- The well-formedness condition used by the decider at the given level. -/
def kxWF : (m : ℕ) → LC m → Prop
  | 0 => fun a ↦ codeOKb a = true
  | m + 1 => WFm (MO [c0, [1]] ks m)

namespace MTower

variable {ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
  (T : MTower [c0, [1]] ks Cc L)

/-- Every answer of the unified decider is correct, without an `MKT` hypothesis. -/
theorem kxDecideNC_correct (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC [c0, [1]] ks lv (m + 1) = true)
    {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO [c0, [1]] ks m) A = true)
    (hdegpos : 0 < degG (MO [c0, [1]] ks m) A)
    (hcop : Nat.Coprime 2 (degG (MO [c0, [1]] ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hdec : kxDecideNC c0 ks lv m g A B kt l cs ps bound rs nmax kmax = some b) :
    HasElementaryIntegral (T.ev (m + 1)
      ((B, kxDen [c0, [1]] ks m A kt l cs) : LC (m + 1)) * θ) ↔ b = true := by
  cases m with
  | zero =>
    exact T.kxDecideNC0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
      bound rs nmax kmax b hdec
  | succ m =>
    exact T.kxDecideNCS3_correct hmon hdeg m (recKF_sound c0 m) (recKF1_sound c0 m) hn hc hk A
      hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound rs nmax kmax b hdec

/-- Completeness at every level, relative to Manin's kernel theorem below that level. -/
theorem kxDecideNC_decides (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (m : ℕ)
    (hQ : Manin.MKT ℚ) (hMK : ∀ j < m, Manin.MKT (KF [c0, [1]] j))
    (hn : T.n = m + 1) (hc : certC [c0, [1]] ks lv (m + 1) = true)
    {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO [c0, [1]] ks m) A = true)
    (hdeg3 : degG (MO [c0, [1]] ks m) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kxOK [c0, [1]] ks m A B kt l cs = true)
    (hrep : kxConst [c0, [1]] ks m g A B kt l cs = true →
      kxRepOK [c0, [1]] ks m g A B kt l cs = true)
    (hAw : ∀ a ∈ A, kxWF c0 ks m a) (hBw : ∀ b ∈ B, kxWF c0 ks m b)
    (hcsw : ∀ c ∈ cs, kxWF c0 ks m c) (hgw : kxWF c0 ks m g) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ N0, ∀ nmax, N0 ≤ nmax →
      ∃ K0, ∀ kmax, K0 ≤ kmax →
        ∃ b, kxDecideNC c0 ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax kmax = some b ∧
          (HasElementaryIntegral (T.ev (m + 1)
            ((B, kxDen [c0, [1]] ks m A kt l cs) : LC (m + 1)) * θ) ↔ b = true) := by
  have hpos : 0 < degG (MO [c0, [1]] ks m) A := by rw [hdeg3]; decide
  have hcop : Nat.Coprime 2 (degG (MO [c0, [1]] ks m) A) := by rw [hdeg3]; decide
  cases m with
  | zero =>
    exact T.kxDecideNC0_decides hmon hdeg hn hc hk A hsqc hpos hcop hdeg3 θ hθ hgen B kt l cs
      hr0 hok hrep c0 rfl hAw hBw hcsw hgw hQ
  | succ m =>
    exact T.kxDecideNCS3_decides_lin c0 hmon hdeg m hQ (fun j hj ↦ hMK j (by omega)) hn hc hk A
      hsqc hpos hcop hdeg3 θ hθ hgen B kt l cs hr0 hok hrep hAw hBw hcsw hgw

end MTower

end Curves.MT
