import RischTragerBronstein.Mixed.KEBridge
import RischTragerBronstein.Mixed.KEReduce
import RischTragerBronstein.Mixed.KPDecide
import RischTragerBronstein.Mixed.MTRde0
import RischTragerBronstein.Algebraic.SupLocalCert

/-!
# Square roots over an exponential level: the algorithm

`keDecide`: for a certified mixed tower whose top level `t = tₘ` is an exponential, `θ² = A(t)`
(`A ∈ Fₘ[t]` squarefree of odd degree, `A(0) ≠ 0`) and the integrand `B(t) θ / tᵏ`:

1. Solve `z′ + ½ (a₀′/a₀) z = 0` in `Fₘ` (`a₀ = A(0)`, `prdeC` with no right-hand side). Without a
   non-zero solution, `A(0)` is not a constant times a square, `P₊ − ∞` is not torsion
   (`nontors_of_nonsquare`), and the answer is the Risch equation `y′ + ½ (A′/A) y = B/tᵏ`.
2. Otherwise normalize `θ̂ = θ z/√κ` (`κ = z² a₀ ∈ ℚ`), `θ̂² = Â(t)` with `Â(0) = 1`, and ask the torsion
   oracle over the code field `Kₘ` (`torsOracle`, reductions `redAtKF`) whether `P₊ − ∞` is torsion.
   Not torsion: the Risch equation as in 1. Torsion of order `N`: the witness `W = W₀ + W₁ θ̂` of
   `N (P₊ − ∞)` (`witW`), `W′/W = E + B_W θ̂`, and the answer is the parametric Risch equation
   `y′ + ½ (A′/A) y = B/tᵏ + c B_W z` (a solution with the coefficient of `B/tᵏ` non-zero).
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- `tᵏ` as a polynomial code. -/
def monoG (m : ℕ) (k : ℕ) : GPoly (LC m) := List.replicate k (MO Fc ks m).zero ++ [(MO Fc ks m).one]

/-- The denominator `tᵏ A(t)ˡ`. -/
def denC (m : ℕ) (k l : ℕ) (A : GPoly (LC m)) : GPoly (LC m) :=
  GPoly.mul (MO Fc ks m) (monoG Fc ks m k) (powG (MO Fc ks m) A l)

/-- The code `a − b`. -/
def subC {α : Type} (O : COps α) (a b : α) : α := O.add a (O.neg b)

/-- The potential `½ a₀′/a₀` at level `m`. -/
def halfFr (m : ℕ) (a0 : LC m) : FRep (LC m) := ⟨(MO Fc ks m).zero, [(mcst Fc ks m (1 / 2), a0)]⟩

/-- A polynomial over level `m` as a code of level `m + 1`. -/
def pc (m : ℕ) (P : GPoly (LC m)) : LC (m + 1) := (P, [(MO Fc ks m).one])

/-- `r = ½ P′/P`. -/
def halfLog (m : ℕ) (P : LC (m + 1)) : LC (m + 1) :=
  (MO Fc ks (m + 1)).mul (mcst Fc ks (m + 1) (1 / 2))
    ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).deriv P) ((MO Fc ks (m + 1)).inv P))

/-- The column `B_W z` of the logarithmic part, from the witness `W₀ + W₁ θ̂`, `θ̂² = Â`. -/
def logCol (m : ℕ) (Ahat W0 W1 : GPoly (LC m)) (z : LC m) : LC (m + 1) :=
  (MO Fc ks (m + 1)).mul
    ((MO Fc ks (m + 1)).mul
      (subC (MO Fc ks (m + 1))
        ((MO Fc ks (m + 1)).mul (pc Fc ks m W0)
          ((MO Fc ks (m + 1)).add ((MO Fc ks (m + 1)).deriv (pc Fc ks m W1))
            ((MO Fc ks (m + 1)).mul (pc Fc ks m W1) (halfLog Fc ks m (pc Fc ks m Ahat)))))
        ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).deriv (pc Fc ks m W0)) (pc Fc ks m W1)))
      ((MO Fc ks (m + 1)).inv (subC (MO Fc ks (m + 1))
        ((MO Fc ks (m + 1)).mul (pc Fc ks m W0) (pc Fc ks m W0))
        ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).mul (pc Fc ks m W1) (pc Fc ks m W1))
          (pc Fc ks m Ahat)))))
    (pc Fc ks m [z])

/-- Normalize a code through the computable field (reduced fractions). -/
def normC (m : ℕ) (q : LC m) : LC m := unTr Fc m (trC Fc m q)

/-- **The decision** with a certificate provider for the torsion oracle (`none`: the oracle did not
answer within its bounds). -/
def keDecideC (m : ℕ) (A B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) : Option Bool :=
  let O := MO Fc ks m
  let a0 := A.getD 0 O.zero
  let rhs : LC (m + 1) := (B, denC Fc ks m k l A)
  let frA := kpFr Fc ks m 1 2 A
  let plain := rdeOKFr Fc ks lv (m + 1) frA rhs
  match (prdeC Fc ks lv m (halfFr Fc ks m a0) []).find? (fun r ↦ !O.isZero r.2) with
  | none => some plain
  | some (_, z) =>
    let κ := (ratValC Fc ks m (O.mul (O.mul z z) a0)).getD 0
    let c := O.mul (O.mul z z) (mcst Fc ks m κ⁻¹)
    let Ahat : GPoly (LC m) := A.map (O.mul c)
    let fK : CPoly (KF Fc m) := CPoly.trim (Ahat.map (trC Fc m))
    match torsOracleC (redAtKF Fc m rs) (cpf fK) ps bound fK 2 (gammaL ![(0 : KF Fc m)] ![1] ![1] 1) with
    | none => none
    | some none => some plain
    | some (some N) =>
      match witW fK 2 (fK.length - 1) ![(0 : KF Fc m)] ![1] ![1] N with
      | none => none
      | some Wb =>
        let W0 := (Wb.getD 0 []).map (unTr Fc m)
        let W1 := (Wb.getD 1 []).map (unTr Fc m)
        some ((prdeC Fc ks lv (m + 1) frA [rhs, normC Fc (m + 1) (logCol Fc ks m Ahat W0 W1 z)]).any
          fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision** (torsion certificates by search modulo `p`). -/
def keDecide (m : ℕ) (A B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  keDecideC Fc ks lv m A B k l ps bound rs fun fK ↦ searchCert fK 2

/-- **The decision with local certificates** (base points modulo `p`; answers for every large
bound at suitable residues `rs`, `keDecideL_decides`). -/
def keDecideL (m : ℕ) (A B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option Bool :=
  keDecideC Fc ks lv m A B k l ps bound rs fun fK ↦ localCert fK 2

end Curves.MT
