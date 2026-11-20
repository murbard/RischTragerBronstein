import RischTragerBronstein.Mixed.KECodes
import RischTragerBronstein.Algebraic.SupRedNFK
import RischTragerBronstein.Algebraic.SupRedOracle

/-!
# Reductions of the code fields modulo `p`

`redKF p s₀ rs m : RedFns p (KF Fc m)`: reduce the base curve by `x ↦ rs 0`, `y ↦ s₀` (a simple
root of the reduced curve equation), and each `tᵢ ↦ rs (i + 1)`. When the base check holds, it is
induced by an embedding `Kₘ → ℚ_p` (`redKF_valid`): the transcendental elements are sent to
transcendental `p`-adic integers with the prescribed residues (`rfFns_exists`), `y` to a Hensel root
(`nfkFns_exists`). `redAtKF` searches `s₀` and provides the reductions required by
`torsOracle_spec` (`redAtKF_valid`).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))]

instance NF_countable {K : Type} [Field K] [DecidableEq K] [CharZero K] [Countable K]
    (f : CPoly K) : Countable (NFK.NF f) := by
  unfold NFK.NF; infer_instance

theorem KF_countable : ∀ m, Countable (KF Fc m)
  | 0 => by
    show Countable (NFK.NF (fKc Fc))
    infer_instance
  | m + 1 => by
    haveI := KF_countable m
    show Countable (RFC.RatFuncC (KF Fc m))
    infer_instance

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- The reduction of `ℚ(x)` at `x ↦ r`. -/
def redX (r : ZMod p) : RedFns p (RFC.RatFuncC ℚ) := rfFns p (ratFns p) r

/-- **The reductions of the code fields.** -/
def redKF (s0 : ZMod p) (rs : ℕ → ZMod p) : (m : ℕ) → RedFns p (KF Fc m)
  | 0 => nfkFns (redX p (rs 0)) (fKc Fc) s0
  | m + 1 => rfFns p (redKF s0 rs m) (rs (m + 1))

/-- The base check: the curve has integral coefficients and `s₀` is a simple root modulo `p`. -/
def baseOK (s0 : ZMod p) (r : ZMod p) : Bool :=
  (fKc Fc).all (redX p r).ok && evalC ((fKc Fc).map (redX p r).red) s0 == 0 &&
    evalC (CPoly.deriv ((fKc Fc).map (redX p r).red)) s0 != 0

/-- **The reductions are induced by embeddings.** -/
theorem redKF_valid (s0 : ZMod p) (rs : ℕ → ZMod p) (h : baseOK Fc p s0 (rs 0) = true) :
    ∀ m, ∃ φ : KF Fc m →+* ℚ_[p], RedValid p (redKF Fc p s0 rs m) φ
  | 0 => by
    simp only [baseOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hok, hs⟩, hs'⟩ := h
    obtain ⟨φx, hφx⟩ := rfFns_exists (ratFns p) (algebraMap ℚ ℚ_[p]) (ratFns_valid p) (rs 0)
    exact nfkFns_exists (redX p (rs 0)) φx hφx (fKc Fc) hok s0 hs hs'
  | m + 1 => by
    obtain ⟨φ, hφ⟩ := redKF_valid s0 rs h m
    haveI := KF_countable Fc m
    exact rfFns_exists (redKF Fc p s0 rs m) φ hφ (rs (m + 1))

end Prime

/-- **The reductions offered to the torsion oracle**: search a simple root `s₀` of the curve modulo
`p`, with the residues `rs` for `x, t₀, t₁, …`. -/
def redAtKF (m : ℕ) (rs : ℕ → ℕ) : (p : ℕ) → Option (RedFns p (KF Fc m)) := fun p ↦
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    ((List.range p).find? fun i ↦ baseOK Fc p (i : ZMod p) (rs 0 : ZMod p)).map fun i ↦
      redKF Fc p (i : ZMod p) (fun j ↦ (rs j : ZMod p)) m
  else none

theorem redAtKF_valid (m : ℕ) (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (R : RedFns p (KF Fc m))
    (h : redAtKF Fc m rs p = some R) : ∃ φ : KF Fc m →+* ℚ_[p], RedValid p R φ := by
  unfold redAtKF at h
  rw [dif_pos (Fact.out)] at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  have hb := List.find?_some hi
  exact redKF_valid Fc p i (fun j ↦ (rs j : ZMod p)) hb m

end Curves.MT
