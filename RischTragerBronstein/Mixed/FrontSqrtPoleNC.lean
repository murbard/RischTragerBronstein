import RischTragerBronstein.Mixed.FrontSqrtPole
import RischTragerBronstein.Mixed.KXAuto

/-!
# Square-root expressions with the complete cubic exponential solver

The existing pole parser now feeds `kxDecideNC` at exponential levels. Its logarithmic branch
is unchanged. The automatic entry point enumerates residue data and search bounds, and retains
the first answer. Soundness does not assume Manin's kernel theorem.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT.Front

open CPoly Sup Curves.LT

universe u

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]

/-- Compile pole expressions and use the recursive cubic solver below an exponential. -/
def frontSqrtPNCE (E a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option Bool :=
  frontSqrtPEWith [c0, [1]]
    (fun K lv m g A B kt l cq ↦ kxDecideNC c0 K lv m g A B kt l cq ps bound rs nmax kmax)
    E a e1 cs ps bound rs

/-- One attempt, decoding both residue data and all three search bounds. -/
def frontSqrtPAutoStage (E a e1 : EE) (cs : List EE) (i : ℕ) : Option Bool :=
  let r := Nat.unpair i
  let p := Nat.unpair r.2
  let q := Nat.unpair p.2
  frontSqrtPNCE c0 E a e1 cs (primesBelow p.1) p.1 (natSeq r.1) q.1 q.2

/-- The pole expression front end with automatic residue data and one search bound. -/
def frontSqrtPAutoE (E a e1 : EE) (cs : List EE) (N : ℕ) : Option Bool :=
  prefixSearch (frontSqrtPAutoStage c0 E a e1 cs) N

/-- Automatically build the tower and search for the integral of `e1 * √a`. -/
def frontSqrtPAuto (a e1 : EE) (cs : List EE) (N : ℕ) : Option Bool :=
  frontSqrtPAutoE c0 (spE a e1 cs) a e1 cs N

/-- An answer is preserved at every larger search bound. -/
theorem frontSqrtPAuto_mono (a e1 : EE) (cs : List EE) {N M : ℕ} {b : Bool}
    (hNM : N ≤ M) (h : frontSqrtPAuto c0 a e1 cs N = some b) :
    frontSqrtPAuto c0 a e1 cs M = some b :=
  prefixSearch_mono hNM h

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- Replacing the exponential backend preserves the parser's semantics. -/
theorem frontSqrtPNCE_sound (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (E a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hb : frontSqrtPNCE c0 E a e1 cs ps bound rs nmax kmax = some b)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    HasElementaryIntegral (evE [c0, [1]] T E.nodesOf e1 * θ) ↔ b = true := by
  apply frontSqrtPEWith_sound _ hmon hdeg E a e1 cs ps bound rs b hb T hn θ hθ hgen
  intro m hn hc g hk A hsq hp hcop θ hθ hgen B kt l cq b hb
  exact T.kxDecideNC_correct c0 hmon hdeg m hn hc hk A hsq hp hcop θ hθ hgen B kt l cq
    ps bound rs nmax kmax b hb

/-- Every answer of the automatic search has the requested expression semantics. -/
theorem frontSqrtPAutoE_sound (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (E a e1 : EE) (cs : List EE)
    (N : ℕ) (b : Bool) (hb : frontSqrtPAutoE c0 E a e1 cs N = some b)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    HasElementaryIntegral (evE [c0, [1]] T E.nodesOf e1 * θ) ↔ b = true := by
  obtain ⟨i, -, hi⟩ := prefixSearch_sound hb
  exact frontSqrtPNCE_sound c0 hmon hdeg E a e1 cs _ _ _ _ _ b hi T hn θ hθ hgen

/-- The tower-building automatic front end is sound, without an `MKT` hypothesis. -/
theorem frontSqrtPAuto_sound (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (a e1 : EE) (cs : List EE)
    (N : ℕ) (b : Bool) (hb : frontSqrtPAuto c0 a e1 cs N = some b)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] (spE a e1 cs)) Cc L)
    (hn : T.n = (spE a e1 cs).nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T (spE a e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spE a e1 cs).nodesOf.length) {θ}) :
    HasElementaryIntegral (evE [c0, [1]] T (spE a e1 cs).nodesOf e1 * θ) ↔ b = true :=
  frontSqrtPAutoE_sound c0 hmon hdeg _ a e1 cs N b hb T hn θ hθ hgen

end Curves.MT.Front
