import RischTragerBronstein.Mixed.FrontSqrtPoleNC

/-!+# Coverage of the automatic square-root pole search

Only the first `E.nodesOf.length` residue entries affect a compiled expression. Thus the
automatic search reaches every successful attempt whose prime list is `primesBelow bound`.
This is a coverage theorem for accepted attempts, not completeness for arbitrary expressions.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT.Front

open CPoly Sup Curves.LT

universe u

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]

/-- The pole front end reads only one residue entry per tower level. -/
theorem frontSqrtPNCE_congr_prefix (E a e1 : EE) (cs : List EE) (ps : List ℕ)
    (bound nmax kmax : ℕ) {rs rt : ℕ → ℕ}
    (h : ∀ j < E.nodesOf.length, rs j = rt j) :
    frontSqrtPNCE c0 E a e1 cs ps bound rs nmax kmax =
      frontSqrtPNCE c0 E a e1 cs ps bound rt nmax kmax := by
  unfold frontSqrtPNCE frontSqrtPEWith
  split
  · rfl
  · rename_i m hm
    have hr := redAtKF_congr_prefix [c0, [1]] m
      (fun j hj ↦ h j (by omega))
    have hx := fun g A B kt l cq ↦
      kxDecideNC_congr_prefix c0 (ksOf [c0, [1]] E) (lvOf [c0, [1]] E)
        m g A B kt l cq ps bound nmax kmax (fun j hj ↦ h j (by omega))
    simp only [hx, kqDecide, kqDecideC, hr]

/-- Encode a successful parameter choice as one stage of the automatic search. -/
theorem frontSqrtPAutoStage_reaches (E a e1 : EE) (cs : List EE)
    (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) :
    frontSqrtPAutoStage c0 E a e1 cs
        (Nat.pair (natSeqCode E.nodesOf.length rs) (Nat.pair bound (Nat.pair nmax kmax))) =
      frontSqrtPNCE c0 E a e1 cs (primesBelow bound) bound rs nmax kmax := by
  simp only [frontSqrtPAutoStage, Nat.unpair_pair]
  exact frontSqrtPNCE_congr_prefix c0 E a e1 cs (primesBelow bound) bound nmax kmax
    (natSeq_code E.nodesOf.length rs)

/-- A successful attempt guarantees an eventual, persistent answer of the automatic search. -/
theorem frontSqrtPAutoE_complete (E a e1 : EE) (cs : List EE)
    (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hb : frontSqrtPNCE c0 E a e1 cs (primesBelow bound) bound rs nmax kmax = some b) :
    ∃ N0 b', ∀ N, N0 ≤ N → frontSqrtPAutoE c0 E a e1 cs N = some b' := by
  have hi := (frontSqrtPAutoStage_reaches c0 E a e1 cs bound rs nmax kmax).trans hb
  obtain ⟨b', hb'⟩ := prefixSearch_complete hi
  exact ⟨Nat.pair (natSeqCode E.nodesOf.length rs) (Nat.pair bound (Nat.pair nmax kmax)) + 1,
    b', fun N hN ↦ hb' N (by omega)⟩

/-- The tower-building search also reaches every successful parameter choice. -/
theorem frontSqrtPAuto_complete (a e1 : EE) (cs : List EE)
    (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hb : frontSqrtPNCE c0 (spE a e1 cs) a e1 cs (primesBelow bound) bound rs nmax kmax =
      some b) :
    ∃ N0 b', ∀ N, N0 ≤ N → frontSqrtPAuto c0 a e1 cs N = some b' :=
  frontSqrtPAutoE_complete c0 _ a e1 cs bound rs nmax kmax b hb

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- With a realization, every sufficiently large automatic search returns the same answer
as the successful attempt, including a negative answer. No `MKT` hypothesis is needed. -/
theorem frontSqrtPAutoE_decides_of_attempt (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (E a e1 : EE) (cs : List EE)
    (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hb : frontSqrtPNCE c0 E a e1 cs (primesBelow bound) bound rs nmax kmax = some b)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    (∃ N0, ∀ N, N0 ≤ N → frontSqrtPAutoE c0 E a e1 cs N = some b) ∧
      (HasElementaryIntegral (evE [c0, [1]] T E.nodesOf e1 * θ) ↔ b = true) := by
  have hs := frontSqrtPNCE_sound c0 hmon hdeg E a e1 cs _ bound rs nmax kmax b hb
    T hn θ hθ hgen
  obtain ⟨N0, b', hN⟩ := frontSqrtPAutoE_complete c0 E a e1 cs bound rs nmax kmax b hb
  have hs' := frontSqrtPAutoE_sound c0 hmon hdeg E a e1 cs N0 b' (hN N0 le_rfl)
    T hn θ hθ hgen
  have heq : b' = b := by cases b <;> cases b' <;> simp_all
  exact ⟨⟨N0, by simpa only [heq] using hN⟩, hs⟩

/-- The same-answer guarantee for the tower-building entry point. -/
theorem frontSqrtPAuto_decides_of_attempt (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (a e1 : EE) (cs : List EE)
    (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hb : frontSqrtPNCE c0 (spE a e1 cs) a e1 cs (primesBelow bound) bound rs nmax kmax =
      some b)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] (spE a e1 cs)) Cc L)
    (hn : T.n = (spE a e1 cs).nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T (spE a e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spE a e1 cs).nodesOf.length) {θ}) :
    (∃ N0, ∀ N, N0 ≤ N → frontSqrtPAuto c0 a e1 cs N = some b) ∧
      (HasElementaryIntegral (evE [c0, [1]] T (spE a e1 cs).nodesOf e1 * θ) ↔ b = true) :=
  frontSqrtPAutoE_decides_of_attempt c0 hmon hdeg _ a e1 cs bound rs nmax kmax b hb
    T hn θ hθ hgen

end Curves.MT.Front
