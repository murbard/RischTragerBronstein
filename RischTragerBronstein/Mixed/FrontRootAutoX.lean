import RischTragerBronstein.Mixed.FrontRootSumX
import RischTragerBronstein.Mixed.FrontRootAutoP

/-!
# Arbitrary rational expressions in an `n`-th root over a logarithm or an exponential

`frontRootAutoX M n zN a s pls gss`: an expression `s : SE` rational in `θ` (`θⁿ = a`) is split
as `∑_{j<n} eⱼ θʲ` by `SE.splitN` and decided by `frontRootSumX`, whose top generator may be a
logarithm or an exponential. `frontRootAutoX_sound`: every answer is correct.
-/

open Polynomial Differential IntermediateField Finset

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **The front end for `∫ s`, `s` rational in `θ`, `θⁿ = a`, over a logarithm or an exponential.** -/
def frontRootAutoX (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n : ℕ)
    [∀ m, Fact (Irreducible (toPoly (cycK Fc m n)))]
    (zN : CPoly ℚ) (a : EE) (s : SE) (pls : List (List EE)) (gss : List (List (CPoly ℚ)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) : Option Bool :=
  frontRootSumX Fc M n zN a (s.splitN n a) pls gss ps bound rs N

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **What an answer of `frontRootSumX` certifies about `a`.** -/
lemma frontRootSumX_data (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n : ℕ)
    [∀ m, Fact (Irreducible (toPoly (cycK Fc m n)))]
    (zN : CPoly ℚ) (a : EE) (es : List EE) (pls : List (List EE)) (gss : List (List (CPoly ℚ)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontRootSumX Fc M n zN a es pls gss ps bound rs N = some b) :
    ∃ (m : ℕ) (qa : LC (m + 1)), (rspE a es pls).nodesOf.length = m + 1 ∧
      certC Fc (ksOf Fc (rspE a es pls)) (lvOf Fc (rspE a es pls)) (m + 1) = true ∧
      comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) a = some qa ∧
      degG (MO Fc (ksOf Fc (rspE a es pls)) m) qa.2 = 0 ∧
      GPoly.isZero (MO Fc (ksOf Fc (rspE a es pls)) m) qa.2 = false ∧
      GPoly.squarefreeCheck (MO Fc (ksOf Fc (rspE a es pls)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rspE a es pls)) m).mul ((MO Fc (ksOf Fc (rspE a es pls)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rspE a es pls)) m).zero)))) = true ∧
      0 < degG (MO Fc (ksOf Fc (rspE a es pls)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rspE a es pls)) m).mul ((MO Fc (ksOf Fc (rspE a es pls)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rspE a es pls)) m).zero)))) ∧ 0 < n := by
  classical
  unfold frontRootSumX at hb
  obtain ⟨m, hlen⟩ : ∃ m, (rspE a es pls).nodesOf.length = m + 1 := by
    rcases h0 : (rspE a es pls).nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc (rspE a es pls)) (lvOf Fc (rspE a es pls))
      (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨-, hc⟩ := Bool.and_eq_true_iff.mp hcs
  rcases hqa : comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hf0 : comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1)
    (es.getD 0 (EE.cst 0)) with _ | f0
  · rw [hqa, hf0] at hb; cases hb
  rw [hqa, hf0] at hb
  dsimp only at hb
  by_cases hd1 : degG (MO Fc (ksOf Fc (rspE a es pls)) m) qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc (rspE a es pls)) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc (rspE a es pls)) m)
      (qa.1.map ((MO Fc (ksOf Fc (rspE a es pls)) m).mul ((MO Fc (ksOf Fc (rspE a es pls)) m).inv
        (qa.2.getD 0 (MO Fc (ksOf Fc (rspE a es pls)) m).zero))))) = true ∨
      degG (MO Fc (ksOf Fc (rspE a es pls)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rspE a es pls)) m).mul ((MO Fc (ksOf Fc (rspE a es pls)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rspE a es pls)) m).zero)))) = 0 ∨
      Nat.gcd n (degG (MO Fc (ksOf Fc (rspE a es pls)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rspE a es pls)) m).mul ((MO Fc (ksOf Fc (rspE a es pls)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rspE a es pls)) m).zero))))) ≠ 1 ∨ n = 0 ∨ n < es.length
  · rw [if_pos hd2] at hb; cases hb
  push Not at hd2
  obtain ⟨hsq, hdegpos, -, hn0, -⟩ := hd2
  exact ⟨m, qa, hlen, hc, hqa, hd1.1, by simpa using hd1.2, by simpa using hsq,
    Nat.pos_of_ne_zero hdegpos, Nat.pos_of_ne_zero hn0⟩

/-- The splitting is correct for every realization. -/
lemma frontRootAutoX_split (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n : ℕ)
    [∀ m, Fact (Irreducible (toPoly (cycK Fc m n)))]
    (zN : CPoly ℚ) (a : EE) (s : SE) (pls : List (List EE)) (gss : List (List (CPoly ℚ)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontRootAutoX Fc M n zN a s pls gss ps bound rs N = some b)
    (T : MTower Fc (ksOf Fc (rapE n a s pls)) Cc L) (hn : T.n = (rapE n a s pls).nodesOf.length)
    (θ : L) (hθ : θ ^ n = evE Fc T (rapE n a s pls).nodesOf a) :
    evS T (rapE n a s pls).nodesOf θ s = ∑ j ∈ range n,
      evE Fc T (rapE n a s pls).nodesOf ((s.splitN n a).getD j (EE.cst 0)) * θ ^ j := by
  classical
  obtain ⟨m, qa, hlen, hc, hqa, hd, hz, hsqc, hdegpos, hn0⟩ :=
    frontRootSumX_data M n zN a (s.splitN n a) pls gss ps bound rs N b hb
  have hTn : T.n = m + 1 := by rw [hn]; exact hlen
  have MS := T.mspecs hmon hdeg (lvOf Fc (rapE n a s pls)) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hva := comp_spec Fc T (rapE n a s pls).nodesOf (m + 1) hTr a qa hqa
  have hθA : θ ^ n = T.evP m (qa.1.map ((MO Fc (ksOf Fc (rapE n a s pls)) m).mul
      ((MO Fc (ksOf Fc (rapE n a s pls)) m).inv
        (qa.2.getD 0 (MO Fc (ksOf Fc (rapE n a s pls)) m).zero)))) := by
    rw [hθ, ← hva, ev_constDen T m hTm qa hd hz]
  refine SE.splitN_spec T _ n hn0 a θ hθ (T.F T.n).toSubfield (evE_mem T _) ?_ s
  intro w hw h0
  exact theta_indep T m hTr _ hsqc hdegpos n hn0 θ hθA w (fun i ↦ by rw [← hTn]; exact hw i) h0

/-- **Every answer of `frontRootAutoX` is correct**: for every realization `T` of the compiled
tower and every `n`-th root `θ` of `a` generating `L` over it, `∫ s` is elementary iff the
answer is `true`. -/
theorem frontRootAutoX_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n : ℕ)
    [∀ m, Fact (Irreducible (toPoly (cycK Fc m n)))]
    (zN : CPoly ℚ) (a : EE) (s : SE) (pls : List (List EE)) (gss : List (List (CPoly ℚ)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontRootAutoX Fc M n zN a s pls gss ps bound rs N = some b)
    (T : MTower Fc (ksOf Fc (rapE n a s pls)) Cc L) (hn : T.n = (rapE n a s pls).nodesOf.length)
    (θ : L) (hθ : θ ^ n = evE Fc T (rapE n a s pls).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (rapE n a s pls).nodesOf.length) {θ}) :
    HasElementaryIntegral (evS T (rapE n a s pls).nodesOf θ s) ↔ b = true := by
  rw [frontRootAutoX_split hmon hdeg M n zN a s pls gss ps bound rs N b hb T hn θ hθ]
  exact frontRootSumX_sound hmon hdeg M n zN a _ pls gss ps bound rs N b hb T hn θ hθ hgen

end Curves.MT.Front
