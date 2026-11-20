import RischTragerBronstein.Mixed.FrontSqrt
import RischTragerBronstein.Mixed.KLDecideW
import RischTragerBronstein.Mixed.MTElemTower

/-!
# The front end with a square root: whole integrands `e₀ + e₁ √a`

`frontSqrtSum a e₀ e₁ … N`: decides `∫ (e₀ + e₁ √a)` over the tower of all three expressions:
`e₀` by `elM`, `e₁ √a` by `frontSqrtE`; the integral is elementary iff both parts are
(`kl_componentsW`: the components of an elementary integrand are elementary, for a top level of
either kind; conversely `HasElementaryIntegral.add_in`, the part `e₀` having an integral over
every elementary extension). `frontSqrtSum_sound`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- The expression whose nodes make the tower. -/
def ssE (a e0 e1 : EE) : EE := EE.add a (EE.add e0 e1)

/-- **The front end for `∫ (e₀ + e₁ √a)`.** -/
def frontSqrtSum (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) : Option Bool :=
  match (ssE a e0 e1).nodesOf.length with
  | 0 => none
  | m + 1 =>
    match comp Fc (ssE a e0 e1).nodesOf (ksOf Fc (ssE a e0 e1)) (m + 1) e0 with
    | none => none
    | some f0 =>
      match elM Fc (ksOf Fc (ssE a e0 e1)) (lvOf Fc (ssE a e0 e1)) (m + 1) f0 N,
        frontSqrtE Fc (ssE a e0 e1) a e1 ps bound rs with
      | some b0, some b1 => some (b0 && b1)
      | _, _ => none

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **What an answer of `frontSqrtE` certifies about its data.** -/
lemma frontSqrtE_data (E a e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hb : frontSqrtE Fc E a e1 ps bound rs = some b) :
    ∃ (m : ℕ) (qa q1 : LC (m + 1)), E.nodesOf.length = m + 1 ∧ curveShape Fc = true ∧
      certC Fc (ksOf Fc E) (lvOf Fc E) (m + 1) = true ∧
      comp Fc E.nodesOf (ksOf Fc E) (m + 1) a = some qa ∧
      comp Fc E.nodesOf (ksOf Fc E) (m + 1) e1 = some q1 ∧
      degG (MO Fc (ksOf Fc E) m) qa.2 = 0 ∧ GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = false ∧
      GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m)
        (qa.1.map ((MO Fc (ksOf Fc E) m).mul ((MO Fc (ksOf Fc E) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero)))) = true ∧
      0 < degG (MO Fc (ksOf Fc E) m)
        (qa.1.map ((MO Fc (ksOf Fc E) m).mul ((MO Fc (ksOf Fc E) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero)))) := by
  classical
  unfold frontSqrtE at hb
  obtain ⟨m, hlen⟩ : ∃ m, E.nodesOf.length = m + 1 := by
    rcases h0 : E.nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc E) (lvOf Fc E) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨hsh, hc⟩ := Bool.and_eq_true_iff.mp hcs
  rcases hqa : comp Fc E.nodesOf (ksOf Fc E) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hq1 : comp Fc E.nodesOf (ksOf Fc E) (m + 1) e1 with _ | q1
  · rw [hqa, hq1] at hb; cases hb
  rw [hqa, hq1] at hb
  dsimp only at hb
  by_cases hd1 : degG (MO Fc (ksOf Fc E) m) qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m)
      (qa.1.map ((MO Fc (ksOf Fc E) m).mul ((MO Fc (ksOf Fc E) m).inv
        (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero))))) = true ∨
      degG (MO Fc (ksOf Fc E) m) (qa.1.map ((MO Fc (ksOf Fc E) m).mul ((MO Fc (ksOf Fc E) m).inv
        (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero)))) % 2 = 0
  · rw [if_pos hd2] at hb; cases hb
  push Not at hd2
  exact ⟨m, qa, q1, hlen, hsh, hc, hqa, hq1, hd1.1, by simpa using hd1.2, by simpa using hd2.1,
    by omega⟩

/-- **Every answer of `frontSqrtSum` is correct**: for every realization `T` of the compiled
tower and every square root `θ` of `a` generating `L` over it, `∫ (e₀ + e₁ θ)` is elementary iff
the answer is `true`. -/
theorem frontSqrtSum_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontSqrtSum Fc a e0 e1 ps bound rs N = some b)
    (T : MTower Fc (ksOf Fc (ssE a e0 e1)) Cc L) (hn : T.n = (ssE a e0 e1).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (ssE a e0 e1).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (ssE a e0 e1).nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T (ssE a e0 e1).nodesOf e0 +
      evE Fc T (ssE a e0 e1).nodesOf e1 * θ) ↔ b = true := by
  classical
  have hn0 := hn
  have hgen0 := hgen
  unfold frontSqrtSum at hb
  obtain ⟨m, hlen⟩ : ∃ m, (ssE a e0 e1).nodesOf.length = m + 1 := by
    rcases h0 : (ssE a e0 e1).nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  rcases hf0 : comp Fc (ssE a e0 e1).nodesOf (ksOf Fc (ssE a e0 e1)) (m + 1) e0 with _ | f0
  · rw [hf0] at hb; cases hb
  rw [hf0] at hb
  dsimp only at hb
  rcases hb0 : elM Fc (ksOf Fc (ssE a e0 e1)) (lvOf Fc (ssE a e0 e1)) (m + 1) f0 N with _ | b0
  · rw [hb0] at hb; cases hb
  rcases hb1 : frontSqrtE Fc (ssE a e0 e1) a e1 ps bound rs with _ | b1
  · rw [hb0, hb1] at hb; cases hb
  rw [hb0, hb1] at hb
  obtain rfl := (Option.some.inj hb).symm
  obtain ⟨m', qa, q1, hlen', hsh, hc, hqa, hq1, hd, hz, hsqc, hdegpos⟩ :=
    frontSqrtE_data (ssE a e0 e1) a e1 ps bound rs b1 hb1
  obtain rfl : m' = m := by omega
  have hsound1 := frontSqrtE_sound hmon hdeg (ssE a e0 e1) a e1 ps bound rs b1 hb1 T hn0 θ hθ hgen0
  have MS := T.mspecs hmon hdeg (lvOf Fc (ssE a e0 e1)) (m' + 1) (by omega) hc
  have hTr : T.Tr (m' + 1) := MS.hyp.tr
  have hTm : T.Tr m' := hTr.of_succ
  have hva := comp_spec Fc T (ssE a e0 e1).nodesOf (m' + 1) hTr a qa hqa
  have hv0 := comp_spec Fc T (ssE a e0 e1).nodesOf (m' + 1) hTr e0 f0 hf0
  have hv1 := comp_spec Fc T (ssE a e0 e1).nodesOf (m' + 1) hTr e1 q1 hq1
  have hθA : θ ^ 2 = T.evP m' (qa.1.map ((MO Fc (ksOf Fc (ssE a e0 e1)) m').mul
      ((MO Fc (ksOf Fc (ssE a e0 e1)) m').inv (qa.2.getD 0 (MO Fc (ksOf Fc (ssE a e0 e1)) m').zero)))) := by
    rw [hθ, ← hva, ev_constDen T m' hTm qa hd hz]
  -- `L` is algebraic and elementary over `Fₘ₊₁`
  have hθmem : θ ^ 2 ∈ T.F (m' + 1) := by
    rw [hθA, ← T.sem_poly_code m' hTr]
    exact SetLike.coe_mem _
  have hθi : IsIntegral (T.F (m' + 1)) θ := by
    refine ⟨X ^ 2 - C ⟨θ ^ 2, hθmem⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub, eval₂_X_pow, eval₂_C]
  have halg : Algebra.IsAlgebraic (T.F (m' + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m' + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have hE := T.isElementary_alg hmon hdeg (m' + 1) hn hc θ hθi hgen (m' + 1) le_rfl
  -- the part `e₀` in the subtower
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m' + 1) (by omega)
  have hs0 := elM_sound hmon hdeg hsh T' (m' + 1) hT'n hc hT'gen f0 N b0 hb0
  have hT'v : algebraMap (T.F (m' + 1)) L (T'.ev (m' + 1) f0) = T.ev (m' + 1) f0 :=
    hT'ev (m' + 1) le_rfl f0
  have h0 : HasElementaryIntegral (T.ev (m' + 1) f0) ↔ b0 = true := by
    rw [← hT'v, hasElementaryIntegral_isAlgebraic_iff halg]
    exact hs0.1
  rw [← hv0, Bool.and_eq_true]
  constructor
  · intro hf
    set cs : ℕ → LC (m' + 1) := fun j ↦ if j = 0 then f0 else q1 with hcs
    have hf' : HasElementaryIntegral (∑ j ∈ Finset.range 2, T.ev (m' + 1) (cs j) * θ ^ j) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hcs, zero_add, pow_zero, mul_one,
        pow_one, if_pos rfl, one_ne_zero, if_false]
      rw [← hv1] at hf
      exact hf
    have hcomp := T.kl_componentsW hmon hdeg m' hn hc _ 2 two_pos hsqc hdegpos θ hθA hgen cs hf'
    have hc0 := hcomp 0 two_pos
    have hc1 := hcomp 1 one_lt_two
    simp only [hcs, if_pos rfl, pow_zero, mul_one, one_ne_zero, if_false, pow_one] at hc0 hc1
    rw [hv1] at hc1
    exact ⟨h0.mp hc0, hsound1.mp hc1⟩
  · rintro ⟨h0t, h1t⟩
    have hIn : HasElementaryIntegralIn (T.ev (m' + 1) f0) := by
      rw [← hT'v]
      exact HasElementaryIntegralIn.of_base hE (hs0.2 h0t)
    rw [add_comm]
    exact (hsound1.mpr h1t).add_in hIn

end Curves.MT.Front
