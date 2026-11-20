import RischTragerBronstein.Mixed.FrontSqrtAuto
import RischTragerBronstein.Mixed.FrontSqrtPoleW

/-!
# Whole integrands `e₀ + e₁ √a` with poles, and rational expressions in `√a` with poles

`frontSqrtSumP a e₀ e₁ cs`: `e₀` by `elM`, `e₁ √a` by `frontSqrtPE` (poles `cs` one level below
the top), elementary iff both are (`frontSqrtSumP_sound`); with the antiderivatives
`frontSqrtSumPW` (`frontSqrtSumPW_isSome`, `frontSqrtSumPW_valid`). `frontSqrtAutoP a s cs`: an
expression rational in `√a` (`SE`) split by `SE.split`, then `frontSqrtSumP`
(`frontSqrtAutoP_sound`, `frontSqrtAutoPW_valid`); e.g. `∫ 1/(1 + √(log x))` reduces to
`(1 − √(log x))/(1 − log x)`, a pole at `log x = 1`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- The expression whose nodes make the tower. -/
def spsE (a e0 e1 : EE) (cs : List EE) : EE := EE.add (spE a e1 cs) e0

/-- The antiderivative of `e₀ + e₁ √a` with poles. -/
inductive SumPW where
  | mk (m : ℕ) (w0 : ADW (m + 1)) (w1 : PoleW)

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **The front end for `∫ (e₀ + e₁ √a)`.** -/
def frontSqrtSumP (a e0 e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) : Option Bool :=
  match (spsE a e0 e1 cs).nodesOf.length with
  | 0 => none
  | m + 1 =>
    match comp Fc (spsE a e0 e1 cs).nodesOf (ksOf Fc (spsE a e0 e1 cs)) (m + 1) e0 with
    | none => none
    | some f0 =>
      match elM Fc (ksOf Fc (spsE a e0 e1 cs)) (lvOf Fc (spsE a e0 e1 cs)) (m + 1) f0 N,
        frontSqrtPE Fc (spsE a e0 e1 cs) a e1 cs ps bound rs with
      | some b0, some b1 => some (b0 && b1)
      | _, _ => none

/-- **`frontSqrtSum` with the antiderivative.** -/
def frontSqrtSumPW (a e0 e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    Option (Option SumPW) :=
  match (spsE a e0 e1 cs).nodesOf.length with
  | 0 => none
  | m + 1 =>
    match comp Fc (spsE a e0 e1 cs).nodesOf (ksOf Fc (spsE a e0 e1 cs)) (m + 1) e0 with
    | none => none
    | some f0 =>
      match elMW Fc (ksOf Fc (spsE a e0 e1 cs)) (lvOf Fc (spsE a e0 e1 cs)) (m + 1) f0 N,
        frontSqrtPEW Fc (spsE a e0 e1 cs) a e1 cs ps bound rs with
      | some o0, some o1 => some (match o0, o1 with
        | some w0, some w1 => some (.mk m w0 w1)
        | _, _ => none)
      | _, _ => none

/-- **`frontSqrtSumPW` answers as `frontSqrtSum`.** -/
theorem frontSqrtSumPW_isSome (a e0 e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    (frontSqrtSumPW Fc a e0 e1 cs ps bound rs N).map Option.isSome =
      frontSqrtSumP Fc a e0 e1 cs ps bound rs N := by
  unfold frontSqrtSumPW frontSqrtSumP
  rcases (spsE a e0 e1 cs).nodesOf.length with _ | m
  · rfl
  dsimp only
  rcases comp Fc (spsE a e0 e1 cs).nodesOf (ksOf Fc (spsE a e0 e1 cs)) (m + 1) e0 with _ | f0
  · rfl
  dsimp only
  rw [← elMW_isSome, ← frontSqrtPEW_isSome]
  rcases elMW Fc (ksOf Fc (spsE a e0 e1 cs)) (lvOf Fc (spsE a e0 e1 cs)) (m + 1) f0 N with _ | o0
  · rfl
  rcases frontSqrtPEW Fc (spsE a e0 e1 cs) a e1 cs ps bound rs with _ | o1
  · rfl
  cases o0 <;> cases o1 <;> rfl

/-- **The front end for `∫ s`, `s` rational in `√a`, with poles `cs`.** -/
def frontSqrtAutoP (a : EE) (s : SE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (N : ℕ) : Option Bool :=
  frontSqrtSumP Fc a (s.split a).1 (s.split a).2 cs ps bound rs N

/-- The tower expression of `frontSqrtAutoP`. -/
def sapE (a : EE) (s : SE) (cs : List EE) : EE := spsE a (s.split a).1 (s.split a).2 cs

/-- **`frontSqrtAutoP` with the antiderivative.** -/
def frontSqrtAutoPW (a : EE) (s : SE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (N : ℕ) : Option (Option SumPW) :=
  frontSqrtSumPW Fc a (s.split a).1 (s.split a).2 cs ps bound rs N

theorem frontSqrtAutoPW_isSome (a : EE) (s : SE) (cs : List EE) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (N : ℕ) : (frontSqrtAutoPW Fc a s cs ps bound rs N).map Option.isSome =
      frontSqrtAutoP Fc a s cs ps bound rs N :=
  frontSqrtSumPW_isSome Fc _ _ _ _ _ _ _ _

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **What an answer of `frontSqrtPE` certifies about its data.** -/
lemma frontSqrtPE_data (E a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (b : Bool) (hb : frontSqrtPE Fc E a e1 cs ps bound rs = some b) :
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
  unfold frontSqrtPE frontSqrtPEWith at hb
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
  rcases hcq : allSomeL (cs.map fun c ↦ comp Fc E.nodesOf (ksOf Fc E) m c) with _ | cq
  · rw [hqa, hq1, hcq] at hb; cases hb
  rw [hqa, hq1, hcq] at hb
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
theorem frontSqrtSumP_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a e0 e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontSqrtSumP Fc a e0 e1 cs ps bound rs N = some b)
    (T : MTower Fc (ksOf Fc (spsE a e0 e1 cs)) Cc L) (hn : T.n = (spsE a e0 e1 cs).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (spsE a e0 e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spsE a e0 e1 cs).nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T (spsE a e0 e1 cs).nodesOf e0 +
      evE Fc T (spsE a e0 e1 cs).nodesOf e1 * θ) ↔ b = true := by
  classical
  have hn0 := hn
  have hgen0 := hgen
  unfold frontSqrtSumP at hb
  obtain ⟨m, hlen⟩ : ∃ m, (spsE a e0 e1 cs).nodesOf.length = m + 1 := by
    rcases h0 : (spsE a e0 e1 cs).nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  rcases hf0 : comp Fc (spsE a e0 e1 cs).nodesOf (ksOf Fc (spsE a e0 e1 cs)) (m + 1) e0 with _ | f0
  · rw [hf0] at hb; cases hb
  rw [hf0] at hb
  dsimp only at hb
  rcases hb0 : elM Fc (ksOf Fc (spsE a e0 e1 cs)) (lvOf Fc (spsE a e0 e1 cs)) (m + 1) f0 N with _ | b0
  · rw [hb0] at hb; cases hb
  rcases hb1 : frontSqrtPE Fc (spsE a e0 e1 cs) a e1 cs ps bound rs with _ | b1
  · rw [hb0, hb1] at hb; cases hb
  rw [hb0, hb1] at hb
  obtain rfl := (Option.some.inj hb).symm
  obtain ⟨m', qa, q1, hlen', hsh, hc, hqa, hq1, hd, hz, hsqc, hdegpos⟩ :=
    frontSqrtPE_data (spsE a e0 e1 cs) a e1 cs ps bound rs b1 hb1
  obtain rfl : m' = m := by omega
  have hsound1 := frontSqrtPE_sound hmon hdeg (spsE a e0 e1 cs) a e1 cs ps bound rs b1 hb1 T hn0 θ hθ hgen0
  have MS := T.mspecs hmon hdeg (lvOf Fc (spsE a e0 e1 cs)) (m' + 1) (by omega) hc
  have hTr : T.Tr (m' + 1) := MS.hyp.tr
  have hTm : T.Tr m' := hTr.of_succ
  have hva := comp_spec Fc T (spsE a e0 e1 cs).nodesOf (m' + 1) hTr a qa hqa
  have hv0 := comp_spec Fc T (spsE a e0 e1 cs).nodesOf (m' + 1) hTr e0 f0 hf0
  have hv1 := comp_spec Fc T (spsE a e0 e1 cs).nodesOf (m' + 1) hTr e1 q1 hq1
  have hθA : θ ^ 2 = T.evP m' (qa.1.map ((MO Fc (ksOf Fc (spsE a e0 e1 cs)) m').mul
      ((MO Fc (ksOf Fc (spsE a e0 e1 cs)) m').inv (qa.2.getD 0 (MO Fc (ksOf Fc (spsE a e0 e1 cs)) m').zero)))) := by
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

/-- **Every antiderivative returned by `frontSqrtSumPW` is valid**: the pieces of `e₀` are a valid
`elMW` witness for its code, and the square-root part is valid. -/
theorem frontSqrtSumPW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a e0 e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (m : ℕ) (w0 : ADW (m + 1))
    (w1 : PoleW) (hb : frontSqrtSumPW Fc a e0 e1 cs ps bound rs N = some (some (.mk m w0 w1)))
    (T : MTower Fc (ksOf Fc (spsE a e0 e1 cs)) Cc L) (hn : T.n = (spsE a e0 e1 cs).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (spsE a e0 e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spsE a e0 e1 cs).nodesOf.length) {θ}) :
    (∃ f0 : LC (m + 1), T.ev (m + 1) f0 = evE Fc T (spsE a e0 e1 cs).nodesOf e0 ∧
      T.ValidW (m + 1) f0 w0) ∧
    PoleW.Valid T (lvOf Fc (spsE a e0 e1 cs)) θ (evE Fc T (spsE a e0 e1 cs).nodesOf e1 * θ) w1 := by
  classical
  have hn0 := hn
  have hgen0 := hgen
  unfold frontSqrtSumPW at hb
  obtain ⟨m', hlen⟩ : ∃ m', (spsE a e0 e1 cs).nodesOf.length = m' + 1 := by
    rcases h0 : (spsE a e0 e1 cs).nodesOf.length with _ | m'
    · rw [h0] at hb; cases hb
    · exact ⟨m', rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  rcases hf0 : comp Fc (spsE a e0 e1 cs).nodesOf (ksOf Fc (spsE a e0 e1 cs)) (m' + 1) e0 with _ | f0
  · rw [hf0] at hb; cases hb
  rw [hf0] at hb
  dsimp only at hb
  rcases hb0 : elMW Fc (ksOf Fc (spsE a e0 e1 cs)) (lvOf Fc (spsE a e0 e1 cs)) (m' + 1) f0 N with _ | o0
  · rw [hb0] at hb; cases hb
  rcases hb1 : frontSqrtPEW Fc (spsE a e0 e1 cs) a e1 cs ps bound rs with _ | o1
  · rw [hb0, hb1] at hb; cases hb
  rw [hb0, hb1] at hb
  rcases o0 with _ | w0'
  · cases hb
  rcases o1 with _ | w1'
  · cases hb
  simp only [Option.some.injEq, SumPW.mk.injEq] at hb
  obtain ⟨rfl, hw0, rfl⟩ := hb
  subst hw0
  have hsq := frontSqrtPEW_isSome Fc (spsE a e0 e1 cs) a e1 cs ps bound rs
  rw [hb1] at hsq
  obtain ⟨m'', qa, q1, hlen', hsh, hc, hqa, hq1, hd, hz, hsqc, hdegpos⟩ :=
    frontSqrtPE_data (spsE a e0 e1 cs) a e1 cs ps bound rs true hsq.symm
  obtain rfl : m'' = m' := by omega
  have MS := T.mspecs hmon hdeg (lvOf Fc (spsE a e0 e1 cs)) (m'' + 1) (by omega) hc
  have hTr : T.Tr (m'' + 1) := MS.hyp.tr
  have hTm : T.Tr m'' := hTr.of_succ
  have hva := comp_spec Fc T (spsE a e0 e1 cs).nodesOf (m'' + 1) hTr a qa hqa
  have hθA : θ ^ 2 = T.evP m'' (qa.1.map ((MO Fc (ksOf Fc (spsE a e0 e1 cs)) m'').mul
      ((MO Fc (ksOf Fc (spsE a e0 e1 cs)) m'').inv (qa.2.getD 0 (MO Fc (ksOf Fc (spsE a e0 e1 cs)) m'').zero)))) := by
    rw [hθ, ← hva, ev_constDen T m'' hTm qa hd hz]
  have hθmem : θ ^ 2 ∈ T.F (m'' + 1) := by
    rw [hθA, ← T.sem_poly_code m'' hTr]
    exact SetLike.coe_mem _
  have hθi : IsIntegral (T.F (m'' + 1)) θ := by
    refine ⟨X ^ 2 - C ⟨θ ^ 2, hθmem⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub, eval₂_X_pow, eval₂_C]
  have hE0 := T.isElementary_alg hmon hdeg (m'' + 1) hn hc θ hθi hgen 0 (Nat.zero_le _)
  exact ⟨⟨f0, comp_spec Fc T _ (m'' + 1) hTr e0 f0 hf0,
    T.elMW_validE hmon hdeg hsh (m'' + 1) hn hc hE0 (m'' + 1) le_rfl f0 N _ hb0⟩,
    frontSqrtPEW_valid hmon hdeg (spsE a e0 e1 cs) a e1 cs ps bound rs w1' hb1 T hn0 θ hθ hgen0⟩

/-- An answer of `frontSqrtSumP` comes with an answer for the part `e₁ √a`. -/
lemma frontSqrtSumP_e1 (a e0 e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (N : ℕ) (b : Bool) (hb : frontSqrtSumP Fc a e0 e1 cs ps bound rs N = some b) :
    ∃ b1, frontSqrtPE Fc (spsE a e0 e1 cs) a e1 cs ps bound rs = some b1 := by
  unfold frontSqrtSumP at hb
  revert hb
  rcases (spsE a e0 e1 cs).nodesOf.length with _ | m
  · intro hb; cases hb
  dsimp only
  rcases comp Fc (spsE a e0 e1 cs).nodesOf (ksOf Fc (spsE a e0 e1 cs)) (m + 1) e0 with _ | f0
  · intro hb; cases hb
  dsimp only
  rcases elM Fc (ksOf Fc (spsE a e0 e1 cs)) (lvOf Fc (spsE a e0 e1 cs)) (m + 1) f0 N with _ | b0 <;>
  rcases frontSqrtPE Fc (spsE a e0 e1 cs) a e1 cs ps bound rs with _ | b1
  all_goals first | (intro hb; cases hb; done) | exact fun _ ↦ ⟨_, rfl⟩

/-- Shared setup: `θ ∉ Fₘ₊₁`. -/
lemma frontSqrtAutoP_irr (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (E a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b1 : Bool)
    (hb1 : frontSqrtPE Fc E a e1 cs ps bound rs = some b1)
    (T : MTower Fc (ksOf Fc E) Cc L) (hn : T.n = E.nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T E.nodesOf a) :
    ∀ u v : L, u ∈ T.F T.n → v ∈ T.F T.n → u = v * θ → v = 0 := by
  classical
  obtain ⟨m, qa, q1, hlen, hsh, hc, hqa, hq1, hd, hz, hsqc, hdegpos⟩ :=
    frontSqrtPE_data E a e1 cs ps bound rs b1 hb1
  have MS := T.mspecs hmon hdeg (lvOf Fc E) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hva := comp_spec Fc T E.nodesOf (m + 1) hTr a qa hqa
  have hθA : θ ^ 2 = T.evP m (qa.1.map ((MO Fc (ksOf Fc E) m).mul
      ((MO Fc (ksOf Fc E) m).inv (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero)))) := by
    rw [hθ, ← hva, ev_constDen T m hTm qa hd hz]
  have hnot := theta_notMem T m hTr _ hsqc hdegpos θ hθA
  intro u v hu hv huv
  by_contra hv0
  apply hnot
  have : θ = u / v := by rw [huv]; field_simp
  rw [this, ← hlen, ← hn]
  exact div_mem hu hv

/-- **Every answer of `frontSqrtAutoP` is correct**: for every realization `T` of the compiled
tower and every square root `θ` of `a` generating `L` over it, `∫ s` is elementary iff the
answer is `true`. -/
theorem frontSqrtAutoP_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a : EE) (s : SE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontSqrtAutoP Fc a s cs ps bound rs N = some b)
    (T : MTower Fc (ksOf Fc (sapE a s cs)) Cc L) (hn : T.n = (sapE a s cs).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (sapE a s cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (sapE a s cs).nodesOf.length) {θ}) :
    HasElementaryIntegral (evS T (sapE a s cs).nodesOf θ s) ↔ b = true := by
  classical
  have hs := frontSqrtSumP_sound hmon hdeg a _ _ cs ps bound rs N b hb T hn θ hθ hgen
  obtain ⟨b1, hb1⟩ := frontSqrtSumP_e1 a _ _ cs ps bound rs N b hb
  have hirr := frontSqrtAutoP_irr hmon hdeg _ a _ cs ps bound rs b1 hb1 T hn θ hθ
  rw [SE.split_spec T _ a θ hθ (T.F T.n : Set L) (evE_mem T _) hirr s]
  exact hs

/-- **Every antiderivative returned by `frontSqrtAutoPW` is valid**, for the integrand `s`. -/
theorem frontSqrtAutoPW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a : EE) (s : SE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (m : ℕ)
    (w0 : ADW (m + 1)) (w1 : PoleW)
    (hb : frontSqrtAutoPW Fc a s cs ps bound rs N = some (some (.mk m w0 w1)))
    (T : MTower Fc (ksOf Fc (sapE a s cs)) Cc L) (hn : T.n = (sapE a s cs).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (sapE a s cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (sapE a s cs).nodesOf.length) {θ}) :
    evS T (sapE a s cs).nodesOf θ s = evE Fc T (sapE a s cs).nodesOf (s.split a).1 +
      evE Fc T (sapE a s cs).nodesOf (s.split a).2 * θ ∧
    (∃ f0 : LC (m + 1), T.ev (m + 1) f0 = evE Fc T (sapE a s cs).nodesOf (s.split a).1 ∧
      T.ValidW (m + 1) f0 w0) ∧
    PoleW.Valid T (lvOf Fc (sapE a s cs)) θ
      (evE Fc T (sapE a s cs).nodesOf (s.split a).2 * θ) w1 := by
  classical
  have hv := frontSqrtSumPW_valid hmon hdeg a _ _ cs ps bound rs N m w0 w1 hb T hn θ hθ hgen
  refine ⟨?_, hv⟩
  have hsome : (frontSqrtAutoPW Fc a s cs ps bound rs N).map Option.isSome = some true := by
    rw [hb]; rfl
  rw [frontSqrtAutoPW_isSome] at hsome
  obtain ⟨b1, hb1⟩ := frontSqrtSumP_e1 a _ _ cs ps bound rs N true hsome
  have hirr := frontSqrtAutoP_irr hmon hdeg _ a _ cs ps bound rs b1 hb1 T hn θ hθ
  exact SE.split_spec T _ a θ hθ (T.F T.n : Set L) (evE_mem T _) hirr s

end Curves.MT.Front
