import RischTragerBronstein.Mixed.FrontSqrtW

/-!
# Whole integrands `e₀ + e₁ √a` with the antiderivative

`frontSqrtSumW` mirrors `frontSqrtSum` (`frontSqrtSumW_isSome`) and returns the antiderivative of
`e₀` (`elMW`) and of `e₁ √a` (`frontSqrtEW`); `frontSqrtSumW_valid`; `frontSqrtSumShow` prints both.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- The antiderivative of `e₀ + e₁ √a`: the pieces for `e₀` and the square-root part. -/
inductive SumW where
  | mk (m : ℕ) (w0 : ADW (m + 1)) (w1 : SqW)

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **`frontSqrtSum` with the antiderivative.** -/
def frontSqrtSumW (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    Option (Option SumW) :=
  match (ssE a e0 e1).nodesOf.length with
  | 0 => none
  | m + 1 =>
    match comp Fc (ssE a e0 e1).nodesOf (ksOf Fc (ssE a e0 e1)) (m + 1) e0 with
    | none => none
    | some f0 =>
      match elMW Fc (ksOf Fc (ssE a e0 e1)) (lvOf Fc (ssE a e0 e1)) (m + 1) f0 N,
        frontSqrtEW Fc (ssE a e0 e1) a e1 ps bound rs with
      | some o0, some o1 => some (match o0, o1 with
        | some w0, some w1 => some (.mk m w0 w1)
        | _, _ => none)
      | _, _ => none

/-- **`frontSqrtSumW` answers as `frontSqrtSum`.** -/
theorem frontSqrtSumW_isSome (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    (frontSqrtSumW Fc a e0 e1 ps bound rs N).map Option.isSome =
      frontSqrtSum Fc a e0 e1 ps bound rs N := by
  unfold frontSqrtSumW frontSqrtSum
  rcases (ssE a e0 e1).nodesOf.length with _ | m
  · rfl
  dsimp only
  rcases comp Fc (ssE a e0 e1).nodesOf (ksOf Fc (ssE a e0 e1)) (m + 1) e0 with _ | f0
  · rfl
  dsimp only
  rw [← elMW_isSome, ← frontSqrtEW_isSome]
  rcases elMW Fc (ksOf Fc (ssE a e0 e1)) (lvOf Fc (ssE a e0 e1)) (m + 1) f0 N with _ | o0
  · rfl
  rcases frontSqrtEW Fc (ssE a e0 e1) a e1 ps bound rs with _ | o1
  · rfl
  cases o0 <;> cases o1 <;> rfl

/-- **The antiderivative as strings**: the tower, the pieces for `e₀`, the square-root part. -/
def frontSqrtSumShow (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    List String :=
  match frontSqrtSumW Fc a e0 e1 ps bound rs N with
  | none => ["no answer at this bound"]
  | some none => ["not elementary"]
  | some (some (.mk m w0 w1)) => "elementary; tower:" :: nodesRender (ssE a e0 e1) ++
      "antiderivative of e0 = sum of the pieces:" ::
        ADW.render Fc (ksOf Fc (ssE a e0 e1)) N (m + 1) w0 ++
      ["antiderivative of e1 sqrt(a): " ++ w1.render Fc (ksOf Fc (ssE a e0 e1)) a.toStr]

universe u

variable {Fc}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every antiderivative returned by `frontSqrtSumW` is valid**: the pieces of `e₀` are a valid
`elMW` witness for its code, and the square-root part is valid. -/
theorem frontSqrtSumW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (m : ℕ) (w0 : ADW (m + 1))
    (w1 : SqW) (hb : frontSqrtSumW Fc a e0 e1 ps bound rs N = some (some (.mk m w0 w1)))
    (T : MTower Fc (ksOf Fc (ssE a e0 e1)) Cc L) (hn : T.n = (ssE a e0 e1).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (ssE a e0 e1).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (ssE a e0 e1).nodesOf.length) {θ}) :
    (∃ f0 : LC (m + 1), T.ev (m + 1) f0 = evE Fc T (ssE a e0 e1).nodesOf e0 ∧
      T.ValidW (m + 1) f0 w0) ∧
    SqW.Valid T θ (evE Fc T (ssE a e0 e1).nodesOf e1 * θ) w1 := by
  classical
  have hn0 := hn
  have hgen0 := hgen
  unfold frontSqrtSumW at hb
  obtain ⟨m', hlen⟩ : ∃ m', (ssE a e0 e1).nodesOf.length = m' + 1 := by
    rcases h0 : (ssE a e0 e1).nodesOf.length with _ | m'
    · rw [h0] at hb; cases hb
    · exact ⟨m', rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  rcases hf0 : comp Fc (ssE a e0 e1).nodesOf (ksOf Fc (ssE a e0 e1)) (m' + 1) e0 with _ | f0
  · rw [hf0] at hb; cases hb
  rw [hf0] at hb
  dsimp only at hb
  rcases hb0 : elMW Fc (ksOf Fc (ssE a e0 e1)) (lvOf Fc (ssE a e0 e1)) (m' + 1) f0 N with _ | o0
  · rw [hb0] at hb; cases hb
  rcases hb1 : frontSqrtEW Fc (ssE a e0 e1) a e1 ps bound rs with _ | o1
  · rw [hb0, hb1] at hb; cases hb
  rw [hb0, hb1] at hb
  rcases o0 with _ | w0'
  · cases hb
  rcases o1 with _ | w1'
  · cases hb
  simp only [Option.some.injEq, SumW.mk.injEq] at hb
  obtain ⟨rfl, hw0, rfl⟩ := hb
  subst hw0
  have hsq := frontSqrtEW_isSome Fc (ssE a e0 e1) a e1 ps bound rs
  rw [hb1] at hsq
  obtain ⟨m'', qa, q1, hlen', hsh, hc, hqa, hq1, hd, hz, hsqc, hdegpos⟩ :=
    frontSqrtE_data (ssE a e0 e1) a e1 ps bound rs true hsq.symm
  obtain rfl : m'' = m' := by omega
  have MS := T.mspecs hmon hdeg (lvOf Fc (ssE a e0 e1)) (m'' + 1) (by omega) hc
  have hTr : T.Tr (m'' + 1) := MS.hyp.tr
  have hTm : T.Tr m'' := hTr.of_succ
  have hva := comp_spec Fc T (ssE a e0 e1).nodesOf (m'' + 1) hTr a qa hqa
  have hθA : θ ^ 2 = T.evP m'' (qa.1.map ((MO Fc (ksOf Fc (ssE a e0 e1)) m'').mul
      ((MO Fc (ksOf Fc (ssE a e0 e1)) m'').inv (qa.2.getD 0 (MO Fc (ksOf Fc (ssE a e0 e1)) m'').zero)))) := by
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
    frontSqrtEW_valid hmon hdeg (ssE a e0 e1) a e1 ps bound rs w1' hb1 T hn0 θ hθ hgen0⟩

end Curves.MT.Front
