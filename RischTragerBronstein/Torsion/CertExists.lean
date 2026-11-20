import RischTragerBronstein.Torsion.DecideEnum
import RischTragerBronstein.Torsion.ValidExist
import RischTragerBronstein.Torsion.SepInf

/-!
# Certificates exist unless the integrand has a logarithmic part

**`certExists_or_residues`**: for an integration problem over `ℚ` with valid shape, separable at the
finite fibres and at infinity (both automatic from `shapeOK`: `hsep_of_shapeOK`, `hsepI_of_shapeOK`), either valid certificates exist (`CertExists`, so the total decision
`decideTotal` answers) or there are valid branch data for which the linear system of the
algebraic part is solvable and the residues do not all vanish. Only then are logarithmic or
non-torsion witnesses needed.

**`decideTotal_complete_noRes`**: the total decision answers for every large bound unless the
integrand has a logarithmic part.
-/

open Polynomial

namespace Curves

open CPoly Sup NFC

/-- **Separability at the finite fibres from the shape**: `disc · D ≠ 0` gives a Bézout identity
`Res(F, F_Y) = p F + q F_Y`. -/
theorem hsep_of_shapeOK (P0 : CurveProb ℚ) (hS : P0.shapeOK = true) :
    ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧
      Polynomial.C R = A * toB P0.Fc + B * derivative (toB P0.Fc) := by
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, h7⟩, -⟩, h9⟩, -⟩, -⟩ := hS'
  obtain ⟨hmon, hn, hk⟩ := shape_monic P0.Fc P0.n P0.k h2 h3 h7
  set G := toB P0.Fc
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant G (derivative G)
    (m := P0.n) (n := P0.n - 1) (by rw [hn])
    (by have := natDegree_derivative_le G; rw [hn] at this; exact this) (Or.inl (by omega))
  have hR : G.resultant (derivative G) P0.n (P0.n - 1) ≠ 0 := by
    rw [← toPoly_discRC P0.Fc P0.n P0.k hmon hn hk]
    intro h0
    have hR0 : toPoly P0.R0 = 0 := by
      simp only [CurveProb.R0, toPoly_trim, CPoly.toPoly_mul, h0, zero_mul]
    rw [← trim_eq_nil_iff] at hR0
    rw [hR0] at h9
    simp at h9
  exact ⟨_, p, q, hR, by rw [← hpq]; ring⟩

/-- A certificate without witnesses. -/
def CertQ.mk0 (M : CPoly ℚ) (hM : Kron.irredQ M = true) (pts : List (NF M × BranchCert (NF M)))
    (inf : BranchCert (NF M)) : CertQ :=
  ⟨⟨M, hM⟩, (pts, inf, [], [], none)⟩

lemma CertQ.run_mk0 (P0 : CurveProb ℚ) (M : CPoly ℚ) (hM : Kron.irredQ M = true)
    (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)) :
    haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    (CertQ.mk0 M hM pts inf).run P0 =
      (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).decideLog [] := by
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  dsimp only [CertQ.run, CertQ.mk0]
  simp only [decideLogTP, decideLogT]
  generalize (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).decideLog [] = r
  cases r <;> simp

/-- **Certificates exist, or the residues are needed.** -/
theorem certExists_or_residues (P0 : CurveProb ℚ) (hS : P0.shapeOK = true) :
    CertExists P0 ∨ ∃ M : CPoly ℚ, ∃ hM : Kron.irredQ M = true,
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∃ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)),
        (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).valid = true ∧
        ∃ cs, linSolve (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).cols
            (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).rhs = some cs ∧
          (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).allRes.all (· = 0) = false := by
  obtain ⟨M, hM, pts, inf, hvalid⟩ := exists_valid P0 hS (hsep_of_shapeOK P0 hS)
    (hsepI_of_shapeOK P0 hS)
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  have hrun := CertQ.run_mk0 P0 M hM pts inf
  cases hls : linSolve (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).cols
      (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).rhs with
  | none =>
    left
    refine ⟨CertQ.mk0 M hM pts inf, ?_⟩
    rw [hrun]
    simp [CurveProb.decideLog, hvalid, hls]
  | some cs =>
    cases hres : (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).allRes.all (· = 0) with
    | true =>
      left
      refine ⟨CertQ.mk0 M hM pts inf, ?_⟩
      rw [hrun]
      simp only [CurveProb.decideLog, hvalid, hls, if_true]
      rw [if_pos hres]
      rfl
    | false =>
      exact Or.inr ⟨M, hM, pts, inf, hvalid, cs, hls, hres⟩

/-- **The total decision answers unless the integrand has a logarithmic part.** -/
theorem decideTotal_complete_or_residues (Fc A : BPoly ℚ) (D : CPoly ℚ)
    (hS : (curveProbQ Fc A D).shapeOK = true) :
    (∃ N₀, ∀ N, N₀ ≤ N → (decideTotal Fc A D N).isSome) ∨
      ∃ M : CPoly ℚ, ∃ hM : Kron.irredQ M = true,
        haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
        ∃ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)),
          ((curveProbQ Fc A D).baseChange (algebraMap ℚ (NF M)) (curveProbQ Fc A D).k pts inf).valid
            = true ∧
          ∃ cs, linSolve ((curveProbQ Fc A D).baseChange (algebraMap ℚ (NF M))
              (curveProbQ Fc A D).k pts inf).cols
              ((curveProbQ Fc A D).baseChange (algebraMap ℚ (NF M)) (curveProbQ Fc A D).k pts inf).rhs
                = some cs ∧
            ((curveProbQ Fc A D).baseChange (algebraMap ℚ (NF M)) (curveProbQ Fc A D).k pts
              inf).allRes.all (· = 0) = false := by
  rcases certExists_or_residues (curveProbQ Fc A D) hS with h | h
  · exact Or.inl (decideTotal_complete Fc A D h)
  · exact Or.inr h

end Curves
