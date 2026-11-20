import RischTragerBronstein.Mixed.MTBaseLine
import RischTragerBronstein.Torsion.CurveWitMob

/-!
# The base part explicitly, on any curve

At level `0`, `elMW` keeps the remaining integrand `c` on the curve; `baseCurveW Fc c N` runs the
total decision with witnesses (`decideTotalW`) on it. It answers exactly as `elM` at level `0`
(`baseCurveW_isSome`), and a direct witness gives the antiderivative explicitly:
`c = v′ + ∑ⱼ cⱼ uⱼ′/uⱼ` with `v = Wsol(cs)/R0` and `uⱼ = Wⱼ(x, y)/Qⱼ(x)` over the number field
`ℚ[γ]/(M)` (`baseCurve_explicit`, for every realization of the curve over any constants of
characteristic zero and every embedding of the number field into them).
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT

/-- **The base part with the curve antiderivative.** -/
def baseCurveW (Fc : BPoly ℚ) (c : LC 0) (N : ℕ) : Option (Option CurveWQ) :=
  decideTotalW Fc ((codeW (cvNorm Fc c)).map trim) (codeQ (cvNorm Fc c)) N

lemma baseCurveW_isSome (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m) (c : LC 0)
    (N : ℕ) : (baseCurveW Fc c N).map Option.isSome = elM Fc ks lv 0 c N :=
  decideTotalW_isSome _ _ _ _

section Valid

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The curve antiderivative of the base part, explicitly.** -/
theorem baseCurve_explicit {Fc : BPoly ℚ} (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E)
    (hx : S.x′ = 1) (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc))) (c : LC 0) (N : ℕ)
    (W : CurveWQ) (h : baseCurveW Fc c N = some (some W)) (hmob : W.mob = none) :
    haveI : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
    ∀ ι : NFC.NF W.M.1 →+* Kc, (cM hC S hx Fc hSF).sem c = (S.fE W.P ι : E) ∧
      W.w.Valid S W.P ι := by
  have : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
  intro ι
  obtain ⟨d, rfl⟩ : ∃ d : GPoly (GFrac ℚ), (d : LC 0) = c := ⟨c, rfl⟩
  set M := cM hC S hx Fc hSF
  set Wc := (codeW (cvNorm Fc d)).map trim with hW
  set Q := codeQ (cvNorm Fc d) with hQ
  have hval : ((S.fE (curveProbQ Fc Wc Q) (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) = M.sem d := by
    change S.evXY _ / aeval S.x _ = M.sem d
    change S.evXY ((toB Wc).map (mapRingHom (algebraMap ℚ Kc))) /
      aeval S.x ((toPoly Q).map (algebraMap ℚ Kc)) = _
    rw [hW, toB_map_trim, ← evRH_eq_evXY, evRH_toB, eval_codeW hC S hx Fc hSF,
      sem_cvNorm hC S hx Fc hSF]
    have hne := aeval_codeQ_ne_zero S (cvNorm Fc d)
    rw [← hQ] at hne ⊢
    exact mul_div_cancel_left₀ _ hne
  have hsrc := decideTotalW_src Fc Wc Q N W h
  obtain ⟨h1, h2⟩ := CurveWQ.valid hC S hx (curveProbQ Fc Wc Q) hSF W hsrc hmob ι
  refine ⟨?_, h2⟩
  rw [← hval, h1]

/-- **The curve antiderivative of the base part from a Möbius certificate**: in the variables
`X = 1/(x − e)`, `Y = y Xᵏ⁰` of the transformed curve `S'`. -/
theorem baseCurve_explicit_mob {Fc : BPoly ℚ} (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E)
    (hx : S.x′ = 1) (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc))) (c : LC 0) (N : ℕ)
    (W : CurveWQ) (h : baseCurveW Fc c N = some (some W)) (e : NFC.NF W.M.1) (k₀ DA k' : ℕ)
    (hmob : W.mob = some (e, k₀, DA, k')) :
    haveI : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
    ∀ ι : NFC.NF W.M.1 →+* Kc, ∃ S' : CurveData Kc E,
      S'.x = 1 / (S.x - algebraMap Kc E (ι e)) ∧ S'.y = S.y * S'.x ^ k₀ ∧
      (cM hC S hx Fc hSF).sem c = (S'.vvE W.P ι W.w.cs : E)′ +
        (if W.w.logs then ∑ j : Fin (EllQuad.QCoords.dim (NFC.NF W.M.1)),
          algebraMap Kc E (CurveData.cj ι W.w.ws j) *
            ((S'.uE ι (CurveProb.witAt W.w.ws j) : E)′ / (S'.uE ι (CurveProb.witAt W.w.ws j) : E))
          else 0) ∧
      (W.w.logs = true → ∀ j, (S'.uE ι (CurveProb.witAt W.w.ws j) : E) ≠ 0) := by
  have : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
  intro ι
  obtain ⟨d, rfl⟩ : ∃ d : GPoly (GFrac ℚ), (d : LC 0) = c := ⟨c, rfl⟩
  set M := cM hC S hx Fc hSF
  set Wc := (codeW (cvNorm Fc d)).map trim with hW
  set Q := codeQ (cvNorm Fc d) with hQ
  have hval : ((S.fE (curveProbQ Fc Wc Q) (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) = M.sem d := by
    change S.evXY _ / aeval S.x _ = M.sem d
    change S.evXY ((toB Wc).map (mapRingHom (algebraMap ℚ Kc))) /
      aeval S.x ((toPoly Q).map (algebraMap ℚ Kc)) = _
    rw [hW, toB_map_trim, ← evRH_eq_evXY, evRH_toB, eval_codeW hC S hx Fc hSF,
      sem_cvNorm hC S hx Fc hSF]
    have hne := aeval_codeQ_ne_zero S (cvNorm Fc d)
    rw [← hQ] at hne ⊢
    exact mul_div_cancel_left₀ _ hne
  have hsrc := decideTotalW_src Fc Wc Q N W h
  obtain ⟨S', h1, h2, h3, h4⟩ := CurveWQ.validMob hC S hx (curveProbQ Fc Wc Q) hSF W hsrc e k₀ DA k'
    hmob ι
  exact ⟨S', h1, h2, by rw [← hval, h3], h4⟩

end Valid

end Curves.MT
