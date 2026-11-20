import RischTragerBronstein.Torsion.TriExample
import RischTragerBronstein.Torsion.AutoPrime

/-!
# The trigonal example with computed prime data

The same integral as `TriExample.not_elementaryZ`, but the certificates at the primes `13` and
`109` (reduced integral bases, base point, non-speciality coefficients, irreducible
specialization, multipliers `m_p`, witnesses) and the failed test over `ℚ(ζ₁₂)` are **computed**
by `autoWitAt` in the kernel; only the global data (curve, integral basis, places) is supplied.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.TriEx

/-- The prime part of `torsOKP`. -/
noncomputable def primePart (tw : TorsWitP QZ) : Bool :=
  primeOKP redZ tw.T tw.Pc tw.p tw.Pp tw.Qp && primeOKP redZ tw.T tw.Pc tw.q tw.Pq tw.Qq &&
    nonPrincOK tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp * tw.Pc.cΓ) tw.Pb tw.T.I.δL tw.T.I.Bc
      tw.T.I.Dc tw.Pc.αs (tw.Pc.fcerts tw.T.n) (tw.Pc.bL tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp))
      tw.Lm

/-- The computed witness. -/
noncomputable def autoZ : Option (TorsWitP QZ) := autoWitAt redZ TZ PcZ [1, 1] 1 ⟨3, by decide +kernel⟩ 3 13 109

set_option maxRecDepth 200000 in
lemma autoZ_ok : autoZ.map primePart = some true := by decide +kernel

lemma autoZ_data {tw : TorsWitP QZ} (h : autoZ = some tw) :
    tw.T = TZ ∧ tw.Pc = PcZ ∧ tw.eL = [1, 1] ∧ tw.s = 1 ∧ tw.j₀ = twZ.j₀ ∧ tw.p = 13 ∧
      tw.q = 109 := by
  unfold autoZ autoWitAt at h
  split_ifs at h with hp hq
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact absurd h (by simp)

lemma torsOKP_autoZ {tw : TorsWitP QZ} (h : autoZ = some tw) : torsOKP redZ probZ tw = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := autoZ_data h
  have hp : primePart tw = true := by
    have := autoZ_ok
    rw [h, Option.map_some] at this
    exact Option.some.inj this
  unfold primePart at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨hp1, hp2⟩, hn⟩ := hp
  unfold torsOKP
  rw [hp1, hp2, hn, Bool.or_true, h1, h2, h3, h4, h5, h6, h7]
  have e1 : TZ.globalCheck = true := okG
  have e2 : PcZ.check TZ.Fc TZ.n = true := okPc
  have e3 : torsResCheckP probZ TZ PcZ [1, 1] 1 twZ.j₀ = true := okR
  rw [okV, e1, e2, e3]
  decide

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **`not_elementaryZ` with computed prime certificates.** -/
theorem not_elementaryZA (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ w : E, w ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probZ.Fc).map (mapRingHom (ιZ (Kc := Kc)))) :
    ¬ HasElementaryIntegral ((S.fE probZ ιZ : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  have hz := autoZ_ok
  obtain ⟨tw, htw, -⟩ := Option.map_eq_some_iff.mp hz
  exact not_elementary_of_torsOKP hC S hx hgen redZ hredZ probZ ιZ hSF tw (torsOKP_autoZ htw)

end Curves.TriEx
