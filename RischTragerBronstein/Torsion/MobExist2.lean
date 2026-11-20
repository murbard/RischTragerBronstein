import RischTragerBronstein.Torsion.MobExist1
import RischTragerBronstein.Torsion.CertExistsTors

/-!
# Möbius transformations in the certificate search (2): certificates of the transformed problem

* `CertExistsN`: certificates without the Möbius option; `certExists_of_N`;
* `certExistsN_of_tors`: `certExists_of_tors` producing such certificates;
* **`certExists_of_mobN`**: certificates without Möbius option for the Möbius transform of `P0`
  (over `ℚ`) give certificates for `P0` (through the Möbius option of `CertQ`).
-/

open Polynomial

namespace Curves

open CPoly Sup NFC EllQuad.QCoords IntermediateField

/-- Certificates without the Möbius option. -/
def CertExistsN (P0 : CurveProb ℚ) : Prop :=
  ∃ (M : CPoly ℚ) (hM : Kron.irredQ M = true),
    haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    ∃ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)) (ws : List (LogWit (NF M)))
      (twps : List (TorsWitP (NF M))),
      (decideLogTP (redAtM M) (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf) ws [] twps).isSome

lemma certExists_of_N {P0 : CurveProb ℚ} (h : CertExistsN P0) : CertExists P0 := by
  obtain ⟨M, hM, pts, inf, ws, twps, h⟩ := h
  exact ⟨⟨⟨M, hM⟩, (pts, inf, ws, twps, none)⟩, h⟩

section Exists

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

/-- **Certificates without Möbius option exist when all residue coordinates are torsion**: given valid data over a
number field (the residue case of `certExists_or_residues`) and torsion data for every
coordinate on some model of the curve. -/
theorem certExistsN_of_tors (P0 : CurveProb ℚ) (M : CPoly ℚ) (hM : Kron.irredQ M = true)
    (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M))
    (hvalid : (haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).valid) = true)
    (S : CurveData C L) (ψ₀ : (haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      NF M →+* C))
    (hSF : haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      S.F = (toB (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).Fc).map (mapRingHom ψ₀))
    (hT : haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ j : Fin (dim (NF M)), ∃ m, 0 < m ∧ ∃ Λ : K →ₗ[ℚ] ℚ,
      (∀ r : NF M, Λ (algebraMap C K (ψ₀ r)) = coord j r) ∧ ∃ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
        S.TorsOrdStd (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf) ψ₀ m w Λ) :
    CertExistsN P0 := by
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set P := P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf with hP
  have hV := P.valid_spec hvalid
  obtain ⟨ws, B, hws⟩ := S.witCheck_of_tors P ψ₀ hSF hV hT
  obtain ⟨P', hFc, hn, hk, hA, hD, -, hpts, hB, hBi, hinfN, hv'⟩ := raise_valid P hvalid B
  have hP' : P' = P0.baseChange (algebraMap ℚ (NF M)) P0.k P'.pts P'.inf := by
    obtain ⟨Fc', n', k', A', D', pts', inf'⟩ := P'
    simp only at hFc hn hk hA hD
    subst hFc hn hk hA hD
    rfl
  have hwc := hws P' hFc hn hk hA hD hpts hinfN (P'.valid_spec hv') hB hBi
  refine ⟨M, hM, P'.pts, P'.inf, ws, [], ?_⟩
  rw [← hP']
  exact decideLogTP_isSome _ _ _ _ _ (decideLog_isSome P' ws hv' hwc)

end Exists

/-- **Certificates through the Möbius option.** -/
theorem certExists_of_mobN (P0 : CurveProb ℚ) (e : ℚ) (k₀ DA k' : ℕ)
    (hF : invOKb k₀ (k₀ * P0.n) (shiftB P0.Fc e) = true)
    (hA : invOKb k₀ DA (shiftB P0.A e) = true)
    (hl : (compC P0.D (shiftC e 1)).length ≤ P0.D.length - 1 + 1) (hDA : P0.D.length - 1 ≤ DA + 2)
    (h : CertExistsN (P0.mobT e k₀ DA k' [] ⟨1, [], 0⟩)) : CertExists P0 := by
  obtain ⟨M, hM, pts, inf, ws, twps, h⟩ := h
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set φ := algebraMap ℚ (NF M)
  refine ⟨⟨⟨M, hM⟩, (pts, inf, ws, twps, some (φ e, k₀, DA, k'))⟩, ?_⟩
  dsimp only [CertQ.run]
  rw [if_pos (mobCheck_baseChange φ P0 e k₀ DA k' [] ⟨1, [], 0⟩ pts inf hF hA hl hDA),
    baseChange_mobT φ P0 e k₀ DA k' [] ⟨1, [], 0⟩ pts inf [] ⟨1, [], 0⟩]
  exact h

end Curves
