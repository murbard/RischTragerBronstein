import RischTragerBronstein.Torsion.DecideLogP

/-!
# Base change of the coefficient field

The special points of an integrand need not split over its coefficient field `F` (residues at
points over a number field). `CurveProb.baseChange φ P k pts inf` is the same integrand over a
larger computable field `F'` (for example a splitting field built by `NFAdjoin`), with branch
certificates over `F'`. **`decideLogTP_baseChange_spec`**: an answer of `decideLogTP` over `F'`
decides the original integrand.
-/

open Polynomial IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential GTors

section BC

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']

/-- The integrand of `P` with coefficients mapped along `φ`, with certificates over `F'`. -/
def CurveProb.baseChange (φ : F →+* F') (P : CurveProb F) (k : ℕ) (pts : List (F' × BranchCert F'))
    (inf : BranchCert F') : CurveProb F' :=
  ⟨P.Fc.map (·.map φ), P.n, k, P.A.map (·.map φ), P.D.map φ, pts, inf⟩

lemma toB_mapL (φ : F →+* F') (W : BPoly F) :
    toB (W.map (·.map φ)) = (toB W).map (mapRingHom φ) := by
  induction W with
  | nil => simp
  | cons c W ih =>
    rw [List.map_cons, toB_cons, toB_cons, ih, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, Sup.toPoly_mapHom]

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

lemma CurveData.fE_baseChange (S : CurveData C L) (φ : F →+* F') (P : CurveProb F) (k : ℕ)
    (pts : List (F' × BranchCert F')) (inf : BranchCert F') (ψ : F' →+* C) :
    S.fE (P.baseChange φ k pts inf) ψ = S.fE P (ψ.comp φ) := by
  apply Subtype.ext
  simp only [CurveData.fE, CurveProb.baseChange, toB_mapL, Sup.toPoly_mapHom, Polynomial.map_map,
    mapRingHom_comp]

end BC

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F'] [CharZero F']
  [EllQuad.QCoords F']

/-- **Deciding an integrand over a larger coefficient field.** -/
theorem decideLogTP_baseChange_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F'))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F'), redAt p = some R →
      ∃ φp : F' →+* ℚ_[p], RedValid p R φp)
    (φ : F →+* F') (P : CurveProb F) (k : ℕ) (pts : List (F' × BranchCert F'))
    (inf : BranchCert F') (ι : F' →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom (ι.comp φ)))
    (ws : List (LogWit F')) (tws : List (TorsWit F')) (twps : List (TorsWitP F')) (b : Bool)
    (h : decideLogTP redAt (P.baseChange φ k pts inf) ws tws twps = some b) :
    HasElementaryIntegral ((S.fE P (ι.comp φ) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  have hSF' : S.F = (toB (P.baseChange φ k pts inf).Fc).map (mapRingHom ι) := by
    rw [hSF, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp]
  rw [← S.fE_baseChange φ P k pts inf ι]
  exact decideLogTP_spec hC S hx hgen redAt hred _ ι hSF' ws tws twps b h

end Main

end Curves
