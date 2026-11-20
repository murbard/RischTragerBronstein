import RischTragerBronstein.Torsion.RamRes
import RischTragerBronstein.Torsion.DecideLogT

/-!
# The logarithmic decision with non-torsion certificates at places

`decideLogTP redAt P ws tws twps`: `decideLogT redAt P ws tws` when it answers; otherwise
`some false` if one of the witnesses `twps` for divisors at (possibly ramified) places passes
`torsOKP`.

**`decideLogTP_spec`**: `decideLogTP … = some b ⇒ (HasElementaryIntegral f ↔ b = true)`.
-/

open Polynomial IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries GTors

section Defs

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- A non-torsion witness for a component of the residue divisor, supported at places. -/
structure TorsWitP (F : Type*) [Field F] [CharZero F] [EllQuad.QCoords F] where
  T : GlobalCert F
  Pc : PlaceCert F
  eL : List ℤ
  s : ℕ
  j₀ : Fin (dim F)
  p : ℕ
  q : ℕ
  Pp : PrimeCert p
  Pq : PrimeCert q
  Qp : PlaceCert.PrimeData p
  Qq : PlaceCert.PrimeData q
  Pb : ℕ
  Lm : List (List F)

/-- The checks at a prime. -/
def primeOKP (redAt : (p : ℕ) → Option (RedFns p F)) (T : GlobalCert F) (Pc : PlaceCert F)
    (p : ℕ) (Pp : PrimeCert p) (Qp : PlaceCert.PrimeData p) : Bool :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    match redAt p with
    | some R => primeCheck R T Pp && Pc.primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp
    | none => false
  else false

/-- **The non-torsion check at places.** -/
def torsOKP (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F) (tw : TorsWitP F) : Bool :=
  P.valid && tw.T.globalCheck && tw.Pc.check tw.T.Fc tw.T.n &&
  torsResCheckP P tw.T tw.Pc tw.eL tw.s tw.j₀ && decide (tw.p ≠ tw.q) &&
  primeOKP redAt tw.T tw.Pc tw.p tw.Pp tw.Qp && primeOKP redAt tw.T tw.Pc tw.q tw.Pq tw.Qq &&
  (nonPrincOK tw.T.n ((tw.Qp.mp * tw.Qq.mp) * tw.Pc.cΓ) tw.Pb tw.T.I.δL tw.T.I.Bc tw.T.I.Dc
    tw.Pc.αs (tw.Pc.fcerts tw.T.n) (tw.Pc.bL tw.T.n (tw.Qp.mp * tw.Qq.mp)) tw.Lm ||
   nonPrincOK tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp * tw.Pc.cΓ) tw.Pb tw.T.I.δL tw.T.I.Bc
    tw.T.I.Dc tw.Pc.αs (tw.Pc.fcerts tw.T.n) (tw.Pc.bL tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp))
    tw.Lm)

/-- **The decision with non-torsion certificates, including divisors at places.** -/
def decideLogTP (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F) (ws : List (LogWit F))
    (tws : List (TorsWit F)) (twps : List (TorsWitP F)) : Option Bool :=
  match decideLogT redAt P ws tws with
  | some b => some b
  | none => if twps.any (torsOKP redAt P) then some false else none

lemma primeOKP_spec {redAt : (p : ℕ) → Option (RedFns p F)} {T : GlobalCert F} {Pc : PlaceCert F}
    {p : ℕ} {Pp : PrimeCert p} {Qp : PlaceCert.PrimeData p}
    (h : primeOKP redAt T Pc p Pp Qp = true) :
    ∃ hp : p.Prime, ∃ R : RedFns p F, redAt p = some R ∧
      (haveI : Fact p.Prime := ⟨hp⟩; primeCheck R T Pp = true ∧
        Pc.primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true) := by
  unfold primeOKP at h
  split_ifs at h with hp
  refine ⟨hp, ?_⟩
  revert h
  cases hr : redAt p with
  | none => intro h; exact absurd h (by simp)
  | some R =>
    intro h
    simp only [Bool.and_eq_true] at h
    exact ⟨R, rfl, h⟩

end Defs

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **A passing non-torsion witness at places proves non-elementarity.** -/
theorem not_elementary_of_torsOKP (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (tw : TorsWitP F) (h : torsOKP redAt P tw = true) :
    ¬ HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  classical
  simp only [torsOKP, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hval, hT⟩, hPc⟩, hTR⟩, hpq⟩, hPp⟩, hPq⟩, htest⟩ := h
  have hV := P.valid_spec hval
  obtain ⟨hpp, Rp, hRp, hPp', hQp'⟩ := primeOKP_spec hPp
  obtain ⟨hqp, Rq, hRq, hPq', hQq'⟩ := primeOKP_spec hPq
  haveI : Fact tw.p.Prime := ⟨hpp⟩
  haveI : Fact tw.q.Prime := ⟨hqp⟩
  obtain ⟨φp, hφp⟩ := hred tw.p Rp hRp
  obtain ⟨φq, hφq⟩ := hred tw.q Rq hRq
  intro hel
  refine curve_lift hC S hx hgen _ hel ?_
  intro Cc L _ _ _ _ _ _ _ _ φ jE SL hCc hxc hconst hxL hyL hFL hjd hjC hjE v hv ιI sI d w
    hd hw heq
  have hSF' : SL.F = (toB P.Fc).map (mapRingHom (φ.comp ι)) := by
    rw [hFL, hSF, Polynomial.map_map, ← mapRingHom_comp]
  have hjf : jE (S.fE P ι : E) = (SL.fE P (φ.comp ι) : L) := by
    simp only [CurveData.fE, map_div₀]
    rw [S.jE_evXY SL φ jE hxL hyL hjC, S.jE_aeval SL φ jE hxL hjC, Polynomial.map_map,
      Polynomial.map_map, ← mapRingHom_comp]
  rw [hjf] at heq
  obtain ⟨dc, uu, hu, hu0, heq'⟩ := SL.liouville_C hconst _ v sI d w hd hw heq
  exact SL.false_of_torsResP hCc hxc P (φ.comp ι) hSF' hV tw.T hT tw.Pc hPc tw.eL tw.s tw.j₀ hTR
    hpq Rp φp hφp tw.Pp hPp' tw.Qp hQp' Rq φq hφq tw.Pq hPq' tw.Qq hQq' tw.Pb tw.Lm htest v hv sI
    dc uu hu hu0 heq'

/-- **Correctness of the decision with non-torsion certificates at places.** -/
theorem decideLogTP_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (ws : List (LogWit F)) (tws : List (TorsWit F)) (twps : List (TorsWitP F)) (b : Bool)
    (h : decideLogTP redAt P ws tws twps = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  unfold decideLogTP at h
  split at h
  · rename_i b' hb'
    obtain rfl := Option.some.inj h
    exact decideLogT_spec hC S hx hgen redAt hred P ι hSF ws tws b' hb'
  · split_ifs at h with hany
    obtain rfl := (Option.some.inj h).symm
    obtain ⟨tw, -, htw⟩ := List.any_eq_true.mp hany
    simp only [Bool.false_eq_true, iff_false]
    exact not_elementary_of_torsOKP hC S hx hgen redAt hred P ι hSF tw htw

end Main

end Curves
