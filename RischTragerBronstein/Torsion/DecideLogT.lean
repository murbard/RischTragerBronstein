import RischTragerBronstein.Torsion.ResTors

/-!
# The logarithmic decision with non-torsion certificates

`decideLogT redAt P ws tws`: `decideLog P ws` when it answers; otherwise `some false` if one of the
torsion witnesses `tws` passes `torsOK`: `s` times a component `j₀` of the residue divisor of
`f dx` equals `Γ − c ∞ₓ` up to principal divisors of `x − a` (residues uniform along the
certified branches at the special points outside `Γ` and above infinity), and two good primes
(reductions `redAt p`) with a failed principality test prove that it is not torsion.

**`decideLogT_spec`**: `decideLogT … = some b ⇒ (HasElementaryIntegral f ↔ b = true)`.
-/

open Polynomial IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries GTors

section Defs

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- A non-torsion witness for a component of the residue divisor. -/
structure TorsWit (F : Type*) [Field F] [CharZero F] [EllQuad.QCoords F] where
  T : GlobalCert F
  eL : List ℤ
  s : ℕ
  j₀ : Fin (dim F)
  p : ℕ
  q : ℕ
  Pp : PrimeCert p
  Pq : PrimeCert q
  Pb : ℕ
  Lm : List (List F)

/-- The check at a prime. -/
def primeOK (redAt : (p : ℕ) → Option (RedFns p F)) (T : GlobalCert F) (p : ℕ)
    (Pc : PrimeCert p) : Bool :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    match redAt p with
    | some R => primeCheck R T Pc
    | none => false
  else false

/-- **The non-torsion check.** -/
def torsOK (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F) (tw : TorsWit F) : Bool :=
  P.valid && tw.T.globalCheck && torsResCheck P tw.T tw.eL tw.s tw.j₀ && decide (tw.p ≠ tw.q) &&
  primeOK redAt tw.T tw.p tw.Pp && primeOK redAt tw.T tw.q tw.Pq &&
  nonPrincCheck tw.T.n ((tw.Pp.mp * tw.Pq.mp) * tw.T.cdeg) tw.Pb tw.T.I.δL tw.T.I.Bc tw.T.I.Dc
    tw.T.αL tw.T.cΓ (tw.T.ΓL.map (·.map ((tw.Pp.mp * tw.Pq.mp) * ·))) tw.Lm

/-- **The decision with logarithmic part and non-torsion certificates.** -/
def decideLogT (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F) (ws : List (LogWit F))
    (tws : List (TorsWit F)) : Option Bool :=
  match P.decideLog ws with
  | some b => some b
  | none => if tws.any (torsOK redAt P) then some false else none

lemma primeOK_spec {redAt : (p : ℕ) → Option (RedFns p F)} {T : GlobalCert F} {p : ℕ}
    {Pc : PrimeCert p} (h : primeOK redAt T p Pc = true) :
    ∃ hp : p.Prime, ∃ R : RedFns p F, redAt p = some R ∧
      (haveI : Fact p.Prime := ⟨hp⟩; primeCheck R T Pc = true) := by
  unfold primeOK at h
  split_ifs at h with hp
  refine ⟨hp, ?_⟩
  revert h
  cases hr : redAt p with
  | none => intro h; exact absurd h (by simp)
  | some R => intro h; exact ⟨R, rfl, h⟩

end Defs

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **A passing non-torsion witness proves non-elementarity.** -/
theorem not_elementary_of_torsOK (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (tw : TorsWit F) (h : torsOK redAt P tw = true) :
    ¬ HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  classical
  simp only [torsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hval, hT⟩, hTR⟩, hpq⟩, hPp⟩, hPq⟩, htest⟩ := h
  have hV := P.valid_spec hval
  obtain ⟨hpp, Rp, hRp, hPp'⟩ := primeOK_spec hPp
  obtain ⟨hqp, Rq, hRq, hPq'⟩ := primeOK_spec hPq
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
  exact SL.false_of_torsRes hCc hxc P (φ.comp ι) hSF' hV tw.T hT tw.eL tw.s tw.j₀ hTR hpq Rp φp hφp
    tw.Pp hPp' Rq φq hφq tw.Pq hPq' tw.Pb tw.Lm htest v hv sI dc uu hu hu0 heq'

/-- **Correctness of the decision with non-torsion certificates.** -/
theorem decideLogT_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (ws : List (LogWit F)) (tws : List (TorsWit F)) (b : Bool)
    (h : decideLogT redAt P ws tws = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  unfold decideLogT at h
  split at h
  · rename_i b' hb'
    obtain rfl := Option.some.inj h
    exact decideLog_spec hC S hx hgen P ι hSF ws b' hb'
  · split_ifs at h with hany
    obtain rfl := (Option.some.inj h).symm
    obtain ⟨tw, -, htw⟩ := List.any_eq_true.mp hany
    simp only [Bool.false_eq_true, iff_false]
    exact not_elementary_of_torsOK hC S hx hgen redAt hred P ι hSF tw htw

end Main

end Curves
