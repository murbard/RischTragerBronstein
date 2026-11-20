import RischTragerBronstein.Torsion.AutoPipeline
import RischTragerBronstein.Torsion.MobP

/-!
# The automatic decision after a Möbius transformation

Residues above infinity need not be uniform; after `t = 1/(x − e)` (`e` not special) the old
places above infinity lie above `t = 0`, where the place certificates handle them, and the new
infinity (above `x = e`) carries no residue. `mobData` computes the transformed curve and integrand
(the smallest weights), `decideAutoPM` runs the automatic pipeline on them, and
**`decideAutoPM_spec`**: every answer is correct for the original integrand
(`decideLogTP_mob_spec`).
-/

namespace Curves

open CPoly Sup EllQuad.QCoords

section Mob

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- The transformed curve and integrand at `e` (weights searched up to `bound`). -/
def mobData (P : CurveProb F) (e : F) (bound : ℕ) :
    Option (BPoly F × BPoly F × CPoly F × ℕ × ℕ) :=
  ((List.range (bound + 1)).find? fun k ↦ invOKb k (k * P.n) (shiftB P.Fc e)).bind fun k0 ↦
  ((List.range (bound + 1)).find? fun d ↦
    invOKb k0 d (shiftB P.A e) && decide (P.D.length - 1 ≤ d + 2)).map fun DA ↦
  (invB (shiftB P.Fc e) k0 (k0 * P.n), mobA P.A e k0 DA,
    mul (reflectC (P.D.length - 1) (compC P.D (shiftC e 1))) (xPowC (DA + 2 - (P.D.length - 1))),
    k0, DA)

/-- **The automatic decision through a Möbius transformation at `e`.** -/
def decideAutoPM (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (e : F) (bound kP kI ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) (ws : List (LogWit F)) :
    Option Bool :=
  match mobData P e bound with
  | none => none
  | some (Fc', A', D', k0, DA) =>
    match autoCurveProb rf Fc' P.n kP A' D' ex, autoGlobal rf Fc' P.n kI ex fuel with
    | some P', some T => if mobCheck P P' e k0 DA then decideAutoP rf redAt P' T ws L tp B pqs else none
    | _, _ => none

end Mob

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

open IntermediateField Differential Polynomial in
/-- **Soundness of the automatic decision through a Möbius transformation.** -/
theorem decideAutoPM_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι)) (e : F)
    (bound kP kI ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) (ws : List (LogWit F)) (b : Bool)
    (h : decideAutoPM rf redAt P e bound kP kI ex fuel L tp B pqs ws = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  unfold decideAutoPM at h
  split at h
  · exact absurd h (by simp)
  · rename_i Fc' A' D' k0 DA _
    split at h
    · rename_i P' T _ _
      split_ifs at h with hmob
      exact decideLogTP_mob_spec hC S hx hgen redAt hred P P' ι hSF e k0 DA hmob ws [] _ b h
    · exact absurd h (by simp)

end Main

end Curves
