import RischTragerBronstein.Mixed.MTRde0
import RischTragerBronstein.Mixed.MTRdeEF

/-!
# Mixed towers over a curve: the solvers are correct at every certified level

`mspecs`: for a realization of height `n` and a certified level `k ≤ n`, the structure-theorem
hypotheses `MixHyp k`, the parametric Risch equation `prdeC k` (for every `f = h′ + ∑ cⱼ wⱼ′/wⱼ`
with constant `cⱼ`) and parametric limited integration `paramLimC k` are correct. Simultaneous
induction on `k`; the base is the curve (`prde0C_spec`, `paramLim0C_spec`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)

/-- The specifications at level `k`. -/
structure MSpecs (lv : (m : ℕ) → LC m) (k : ℕ) : Prop where
  hyp : T.MixHyp k
  rde : ∀ fr : FRep (LC k), FRepOK (T.MP k hyp.tr) fr →
    RdeSpecK (algebraMap Cc (T.F k)) (T.MP k hyp.tr) ((T.MP k hyp.tr).sem (fCode (MO Fc ks k) fr))
      (prdeC Fc ks lv k fr)
  lim : LimSpec (algebraMap Cc (T.F k)) (T.MP k hyp.tr) (paramLimC Fc ks lv k)

/-- The Risch equation `y′ + h′ y = ∑ cᵢ wᵢ` from the specification with `f = h′`. -/
lemma rde_deriv_of {k : ℕ} (h : T.Tr k) (lower : FRep (LC k) → List (LC k) →
    List (List ℚ × LC k))
    (hl : ∀ fr : FRep (LC k), FRepOK (T.MP k h) fr →
      RdeSpecK (algebraMap Cc (T.F k)) (T.MP k h) ((T.MP k h).sem (fCode (MO Fc ks k) fr))
        (lower fr)) (f : LC k) :
    RdeSpecK (algebraMap Cc (T.F k)) (T.MP k h) ((T.MP k h).sem f)′ (lower ⟨f, []⟩) := by
  have := hl ⟨f, []⟩ (fun cw hcw ↦ by simp at hcw)
  rwa [sem_fCode, logSumV, List.map_nil, List.sum_nil, add_zero] at this

/-- **All the specifications hold at every certified level below the height.** -/
theorem mspecs (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (lv : (m : ℕ) → LC m) : ∀ k, k ≤ T.n → certC Fc ks lv k = true → T.MSpecs lv k
  | 0, _, _ => ⟨T.mixHyp_zero, fun fr hok ↦ T.prde0C_spec lv hmon hdeg _ fr hok,
      T.paramLim0C_spec lv hmon hdeg _⟩
  | k + 1, hkn, hc => by
    rw [certX_succ, Bool.and_eq_true] at hc
    have IH := mspecs hmon hdeg lv k (by omega) hc.1
    have hM := T.mixHyp_succ lv k IH.hyp (by omega) IH.lim hc.2
    have hrdeD := T.rde_deriv_of IH.hyp.tr (prdeC Fc ks lv k) IH.rde
    rcases hk : ks k with η | a
    · -- a logarithmic level
      obtain ⟨hv, hlv⟩ := T.certLevel_prim hk IH.hyp.tr hc.2
      have hnd := MixHyp.ndX T hM (Nat.lt_succ_self k) hk hM.tr
      refine ⟨hM, fun fr hok ↦ ?_, ?_⟩
      · have e : prdeC Fc ks lv (k + 1) fr = prdePrimC Fc ks k η (lv k) (prdeC Fc ks lv k)
            (paramLimC Fc ks lv k) fr := by
          simp only [prdeC, hk]
        rw [e]
        exact T.prdePrimX_spec k hM hk (lv k) hv hlv (prdeC Fc ks lv k) IH.rde
          (paramLimC Fc ks lv k) IH.lim fr hok
      · have e : paramLimC Fc ks lv (k + 1) = primLimStepC Fc ks k η (paramLimC Fc ks lv k) := by
          funext W; simp only [paramLimC, hk]
        rw [e]
        exact T.primLimStep_spec k hM.tr hk hnd _ IH.lim
    · -- an exponential level
      have hc2 := certLevel_exp hk hc.2
      have hhom := MixHyp.homX T hM (Nat.lt_succ_self k) hk hM.tr
      refine ⟨hM, fun fr hok ↦ ?_, ?_⟩
      · have e : prdeC Fc ks lv (k + 1) fr = prdeExpC Fc ks k a (prdeC Fc ks lv k) fr := by
          simp only [prdeC, hk]
        rw [e]
        exact T.prdeExpX_spec k hM hk hc2 (prdeC Fc ks lv k) IH.rde fr hok
      · have e : paramLimC Fc ks lv (k + 1) =
            expLimStepC Fc ks k a (paramLimC Fc ks lv k) (fun h ↦ prdeC Fc ks lv k ⟨h, []⟩) := by
          funext W; simp only [paramLimC, hk]
        rw [e]
        exact T.expLimStepX_spec k hM.tr hk hhom _ IH.lim _ hrdeD

end MTower

end Curves.MT
