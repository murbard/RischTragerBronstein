import RischTragerBronstein.Mixed.KXForwardMW
import RischTragerBronstein.Mixed.KXMain

/-!
# Non-elementarity in the Mordell–Weil exception, at the decider's level

`kx_not_elementary_mw`: in the exception of `kxDecide` (`√A(0) ∈ Fₘ` via `kxZ`, `deg A = 3`), if
**in every realization** of the tower the group condition holds for some choice of the square roots
(hypothesis `HG`, realization-independent, as produced by a code-level height certificate), then
`∫ B(t) θ / (tᵏ ∏ (t − c_q) Aˡ) dx` is not elementary. The proof lifts a hypothetical elementary
integral to a realization with the needed square roots (`kqm_lift`) and applies `kx_forward_mw`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
theorem kx_not_elementary_mw (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (hdeg3 : degG (MO Fc ks m) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (k : Fin (kxCls Fc ks m g A B kt l cs).length) (z : LC m) (hz : kxZ Fc ks lv m A = some z)
    (HG : ∀ (E : Type u) [Field E] [Differential E] [CharZero E]
      (TE : MTower Fc ks (constants E) E) (_ : TE.n = m + 1) (hTm : TE.Tr m)
      (rtsE : List E) (_ : rtsE.length = (kxGens Fc ks m g A B kt l cs).length)
      (_ : ∀ i (hi : i < rtsE.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
        rtsE[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : E) ∧ rtsE[i]′ = 0)
      (s : E) (_ : s ^ 2 = (kxKap Fc ks m A z : E)) (_ : s′ = 0)
      (θE : E) (_ : θE ^ 2 = TE.evP m A),
      ∃ (rtsK : List (AlgebraicClosure (TE.F m)))
      (hrK : rtsK.length = (kxGens Fc ks m g A B kt l cs).length)
      (hsK : ∀ i (hi : i < rtsK.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
        rtsK[i] ^ 2 = algebraMap (TE.F m) _ ((kxGens Fc ks m g A B kt l cs)[i] : TE.F m))
      (b0K : AlgebraicClosure (TE.F m))
      (hb0K : b0K ^ 2 = algebraMap (TE.F m) _ ((TE.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)))
      (hgrpK : let cK : ℕ → AlgebraicClosure (TE.F m) := (fun i ↦
            algebraMap (TE.F m) _ ((GPoly.toPoly (TE.MP m hTm) A).coeff i))
          let xK : Fin cs.length → AlgebraicClosure (TE.F m) := (fun q ↦
            algebraMap (TE.F m) _ ((TE.MP m hTm).sem (kqC Fc ks m cs q)))
          let βK : Fin cs.length → AlgebraicClosure (TE.F m) := (fun q ↦
            ((kxRep Fc ks m g A B kt l cs q).2 : AlgebraicClosure (TE.F m)) *
              SqrtIndep.prodRoots rtsK (kxRep Fc ks m g A B kt l cs q).1 *
              algebraMap (TE.F m) _ ((TE.MP m hTm).sem (kxD Fc ks m g cs q) *
                (TE.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
                (GPoly.toPoly (TE.MP m hTm) B).eval ((TE.MP m hTm).sem (kqC Fc ks m cs q))))
          ∀ (hns : ∀ q, (Differential.SuperData.WG (cK 3) (cK 2) (cK 1) (cK 0)).Nonsingular
              (cK 3 * xK q) (cK 3 * βK q))
            (hns0 : (Differential.SuperData.WG (cK 3) (cK 2) (cK 1) (cK 0)).Nonsingular
              (cK 3 * 0) (cK 3 * b0K)),
            ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
              (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k q : ℤ) •
                WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
                (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0),
        True) :
    ¬ HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hok0.1
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  obtain ⟨hz0, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q0 z hq0
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs).2
  have hκs : ∀ κ' ∈ kxKap Fc ks m A z :: kxGens Fc ks m g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
    rcases List.mem_cons.mp h with rfl | h
    · exact hκ0
    · exact hg0 κ' h
  intro hf
  obtain ⟨E, _, _, _, TE, θE, rts0, ι, sI, c, u, v, hTEn, hθE, hrl0, hrts0, hcd, hu, hv, heq⟩ :=
    T.kqm_lift m hn A θ hθ hgen _ hf _ hκs
  obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTmE : TE.Tr m := MSE.hyp.tr.of_succ
  have hdeg3' : (GPoly.toPoly (TE.MP m hTmE) A).natDegree = 3 := by
    rw [← degG_eq (TE.MP m hTmE) A]; exact hdeg3
  obtain ⟨rtsK, hrK, hsK, b0K, hb0K, hgrpK, -⟩ := HG E TE hTEn hTmE rts hrl hrts s hs2 hs' θE hθE
  exact TE.kx_forward_mw hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst hrep k z s hz
    hs2 hs' θE hθE sI c u hcd hu v hv heq rts hrl hrts hTmE hdeg3' rtsK hrK hsK b0K hb0K hgrpK

set_option maxHeartbeats 2000000 in
open Classical in
theorem kx_not_elementary_mwC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (hdeg3 : degG (MO Fc ks m) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (k : Fin (kxCls Fc ks m g A B kt l cs).length) (z : LC m) (hz : kxZ Fc ks lv m A = some z)
    (HGC : ∀ (E : Type u) [Field E] [Differential E] [CharZero E]
      (TE : MTower Fc ks (constants E) E) (_ : TE.n = m + 1) (hTm : TE.Tr m)
      (rtsF : List (TE.F m)) (_ : rtsF.length = (kxGens Fc ks m g A B kt l cs).length)
      (_ : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
        rtsF[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : TE.F m))
      (b₀ : TE.F m) (_ : b₀ ^ 2 = (TE.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)),
      let cC : ℕ → TE.F m := (fun i ↦ (GPoly.toPoly (TE.MP m hTm) A).coeff i)
      let xC : Fin cs.length → TE.F m := (fun q ↦ (TE.MP m hTm).sem (kqC Fc ks m cs q))
      let βC : Fin cs.length → TE.F m := (fun q ↦
        ((kxRep Fc ks m g A B kt l cs q).2 : TE.F m) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
          ((TE.MP m hTm).sem (kxD Fc ks m g cs q) * (TE.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
            (GPoly.toPoly (TE.MP m hTm) B).eval ((TE.MP m hTm).sem (kqC Fc ks m cs q))))
      ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
          (cC 3 * xC q) (cC 3 * βC q))
        (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
          (cC 3 * 0) (cC 3 * b₀)),
        ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
          (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
            (kxCl m g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
            (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0) :
    ¬ HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) := by
  refine T.kx_not_elementary_mw hmon hdeg m hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs hok
    hcst hrep k z hz ?_
  intro E _ _ _ TE hTEn hTm rtsE hrlE hrtsE s hs2 hs' θE hθE
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTrE : TE.Tr (m + 1) := MSE.hyp.tr
  have hsq := GPoly.squarefreeCheck_sound (TE.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (TE.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (TE.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (TE.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (TE.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hok0 := TE.kxOK_spec m hTm A B kt l cs hok
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((TE.MP m hTm).isZero_iff _).mp h) hok0.1
  obtain ⟨b₀, -, -, hb₀2, -⟩ :=
    TE.kx_zero_twist hmon hdeg m hTEn hc hTrE A hsq hdegA hcopA ha0 z hz θE hθE s hs2 hs'
  obtain ⟨rtsF, hFl, hFv⟩ := TE.roots_F m rtsE (fun i hi ↦ (hrtsE i hi (by omega)).2)
  have hrlF : rtsF.length = (kxGens Fc ks m g A B kt l cs).length := by rw [hFl, hrlE]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : TE.F m) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrtsE i (by omega) hi').1]; simp)
  set f := algebraMap (TE.F m) (AlgebraicClosure (TE.F m))
  refine ⟨rtsF.map f, by simp [hrlF], fun i hi hi' ↦ ?_, f b₀, by rw [← map_pow, hb₀2], ?_, trivial⟩
  · simp only [List.getElem_map, ← map_pow, hrsF i (by simpa using hi) hi']
  · intro cK xK βK hns hns0
    set βC : Fin cs.length → TE.F m := fun q ↦
      ((kxRep Fc ks m g A B kt l cs q).2 : TE.F m) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
        ((TE.MP m hTm).sem (kxD Fc ks m g cs q) * (TE.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
          (GPoly.toPoly (TE.MP m hTm) B).eval ((TE.MP m hTm).sem (kqC Fc ks m cs q))) with hβC
    set cC : ℕ → TE.F m := fun i ↦ (GPoly.toPoly (TE.MP m hTm) A).coeff i with hcC
    set xC : Fin cs.length → TE.F m := fun q ↦ (TE.MP m hTm).sem (kqC Fc ks m cs q) with hxC
    have e : ∀ q, βK q = f (βC q) := fun q ↦ by
      simp only [βK, hβC, map_mul, map_ratCast, SqrtIndep.map_prodRoots]
    have hW : (Differential.SuperData.WG (f (cC 3)) (f (cC 2)) (f (cC 1)) (f (cC 0))) =
        (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).map f := by
      simp [Differential.SuperData.WG, FFHeight.longF, WeierstrassCurve.Affine.map,
        WeierstrassCurve.map]
    have pull : ∀ x y : TE.F m, (Differential.SuperData.WG (f (cC 3)) (f (cC 2)) (f (cC 1))
        (f (cC 0))).Nonsingular (f x) (f y) →
        (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular x y := fun x y h ↦ by
      rw [hW] at h
      exact (WeierstrassCurve.Affine.map_nonsingular _ f.injective x y).mp h
    have hnsq' : ∀ q, (Differential.SuperData.WG (f (cC 3)) (f (cC 2)) (f (cC 1)) (f (cC 0))).Nonsingular
        (f (cC 3) * f (xC q)) (f (cC 3) * f (βC q)) := fun q ↦ by rw [← e]; exact hns q
    have hns0' : (Differential.SuperData.WG (f (cC 3)) (f (cC 2)) (f (cC 1)) (f (cC 0))).Nonsingular
        (f (cC 3) * 0) (f (cC 3) * f b₀) := hns0
    have hnsC : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q) := fun q ↦ pull _ _ (by simpa only [map_mul] using hnsq' q)
    have hns0C : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀) := pull _ _ (by simpa only [map_mul, map_zero] using hns0')
    have hC := HGC E TE hTEn hTm rtsF hrlF hrsF b₀ hb₀2 hnsC hns0C
    have hK := Differential.SuperData.hgrp_of_C (K := AlgebraicClosure (TE.F m)) xC βC
      (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k (cC 3) (cC 2) (cC 1) (cC 0) b₀
      hnsC hns0C ?hh hnsq' hns0'
    case hh =>
      intro N hN μ
      have := hC N hN μ
      convert this
    have hpt : ∀ q, WeierstrassCurve.Affine.Point.some _ _ (hns q) =
        WeierstrassCurve.Affine.Point.some _ _ (hnsq' q) := fun q ↦ by
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, by rw [e]⟩
    intro N hN μ
    rw [Finset.sum_congr rfl (fun q _ ↦ by rw [hpt q])]
    exact hK N hN μ


end MTower

end Curves.MT
