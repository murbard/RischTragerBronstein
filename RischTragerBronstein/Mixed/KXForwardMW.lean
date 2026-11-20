import RischTragerBronstein.Mixed.KXForward
import RischTragerBronstein.Mixed.KXAbel
import RischTragerBronstein.Mixed.KXRootSign

/-!
# The Mordell–Weil exception of `kxDecide`, forward direction (step 4c)

`kx_forward_mw`: in the exception (`√A(0) ∈ Fₘ`, a class `k` and `P₊ − ∞` both non-torsion) with
`deg A = 3`, a Liouville form is impossible as soon as the group condition holds for **one** choice
of the square roots (`rtsK`, `b0K` in the algebraic closure): the proof's own roots differ by signs
per class (`prodRoots_sign`) and the condition is sign-invariant (`grp_signs`); `kxe_norel_group`
does the rest (Abel's theorem on the curve over the algebraic closure).
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
theorem kx_forward_mw (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (k : Fin (kxCls Fc ks m g A B kt l cs).length)
    (z : LC m) (s : L) (hz : kxZ Fc ks lv m A = some z) (hs2 : s ^ 2 = (kxKap Fc ks m A z : L))
    (hs' : s′ = 0)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (rts : List L) (hrl : rts.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrts : ∀ i (hi : i < rts.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rts[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : L) ∧ rts[i]′ = 0)
    (hTm : T.Tr m) (hdeg3 : (GPoly.toPoly (T.MP m hTm) A).natDegree = 3)
    (rtsK : List (AlgebraicClosure (T.F m)))
    (hrK : rtsK.length = (kxGens Fc ks m g A B kt l cs).length)
    (hsK : ∀ i (hi : i < rtsK.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rtsK[i] ^ 2 = algebraMap (T.F m) _ ((kxGens Fc ks m g A B kt l cs)[i] : T.F m))
    (b0K : AlgebraicClosure (T.F m))
    (hb0K : b0K ^ 2 = algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)))
    (hgrpK : let cK : ℕ → AlgebraicClosure (T.F m) := (fun i ↦
          algebraMap (T.F m) _ ((GPoly.toPoly (T.MP m hTm) A).coeff i))
        let xK : Fin cs.length → AlgebraicClosure (T.F m) := (fun q ↦
          algebraMap (T.F m) _ ((T.MP m hTm).sem (kqC Fc ks m cs q)))
        let βK : Fin cs.length → AlgebraicClosure (T.F m) := (fun q ↦
          ((kxRep Fc ks m g A B kt l cs q).2 : AlgebraicClosure (T.F m)) *
            SqrtIndep.prodRoots rtsK (kxRep Fc ks m g A B kt l cs q).1 *
            algebraMap (T.F m) _ ((T.MP m hTm).sem (kxD Fc ks m g cs q) *
              (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
              (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))))
        ∀ (hns : ∀ q, (Differential.SuperData.WG (cK 3) (cK 2) (cK 1) (cK 0)).Nonsingular
            (cK 3 * xK q) (cK 3 * βK q))
          (hns0 : (Differential.SuperData.WG (cK 3) (cK 2) (cK 1) (cK 0)).Nonsingular
            (cK 3 * 0) (cK 3 * b0K)),
          ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
            (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k q : ℤ) •
              WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
              (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0) : False := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := T.roots_F m rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kxGens Fc ks m g A B kt l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kx_data m hTr A hsq hdegA θ hθ (by omega) B kt l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have hc0 : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := fun q ↦
    (hok0.2 q q.2).1
  have hRne := T.kx_Rne m hTm A B kt l cs hok
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kxm_abs m MS.hyp hk A B kt l cs hok hcst hrep rtsF hrlF hrsF
  set Tk := (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] with hTk
  obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) m g A B kt l cs _ (List.getElem_mem (n := (k : ℕ)) k.2)
  have hk0 : ∃ q, kxCl m g A B kt l cs q = k ∧ kxMNm Fc ks m g A B kt l cs q ≠ 0 := by
    refine ⟨⟨q0, hq0⟩, (kxCl_eq_iff m g A B kt l cs _ k).mpr hq0T, fun h0 ↦ ?_⟩
    obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) m g A B kt l cs hrep q0 hq0
    have hm := kxMNm_eq (Fc := Fc) (ks := ks) m g A B kt l cs q0 hq0 hc0'
    rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at hm
    rcases hm with h | h
    · exact (kxDenM_pos (Fc := Fc) (ks := ks) m g A B kt l cs).ne' (by exact_mod_cast h)
    · rw [h] at hκ; simp at hκ
      exact T.kxK_ne m MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
  have hp0v : (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)) := by
    rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
    congr 1
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have hc0K : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := hc0
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  -- `b₀ = √A(0)` in `Fₘ`
  obtain ⟨b₀, μ₀, hb₀, hb₀2, -⟩ :=
    T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA (by
      cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
      · rfl
      · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v) z hz θ hθ s hs2 hs'
  set β₀ : (AlgebraicClosure (T.F m)) := algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) _).injective).mpr hb₀
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
    rw [hp0v]; show β₀ ^ 2 = _; rw [← map_pow, hb₀2]
  -- the cubic
  set P3 := GPoly.toPoly (T.MP m hTm) A with hP3
  set c3 := P3.coeff 3
  set c2 := P3.coeff 2
  set c1 := P3.coeff 1
  set c0 := P3.coeff 0
  have hP3e : P3 = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0 := by
    conv_lhs => rw [P3.as_sum_range_C_mul_X_pow, hdeg3]
    simp [Finset.sum_range_succ]; ring
  have hc3 : c3 ≠ 0 := by
    have : P3.leadingCoeff ≠ 0 := by
      rw [Ne, leadingCoeff_eq_zero]; intro h0; rw [h0] at hdeg3; simp at hdeg3
    rwa [leadingCoeff, hdeg3] at this
  have hpE : S.p = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0 := by
    show Polynomial.C ((1 : T.F m) ^ 2) * P3 = _
    rw [one_pow, map_one, one_mul, hP3e]
  set β : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
      SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
      ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
        (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβdef
  -- separability over the closure
  let f : T.F m →+* AlgebraicClosure (T.F m) := algebraMap (T.F m) (AlgebraicClosure (T.F m))
  have hc3K : f c3 ≠ 0 := (map_ne_zero_iff _ f.injective).mpr hc3
  have hsepK : (Polynomial.C (f c3) * X ^ 3 + Polynomial.C (f c2) * X ^ 2 + Polynomial.C (f c1) * X +
      Polynomial.C (f c0)).Separable := by
    have hs3 : P3.Separable := PerfectField.separable_iff_squarefree.mpr hsq
    have := hs3.map (f := f)
    rw [hP3e] at this
    simpa using this
  -- the points of the proof
  have hptq : ∀ q : Fin cs.length, (f (c3 * β q)) ^ 2 = (f (c3 * (T.MP m hTm).sem (kqC Fc ks m cs q))) ^ 3 +
      f c2 * (f (c3 * (T.MP m hTm).sem (kqC Fc ks m cs q))) ^ 2 +
      f c1 * f c3 * f (c3 * (T.MP m hTm).sem (kqC Fc ks m cs q)) + f c0 * f c3 ^ 2 := fun q ↦ by
    have h := (hβ q).2
    rw [one_pow, map_one, one_mul, hP3e] at h
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
    simp only [← map_mul, ← map_pow, ← map_add]
    congr 1
    show (c3 * β q) ^ 2 = _
    rw [mul_pow, h]; ring
  have hnsq : ∀ q : Fin cs.length, (Differential.SuperData.WG (f c3) (f c2) (f c1) (f c0)).Nonsingular
      (f c3 * f ((T.MP m hTm).sem (kqC Fc ks m cs q))) (f c3 * f (β q)) := fun q ↦ by
    have := Differential.SuperData.ns_of_eq hc3K hsepK _ _ (hptq q)
    simpa only [map_mul] using this
  have hpt0 : (f c3 * β₀) ^ 2 = (f c3 * 0) ^ 3 + f c2 * (f c3 * 0) ^ 2 + f c1 * f c3 * (f c3 * 0) +
      f c0 * f c3 ^ 2 := by
    have h := hv0
    rw [hpE] at h
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
    rw [mul_pow, show S.n = 2 from rfl] at *
    rw [h]; ring
  have hns0 := Differential.SuperData.ns_of_eq hc3K hsepK _ _ hpt0
  -- the reference points, and the comparison of roots
  set βK : Fin cs.length → (AlgebraicClosure (T.F m)) := fun q ↦
    ((kxRep Fc ks m g A B kt l cs q).2 : (AlgebraicClosure (T.F m))) *
      SqrtIndep.prodRoots rtsK (kxRep Fc ks m g A B kt l cs q).1 *
      f ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
        (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβKdef
  have hlen : (rtsF.map f).length = rtsK.length := by rw [List.length_map, hrlF, hrK]
  have hsqs : ∀ i (h : i < rtsK.length) (h' : i < (rtsF.map f).length),
      (rtsF.map f)[i] ^ 2 = rtsK[i] ^ 2 := fun i h h' ↦ by
    rw [List.getElem_map, ← map_pow, hrsF i (by simpa using h') (by omega), hsK i h (by omega)]
  have hfβ : ∀ q, f (β q) = ((kxRep Fc ks m g A B kt l cs q).2 : (AlgebraicClosure (T.F m))) *
      SqrtIndep.prodRoots (rtsF.map f) (kxRep Fc ks m g A B kt l cs q).1 *
      f ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
        (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) := fun q ↦ by
    simp only [hβdef, map_mul, map_ratCast, SqrtIndep.map_prodRoots]
  have hβpm : ∀ q, f (β q) = βK q ∨ f (β q) = -βK q := fun q ↦ by
    rcases SqrtIndep.prodRoots_sign rtsK (rtsF.map f) hlen hsqs (kxRep Fc ks m g A B kt l cs q).1
      with h | h
    · left; rw [hfβ, h]
    · right; rw [hfβ, h, hβKdef]; ring
  have hnsK : ∀ q : Fin cs.length, (Differential.SuperData.WG (f c3) (f c2) (f c1) (f c0)).Nonsingular
      (f c3 * f ((T.MP m hTm).sem (kqC Fc ks m cs q))) (f c3 * βK q) := fun q ↦ by
    have e : (f c3 * βK q) ^ 2 = (f (c3 * β q)) ^ 2 := by
      rcases hβpm q with h | h <;> rw [map_mul, h] <;> ring
    have := Differential.SuperData.ns_of_eq hc3K hsepK _ _ ((e.trans (hptq q)))
    simpa only [map_mul] using this
  have hb0pm : β₀ = b0K ∨ β₀ = -b0K := by
    have e : β₀ ^ 2 = b0K ^ 2 := by
      rw [hb0K]; show f b₀ ^ 2 = _; rw [← map_pow, hb₀2]
    have h2 : (β₀ - b0K) * (β₀ + b0K) = 0 := by linear_combination e
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
  have hns0K : (Differential.SuperData.WG (f c3) (f c2) (f c1) (f c0)).Nonsingular (f c3 * 0)
      (f c3 * b0K) := by
    have e : (f c3 * b0K) ^ 2 = (f c3 * β₀) ^ 2 := by rcases hb0pm with h | h <;> rw [h] <;> ring
    exact Differential.SuperData.ns_of_eq hc3K hsepK _ _ (e.trans hpt0)
  have hgK := hgrpK hnsK hns0K
  -- transfer the group condition to the proof's points
  have hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
        (kxCl m g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hnsq q)) +
        (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
    have hneg : ∀ q, f (β q) = -βK q → WeierstrassCurve.Affine.Point.some _ _ (hnsq q) =
        -WeierstrassCurve.Affine.Point.some _ _ (hnsK q) := fun q h ↦ by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq, Differential.SuperData.negY_G, h]
      exact ⟨trivial, by ring⟩
    have hpos : ∀ q, f (β q) = βK q → WeierstrassCurve.Affine.Point.some _ _ (hnsq q) =
        WeierstrassCurve.Affine.Point.some _ _ (hnsK q) := fun q h ↦ by
      simp only [h]
    refine grp_signs _ _ _ _ ?_ ?_ hgK
    · -- the class `k` flips as a whole
      rcases SqrtIndep.prodRoots_sign rtsK (rtsF.map f) hlen hsqs Tk with hT | hT
      · left
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        by_cases hq : kxCl m g A B kt l cs q = k
        · have hrep' := (kxCl_eq_iff m g A B kt l cs q k).mp hq
          rw [hpos q (by rw [hfβ, hβKdef]; simp only [hrep', ← hTk, hT])]
        · simp [Differential.SuperData.mK, hq]
      · right
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        by_cases hq : kxCl m g A B kt l cs q = k
        · have hrep' := (kxCl_eq_iff m g A B kt l cs q k).mp hq
          rw [hneg q (by rw [hfβ, hβKdef]; simp only [hrep', ← hTk, hT]; ring), zsmul_neg]
        · simp [Differential.SuperData.mK, hq]
    · rcases hb0pm with h | h
      · left; simp only [WeierstrassCurve.Affine.Point.some.injEq]; exact ⟨rfl, by rw [h]⟩
      · right
        rw [WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq, Differential.SuperData.negY_G]
        exact ⟨rfl, by rw [h]; ring⟩
  exact S.kxe_norel_group (K := (AlgebraicClosure (T.F m))) (T.val m g)′
    (T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
    (T.kxS_good m MS.hyp hk) (T.keS_constC m)
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj hc0K
    (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) _
    (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    _ (fun q' ↦ X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne
    hDoff hbP hres rfl β₀ hβ0 hv0 k hk0 hρ c3 c2 c1 c0 hc3 hpE hnsq hns0 hgrp hbm sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq)

end MTower

end Curves.MT
