import RischTragerBronstein.Torsion.IntBasisCheck
import RischTragerBronstein.Torsion.SimpleDisc
import RischTragerBronstein.Computable.Hermite

/-!
# Integral-basis checks with uncertified simple discriminant roots (characteristic `0`)

`ibCheckR` is `ibCheck` with the cover condition relaxed (`coverR`): either every root of the
cover polynomial `G` is a certified point (as in `ibCheck`), or the roots of `D · det [Bⱼ,ᵢ]` are
certified points and what remains of `G` after stripping the certified points is separable
(`sqfreeStrip`). Then at an uncertified point the discriminant vanishes to order `≤ 1`, and local
independence comes from `isIntBasis_of_special_simple` (Puiseux, hence characteristic `0`). No
branch certificate — hence no rational root — is needed at simple discriminant roots: this is
what certificates over function fields need. `ibCheckR_spec` is the analogue of `ibCheck_spec`.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- `P` with the given points stripped is separable (and non-zero). -/
def sqfreeStrip (P : CPoly F) (as : List F) : Bool :=
  let R := as.foldl (fun Q a ↦ stripAt a Q.length Q) P
  !isZero R && (CPoly.trim (CPoly.egcd R (CPoly.deriv R)).1).length == 1

/-- **The relaxed cover condition.** -/
def coverR (G Dc : CPoly F) (Bc : List (BPoly F)) (n : ℕ) (as : List F) : Bool :=
  coverCheck G as || (coverCheck (mul Dc (detC n Bc)) as && sqfreeStrip G as)

/-- **The relaxed integral-basis check.** -/
def ibCheckR (Fc : BPoly F) (n k : ℕ) (I : IntBasisCert F) (G : CPoly F) : Bool :=
  shapeCheck Fc n k && !isZero I.Dc &&
  (List.range n).all (fun j ↦ decide ((I.Bc.getD j []).length ≤ n)) &&
  I.pts.all (fun p ↦ certCheck Fc n p.1 p.2.1 && basisCheckAt n I.Bc I.Dc p.1 p.2.1 p.2.2) &&
  coverR G I.Dc I.Bc n (I.pts.map Prod.fst) &&
  certCheck (invB Fc k (k * n)) n 0 I.infc && basisCheckInfS n k I.Bc I.Dc I.δL I.infc I.Linf

lemma ibCheckR_of_ibCheck {Fc : BPoly F} {n k : ℕ} {I : IntBasisCert F} {G : CPoly F}
    (h : ibCheck Fc n k I G = true) : ibCheckR Fc n k I G = true := by
  simp only [ibCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [ibCheckR, coverR, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, Or.inl h5⟩, h6⟩, h7⟩

end Defs

section Spec

variable {F : Type*} [Field F] [DecidableEq F]

/-- **What `sqfreeStrip` gives**: away from the stripped points, roots are simple. -/
theorem sqfreeStrip_spec (P : CPoly F) (as : List F) (h : sqfreeStrip P as = true)
    {K : Type*} [Field K] (ψ : F →+* K) (z : K) (hz : ∀ a ∈ as, z ≠ ψ a) :
    toPoly P ≠ 0 ∧ ((toPoly P).map ψ).rootMultiplicity z ≤ 1 := by
  simp only [sqfreeStrip, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    beq_iff_eq] at h
  obtain ⟨hnz, hlen⟩ := h
  obtain ⟨Q, hQ, hQr, hQ0⟩ := foldl_strip_spec as P
  set R := as.foldl (fun Q a ↦ stripAt a Q.length Q) P with hR
  have hR0 : toPoly R ≠ 0 := fun h0 ↦ hnz ((isZero_iff R).mpr h0)
  -- separability of the remainder
  have hsep : (toPoly R).Separable := by
    obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp hlen
    obtain ⟨hγ0, hg⟩ := trim_singleton hγ
    have hbez := egcd_spec R (CPoly.deriv R)
    rw [hg, toPoly_deriv] at hbez
    refine ⟨Polynomial.C γ⁻¹ * toPoly (egcd R (CPoly.deriv R)).2.1,
      Polynomial.C γ⁻¹ * toPoly (egcd R (CPoly.deriv R)).2.2, ?_⟩
    have : Polynomial.C γ⁻¹ * Polynomial.C γ = (1 : F[X]) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hγ0, Polynomial.C_1]
    linear_combination Polynomial.C γ⁻¹ * hbez + this
  have hP0 : toPoly P ≠ 0 := by rw [hQ]; exact mul_ne_zero hQ0 hR0
  refine ⟨hP0, ?_⟩
  have hQψ : Q.map ψ ≠ 0 := (Polynomial.map_ne_zero_iff ψ.injective).mpr hQ0
  have hRψ : (toPoly R).map ψ ≠ 0 := (Polynomial.map_ne_zero_iff ψ.injective).mpr hR0
  rw [hQ, Polynomial.map_mul, rootMultiplicity_mul (mul_ne_zero hQψ hRψ),
    rootMultiplicity_eq_zero fun hroot ↦ ?_, zero_add]
  · exact rootMultiplicity_le_one_of_separable (hsep.map) z
  · obtain ⟨a, ha, hza⟩ := hQr ψ z hroot
    exact hz a ha hza

lemma sqfreeStrip_ne_zero (P : CPoly F) (as : List F) (h : sqfreeStrip P as = true) :
    toPoly P ≠ 0 := by
  simp only [sqfreeStrip, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at h
  obtain ⟨Q, hQ, -, hQ0⟩ := foldl_strip_spec.{_, 0} as P
  rw [hQ]
  exact mul_ne_zero hQ0 fun h0 ↦ h.1 ((isZero_iff _).mpr h0)

end Spec

section Basis

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)

/-- **Certified integral bases, simple discriminant roots uncertified.** -/
theorem isIntBasis_of_cert_detR (Fc : BPoly F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree)
    (Bc : List (BPoly F)) (Dc : CPoly F) (δ : List ℕ) (hD : toPoly Dc ≠ 0)
    (hdegB : ∀ j : Fin S.F.natDegree, (toB (Bc.getD j [])).natDegree < S.F.natDegree)
    (hdetB : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (toB (Bc.getD j [])).coeff i).det ≠ 0)
    (pts : List (F × BranchCert F × List (List F)))
    (hpts : ∀ p ∈ pts, certCheck Fc S.F.natDegree p.1 p.2.1 = true ∧
      basisCheckAt S.F.natDegree Bc Dc p.1 p.2.1 p.2.2 = true)
    (G : CPoly F) (hG : resultant (toB Fc) (derivative (toB Fc)) S.F.natDegree
      (S.F.natDegree - 1) * toPoly Dc *
        (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (toB (Bc.getD j [])).coeff i).det ∣ toPoly G)
    (hcovD : coverCheck (mul Dc (detC S.F.natDegree Bc)) (pts.map Prod.fst) = true)
    (hsq : sqfreeStrip G (pts.map Prod.fst) = true)
    (infc : BranchCert F) (Linf : List (List F))
    (hinfc : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 infc = true)
    (hinfb : basisCheckInfS S.F.natDegree k Bc Dc δ infc Linf = true) :
    S.IsIntBasis K (fun j ↦ (toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)
      (fun j ↦ δ.getD j 0) := by
  classical
  haveI : CharZero K := charZero_of_injective_ringHom ((algebraMap C K).comp ψ₀).injective
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  obtain ⟨hinf, hindInf⟩ := S.basisCheckInfS_spec (K := K) Fc ψ₀ hSF hmon hdeg k hok hmon' hn' Bc Dc
    δ infc hinfc Linf hinfb
  set Sp : Finset K := (pts.map fun p ↦ algebraMap C K (ψ₀ p.1)).toFinset with hSp
  have hmemSp : ∀ a ∈ Sp, ∃ p ∈ pts, a = algebraMap C K (ψ₀ p.1) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact ⟨p, hp, rfl⟩
  set resF := resultant (toB Fc) (derivative (toB Fc)) S.F.natDegree (S.F.natDegree - 1)
    with hresF
  set detF := (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (toB (Bc.getD j [])).coeff i).det
    with hdetF
  have hdetmap : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ ((toB (Bc.getD j [])).map
      (mapRingHom ψ₀)).coeff i).det = detF.map ψ₀ := by
    rw [show ∀ P : F[X], P.map ψ₀ = mapRingHom ψ₀ P from fun _ ↦ rfl, RingHom.map_det]
    congr 1
    ext i j
    simp [coeff_map]
  have hres : resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1) = resF.map ψ₀ := by
    have h := resultant_map_map (f := toB Fc) (g := derivative (toB Fc)) (m := S.F.natDegree)
      (n := S.F.natDegree - 1) (mapRingHom ψ₀)
    rw [← Polynomial.derivative_map, ← hSF] at h
    exact h
  have hG0 : toPoly G ≠ 0 := sqfreeStrip_ne_zero G _ hsq
  have hresF0 : resF ≠ 0 := fun h0 ↦ hG0 (zero_dvd_iff.mp (by rwa [h0, zero_mul, zero_mul] at hG))
  have hRC : resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1) ≠ 0 := by
    rw [hres]; exact (Polynomial.map_ne_zero_iff ψ₀.injective).mpr hresF0
  refine S.isIntBasis_of_special_simple ((Polynomial.map_ne_zero_iff ψ₀.injective).mpr hD)
    (fun j ↦ lt_of_le_of_lt natDegree_map_le (hdegB j))
    (by rw [hdetmap]; exact (Polynomial.map_ne_zero_iff ψ₀.injective).mpr hdetB)
    hRC Sp (fun a ha ↦ ?_) (fun j a ha ↦ ?_) (fun a ha ↦ ?_) hinf hindInf
  · -- away from the certified points
    have hz : ∀ b ∈ pts.map Prod.fst, a ≠ ψ b := by
      intro b hb hab
      apply ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, hab.symm⟩)
    have hDd : ((toPoly (mul Dc (detC S.F.natDegree Bc))).map ψ).eval a ≠ 0 := fun h0 ↦ by
      obtain ⟨b, hb, hab⟩ := coverCheck_spec _ _ hcovD ψ a h0
      exact hz b hb hab
    rw [toPoly_mul, toPoly_detC, Polynomial.map_mul, eval_mul] at hDd
    obtain ⟨hDa, hdeta⟩ := mul_ne_zero_iff.mp hDd
    refine ⟨?_, ?_, ?_⟩
    · rw [hres, Polynomial.map_map]
      have hdvd : resF.map ψ ∣ (toPoly G).map ψ :=
        Polynomial.map_dvd ψ (dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hG))
      exact (rootMultiplicity_le_rootMultiplicity_of_dvd
        ((Polynomial.map_ne_zero_iff ψ.injective).mpr hG0) hdvd a).trans
        (sqfreeStrip_spec G _ hsq ψ a hz).2
    · rw [Polynomial.map_map]; exact hDa
    · rw [hdetmap, Polynomial.map_map]; exact hdeta
  · obtain ⟨p, hp, rfl⟩ := hmemSp a ha
    exact ((S.basisCheckAt_spec (K := K) Fc ψ₀ hSF hmon hdeg Bc Dc hD p.1 p.2.1 (hpts p hp).1 p.2.2
      (hpts p hp).2).1 j)
  · obtain ⟨p, hp, rfl⟩ := hmemSp a ha
    exact (S.basisCheckAt_spec (K := K) Fc ψ₀ hSF hmon hdeg Bc Dc hD p.1 p.2.1 (hpts p hp).1 p.2.2
      (hpts p hp).2).2

end CurveData

/-- **The integral basis from `ibCheckR`** (characteristic `0`). -/
theorem ibCheckR_spec (S : CurveData C L) (Fc : BPoly F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB Fc).map (mapRingHom ψ₀)) (n k : ℕ) (hn : n = S.F.natDegree)
    (I : IntBasisCert F) (G : CPoly F) (h : ibCheckR Fc n k I G = true)
    (hG : resultant (toB Fc) (derivative (toB Fc)) n (n - 1) * toPoly I.Dc *
      (Matrix.of fun (i j : Fin n) ↦ (toB (I.Bc.getD j [])).coeff i).det ∣ toPoly G) :
    S.IsIntBasis K (fun j ↦ (toB (I.Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly I.Dc).map ψ₀)
      (fun j ↦ I.δL.getD j 0) := by
  have h' := h
  simp only [ibCheckR, coverR, Bool.and_eq_true, Bool.or_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨hsh, hD⟩, htl⟩, hpts⟩, hcov⟩, hinfc⟩, hinfb⟩ := h'
  rcases hcov with hcov | ⟨hcovD, hsq⟩
  · refine ibCheck_spec S Fc ψ₀ hSF n k hn I G ?_ hG
    simp only [ibCheck, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨hsh, hD⟩, htl⟩, hpts⟩, hcov⟩, hinfc⟩, hinfb⟩
  subst hn
  simp only [Bool.not_eq_true', Bool.eq_false_iff, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.and_eq_true] at hD htl hpts
  obtain ⟨hn0, hmon, hdeg, hok, hmon', hn'⟩ := shapeCheck_spec hsh
  have hG0 : toPoly G ≠ 0 := sqfreeStrip_ne_zero G _ hsq
  refine S.isIntBasis_of_cert_detR Fc ψ₀ hSF hmon hdeg k hok hmon' hn' I.Bc I.Dc I.δL
    (fun h0 ↦ hD ((isZero_iff _).mpr h0)) (fun j ↦ ?_) ?_ I.pts
    (fun p hp ↦ hpts p hp) G hG hcovD hsq I.infc I.Linf hinfc hinfb
  · exact lt_of_le_of_lt (natDegree_toB_le_len' _) (by have := htl j j.2; omega)
  · intro h0
    rw [h0, mul_zero] at hG
    exact hG0 (zero_dvd_iff.mp hG)

end Basis

end Curves
