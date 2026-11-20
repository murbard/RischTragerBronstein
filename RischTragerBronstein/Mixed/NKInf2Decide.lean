import RischTragerBronstein.Mixed.NKInf2Log
import RischTragerBronstein.Mixed.NKNonTors
import RischTragerBronstein.Mixed.KBIrr

/-!
# Non-Kummer logarithmic levels with two places at infinity

For a constant curve `θⁿ + ∑ aᵢ(t) θⁱ = 0` (`aᵢ ∈ ℚ[t]`, geometrically irreducible) over a
logarithmic level `t`, whose two places at infinity differ by a non-torsion class (certified on
the inverted curve `t′ = 1/t`, `TwoPlaceCertP`), the logarithmic part of an elementary integral of
`f = ∑ bⱼ θʲ` lies in the base, so the decision is that of a single place at infinity:
`∫ f` is elementary iff `f − τ(f)/n` is exact (`exactC`) and `∫ τ(f)/n` is elementary
(`nk_iff2`, `nk_decides2`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open CPoly Sup GTors

section CertP

variable (F : Type*) [Field F] [DecidableEq F] [CharZero F]

/-- **The certificate for a curve over `ℚ`** (over a field `F ⊇ ℚ`). -/
def TwoPlaceCertP (Fc' : BPoly ℚ) : Prop :=
  ∃ (T : GlobalCert F) (Pc : PlaceCert F) (p q : ℕ) (_ : Fact p.Prime) (_ : Fact q.Prime)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (Pp : PrimeCert p) (Qp : PlaceCert.PrimeData p)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (Pq : PrimeCert q) (Qq : PlaceCert.PrimeData q)
    (Pb : ℕ) (Lm : List (List F)),
    toB T.Fc = (toB Fc').map (mapRingHom (algebraMap ℚ F)) ∧ T.globalCheck = true ∧
    Pc.check T.Fc T.n = true ∧
    p ≠ q ∧ RedValid p Rp φp ∧ primeCheck Rp T Pp = true ∧
    Pc.primeCheck Rp T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true ∧
    RedValid q Rq φq ∧ primeCheck Rq T Pq = true ∧
    Pc.primeCheck Rq T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pq.xs Qq = true ∧
    (nonPrincOK T.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true) ∧
    Pc.fib.length = 1 ∧ Pc.pl.length = 2 ∧ Pc.fα 0 = 0

variable {F}

lemma TwoPlaceCertP.cert {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
    (S2 : CurveData C L) (ι : F →+* C) (Fc' : BPoly ℚ) (h : TwoPlaceCertP F Fc')
    (hS : S2.F = (toB Fc').map (mapRingHom (algebraMap ℚ C))) : TwoPlaceCert S2 ι := by
  obtain ⟨T, Pc, p, q, hp, hq, Rp, φp, Pp, Qp, Rq, φq, Pq, Qq, Pb, Lm, hT', hG, rest⟩ := h
  refine ⟨T, Pc, p, q, hp, hq, Rp, φp, Pp, Qp, Rq, φq, Pq, Qq, Pb, Lm, ?_,
    globalCheckR_of_globalCheck hG, rest⟩
  rw [hS, hT', Polynomial.map_map, mapRingHom_comp,
    MT.ratHom_eq (ι.comp (algebraMap ℚ F)) (algebraMap ℚ C)]

/-- **The certificate from the checks of a non-torsion witness** (`primeOKP` at two primes). -/
lemma twoPlaceCertP_of_checks [EllQuad.QCoords F] (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (Fc' : BPoly ℚ) (T : GlobalCert F) (Pc : PlaceCert F) (p q : ℕ) (Pp : PrimeCert p)
    (Pq : PrimeCert q) (Qp : PlaceCert.PrimeData p) (Qq : PlaceCert.PrimeData q) (Pb : ℕ)
    (Lm : List (List F)) (hFc : toB T.Fc = (toB Fc').map (mapRingHom (algebraMap ℚ F)))
    (hG : T.globalCheck = true) (hPc : Pc.check T.Fc T.n = true) (hpq : p ≠ q)
    (hP : primeOKP redAt T Pc p Pp Qp = true) (hQ : primeOKP redAt T Pc q Pq Qq = true)
    (hN : nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true)
    (hfib1 : Pc.fib.length = 1) (hpl2 : Pc.pl.length = 2) (hα0 : Pc.fα 0 = 0) :
    TwoPlaceCertP F Fc' := by
  obtain ⟨hp, Rp, hRp, hPp⟩ := primeOKP_spec hP
  obtain ⟨hq, Rq, hRq, hPq⟩ := primeOKP_spec hQ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨φp, hφp⟩ := hred p Rp hRp
  obtain ⟨φq, hφq⟩ := hred q Rq hRq
  exact ⟨T, Pc, p, q, ⟨hp⟩, ⟨hq⟩, Rp, φp, Pp, Qp, Rq, φq, Pq, Qq, Pb, Lm, hFc, hG, hPc, hpq, hφp,
    hPp.1, hPp.2, hφq, hPq.1, hPq.2, Or.inr hN, hfib1, hpl2, hα0⟩

end CertP

/-- **The inverted curve of a curve over `ℚ`.** -/
lemma mob_data {C : Type*} [Field C] [CharZero C] (Fq : BPoly ℚ) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (W : C[X][X])
    (hW : W = (toB Fq).map (mapRingHom (algebraMap ℚ C))) :
    (∀ i ≤ (shiftP W 0).natDegree, ((shiftP W 0).coeff i).natDegree + k0 * i ≤ M) ∧
      invP (shiftP W 0) k0 M = (toB (invB (shiftB Fq 0) k0 M)).map (mapRingHom (algebraMap ℚ C)) := by
  have hinj : Function.Injective (mapRingHom (algebraMap ℚ C)) :=
    map_injective _ (algebraMap ℚ C).injective
  have hsh : shiftP W 0 = (toB (shiftB Fq 0)).map (mapRingHom (algebraMap ℚ C)) := by
    rw [hW, toB_shiftB, shiftP_map, map_zero]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [hsh, natDegree_map_eq_of_injective hinj] at hi
    rw [hsh, coeff_map, coe_mapRingHom,
      natDegree_map_eq_of_injective (algebraMap ℚ C).injective]
    exact invBound_of_invOK _ _ _ hinv i hi
  · rw [hsh, ← invP_map, toB_invB _ _ _ hinv]

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma nkF_eqQ (m : ℕ) (h0 : T.Tr m) (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ)
    (hPp : Pp = liftCurve Fc ks m Pp.length Fq) (hmonQ : (toB Fq).Monic)
    (hdegQ : (toB Fq).natDegree = Pp.length) :
    T.nkF m h0 Pp = (toB Fq).map (mapRingHom (algebraMap ℚ (T.F m))) := by
  rw [hPp, T.nkF_liftCurve m h0 _ Fq hmonQ hdegQ]

/-- **The curve** `F(tₘ, θ) = 0` of a geometrically irreducible curve over `ℚ`. -/
noncomputable def nkCurveG (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ)
    (hPp : Pp = liftCurve Fc ks m Pp.length Fq) (hmonQ : (toB Fq).Monic)
    (hdegQ : (toB Fq).natDegree = Pp.length) (hgeo : GeomIrr.{u} Fq) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0) :
    CurveData (T.F m) L where
  x := T.ts m
  y := θ
  F := T.nkF m h1.of_succ Pp
  htr := h1 m (by omega)
  monic := polyF_monic _ _
  irr := Curves.MT.curve_irr _ _ (h1 m (by omega)) _ (polyF_monic _ _)
    (by rw [T.nkF_eqQ m h1.of_succ Pp Fq hPp hmonQ hdegQ]; exact hgeo _)
    (T.nkF_root m h1.of_succ Pp θ hθ)
  root := T.nkF_root m h1.of_succ Pp θ hθ

lemma nkCurveG_ind (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ)
    (hPp : Pp = liftCurve Fc ks m Pp.length Fq) (hmonQ : (toB Fq).Monic)
    (hdegQ : (toB Fq).natDegree = Pp.length) (hgeo : GeomIrr.{u} Fq) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (a : ℕ → T.F (m + 1)) (ha : ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0) :
    ∀ j < Pp.length, a j = 0 := by
  set S := T.nkCurveG m h1 Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  have hdeg : S.F.natDegree = Pp.length := polyF_natDegree _ _
  intro j hj
  have := S.coords_uniqueG (fun j ↦ (a j : L)) (fun i _ ↦ (T.mem_F_succ).mp (a i).2)
    (by rw [hdeg]; exact ha) j (by rw [hdeg]; exact hj)
  exact Subtype.ext this

set_option maxHeartbeats 4000000 in
/-- **`⇐`**: an exact `f − τ(f)/n` and an elementary `τ(f)/n` give an elementary `f`. -/
theorem nk_sufficient2 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  have hiff := T.exactC_correct m (by omega) hTr (hTr m (by omega)) hk (paramLimC Fc ks lv m)
    MSm.lim (nkPC Fc ks m Pp) _ θ hP hind res hres
  obtain ⟨Y, hY⟩ := hiff.mp hr
  rw [hlen, T.sum_nkRest m hTr Pp.length hn0] at hY
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ by rw [hY]; ring]
  exact hq.add_in (hasElementaryIntegralIn_deriv _)

set_option maxHeartbeats 16000000 in
/-- **`⇒`**: an elementary `f` has an exact `f − τ(f)/n` and an elementary `τ(f)/n` (the
logarithmic part of a Liouville form lies in `Fₘ`, and `τ` is `n` on `Fₘ`). -/
theorem nk_necessary2 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (hcert : TwoPlaceCertP F (invB (shiftB Fq 0) k0 M))
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  classical
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFl Fc ks m fp) s with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have MSEm := TE.mspecs hmon hdeg lv m (by omega) hcm
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  -- the curve over `C₁ = Fₘ` of the lifted tower
  set S₁ := TE.nkCurveG m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE with hS₁
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  set η₁ : TE.F m := TE.val m η with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁) := by
    rw [aeval_C]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m),
      α′ ≠ ((Polynomial.C η₁).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α ↦ by
      rw [Polynomial.map_C, eval_C]
      exact not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd m (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the integrand is a polynomial in `x, y`
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_pow, hPE]
  set Q : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQ
  have hQv : S₁.evXY Q = ψ f := by
    rw [hψf, CurveData.evXY, hQ, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C,
      eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfT : ψ f ∈ T₁ := hLT f
  have hfQ : (⟨ψ f, hfT⟩ : T₁) = S₁.evT Q := Subtype.ext (by rw [S₁.coe_evT, hQv])
  have hreg : S₁.RegularFinite (AlgebraicClosure (TE.F m)) ⟨ψ f, hfT⟩ := by
    rw [hfQ]; exact S₁.regularFinite_evT Q
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  -- the inverted curve and its certificate
  have hS₁Q : S₁.F = (toB Fq).map (mapRingHom (algebraMap ℚ (TE.F m))) :=
    TE.nkF_eqQ m hTEm Pp Fq hPp hmonQ hdegQ
  obtain ⟨hMb, hinvEq⟩ := mob_data (C := TE.F m) Fq k0 M hinv S₁.F hS₁Q
  have hGm' : (invP (shiftP S₁.F 0) k0 M).Monic := by rw [hinvEq]; exact hGm.map _
  have hGn' : (invP (shiftP S₁.F 0) k0 M).natDegree = S₁.F.natDegree := by
    rw [hinvEq, natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ (TE.F m)).injective),
      hGn, hS₁F]
  have hιmem : ∀ a : F, ψ (algebraMap Cc L (ιC a)) ∈ TE.F m := fun a ↦
    hTEmem m _ (T.const_mem m (ιC a))
  set ιF : F →+* TE.F m := RingHom.codRestrict ((algebraMap L E₁).comp ((algebraMap Cc L).comp ιC))
    (TE.F m) hιmem with hιFdef
  have hcert' : TwoPlaceCert (mobCurve S₁ 0 k0 M hMb hGm' hGn') ιF :=
    hcert.cert _ ιF _ hinvEq
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := by
    rw [hS₁Q, Polynomial.map_map, mapRingHom_comp, ratHom_eq ((algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))).comp (algebraMap ℚ (TE.F m))) (algebraMap ℚ _)]
    exact hgeo _
  obtain ⟨ℓ₀, hℓ₀⟩ := S₁.nk_liouville_two (K := AlgebraicClosure (TE.F m)) (Polynomial.C η₁) hx hK
    hnd k0 M hMb hGm' hGn' hgeo' ιF hcert' hconstC (ψ f) hfT hreg s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  -- the trace
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  obtain ⟨hs0, hτ⟩ := TE.traceC_sound m hTE Pp (ψ θ) hPθE s hs
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  obtain ⟨w, hw, hwe⟩ := S₁.trace_split (fun j ↦ ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁))
    (fun j ↦ (TE.mem_F_succ).mp (M1.sem (s.getD j O1.zero)).2)
    (by rw [hS₁F, hs0]; push_cast; rfl)
    (fun i hi ↦ by
      rw [hS₁F] at hi ⊢
      obtain ⟨c', hc'd, hc's⟩ := hτ i hi
      refine ⟨fun j ↦ (c' j : E₁), fun j ↦ (TE.mem_F_succ).mp (c' j).2, hc'd, ?_⟩
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) hc's
      simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        MTower.coe_deriv] at this
      exact this)
    hdx (fun j ↦ TE.evP m (fp.getD j [])) (fun j ↦ (TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j = _
      rw [← hψf]; exact hℓ₀)
  rw [hS₁F] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ = ∑ i ∈ s', c i * logDeriv (u i) := by
    have := hℓ₀.symm.trans heq₁
    exact add_left_cancel this
  refine ⟨?_, ?_⟩
  · ----------------------------------------------------------------------------------------------
    -- the exact part in the lifted tower
    have hvw : v - w ∈ T₁ := sub_mem (hCT v hv) (IntermediateField.algebraMap_mem T₁
      (⟨w, hw⟩ : (TE.F m)⟮S₁.x⟯))
    obtain ⟨Y', hY'm, hY'⟩ := S₁.exists_coords (v - w) hvw
    rw [hS₁F] at hY'
    have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
    have hind : ∀ a : ℕ → TE.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : E₁) * (ψ θ) ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [hlen]; exact TE.nkCurveG_ind m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE
    have hiff := TE.exactC_correct m (by omega) hTE (hTE m (by omega)) hk (paramLimC Fc ks lv m)
      MSEm.lim (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind res hres
    refine hiff.mpr ⟨fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen, TE.sum_nkRest m hTE n hn0, hTEev (m + 1) q]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map fun i ↦ (c i, u i) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [Finset.mem_toList] at hi
      exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_map, Finset.sum_map_toList]
      rfl
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform


/-- **The logarithmic part over a non-Kummer extension of a logarithmic level**: for
`θⁿ + ∑ aᵢ(t) θⁱ = 0` with a single place at infinity and `f = ∑ bⱼ(t) θʲ`, `f` has an elementary
integral iff `f − τ(f)/n` is exact (`exactC`) and `τ(f)/n ∈ Fₘ₊₁` has one. -/
theorem nk_iff2 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (hcert : TwoPlaceCertP F (invB (shiftB Fq 0) k0 M)) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) :=
  ⟨T.nk_necessary2 hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ ιC k0 M hinv hGm hGn hcert
      hθ hgen s hs fp res hres,
    fun h ↦ T.nk_sufficient2 hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ hθ s fp res hres
      h.1 h.2⟩

set_option maxHeartbeats 4000000 in
/-- **The decision**: `elM` decides `τ(f)/n` (at every large search bound), `exactC` the rest. -/
theorem nk_decides2 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (hcert : TwoPlaceCertP F (invB (shiftB Fq 0) k0 M)) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hshF T' (m + 1) hT'n hc hT'gen q
  -- `L` is algebraic over `F (m + 1)`
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ
  have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have h0 : HasElementaryIntegral (T.ev (m + 1) q) ↔ HasElementaryIntegral (T'.ev (m + 1) q) := by
    rw [← hasElementaryIntegral_isAlgebraic_iff halg]
    rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) q) = T.ev (m + 1) q from
      hT'ev (m + 1) le_rfl q]
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N hN
  refine ⟨b, hb, ?_⟩
  rw [T.nk_iff2 hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo ιC k0 M hinv hGm hGn hcert θ hθ hgen
    s hs fp res hres, h0, hiff]

end MTower

end Curves.MT
