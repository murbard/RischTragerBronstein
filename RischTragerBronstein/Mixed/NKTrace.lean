import RischTragerBronstein.Mixed.NKLogCert
import RischTragerBronstein.Elementary.TraceDeriv
import RischTragerBronstein.Mixed.NKExactT2

/-!
# The trace of a Liouville form

On a curve `S` over a differential base (`x′ = ω(x)`), if `f = v′ + ∑ cᵢ uᵢ′/uᵢ` in `C(x, y)`
(constant `cᵢ ∈ C`), then `Tr f = (Tr v)′ + ∑ cᵢ N(uᵢ)′/N(uᵢ)` in `C(x)` (`trace_liouville`):
the trace down to `C(x)` of an elementary integrand is elementary, whatever its residues and
places at infinity. With `Tr(yʲ)` computed in the power basis (`PowerBasis.trace_gen_pow`) this
gives a **necessary condition** for elementary integrability decided one level down.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

namespace CurveData

open Differential

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)

include hx in
/-- **The trace of a Liouville form is a Liouville form one level down.** -/
theorem trace_liouville {ι : Type*} (I : Finset ι) (c : ι → C) (hc : ∀ i, (c i)′ = 0)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L)
    (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i)) :
    ∃ w : L, w ∈ C⟮S.x⟯ ∧ ∃ Nn : ι → L, (∀ i, Nn i ∈ C⟮S.x⟯ ∧ Nn i ≠ 0) ∧
      ((Algebra.trace C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨f, hf⟩ : C⟮S.x⟯) : L) =
        w′ + ∑ i ∈ I, algebraMap C L (c i) * ((Nn i)′ / Nn i) := by
  classical
  have hK : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x ω hx
  letI : Differential C⟮S.x⟯ := differentialOfDerivClosed hK
  letI : DifferentialAlgebra C⟮S.x⟯ L := differentialAlgebra_of_derivClosed hK
  have hM : DerivClosed C⟮S.x⟯⟮S.y⟯ := S.derivClosedXYW' ω hx
  letI : Differential C⟮S.x⟯⟮S.y⟯ := differentialOfDerivClosed hM
  haveI : DifferentialAlgebra C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ := ⟨fun k ↦ Subtype.ext rfl⟩
  haveI : FiniteDimensional C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ :=
    IntermediateField.adjoin.finiteDimensional S.isIntegral
  haveI : CharZero C⟮S.x⟯ := charZero_of_injective_algebraMap (algebraMap C C⟮S.x⟯).injective
  set U : ι → C⟮S.x⟯⟮S.y⟯ := fun i ↦ ⟨u i, hu i⟩ with hU
  have hU0 : ∀ i, U i ≠ 0 := fun i h ↦ hu0 i (congrArg Subtype.val h)
  set κ : ι → C⟮S.x⟯ := fun i ↦ algebraMap C C⟮S.x⟯ (c i) with hκ
  have hM' : (⟨f, hf⟩ : C⟮S.x⟯⟮S.y⟯) = (⟨v, hv⟩ : C⟮S.x⟯⟮S.y⟯)′ + ∑ i ∈ I, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (κ i) * ((U i)′ / U i) :=
    Subtype.ext (by
      change f = _
      rw [heq, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
      rfl)
  have ht := congrArg (Algebra.trace C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯) hM'
  rw [map_add, map_sum, trace_deriv] at ht
  simp only [← Algebra.smul_def, map_smul, trace_logDeriv _ (hU0 _)] at ht
  refine ⟨((Algebra.trace C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨v, hv⟩ : C⟮S.x⟯) : L), SetLike.coe_mem _,
    fun i ↦ ((Algebra.norm C⟮S.x⟯ (U i) : C⟮S.x⟯) : L), fun i ↦ ⟨SetLike.coe_mem _, fun h ↦ ?_⟩, ?_⟩
  · exact (Algebra.norm_ne_zero_iff.mpr (hU0 i)) (Subtype.ext h)
  · rw [ht, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1

end CurveData

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential Polynomial IntermediateField

section Codes

variable {α : Type} (O : COps α)

/-- The code of `Xᵏ`. -/
def xPowC (k : ℕ) : GPoly α := List.replicate k O.zero ++ [O.one]

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The trace codes** `sᵢ = Tr(θⁱ) = ∑ⱼ [Xʲ](X^{i+j} mod P)`. -/
def traceCodes (m : ℕ) (P : GPoly (LC (m + 1))) : List (LC (m + 1)) :=
  let O1 := MOr Fc ks (m + 1)
  let N := P.length - 1
  (List.range N).map fun i ↦ lsumC O1 ((List.range N).map fun j ↦
    (remP O1 P (xPowC O1 (i + j))).getD j O1.zero)

end Codes

lemma toPoly_xPowC {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α}
    (M : CField α K O) (k : ℕ) : GPoly.toPoly M (xPowC O k) = X ^ k := by
  induction k with
  | zero => simp [xPowC, GPoly.toPoly_cons, M.sem_one]
  | succ k ih =>
    rw [xPowC, List.replicate_succ, List.cons_append, GPoly.toPoly_cons, M.sem_zero, map_zero,
      zero_add, pow_succ, mul_comm]
    rw [xPowC] at ih
    rw [ih]

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The coordinates of `θᵏ` from the code of `Xᵏ mod P`. -/
lemma pow_eq_remP (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (θ : L)
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (hn0 : 0 < Pp.length) (k : ℕ) :
    θ ^ k = ∑ l ∈ Finset.range Pp.length, (((T.MPr (m + 1) h1).sem
      ((remP (MOr Fc ks (m + 1)) (nkPC Fc ks m Pp) (xPowC (MOr Fc ks (m + 1)) k)).getD l
        (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ l := by
  set M1 := T.MPr (m + 1) h1
  set O1 := MOr Fc ks (m + 1)
  have hPm : (GPoly.toPoly M1 (nkPC Fc ks m Pp)).Monic := by
    rw [T.toPoly_nkPC m h1 Pp]; exact polyF_monic _ _
  have hPd : (GPoly.toPoly M1 (nkPC Fc ks m Pp)).natDegree = Pp.length := by
    rw [T.toPoly_nkPC m h1 Pp]; exact polyF_natDegree _ _
  have h1' := T.evθ_remP m h1 θ (nkPC Fc ks m Pp) hP (xPowC O1 k)
  unfold evθ at h1'
  rw [toPoly_xPowC, aeval_X_pow] at h1'
  rw [← h1']
  have hlt : (GPoly.toPoly M1 (remP O1 (nkPC Fc ks m Pp) (xPowC O1 k))).natDegree < Pp.length := by
    by_cases h0 : GPoly.toPoly M1 (remP O1 (nkPC Fc ks m Pp) (xPowC O1 k)) = 0
    · rw [h0, natDegree_zero]; exact hn0
    · rw [← hPd]
      exact natDegree_lt_natDegree h0 (GPoly.divMod_degree_lt M1 _ _ hPm.ne_zero)
  rw [aeval_eq_sum_range' hlt]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [coeff_toPoly_sem, Algebra.smul_def]; rfl


set_option maxHeartbeats 16000000 in
-- the proof lifts the tower to the elementary extension
/-- **The trace test** (logarithmic or exponential level, single place at infinity): if `f = ∑ fⱼ θʲ` (any
coordinates, any poles) has an elementary integral, so has `Tr(f)/n ∈ Fₘ₊₁`, computed from the
trace codes `traceCodes`. Contrapositive: `elM` proving `∫ Tr(f)/n` non-elementary proves `∫ f`
non-elementary. -/
theorem nk_trace_nec (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (fl : List (LC (m + 1))) (h1 : T.Tr (m + 1))
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
      ((T.MPr (m + 1) h1).sem (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j)) :
    HasElementaryIntegral (T.ev (m + 1)
      (nkTau Fc ks m Pp.length fl (traceCodes Fc ks m (nkPC Fc ks m Pp)))) := by
  classical
  set n := Pp.length with hnn
  set O1 := MOr Fc ks (m + 1) with hO1
  set f := ∑ j ∈ Finset.range n, ((T.MPr (m + 1) h1).sem (fl.getD j O1.zero) : L) * θ ^ j
    with hfdef
  set q := nkTau Fc ks m n fl (traceCodes Fc ks m (nkPC Fc ks m Pp)) with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := h1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hsemE : ∀ c0 : LC (m + 1), (((TE.MPr (m + 1) hTE).sem c0 : TE.F (m + 1)) : E₁) =
      ψ (((T.MPr (m + 1) h1).sem c0 : T.F (m + 1)) : L) := fun c0 ↦ by
    rw [MPr_sem, MPr_sem, TE.sem_MP, T.sem_MP, hTEev]
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  set S₁ := TE.nkCurve m hTE Pp hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec m hTEm Pp hsh
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  obtain ⟨ω, hx⟩ : ∃ ω : (TE.F m)[X], S₁.x′ = aeval S₁.x ω := by
    rcases hks : ks m with η | a
    · refine ⟨Polynomial.C (TE.val m η), ?_⟩
      rw [aeval_C]
      change (TE.ts m)′ = _
      rw [TE.ht m (by omega), hks]
      rfl
    · refine ⟨Polynomial.C ((TE.val m a)′) * X, ?_⟩
      rw [map_mul, aeval_C, aeval_X]
      change (TE.ts m)′ = _
      rw [TE.ht m (by omega), hks]
      rfl
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
  -- the Liouville form with constants in `C₁ = Fₘ`
  set U : ι → E₁ := fun i ↦ if i ∈ s' then u i else 1 with hU
  have hUm : ∀ i, U i ∈ T₁ := fun i ↦ by
    simp only [hU]; split_ifs with hi
    · exact hCT _ (hdata i hi).2.1
    · exact one_mem _
  have hU0 : ∀ i, U i ≠ 0 := fun i ↦ by
    simp only [hU]; split_ifs with hi
    · exact (hdata i hi).2.2
    · exact one_ne_zero
  set c₁ : ι → TE.F m := fun i ↦ if h : i ∈ s' then Classical.choose (hconstC (c i) (hdata i h).1)
    else 0 with hc₁
  have hc₁v : ∀ i ∈ s', algebraMap (TE.F m) E₁ (c₁ i) = c i := fun i hi ↦ by
    simp only [hc₁, dif_pos hi]
    exact Classical.choose_spec (hconstC (c i) (hdata i hi).1)
  have hc₁d : ∀ i, (c₁ i)′ = 0 := fun i ↦ by
    by_cases hi : i ∈ s'
    · apply (algebraMap (TE.F m) E₁).injective
      rw [← deriv_algebraMap, hc₁v i hi, (hdata i hi).1, map_zero]
    · simp only [hc₁, dif_neg hi, Derivation.map_zero]
  have hfT : ψ f ∈ T₁ := hLT f
  have heqT : ψ f = v′ + ∑ i ∈ s', algebraMap (TE.F m) E₁ (c₁ i) * ((U i)′ / U i) := by
    rw [show ψ f = _ from heqL, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [hU, if_pos hi, hc₁v i hi, logDeriv]
  obtain ⟨w, hw, Nn, hN, htr⟩ := S₁.trace_liouville ω hx s' c₁ hc₁d U hUm hU0 v
    (ψ f) (hCT v hv) hfT heqT
  -- the trace, computed from the codes
  have hn0 : 0 < n := hsp.1
  have hμ : (minpoly ((TE.F m)⟮S₁.x⟯) S₁.y).natDegree = n := by rw [S₁.natDegree_minpoly, hS₁F]
  set pb := IntermediateField.adjoin.powerBasis (K := ((TE.F m)⟮S₁.x⟯)) S₁.isIntegral with hpb
  have hpbd : pb.dim = n := by rw [hpb, IntermediateField.adjoin.powerBasis_dim, hμ]
  have hpbg : pb.gen = AdjoinSimple.gen ((TE.F m)⟮S₁.x⟯) S₁.y := IntermediateField.adjoin.powerBasis_gen _
  have hμg : minpoly ((TE.F m)⟮S₁.x⟯) pb.gen = minpoly ((TE.F m)⟮S₁.x⟯) S₁.y := by rw [hpbg, IntermediateField.minpoly_gen]
  -- coefficient identity
  have hcoef : ∀ k l, l < n → ((((X ^ k : ((TE.F m)⟮S₁.x⟯)[X]) %ₘ minpoly ((TE.F m)⟮S₁.x⟯) S₁.y).coeff l : ((TE.F m)⟮S₁.x⟯)) : E₁) =
      (((TE.MPr (m + 1) hTE).sem ((remP O1 (nkPC Fc ks m Pp) (xPowC O1 k)).getD l O1.zero) :
        TE.F (m + 1)) : E₁) := by
    intro k l hl
    have hP' : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
    have e1 := TE.pow_eq_remP m hTE Pp (ψ θ) hP' hn0 k
    have hmon := minpoly.monic S₁.isIntegral
    set r := (X ^ k : ((TE.F m)⟮S₁.x⟯)[X]) %ₘ minpoly ((TE.F m)⟮S₁.x⟯) S₁.y with hr
    have e2 : S₁.y ^ k = ∑ l ∈ Finset.range n, ((r.coeff l : ((TE.F m)⟮S₁.x⟯)) : E₁) * S₁.y ^ l := by
      have h := modByMonic_add_div (X ^ k : ((TE.F m)⟮S₁.x⟯)[X]) (minpoly ((TE.F m)⟮S₁.x⟯) S₁.y)
      have h2 := congrArg (aeval S₁.y) h
      rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero, map_pow, aeval_X] at h2
      rw [← h2]
      have hlt : r.natDegree < n := by
        by_cases h0 : r = 0
        · rw [h0, natDegree_zero]; exact hn0
        · rw [← hμ]; exact natDegree_modByMonic_lt _ hmon (minpoly.ne_one _ _)
      rw [aeval_eq_sum_range' hlt]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [Algebra.smul_def]; rfl
    have hz : ∑ l ∈ Finset.range S₁.F.natDegree, (((r.coeff l : ((TE.F m)⟮S₁.x⟯)) : E₁) -
        (((TE.MPr (m + 1) hTE).sem ((remP O1 (nkPC Fc ks m Pp) (xPowC O1 k)).getD l O1.zero) :
          TE.F (m + 1)) : E₁)) * S₁.y ^ l = 0 := by
      rw [hS₁F]
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [← e2]
      change S₁.y ^ k - _ = 0
      rw [sub_eq_zero]
      exact e1
    have := S₁.coords_uniqueG _ (fun i _ ↦ sub_mem (SetLike.coe_mem _)
      ((TE.mem_F_succ).mp (SetLike.coe_mem _))) hz l (by rw [hS₁F]; exact hl)
    exact sub_eq_zero.mp this
  -- `ψ f` in the power basis
  have hfm : ∀ j, ψ (((T.MPr (m + 1) h1).sem (fl.getD j O1.zero) : T.F (m + 1)) : L) ∈ ((TE.F m)⟮S₁.x⟯) :=
    fun j ↦ (TE.mem_F_succ).mp (hTEmem (m + 1) _ (SetLike.coe_mem _))
  have hfe : (⟨ψ f, hfT⟩ : T₁) = ∑ j ∈ Finset.range n,
      algebraMap ((TE.F m)⟮S₁.x⟯) T₁ ⟨ψ (((T.MPr (m + 1) h1).sem (fl.getD j O1.zero) : T.F (m + 1)) : L), hfm j⟩ *
        pb.gen ^ j := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change ψ f = _
    rw [hfdef, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, hpbg, AdjoinSimple.coe_gen, map_mul,
      map_pow]
    rfl
  have htrv : ((Algebra.trace ((TE.F m)⟮S₁.x⟯) T₁ ⟨ψ f, hfT⟩ : ((TE.F m)⟮S₁.x⟯)) : E₁) = ∑ j ∈ Finset.range n,
      ψ (((T.MPr (m + 1) h1).sem (fl.getD j O1.zero) : T.F (m + 1)) : L) *
        ψ (((T.MPr (m + 1) h1).sem ((traceCodes Fc ks m (nkPC Fc ks m Pp)).getD j O1.zero) :
          T.F (m + 1)) : L) := by
    rw [hfe, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← Algebra.smul_def, map_smul, PowerBasis.trace_gen_pow, smul_eq_mul, IntermediateField.coe_mul,
      AddSubmonoidClass.coe_finsetSum, hpbd, hμg]
    congr 1
    rw [← hsemE, traceCodes, NestTower.getD_range_map _ _ (by rw [length_nkPC]; exact Finset.mem_range.mp hj),
      length_nkPC, TE.sem_lsum_range m hTE, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k hk ↦ hcoef _ _ (Finset.mem_range.mp hk)
  -- `ψ (τ(f)/n) = Tr(ψ f)/n` is a Liouville form in `E₁`
  have hnE : (n : E₁) ≠ 0 := by exact_mod_cast hn0.ne'
  have hqv : ψ (T.ev (m + 1) q) = ((Algebra.trace ((TE.F m)⟮S₁.x⟯) T₁ ⟨ψ f, hfT⟩ : ((TE.F m)⟮S₁.x⟯)) : E₁) / n := by
    rw [htrv, ← T.coe_sem_MPr (m + 1) h1 q, hq, T.sem_nkTau m n h1, div_eq_mul_inv]
    push_cast
    rw [map_mul, map_sum, map_inv₀, map_natCast]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_mul]
  set l : List (E₁ × E₁) := s'.toList.map fun i ↦ (algebraMap (TE.F m) E₁ (c₁ i) / n, Nn i)
    with hl0
  have hninv : ((n : E₁)⁻¹)′ = 0 := by
    have h := congrArg (fun z : E₁ ↦ z′) (mul_inv_cancel₀ hnE)
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_natCast, mul_zero, add_zero,
      Derivation.map_one_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hnE
  have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    refine ⟨?_, (hN i).2⟩
    rw [div_eq_mul_inv, Derivation.leibniz, deriv_algebraMap, hc₁d i, map_zero, smul_zero,
      add_zero, hninv, smul_zero]
  have hform := hasElementaryIntegral_of_liouville_form (w / n) l hl
  have hsumeq : (w / n)′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = algebraMap L E₁ (T.ev (m + 1) q) := by
    rw [← hψ, hqv, htr, hl0, List.map_map, Finset.sum_map_toList, add_div, Finset.sum_div]
    congr 1
    · rw [div_eq_mul_inv, div_eq_mul_inv, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hninv,
        mul_zero, zero_add, mul_comm]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Function.comp_apply, logDeriv]
      ring
  rw [hsumeq] at hform
  exact HasElementaryIntegral.of_extension hE₁ hform

set_option maxHeartbeats 4000000 in
-- elM at the top level plus the algebraic invariance of elementary integrability
/-- **The trace test as a decision**: at every large search bound `elM` answers on `Tr(f)/n`,
and a negative answer proves that `∫ f` is not elementary (any poles, any residues). -/
theorem nk_trace_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (fl : List (LC (m + 1))) (h1 : T.Tr (m + 1)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length fl (traceCodes Fc ks m (nkPC Fc ks m Pp))) N = some b ∧
      (b = false → ¬ HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) h1).sem (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j)) := by
  classical
  set q := nkTau Fc ks m Pp.length fl (traceCodes Fc ks m (nkPC Fc ks m Pp))
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hshF T' (m + 1) hT'n hc hT'gen q
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
  refine ⟨b, hb, fun hbf hf ↦ ?_⟩
  have := T.nk_trace_nec hmon hdeg m hn hc Pp hsh θ hθ hgen fl h1 hf
  rw [h0, hiff, hbf] at this
  exact Bool.false_ne_true this

end MTower

end Curves.MT
