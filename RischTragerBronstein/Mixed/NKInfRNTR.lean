import RischTragerBronstein.Mixed.NKInfRNExp
import RischTragerBronstein.Mixed.NKExactTRLExists
import RischTragerBronstein.Mixed.NKExpDecideTRE
import RischTragerBronstein.Mixed.NKSearchTRL
import RischTragerBronstein.Mixed.NKDecidesTR

/-!
# Several places at infinity with the rescaled parametric exact tests

The decisions `nk_iffRN` (logarithmic level) and `nk_iffETRN` (exponential level) with the
parametric exact tests `exactTRL`, `exactTREL` (a basis `w = T θ` rescaled at infinity, and at an
exponential level conjugated by a constant `C`), correct for all parameters: `nk_iffRNTR`,
`nk_iffETRNTRE`. For constant curves the parameters for which these tests answer exist
(`exactTRL_exists`, `exactTREL_exists`), so no basis has to be supplied.
-/

open Polynomial IntermediateField NCodes

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`⇐`** (several places at infinity, units over `ℚ(α)`), from an exact `f − τ(f)/n − ∑ cᵢ gᵢ`. -/
theorem nk_sufficientRNex (m : ℕ) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1))))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (fp : List (GPoly (LC m)))
    (hex : ∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range ((nkPC Fc ks m Pp).length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
          (((T.MPr (m + 1) h1).sem ((nkRest Fc ks m (nkFl Fc ks m fp)
            (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)).getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gss.flatten.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gss.flatten.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θ ^ j)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  obtain ⟨hd, hall⟩ := unitsRNC_spec hU
  have hgl : ∀ i < gss.length, (gss.getD i []).length = μ.length := fun i hi ↦ (hall i hi).2.2.1
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind' : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact hind
  obtain ⟨c, Y, hY⟩ := hex
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hS := T.evθ_RSem m h1 θ
  set αL : Fin μ.length → L := fun i ↦ algebraMap Cc L (αs i) with hαL
  have hμL : ∀ i, αL i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : L) * αL i ^ l = 0 :=
    fun i ↦ by
      have := congrArg (algebraMap Cc L) (hαμ i)
      simpa [map_add, map_sum, map_mul, map_pow, map_intCast] using this
  have hαc : ∀ i, (αL i)′ = 0 := fun i ↦ by rw [hαL]; simp only; rw [deriv_algebraMap, T.hC, map_zero]
  -- the conjugate units `u_{p j}`
  set u : ℕ → Fin μ.length → L := fun p i ↦
    nVal (T.evθ m h1 θ) (αL i) ((Ass.getD p []).map (nkFl Fc ks m)) with hu
  have hu0 : ∀ p < gss.length, ∀ i, u p i ≠ 0 := fun p hp i ↦
    left_ne_zero_of_mul_eq_one (T.unitCN_sound m h1 θ Pp hP μ hd (αL i) (hμL i) _ _
      (hall p hp).1)
  set G : ℕ → ℕ → L := fun p k ↦ T.evθ m h1 θ ((gss.getD p []).getD k []) with hG
  have hGk : ∀ p < gss.length, ∀ k : Fin μ.length, G p k = ∑ i : Fin μ.length,
      algebraMap Cc L ((Matrix.vandermonde αs)⁻¹ k i) * logDeriv (u p i) := by
    intro p hp k
    refine gk_eq_sum αs hαinj (fun k : Fin μ.length ↦ G p k) (fun i ↦ logDeriv (u p i))
      (fun i ↦ ?_) k
    rw [logDeriv, T.logDerChkN_sound m h1 θ Pp hP μ hd (αL i) (hαc i) (hμL i) _ _ dθ wθ
        (hall p hp).2.1, mul_div_assoc, div_self (hu0 p hp i), mul_one,
      nVal_eq_sum hS (αL i) _ μ.length (hgl p hp).le,
      ← Fin.sum_univ_eq_sum_range (fun k ↦ αL i ^ k * T.evθ m h1 θ
        ((gss.getD p []).getD k (θOps Fc ks m).zero))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_pow]; rfl
  -- the exact part
  have hflen := length_flatten_mul μ.length gss hgl
  have hg : ∑ j ∈ Finset.range Pp.length, (∑ q ∈ Finset.range gss.flatten.length,
      algebraMap Cc L (c q) * ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) :
        T.F (m + 1)) : L)) * θ ^ j =
      ∑ p ∈ Finset.range gss.length, ∑ k : Fin μ.length,
        algebraMap Cc L (c (p * μ.length + k)) * G p k := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, hflen, sum_range_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hp' := Finset.mem_range.mp hp
    rw [getD_flatten_mul μ.length [] gss hgl p hp' k k.2, hG]
    simp only
    rw [T.evθ_list_le m h1 θ _ Pp.length ((hall p hp').2.2.2 k k.2).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlen] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRest m h1 Pp.length hn0] at hY
  set e : ℕ → Fin μ.length → Cc := fun p i ↦
    ∑ k : Fin μ.length, c (p * μ.length + k) * (Matrix.vandermonde αs)⁻¹ k i with he
  have hlog : ∑ p ∈ Finset.range gss.length, ∑ k : Fin μ.length,
      algebraMap Cc L (c (p * μ.length + k)) * G p k =
      ∑ p ∈ Finset.range gss.length, ∑ i : Fin μ.length, algebraMap Cc L (e p i) *
        logDeriv (u p i) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    simp only [hGk p (Finset.mem_range.mp hp), Finset.mul_sum, he, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by rw [map_mul]; ring
  rw [hlog] at hY
  set pairs : List (ℕ × Fin μ.length) :=
    (List.range gss.length).flatMap fun p ↦ (List.finRange μ.length).map fun i ↦ (p, i) with hpairs
  have hpsum : ∀ F : ℕ → Fin μ.length → L, (pairs.map fun q ↦ F q.1 q.2).sum =
      ∑ p ∈ Finset.range gss.length, ∑ i : Fin μ.length, F p i := by
    intro F
    have hfm : ∀ l : List ℕ, ((l.flatMap fun p ↦ (List.finRange μ.length).map fun i ↦ (p, i)).map
        fun q ↦ F q.1 q.2).sum = (l.map fun p ↦ (((List.finRange μ.length).map fun i ↦ (p, i)).map
          fun q ↦ F q.1 q.2).sum).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
          List.sum_cons]
    rw [hpairs, hfm, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [List.map_map, Fin.sum_univ_def]
    rfl
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ +
          (pairs.map fun q ↦ algebraMap Cc L (e q.1 q.2) * logDeriv (u q.1 q.2)).sum by
    rw [hpsum (fun p i ↦ algebraMap Cc L (e p i) * logDeriv (u p i)), hY]; ring]
  refine (hq.add_in (hasElementaryIntegralIn_deriv _)).add_in ?_
  exact hasElementaryIntegralIn_logSum (fun q ↦ algebraMap Cc L (e q.1 q.2)) (fun q ↦ u q.1 q.2)
    pairs (fun q hq ↦ ⟨by rw [deriv_algebraMap, T.hC, map_zero], hu0 q.1 (by
      rw [hpairs, List.mem_flatMap] at hq
      obtain ⟨p, hp, hq'⟩ := hq
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq'
      exact List.mem_range.mp hp) q.2⟩)

set_option maxHeartbeats 16000000 in
/-- **`⇒`** (several places at infinity, units over `ℚ(α)`, logarithmic level). -/
theorem nk_necessaryRNTR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ}) (α : Cc)
    (hαμ : α ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * α ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTRL Fc ks m η (paramLimC Fc ks lv m) r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten = some res)
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
  -- the inverted curve and its place data
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
  obtain ⟨Fc', Pc, hFc', hPcc, hfib1, hpl, hα0⟩ := hpd
  have hmon' : (toB Fc').Monic := by rw [hFc']; exact hGm.map _
  have hn0' : 0 < (toB Fc').natDegree := by
    rw [hFc', natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ F).injective), hGn]
    exact hn0
  have hPcd : Pc.Facts Fc' (toB Fc').natDegree := Pc.check_spec hPcc
  have hSF' : (mobCurve S₁ 0 k0 M hMb hGm' hGn').F = (toB Fc').map (mapRingHom ιF) := by
    show invP (shiftP S₁.F 0) k0 M = _
    rw [hinvEq, hFc', Polynomial.map_map, mapRingHom_comp,
      ratHom_eq (ιF.comp (algebraMap ℚ F)) (algebraMap ℚ (TE.F m))]
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := by
    rw [hS₁Q, Polynomial.map_map, mapRingHom_comp, ratHom_eq ((algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))).comp (algebraMap ℚ (TE.F m))) (algebraMap ℚ _)]
    exact hgeo _
  -- the unit `u₀`, its inverse and its logarithmic derivative
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  have hevPol : ∀ W : List (GPoly (LC m)), S₁.evXY (∑ j ∈ Finset.range W.length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (W.getD j [])) * X ^ j) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m W) := by
    intro W
    rw [TE.evθ_nkFl m hTE (ψ θ) W, CurveData.evXY, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
      eval_C, eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  obtain ⟨hd, hall⟩ := unitsRNC_spec hU
  have hgl : ∀ i < gss.length, (gss.getD i []).length = μ.length := fun i hi ↦ (hall i hi).2.2.1
  set k := gss.length with hkk
  set αL : E₁ := ψ (algebraMap Cc L α) with hαL
  have hαc : αL′ = 0 := by rw [hαL, deriv_algebraMap, deriv_algebraMap, T.hC, map_zero, map_zero]
  set α' : Differential.constants E₁ := ⟨αL, hαc⟩ with hα'
  set αE : TE.F m := ⟨αL, TE.const_mem m α'⟩ with hαE
  have hμE : αL ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : E₁) * αL ^ l = 0 := by
    have := congrArg (fun z ↦ ψ (algebraMap Cc L z)) hαμ
    simpa [map_add, map_sum, map_mul, map_pow, map_intCast] using this
  have hevHom : ∀ Q : (TE.F m)[X][X], S₁.evXY Q = ((Polynomial.evalRingHom S₁.y).comp
      (Polynomial.mapRingHom (aeval S₁.x).toRingHom)) Q := fun Q ↦ rfl
  have hevα : S₁.evXY (Polynomial.C (Polynomial.C αE)) = αL := by
    rw [CurveData.evXY, Polynomial.map_C, eval_C]
    simp [hαE, hαL]
  have hgetD : ∀ (Ws : List (List (GPoly (LC m)))) (k : ℕ),
      (Ws.map (nkFl Fc ks m)).getD k [] = nkFl Fc ks m (Ws.getD k []) := fun Ws k ↦ by
    rw [show ([] : List (LC (m + 1))) = nkFl Fc ks m [] from rfl, List.getD_map]
  have hevN : ∀ Ws : List (List (GPoly (LC m))), S₁.evXY (∑ k ∈ Finset.range Ws.length,
      Polynomial.C (Polynomial.C αE) ^ k * ∑ j ∈ Finset.range (Ws.getD k []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) ((Ws.getD k []).getD j [])) * X ^ j) =
      nVal (TE.evθ m hTE (ψ θ)) αL (Ws.map (nkFl Fc ks m)) := by
    intro Ws
    rw [nVal_eq_sum (TE.evθ_RSem m hTE (ψ θ)) αL _ Ws.length (by simp), hevHom, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, ← hevHom, ← hevHom, hevα, hevPol]
    congr 1
    exact congrArg (TE.evθ m hTE (ψ θ)) (hgetD Ws k).symm
  set UQ : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ kk ∈ Finset.range (Ass.getD i []).length,
      Polynomial.C (Polynomial.C αE) ^ kk * ∑ j ∈ Finset.range ((Ass.getD i []).getD kk []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (((Ass.getD i []).getD kk []).getD j [])) * X ^ j
    with hUQ
  set VQ : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ kk ∈ Finset.range (Bss.getD i []).length,
      Polynomial.C (Polynomial.C αE) ^ kk * ∑ j ∈ Finset.range ((Bss.getD i []).getD kk []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (((Bss.getD i []).getD kk []).getD j [])) * X ^ j
    with hVQ
  set u0T : Fin k → T₁ := fun i ↦ S₁.evT (UQ i) with hu0T
  set v0T : Fin k → T₁ := fun i ↦ S₁.evT (VQ i) with hv0T
  have hu0v : ∀ i : Fin k, (u0T i : E₁) =
      nVal (TE.evθ m hTE (ψ θ)) αL ((Ass.getD i []).map (nkFl Fc ks m)) := fun i ↦ by
    rw [hu0T]; simp only; rw [S₁.coe_evT, hUQ]; simp only; rw [hevN]
  have hv0v : ∀ i : Fin k, (v0T i : E₁) =
      nVal (TE.evθ m hTE (ψ θ)) αL ((Bss.getD i []).map (nkFl Fc ks m)) := fun i ↦ by
    rw [hv0T]; simp only; rw [S₁.coe_evT, hVQ]; simp only; rw [hevN]
  have huvE : ∀ i : Fin k, (u0T i : E₁) * (v0T i : E₁) = 1 := fun i ↦ by
    rw [hu0v, hv0v]; exact TE.unitCN_sound m hTE (ψ θ) Pp hPθE μ hd αL hμE _ _ (hall i i.2).1
  have huv1 : ∀ i, u0T i * v0T i = 1 := fun i ↦
    Subtype.ext (by rw [IntermediateField.coe_mul, huvE]; rfl)
  have hu00 : ∀ i, u0T i ≠ 0 := fun i ↦ left_ne_zero_of_mul_eq_one (huv1 i)
  have hu0E : ∀ i, (u0T i : E₁) ≠ 0 := fun i h ↦ hu00 i (Subtype.ext h)
  have hfin0 : ∀ i (a : AlgebraicClosure (TE.F m)) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l),
      (S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S₁.root_of_mem hl hr) (u0T i)).order = 0 := by
    intro i a N hN l hl r hr
    set φ := S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S₁.root_of_mem hl hr)
    have h1 : φ (u0T i) * φ (v0T i) = 1 := by rw [← map_mul, huv1, map_one]
    have hu' : φ (u0T i) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hv' : φ (v0T i) ≠ 0 := right_ne_zero_of_mul_eq_one h1
    have o1 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (UQ i) a N hN l hl r hr
    have o2 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (VQ i) a N hN l hl r hr
    have ho := congrArg HahnSeries.order h1
    rw [HahnSeries.order_mul hu' hv', HahnSeries.order_one] at ho
    change 0 ≤ (φ (u0T i)).order at o1
    change 0 ≤ (φ (v0T i)).order at o2
    omega
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set G : ℕ → ℕ → E₁ := fun i j ↦ ∑ kk ∈ Finset.range μ.length, αL ^ kk *
    ((M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) : TE.F (m + 1)) : E₁) with hG
  have hαmem : αL ∈ (TE.F m)⟮S₁.x⟯ := IntermediateField.algebraMap_mem _ αE
  have hGmem : ∀ i j, G i j ∈ (TE.F m)⟮S₁.x⟯ := fun i j ↦ sum_mem fun kk _ ↦
    mul_mem (pow_mem hαmem _) ((TE.mem_F_succ).mp (M1.sem (((gss.getD i []).getD kk []).getD j
      O1.zero)).2)
  have hlogN : ∀ i : Fin k, (u0T i : E₁)′ =
      nVal (TE.evθ m hTE (ψ θ)) αL (gss.getD i []) * (u0T i : E₁) := fun i ↦ by
    rw [hu0v]
    exact TE.logDerChkN_sound m hTE (ψ θ) Pp hPθE μ hd αL hαc hμE _ _ dθ wθ (hall i i.2).2.1
  have hnVg : ∀ i : Fin k, nVal (TE.evθ m hTE (ψ θ)) αL (gss.getD i []) =
      ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j := by
    intro i
    rw [nVal_eq_sum (TE.evθ_RSem m hTE (ψ θ)) αL _ μ.length (hgl i i.2).le]
    simp only [hG, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun kk hk ↦ ?_
    change αL ^ kk * TE.evθ m hTE (ψ θ) ((gss.getD i []).getD kk []) = _
    rw [TE.evθ_list_le m hTE (ψ θ) _ n ((hall i i.2).2.2.2 kk (Finset.mem_range.mp hk)).1,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hlogu : ∀ i : Fin k, logDeriv (u0T i : E₁) = ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j :=
    fun i ↦ by rw [logDeriv, hlogN i, mul_div_assoc, div_self (hu0E i), mul_one, hnVg i]
  have hindθ := TE.nkCurveG_ind m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE
  have hindU : ∀ a : Fin k → ℤ, (∃ c : TE.F m, ∏ i, (u0T i : E₁) ^ a i =
      algebraMap (TE.F m) E₁ c) → a = 0 :=
    TE.indepCN_sound m hTE (ψ θ) n hindθ μ hd αL αE.2 hμE gss hgl
      (fun i hi kk hkk ↦ ((hall i hi).2.2.2 kk hkk).1) (fun i ↦ (u0T i : E₁)) hu0E
      (fun i ↦ by rw [hlogN i, mul_div_assoc, div_self (hu0E i), mul_one]) J H hJH
  -- the logarithmic part is `∑ κᵢ uᵢ′/uᵢ + ℓ`
  obtain ⟨κ, ℓ₀, hκ, hℓ₀⟩ := S₁.nk_liouville_units (K := AlgebraicClosure (TE.F m))
    (Polynomial.C η₁) hx hK hnd k0 M hMb hGm' hGn' hgeo' ιF Fc' hmon' hSF' Pc hPcd hn0' hfib1
    hα0 hpl u0T hu00 hfin0 hindU hconstC (ψ f) hfT hreg s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  set κE : Fin k → E₁ := fun i ↦ algebraMap (TE.F m) E₁ (κ i) with hκE
  have hκE' : ∀ i, (κE i)′ = 0 := fun i ↦ by
    rw [hκE]; simp only; rw [deriv_algebraMap, hκ i, map_zero]
  have hc0 : ∀ i, κE i ∈ Set.range (algebraMap _ E₁) := fun i ↦ TE.hconst _ (hκE' i)
  simp only [Set.mem_range] at hc0
  choose c0 hc0 using hc0
  have hκsum : ∀ w : ℕ → E₁, ∑ j ∈ Finset.range n, (∑ i : Fin k, κE i * G i j) * w j =
      ∑ i : Fin k, κE i * ∑ j ∈ Finset.range n, G i j * w j := fun w ↦ by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- the trace
  obtain ⟨hs0, hτ⟩ := TE.traceW_sound m hTE Pp (ψ θ) hPθE dθ wθ s hs
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  have hκx : ∀ i, κE i ∈ (TE.F m)⟮S₁.x⟯ := fun i ↦ IntermediateField.algebraMap_mem _ (κ i)
  set fc : ℕ → E₁ := fun j ↦ TE.evP m (fp.getD j []) - ∑ i : Fin k, κE i * G i j with hfc
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
    hdx fc (fun j ↦ sub_mem ((TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
      (sum_mem fun i _ ↦ mul_mem (hκx i) (hGmem i j)))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, fc j * (ψ θ) ^ j = _
      simp only [hfc, sub_mul, Finset.sum_sub_distrib]
      rw [hκsum, ← hψf, hℓ₀]
      simp only [← hlogu, hκE]
      ring)
  rw [hS₁F] at hwe
  -- `τ(uᵢ′/uᵢ) = 0`
  have hτ0 : ∀ i : Fin k, ∑ j ∈ Finset.range n, G i j *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
    intro i
    have hk0 : ∀ kk < μ.length, ∑ j ∈ Finset.range n,
        ((M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) : TE.F (m + 1)) : E₁) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
      intro kk hkk
      have h1 := (M1.isZero_iff _).mp ((hall i i.2).2.2.2 kk hkk).2
      rw [TE.sem_nkTau m n hTE ((gss.getD i []).getD kk []) s] at h1
      have hn' : ((n : ℕ) : TE.F (m + 1)) ≠ 0 := by exact_mod_cast hn0.ne'
      have h2 : ∑ j ∈ Finset.range n, M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) *
          M1.sem (s.getD j O1.zero) = 0 :=
        (mul_eq_zero.mp h1).resolve_right (inv_ne_zero hn')
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) h2
      simpa only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        ZeroMemClass.coe_zero] using this
    simp only [hG, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun kk hk ↦ ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hk0 kk (Finset.mem_range.mp hk), mul_zero]
  have hτf : ∑ j ∈ Finset.range n, fc j * ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) =
      ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) := by
    simp only [hfc, sub_mul, Finset.sum_sub_distrib]
    rw [hκsum, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin k))) fun i _ ↦ by
      rw [hτ0 i, mul_zero], sub_zero]
  rw [hτf] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ =
      ∑ i ∈ s', c i * logDeriv (u i) - ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
    have := hℓ₀.symm.trans heq₁
    rw [eq_sub_iff_add_eq]
    linear_combination this
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
    have hiff := TE.exactTRL_correct hTE (by rw [hTEn, hn]; omega) hk (hTE m (by omega))
      (paramLimC Fc ks lv m) MSEm.lim r (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind Tc Ti gss.flatten res hres
    set c' := fun q ↦ if h : q / μ.length < k then c0 ⟨q / μ.length, h⟩ * α' ^ (q % μ.length)
      else 0 with hc'
    refine hiff.mpr ⟨c', fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [TE.sum_nkRest m hTE n hn0, hTEev (m + 1) q]
    have hflen := length_flatten_mul μ.length gss hgl
    have hcs : ∑ j ∈ Finset.range n, (∑ q ∈ Finset.range gss.flatten.length, algebraMap _ E₁
        (c' q) * ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) : TE.F (m + 1)) : E₁)) *
        (ψ θ) ^ j = ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
      have e : ∀ j, ∑ q ∈ Finset.range gss.flatten.length, algebraMap _ E₁ (c' q) *
          ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) : TE.F (m + 1)) : E₁) =
          ∑ i : Fin k, κE i * G i j := fun j ↦ by
        rw [hflen, sum_range_mul, ← Fin.sum_univ_eq_sum_range (fun i ↦ ∑ kk ∈ Finset.range μ.length,
          algebraMap _ E₁ (c' (i * μ.length + kk)) * ((M1.sem ((gss.flatten.getD (i * μ.length + kk)
            []).getD j O1.zero) : TE.F (m + 1)) : E₁))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [hG, Finset.mul_sum]
        refine Finset.sum_congr rfl fun kk hkk ↦ ?_
        have hkk' := Finset.mem_range.mp hkk
        have hdiv : (i * μ.length + kk) / μ.length = i := by
          rw [show (i : ℕ) * μ.length + kk = kk + μ.length * i by ring,
            Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hkk', zero_add]
        have hmod : (i * μ.length + kk) % μ.length = kk := by
          rw [show (i : ℕ) * μ.length + kk = kk + μ.length * i by ring, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hkk']
        rw [getD_flatten_mul μ.length [] gss hgl i i.2 kk hkk', hc']
        simp only [hdiv, hmod]
        rw [dif_pos i.2]
        simp only [Fin.eta, map_mul, map_pow, hc0]
        have hαα : algebraMap (Differential.constants E₁) E₁ α' = αL := rfl
        rw [hαα]; ring
      simp only [e]
      rw [hκsum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hlogu]
    rw [hcs]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map (fun i ↦ (c i, u i)) ++
      (List.finRange k).map (fun i ↦ (-κE i, (u0T i : E₁))) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        rw [Finset.mem_toList] at hi
        exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
        exact ⟨by rw [map_neg, hκE' i, neg_zero], hu0E i⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_append, List.sum_append, List.map_map,
        Finset.sum_map_toList, List.map_map, ← Fin.sum_univ_def]
      simp only [Function.comp_def, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform



set_option maxHeartbeats 16000000 in
/-- **`⇒`** (several places at infinity, units over `ℚ(α)`, exponential level). -/
theorem nk_necessaryETRNTRE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (hsh0 : nkShape0 Fc ks m Pp = true) (ha0Q : (toB Fq).coeff 0 ≠ 0)
    (θ : L) {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ}) (α : Cc)
    (hαμ : α ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * α ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ))
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTREL Fc ks m a (rdeE Fc ks lv m) r N0 C Ci (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten = some res)
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
  set η₁ : TE.F m := (TE.val m a)′ with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁ * X) := by
    rw [map_mul, aeval_C, aeval_X]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m), α ≠ 0 →
      α′ ≠ ((Polynomial.C η₁ * X).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α hα ↦ by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X]
      refine not_exp_of_integral η₁ (fun dd hdd z hz h ↦ ?_) α (Algebra.IsIntegral.isIntegral α) hα
      have := MSE.hyp.hom m (by omega) a hk (-(dd : ℤ)) (by omega) z hz
      apply this
      rw [h, show TE.val m a = TE.val m a from rfl]
      push_cast
      ring
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
  have hresF : ∀ (b : AlgebraicClosure (TE.F m)), b ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l) (k : ℤ), k < 1 - (N : ℤ) →
      (S₁.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S₁.root_of_mem hl hr) ⟨ψ f, hfT⟩).coeff k = 0 := by
    intro b _ N hN l hl r hr k hk
    apply HahnSeries.coeff_eq_zero_of_lt_order
    have := hreg b N hN l hl r hr
    have : (1 : ℤ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
    omega
  have hsp0 := TE.nkShape0_spec m hTEm Pp hsh0
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  -- the inverted curve and its place data
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
  obtain ⟨Fc', Pc, hFc', hPcc, hfib1, hpl, hα0⟩ := hpd
  have hmon' : (toB Fc').Monic := by rw [hFc']; exact hGm.map _
  have hn0' : 0 < (toB Fc').natDegree := by
    rw [hFc', natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ F).injective), hGn]
    exact hn0
  have hPcd : Pc.Facts Fc' (toB Fc').natDegree := Pc.check_spec hPcc
  have hSF' : (mobCurve S₁ 0 k0 M hMb hGm' hGn').F = (toB Fc').map (mapRingHom ιF) := by
    show invP (shiftP S₁.F 0) k0 M = _
    rw [hinvEq, hFc', Polynomial.map_map, mapRingHom_comp,
      ratHom_eq (ιF.comp (algebraMap ℚ F)) (algebraMap ℚ (TE.F m))]
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := by
    rw [hS₁Q, Polynomial.map_map, mapRingHom_comp, ratHom_eq ((algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))).comp (algebraMap ℚ (TE.F m))) (algebraMap ℚ _)]
    exact hgeo _
  -- the unit `u₀`, its inverse and its logarithmic derivative
  have ha0' : S₁.F.coeff 0 ≠ 0 := by
    rw [hS₁Q, coeff_map, coe_mapRingHom]
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ (TE.F m)).injective).mpr ha0Q
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  have hevPol : ∀ W : List (GPoly (LC m)), S₁.evXY (∑ j ∈ Finset.range W.length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (W.getD j [])) * X ^ j) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m W) := by
    intro W
    rw [TE.evθ_nkFl m hTE (ψ θ) W, CurveData.evXY, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
      eval_C, eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  obtain ⟨hd, hall⟩ := unitsRNC_spec hU
  have hgl : ∀ i < gss.length, (gss.getD i []).length = μ.length := fun i hi ↦ (hall i hi).2.2.1
  set k := gss.length with hkk
  set αL : E₁ := ψ (algebraMap Cc L α) with hαL
  have hαc : αL′ = 0 := by rw [hαL, deriv_algebraMap, deriv_algebraMap, T.hC, map_zero, map_zero]
  set α' : Differential.constants E₁ := ⟨αL, hαc⟩ with hα'
  set αE : TE.F m := ⟨αL, TE.const_mem m α'⟩ with hαE
  have hμE : αL ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : E₁) * αL ^ l = 0 := by
    have := congrArg (fun z ↦ ψ (algebraMap Cc L z)) hαμ
    simpa [map_add, map_sum, map_mul, map_pow, map_intCast] using this
  have hevHom : ∀ Q : (TE.F m)[X][X], S₁.evXY Q = ((Polynomial.evalRingHom S₁.y).comp
      (Polynomial.mapRingHom (aeval S₁.x).toRingHom)) Q := fun Q ↦ rfl
  have hevα : S₁.evXY (Polynomial.C (Polynomial.C αE)) = αL := by
    rw [CurveData.evXY, Polynomial.map_C, eval_C]
    simp [hαE, hαL]
  have hgetD : ∀ (Ws : List (List (GPoly (LC m)))) (k : ℕ),
      (Ws.map (nkFl Fc ks m)).getD k [] = nkFl Fc ks m (Ws.getD k []) := fun Ws k ↦ by
    rw [show ([] : List (LC (m + 1))) = nkFl Fc ks m [] from rfl, List.getD_map]
  have hevN : ∀ Ws : List (List (GPoly (LC m))), S₁.evXY (∑ k ∈ Finset.range Ws.length,
      Polynomial.C (Polynomial.C αE) ^ k * ∑ j ∈ Finset.range (Ws.getD k []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) ((Ws.getD k []).getD j [])) * X ^ j) =
      nVal (TE.evθ m hTE (ψ θ)) αL (Ws.map (nkFl Fc ks m)) := by
    intro Ws
    rw [nVal_eq_sum (TE.evθ_RSem m hTE (ψ θ)) αL _ Ws.length (by simp), hevHom, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, ← hevHom, ← hevHom, hevα, hevPol]
    congr 1
    exact congrArg (TE.evθ m hTE (ψ θ)) (hgetD Ws k).symm
  set UQ : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ kk ∈ Finset.range (Ass.getD i []).length,
      Polynomial.C (Polynomial.C αE) ^ kk * ∑ j ∈ Finset.range ((Ass.getD i []).getD kk []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (((Ass.getD i []).getD kk []).getD j [])) * X ^ j
    with hUQ
  set VQ : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ kk ∈ Finset.range (Bss.getD i []).length,
      Polynomial.C (Polynomial.C αE) ^ kk * ∑ j ∈ Finset.range ((Bss.getD i []).getD kk []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (((Bss.getD i []).getD kk []).getD j [])) * X ^ j
    with hVQ
  set u0T : Fin k → T₁ := fun i ↦ S₁.evT (UQ i) with hu0T
  set v0T : Fin k → T₁ := fun i ↦ S₁.evT (VQ i) with hv0T
  have hu0v : ∀ i : Fin k, (u0T i : E₁) =
      nVal (TE.evθ m hTE (ψ θ)) αL ((Ass.getD i []).map (nkFl Fc ks m)) := fun i ↦ by
    rw [hu0T]; simp only; rw [S₁.coe_evT, hUQ]; simp only; rw [hevN]
  have hv0v : ∀ i : Fin k, (v0T i : E₁) =
      nVal (TE.evθ m hTE (ψ θ)) αL ((Bss.getD i []).map (nkFl Fc ks m)) := fun i ↦ by
    rw [hv0T]; simp only; rw [S₁.coe_evT, hVQ]; simp only; rw [hevN]
  have huvE : ∀ i : Fin k, (u0T i : E₁) * (v0T i : E₁) = 1 := fun i ↦ by
    rw [hu0v, hv0v]; exact TE.unitCN_sound m hTE (ψ θ) Pp hPθE μ hd αL hμE _ _ (hall i i.2).1
  have huv1 : ∀ i, u0T i * v0T i = 1 := fun i ↦
    Subtype.ext (by rw [IntermediateField.coe_mul, huvE]; rfl)
  have hu00 : ∀ i, u0T i ≠ 0 := fun i ↦ left_ne_zero_of_mul_eq_one (huv1 i)
  have hu0E : ∀ i, (u0T i : E₁) ≠ 0 := fun i h ↦ hu00 i (Subtype.ext h)
  have hfin0 : ∀ i (a : AlgebraicClosure (TE.F m)) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l),
      (S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S₁.root_of_mem hl hr) (u0T i)).order = 0 := by
    intro i a N hN l hl r hr
    set φ := S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S₁.root_of_mem hl hr)
    have h1 : φ (u0T i) * φ (v0T i) = 1 := by rw [← map_mul, huv1, map_one]
    have hu' : φ (u0T i) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hv' : φ (v0T i) ≠ 0 := right_ne_zero_of_mul_eq_one h1
    have o1 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (UQ i) a N hN l hl r hr
    have o2 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (VQ i) a N hN l hl r hr
    have ho := congrArg HahnSeries.order h1
    rw [HahnSeries.order_mul hu' hv', HahnSeries.order_one] at ho
    change 0 ≤ (φ (u0T i)).order at o1
    change 0 ≤ (φ (v0T i)).order at o2
    omega
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set G : ℕ → ℕ → E₁ := fun i j ↦ ∑ kk ∈ Finset.range μ.length, αL ^ kk *
    ((M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) : TE.F (m + 1)) : E₁) with hG
  have hαmem : αL ∈ (TE.F m)⟮S₁.x⟯ := IntermediateField.algebraMap_mem _ αE
  have hGmem : ∀ i j, G i j ∈ (TE.F m)⟮S₁.x⟯ := fun i j ↦ sum_mem fun kk _ ↦
    mul_mem (pow_mem hαmem _) ((TE.mem_F_succ).mp (M1.sem (((gss.getD i []).getD kk []).getD j
      O1.zero)).2)
  have hlogN : ∀ i : Fin k, (u0T i : E₁)′ =
      nVal (TE.evθ m hTE (ψ θ)) αL (gss.getD i []) * (u0T i : E₁) := fun i ↦ by
    rw [hu0v]
    exact TE.logDerChkN_sound m hTE (ψ θ) Pp hPθE μ hd αL hαc hμE _ _ dθ wθ (hall i i.2).2.1
  have hnVg : ∀ i : Fin k, nVal (TE.evθ m hTE (ψ θ)) αL (gss.getD i []) =
      ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j := by
    intro i
    rw [nVal_eq_sum (TE.evθ_RSem m hTE (ψ θ)) αL _ μ.length (hgl i i.2).le]
    simp only [hG, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun kk hk ↦ ?_
    change αL ^ kk * TE.evθ m hTE (ψ θ) ((gss.getD i []).getD kk []) = _
    rw [TE.evθ_list_le m hTE (ψ θ) _ n ((hall i i.2).2.2.2 kk (Finset.mem_range.mp hk)).1,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hlogu : ∀ i : Fin k, logDeriv (u0T i : E₁) = ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j :=
    fun i ↦ by rw [logDeriv, hlogN i, mul_div_assoc, div_self (hu0E i), mul_one, hnVg i]
  have hindθ := TE.nkCurveG_ind m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE
  have hindU : ∀ a : Fin k → ℤ, (∃ c : TE.F m, ∏ i, (u0T i : E₁) ^ a i =
      algebraMap (TE.F m) E₁ c) → a = 0 :=
    TE.indepCN_sound m hTE (ψ θ) n hindθ μ hd αL αE.2 hμE gss hgl
      (fun i hi kk hkk ↦ ((hall i hi).2.2.2 kk hkk).1) (fun i ↦ (u0T i : E₁)) hu0E
      (fun i ↦ by rw [hlogN i, mul_div_assoc, div_self (hu0E i), mul_one]) J H hJH
  -- the logarithmic part is `∑ κᵢ uᵢ′/uᵢ + ℓ`
  obtain ⟨κ, ℓ₀, hκ, hℓ₀⟩ := S₁.nk_liouvilleEU (K := AlgebraicClosure (TE.F m))
    (Polynomial.C η₁ * X) hx hK η₁ rfl hnd n _ hS₁F hn0 ha0' k0 M hMb hGm' hGn' hgeo' ιF Fc' hmon'
    hSF' Pc hPcd hn0' hfib1 hα0 hpl u0T hu00 hfin0 hindU hsp0.1 hsp0.2.1 hsp0.2.2 hconstC (ψ f) hfT
    hresF s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  set κE : Fin k → E₁ := fun i ↦ algebraMap (TE.F m) E₁ (κ i) with hκE
  have hκE' : ∀ i, (κE i)′ = 0 := fun i ↦ by
    rw [hκE]; simp only; rw [deriv_algebraMap, hκ i, map_zero]
  have hc0 : ∀ i, κE i ∈ Set.range (algebraMap _ E₁) := fun i ↦ TE.hconst _ (hκE' i)
  simp only [Set.mem_range] at hc0
  choose c0 hc0 using hc0
  have hκsum : ∀ w : ℕ → E₁, ∑ j ∈ Finset.range n, (∑ i : Fin k, κE i * G i j) * w j =
      ∑ i : Fin k, κE i * ∑ j ∈ Finset.range n, G i j * w j := fun w ↦ by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- the trace
  obtain ⟨hs0, hτ⟩ := TE.traceW_sound m hTE Pp (ψ θ) hPθE dθ wθ s hs
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  have hκx : ∀ i, κE i ∈ (TE.F m)⟮S₁.x⟯ := fun i ↦ IntermediateField.algebraMap_mem _ (κ i)
  set fc : ℕ → E₁ := fun j ↦ TE.evP m (fp.getD j []) - ∑ i : Fin k, κE i * G i j with hfc
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
    hdx fc (fun j ↦ sub_mem ((TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
      (sum_mem fun i _ ↦ mul_mem (hκx i) (hGmem i j)))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, fc j * (ψ θ) ^ j = _
      simp only [hfc, sub_mul, Finset.sum_sub_distrib]
      rw [hκsum, ← hψf, hℓ₀]
      simp only [← hlogu, hκE]
      ring)
  rw [hS₁F] at hwe
  -- `τ(uᵢ′/uᵢ) = 0`
  have hτ0 : ∀ i : Fin k, ∑ j ∈ Finset.range n, G i j *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
    intro i
    have hk0 : ∀ kk < μ.length, ∑ j ∈ Finset.range n,
        ((M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) : TE.F (m + 1)) : E₁) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
      intro kk hkk
      have h1 := (M1.isZero_iff _).mp ((hall i i.2).2.2.2 kk hkk).2
      rw [TE.sem_nkTau m n hTE ((gss.getD i []).getD kk []) s] at h1
      have hn' : ((n : ℕ) : TE.F (m + 1)) ≠ 0 := by exact_mod_cast hn0.ne'
      have h2 : ∑ j ∈ Finset.range n, M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) *
          M1.sem (s.getD j O1.zero) = 0 :=
        (mul_eq_zero.mp h1).resolve_right (inv_ne_zero hn')
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) h2
      simpa only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        ZeroMemClass.coe_zero] using this
    simp only [hG, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun kk hk ↦ ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hk0 kk (Finset.mem_range.mp hk), mul_zero]
  have hτf : ∑ j ∈ Finset.range n, fc j * ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) =
      ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) := by
    simp only [hfc, sub_mul, Finset.sum_sub_distrib]
    rw [hκsum, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin k))) fun i _ ↦ by
      rw [hτ0 i, mul_zero], sub_zero]
  rw [hτf] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ =
      ∑ i ∈ s', c i * logDeriv (u i) - ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
    have := hℓ₀.symm.trans heq₁
    rw [eq_sub_iff_add_eq]
    linear_combination this
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
    obtain ⟨hrdeE, homE⟩ := TE.expTRE_specs hmon hdeg m (by rw [hTEn]; exact hn) hc hk
    have hiff := TE.exactTREL_correct hTE (by rw [hTEn, hn]; omega) hk (hTE m (by omega))
      (rdeE Fc ks lv m) hrdeE homE r N0 C Ci (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind Tc Ti gss.flatten res
      hres
    set c' := fun q ↦ if h : q / μ.length < k then c0 ⟨q / μ.length, h⟩ * α' ^ (q % μ.length)
      else 0 with hc'
    refine hiff.mpr ⟨c', fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [TE.sum_nkRest m hTE n hn0, hTEev (m + 1) q]
    have hflen := length_flatten_mul μ.length gss hgl
    have hcs : ∑ j ∈ Finset.range n, (∑ q ∈ Finset.range gss.flatten.length, algebraMap _ E₁
        (c' q) * ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) : TE.F (m + 1)) : E₁)) *
        (ψ θ) ^ j = ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
      have e : ∀ j, ∑ q ∈ Finset.range gss.flatten.length, algebraMap _ E₁ (c' q) *
          ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) : TE.F (m + 1)) : E₁) =
          ∑ i : Fin k, κE i * G i j := fun j ↦ by
        rw [hflen, sum_range_mul, ← Fin.sum_univ_eq_sum_range (fun i ↦ ∑ kk ∈ Finset.range μ.length,
          algebraMap _ E₁ (c' (i * μ.length + kk)) * ((M1.sem ((gss.flatten.getD (i * μ.length + kk)
            []).getD j O1.zero) : TE.F (m + 1)) : E₁))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [hG, Finset.mul_sum]
        refine Finset.sum_congr rfl fun kk hkk ↦ ?_
        have hkk' := Finset.mem_range.mp hkk
        have hdiv : (i * μ.length + kk) / μ.length = i := by
          rw [show (i : ℕ) * μ.length + kk = kk + μ.length * i by ring,
            Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hkk', zero_add]
        have hmod : (i * μ.length + kk) % μ.length = kk := by
          rw [show (i : ℕ) * μ.length + kk = kk + μ.length * i by ring, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hkk']
        rw [getD_flatten_mul μ.length [] gss hgl i i.2 kk hkk', hc']
        simp only [hdiv, hmod]
        rw [dif_pos i.2]
        simp only [Fin.eta, map_mul, map_pow, hc0]
        have hαα : algebraMap (Differential.constants E₁) E₁ α' = αL := rfl
        rw [hαα]; ring
      simp only [e]
      rw [hκsum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hlogu]
    rw [hcs]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map (fun i ↦ (c i, u i)) ++
      (List.finRange k).map (fun i ↦ (-κE i, (u0T i : E₁))) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        rw [Finset.mem_toList] at hi
        exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
        exact ⟨by rw [map_neg, hκE' i, neg_zero], hu0E i⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_append, List.sum_append, List.map_map,
        Finset.sum_map_toList, List.map_map, ← Fin.sum_univ_def]
      simp only [Function.comp_def, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform



/-- **The decision with several places at infinity**, any basis (`exactTRL`; logarithmic level; units over `ℚ(α)`,
independent by `indepCN`, with `τ(gᵢₖ) = 0`). -/
theorem nk_iffRNTR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTRL Fc ks m η (paramLimC Fc ks lv m) r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  have hd := (unitsRNC_spec hU).1
  refine ⟨T.nk_necessaryRNTR hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ ιC k0 M hinv hGm
    hGn μ Ass Bss gss hpd dθ wθ s hU J H hJH hθ hgen (αs ⟨0, hd⟩) (hαμ _) hs fp r Tc Ti res hres,
    fun h ↦ ?_⟩
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind' : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  have hiff := T.exactTRL_correct hTr (by omega) hk (hTr m (by omega)) (paramLimC Fc ks lv m)
    MSm.lim r (nkPC Fc ks m Pp) _ θ hP hind' Tc Ti gss.flatten res hres
  exact T.nk_sufficientRNex m hTr (hTr m (by omega)) Pp hn0 θ hθ
    (T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ) μ Ass Bss gss dθ wθ s hU
    αs hαinj hαμ fp (hiff.mp h.1) h.2

/-- **The decision with several places at infinity**, any basis (`exactTREL`; exponential level, a single place above `t = 0`; units over `ℚ(α)`,
independent by `indepCN`, with `τ(gᵢₖ) = 0`). -/
theorem nk_iffETRNTRE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (hsh0 : nkShape0 Fc ks m Pp = true) (ha0Q : (toB Fq).coeff 0 ≠ 0)
    (θ : L) {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ))
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTREL Fc ks m a (rdeE Fc ks lv m) r N0 C Ci (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  have hd := (unitsRNC_spec hU).1
  refine ⟨T.nk_necessaryETRNTRE hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo hsh0 ha0Q θ ιC k0 M
    hinv hGm
    hGn μ Ass Bss gss hpd dθ wθ s hU J H hJH hθ hgen (αs ⟨0, hd⟩) (hαμ _) hs fp r N0 C Ci Tc Ti res hres,
    fun h ↦ ?_⟩
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind' : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  obtain ⟨hrde, hom⟩ := T.expTRE_specs hmon hdeg m hn hc hk
  have hiff := T.exactTREL_correct hTr (by omega) hk (hTr m (by omega)) (rdeE Fc ks lv m) hrde hom
    r N0 C Ci (nkPC Fc ks m Pp) _ θ hP hind' Tc Ti gss.flatten res hres
  exact T.nk_sufficientRNex m hTr (hTr m (by omega)) Pp hn0 θ hθ
    (T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ) μ Ass Bss gss dθ wθ s hU
    αs hαinj hαμ fp (hiff.mp h.1) h.2

set_option maxHeartbeats 8000000 in
/-- **The decision with several places at infinity, no basis supplied** (logarithmic level,
constant curve): for every large bound, `elM` decides `τ(f)/n` and `searchTRL` the exact part. -/
theorem nk_decidesRNTR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true) (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchTRL Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten N = some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
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
  have hPlen : (nkPC Fc ks m Pp).length = F0.natDegree + 1 := by
    have := length_nkPC (Fc := Fc) (ks := ks) m Pp; omega
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0 := by
    rw [← hlen]; exact T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  obtain ⟨A, B, Ai, Bi, r, hex⟩ := T.exactTRL_exists m hTr (by omega) hk (hTr m (by omega))
    (paramLimC Fc ks lv m) MSm.lim (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega)))
    F0 hF0 (by omega) (nkPC Fc ks m Pp) hPlen (T.nkPC_sem_const m hTr Pp F0 hF0 hlen hcoef) θ hP hind
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gss.flatten
  obtain ⟨B0, hB0⟩ := searchTRL_complete Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gss.flatten F0.natDegree (by omega) A B Ai Bi r hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨r', Tc, Ti, hex'⟩ := searchTRL_sound Fc ks m η _ _ _ _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffRNTR hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ ιC k0 M hinv hGm hGn μ Ass
    Bss gss hpd dθ wθ s hU J H hJH hθ hgen αs hαinj hαμ hs fp r' Tc Ti res hex', h0, hiff]

set_option maxHeartbeats 8000000 in
/-- **The decision with several places at infinity, no basis supplied** (exponential level,
constant curve, a single place above `t = 0`): `elM` and `searchTREL` decide. -/
theorem nk_decidesETRNTRE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (hsh0 : nkShape0 Fc ks m Pp = true) (ha0Q : (toB Fq).coeff 0 ≠ 0)
    (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true) (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchTREL Fc ks m a (rdeE Fc ks lv m) (nkPC Fc ks m Pp)
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten N = some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
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
  have hPlen : (nkPC Fc ks m Pp).length = F0.natDegree + 1 := by
    have := length_nkPC (Fc := Fc) (ks := ks) m Pp; omega
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0 := by
    rw [← hlen]; exact T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  have hb0 : (T.MP m hTr.of_succ).sem ((MO Fc ks m).deriv a) ≠ 0 := by
    have h1 := (T.expTRE_specs hmon hdeg m hn hc hk).2 1 one_ne_zero 1 one_ne_zero
    simpa using h1
  obtain ⟨A, B, Ai, Bi, r, N0, C, Ci, hex⟩ := T.exactTREL_exists m hTr (by omega) hk
    (hTr m (by omega)) (rdeE Fc ks lv m) hb0 F0 hF0 (by omega) (nkPC Fc ks m Pp) hPlen (T.nkPC_sem_const m hTr Pp F0 hF0 hlen hcoef) θ hP hind
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gss.flatten
  obtain ⟨B0, hB0⟩ := searchTREL_complete Fc ks m a (rdeE Fc ks lv m) (nkPC Fc ks m Pp)
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gss.flatten F0.natDegree (by omega) A B Ai Bi r N0 C Ci hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨r', N0', C', Ci', Tc, Ti, hex'⟩ := searchTREL_sound Fc ks m a _ _ _ _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETRNTRE hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo hsh0 ha0Q θ ιC k0 M hinv
    hGm hGn μ Ass Bss gss hpd dθ wθ s hU J H hJH hθ hgen αs hαinj hαμ hs fp r' N0' C' Ci' Tc Ti res
    hex', h0, hiff]

end MTower

end Curves.MT
