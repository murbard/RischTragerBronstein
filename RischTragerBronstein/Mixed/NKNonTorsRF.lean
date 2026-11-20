import RischTragerBronstein.Mixed.NKNonTors
import RischTragerBronstein.Mixed.KECodes

/-!
# Non-elementary integrals on curves over `N(x)`

The certificates of `nk_not_elementary` over the computable field `F = N(x)` (`RatFuncC N`, `N` a
computable field embedded in the constants by `ιC`), for towers over the line (`y = x`): the curve
`θⁿ + ∑ aᵢ(t) θⁱ` may then have coefficients depending on `x`, given by codes of level `0` and
translated to `F` by `trRF`. The realization `psiN : N(x) → L` (`x ↦ x`) sends `trRF q` to the
value of the code `q` (`psiN_trRF`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential

section Tr

variable (N : Type) [Field N] [DecidableEq N] [CharZero N]

/-- A fraction of `ℚ[x]` in `N(x)`. -/
def frRF (q : GFrac ℚ) : RFC.RatFuncC N :=
  RFC.mk (q.1.map (algebraMap ℚ N)) (q.2.map (algebraMap ℚ N))

/-- **A code of level `0` on the line `y = x`** as an element of `N(x)`. -/
def trRF (a : LC 0) : RFC.RatFuncC N :=
  a.foldr (fun q acc ↦ frRF N q + RFC.mk [0, 1] [1] * acc) 0

end Tr

section Checks

variable (N : Type) [Field N] [DecidableEq N] [CharZero N]

/-- The curve `Yⁿ + ∑ aᵢ Yⁱ` from codes of level `0`. -/
def trCurve (Pk : List (GPoly (LC 0))) : BPoly (RFC.RatFuncC N) :=
  Pk.map (·.map (trRF N)) ++ [[1]]

/-- **The residue-divisor check over `N(x)`**: the curve is `trCurve Pk`, `deg_Y B < n`,
`D = ∏ⱼ (X − αⱼ)` with constant `αⱼ = cⱼ`, `D′(αⱼ) ≠ 0`, the residues are the rationals `rq`, and
`Γⱼₖ = s ρⱼₖ + eⱼ`. -/
def resDivCheckRF (G : GlobalCert (RFC.RatFuncC N)) (Pk : List (GPoly (LC 0))) (B : BPoly ℚ)
    (Dq : CPoly ℚ) (αc : List N) (rq : List (List ℚ)) (sc : ℕ) (eS : List ℤ) : Bool :=
  decide (G.Fc = trCurve N Pk) && decide (Pk.length = G.n) && decide (B.length ≤ G.n) &&
  CPoly.beq (Dq.map (algebraMap ℚ (RFC.RatFuncC N))) (denQ G.αL) &&
  (List.range G.αL.length).all fun j ↦
    decide (G.αL.getD j 0 = RFC.mk [αc.getD j 0] [1]) &&
    decide (Kron.evalC (CPoly.deriv (denQ G.αL)) (G.αL.getD j 0) ≠ 0) &&
    (List.range G.n).all fun k ↦
      decide (algebraMap ℚ (RFC.RatFuncC N) ((rq.getD j []).getD k 0) =
        resF (mapBQ B) G.αL j ((G.yL.getD j []).getD k 0)) &&
      decide ((((G.ΓL.getD j []).getD k 0 : ℕ) : ℚ) = sc * (rq.getD j []).getD k 0 + eS.getD j 0)

variable {N}

lemma resDivCheckRF_spec {G : GlobalCert (RFC.RatFuncC N)} {Pk : List (GPoly (LC 0))}
    {B : BPoly ℚ} {Dq : CPoly ℚ} {αc : List N} {rq : List (List ℚ)} {sc : ℕ} {eS : List ℤ}
    (h : resDivCheckRF N G Pk B Dq αc rq sc eS = true) :
    G.Fc = trCurve N Pk ∧ Pk.length = G.n ∧ B.length ≤ G.n ∧
      toPoly (Dq.map (algebraMap ℚ (RFC.RatFuncC N))) = toPoly (denQ G.αL) ∧
      ∀ j < G.αL.length, G.αL.getD j 0 = RFC.mk [αc.getD j 0] [1] ∧
        Kron.evalC (CPoly.deriv (denQ G.αL)) (G.αL.getD j 0) ≠ 0 ∧ ∀ k < G.n,
          algebraMap ℚ (RFC.RatFuncC N) ((rq.getD j []).getD k 0) =
            resF (mapBQ B) G.αL j ((G.yL.getD j []).getD k 0) ∧
          (((G.ΓL.getD j []).getD k 0 : ℕ) : ℚ) = sc * (rq.getD j []).getD k 0 + eS.getD j 0 := by
  simp only [resDivCheckRF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, CPoly.beq_iff] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, fun j hj ↦ ⟨(h.2 j hj).1.1, (h.2 j hj).1.2,
    (h.2 j hj).2⟩⟩

end Checks

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) {N : Type} [Field N] [DecidableEq N] [CharZero N]
  (ιC : N →+* Cc)


/-- On the line `y = x` (base curve `[[0, -1], [1]]`), `y = x`. -/
lemma y_eq_x_line (hFc : Fc = [[0, -1], [1]]) : T.S.y = T.S.x := by
  have h := T.S.root
  have e : toB Fc = X + Polynomial.C (-X) := by subst hFc; simp [toB, CPoly.toPoly, add_comm]
  rw [T.hSF, e] at h
  simp at h
  linear_combination h

lemma transc_xN : RFC.Transc ((algebraMap Cc L).comp ιC) T.S.x := fun P hP h ↦
  T.S.htr ⟨P.map ιC, (Polynomial.map_ne_zero_iff ιC.injective).mpr hP,
    by rw [aeval_def, eval₂_map]; exact h⟩

/-- `N(x) → L`, `x ↦ x`. -/
noncomputable def psiN : RFC.RatFuncC N →+* L := RFC.evalHom (T.transc_xN ιC)

lemma eval₂_rat {E : Type*} [CommRing E] (f g : ℚ →+* E) (z : E) (p : ℚ[X]) :
    p.eval₂ f z = p.eval₂ g z := by
  rw [show f = g from Subsingleton.elim _ _]

lemma psiN_frRF (q : GFrac ℚ) :
    T.psiN ιC (frRF N q) =
      aeval T.S.x ((CPoly.toPoly q.1).map (algebraMap ℚ Cc)) /
        aeval T.S.x ((CPoly.toPoly q.2).map (algebraMap ℚ Cc)) := by
  rw [psiN, frRF, RFC.evalHom_mk, toPoly_mapHom, toPoly_mapHom, eval₂_map, eval₂_map,
    aeval_def, aeval_def, eval₂_map, eval₂_map]
  congr 1 <;> exact eval₂_rat _ _ _ _

lemma psiN_X : T.psiN ιC (RFC.mk [0, 1] [1]) = T.S.x := by
  rw [psiN, RFC.evalHom_mk]
  simp [toPoly_cons]

lemma psiN_mem (c : RFC.RatFuncC N) : T.psiN ιC c ∈ T.F 0 := by
  induction c using Quotient.inductionOn with
  | h a =>
    rw [psiN, RFC.evalHom_quot]
    have hq : ∀ c : N, ((algebraMap Cc L).comp ιC) c ∈ T.F 0 := fun c ↦ T.const_mem 0 _
    have hx : T.S.x ∈ T.F 0 := (Cc⟮T.S.x⟯⟮T.S.y⟯).algebraMap_mem
      ⟨T.S.x, IntermediateField.mem_adjoin_simple_self Cc T.S.x⟩
    exact div_mem (eval₂_mem _ _ _ hx hq _) (eval₂_mem _ _ _ hx hq _)

/-- **The realization of the translation** (towers over the line `y = x`). -/
lemma psiN_trRF (hyx : T.S.y = T.S.x) (a : LC 0) : T.psiN ιC (trRF N a) = T.ev 0 a := by
  change T.psiN ιC (trRF N a) =
    (GPoly.toPoly (xModel (algebraMap ℚ Cc) T.hC T.S T.hx) a).eval T.S.y
  induction a with
  | nil => simp [trRF]
  | cons q a ih =>
    have e : trRF N (q :: a) = frRF N q + RFC.mk [0, 1] [1] * trRF N a := rfl
    rw [e, map_add, map_mul, ih, psiN_frRF, psiN_X,
      GPoly.toPoly_cons, eval_add, eval_mul, eval_C, eval_X, sem_xModel, hyx]

lemma psiN_const (c : N) : T.psiN ιC (RFC.mk [c] [1]) = algebraMap Cc L (ιC c) := by
  rw [psiN, RFC.evalHom_mk]
  simp [toPoly_cons]

/-- The curve of the codes is the translated curve, mapped. -/
lemma nkF_trCurve {Cc' E : Type u} [Field Cc'] [Field E] [Algebra Cc' E] [Differential Cc']
    [Differential E] [DifferentialAlgebra Cc' E] [CharZero Cc'] [CharZero E]
    (TE : MTower Fc ks Cc' E) (h0 : TE.Tr 0) (ι : RFC.RatFuncC N →+* TE.F 0)
    (hι : ∀ q, ι (trRF N q) = (TE.MP 0 h0).sem q) (Pk : List (GPoly (LC 0))) :
    TE.nkF 0 h0 Pk = (toB (trCurve N Pk)).map (mapRingHom ι) := by
  have hp : ∀ p : GPoly (LC 0), (toPoly (p.map (trRF N))).map ι = GPoly.toPoly (TE.MP 0 h0) p := by
    intro p
    induction p with
    | nil => simp
    | cons a p ih =>
      rw [List.map_cons, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, ih, hι, GPoly.toPoly_cons]
  rw [nkF]
  ext1 i
  rw [coeff_map, coeff_toB, trCurve]
  rcases lt_trichotomy i Pk.length with hi | rfl | hi
  · have e : (Pk.map (·.map (trRF N))).getD i [] = (Pk.getD i []).map (trRF N) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
    rw [polyF_coeff _ _ _ hi, List.getD_append _ _ _ _ (by simpa using hi), e, coe_mapRingHom, hp]
  · have h1 := (polyF_monic (fun j ↦ GPoly.toPoly (TE.MP 0 h0) (Pk.getD j [])) Pk.length)
    rw [Monic, Polynomial.leadingCoeff, polyF_natDegree] at h1
    rw [h1, List.getD_append_right _ _ _ _ (by simp), List.length_map, Nat.sub_self]
    simp [toPoly_cons]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [polyF_natDegree]; exact hi),
      List.getD_eq_default _ _ (by simp; omega)]
    simp

set_option maxHeartbeats 32000000 in
/-- **Non-elementary integrals on curves over `N(x)`.** Over `t = log x`-type levels on the line
(`y = x`), on the curve `θⁿ + ∑ aᵢ(x, t) θⁱ = 0` (codes `Pk` of level `0`, single place at
infinity), certified over `F = N(x)` (`N` embedded in the constants by `ιC`), the integrand
`η B(t, θ)/D(t)` with constant poles `αⱼ` and rational residues: a non-torsion certificate for
`Γⱼₖ = s ρⱼₖ + eⱼ` proves that it has no elementary integral. -/
theorem nk_not_elementary_RF {N : Type} [Field N] [DecidableEq N] [CharZero N] (ιC : N →+* Cc)
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (hyx : T.S.y = T.S.x)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {η : LC 0} (hk : ks 0 = .prim η)
    (G : GlobalCert (RFC.RatFuncC N)) (Pk : List (GPoly (LC 0)))
    (hsh : nkShape Fc ks 0 Pk = true) (θ : L)
    (hθ : θ ^ Pk.length + ∑ i ∈ Finset.range Pk.length, T.evP 0 (Pk.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hG : G.globalCheck = true) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p (RFC.RatFuncC N)) (φp : RFC.RatFuncC N →+* ℚ_[p]) (hRp : RedValid p Rp φp)
    (Cp : PrimeCert p) (hCp : primeCheck Rp G Cp = true)
    (Rq : RedFns q (RFC.RatFuncC N)) (φq : RFC.RatFuncC N →+* ℚ_[q]) (hRq : RedValid q Rq φq)
    (Cq : PrimeCert q) (hCq : primeCheck Rq G Cq = true) (Pb : ℕ) (Lm : List (List (RFC.RatFuncC N)))
    (htest : nonPrincCheck G.n ((Cp.mp * Cq.mp) * G.cdeg) Pb G.I.δL G.I.Bc G.I.Dc G.αL G.cΓ
      (G.ΓL.map (·.map ((Cp.mp * Cq.mp) * ·))) Lm = true)
    (B : BPoly ℚ) (Dq : CPoly ℚ) (αc : List N) (rq : List (List ℚ)) (sc : ℕ) (eS : List ℤ)
    (hchk : resDivCheckRF N G Pk B Dq αc rq sc eS = true) :
    ¬ HasElementaryIntegral (T.ev 0 η * ∑ j ∈ Finset.range G.n,
      T.evP 0 (liftQC Fc ks 0 (B.getD j [])) / T.evP 0 (liftQC Fc ks 0 Dq) * θ ^ j) := by
  classical
  have hPkn := (resDivCheckRF_spec hchk).2.1
  intro hf
  set Pc := Pk with hPc
  have hθ' := hθ
  set f := T.ev 0 η * ∑ j ∈ Finset.range G.n,
      T.evP 0 (liftQC Fc ks 0 (B.getD j [])) / T.evP 0 (liftQC Fc ks 0 Dq) * θ ^ j with hfdef
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv 1 (by omega) hc
  have hTE : TE.Tr 1 := MSE.hyp.tr
  have hTEm : TE.Tr 0 := hTE.of_succ
  have hTr : T.Tr 1 := (T.mspecs hmon hdeg lv 1 (by omega) hc).hyp.tr
  have hPE : ∀ P : GPoly (LC 0), TE.evP 0 P = ψ (T.evP 0 P) := fun P ↦ by
    rw [← TE.sem_poly_code 0 hTE, ← T.sem_poly_code 0 hTr]
    exact (TE.sem_MP 1 hTE _).trans ((hTEev 1 _).trans
      (congrArg ψ (T.sem_MP 1 hTr _).symm))
  have hθE : (ψ θ) ^ Pc.length + ∑ i ∈ Finset.range Pc.length,
      TE.evP 0 (Pc.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ', map_zero]
  set S₁ := TE.nkCurve 0 hTE Pc hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec 0 hTEm Pc hsh
  have hS₁F : S₁.F.natDegree = Pc.length := polyF_natDegree _ _
  have hnS : S₁.F.natDegree = G.n := hS₁F.trans hPkn
  set η₁ : TE.F 0 := TE.val 0 η with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁) := by
    rw [aeval_C]
    change (TE.ts 0)′ = _
    rw [TE.ht 0 (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F 0),
      α′ ≠ ((Polynomial.C η₁).map (algebraMap (TE.F 0) (AlgebraicClosure (TE.F 0)))).eval α :=
    fun α ↦ by
      rw [Polynomial.map_C, eval_C]
      exact not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd 0 (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
  have hK : ∀ c : TE.F 0, (algebraMap (TE.F 0) (AlgebraicClosure (TE.F 0)) c)′ =
      algebraMap (TE.F 0) (AlgebraicClosure (TE.F 0)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F 0) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem 0 c0⟩, rfl⟩
  set T₁ := (TE.F 0)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F 1, w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F 0)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem 1 _ w.2)
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
  ------------------------------------------------------------------------------------------------
  -- the curve over `ℚ`, the certificate over `(RFC.RatFuncC N)`
  have hGf := globalCheck_spec hG
  obtain ⟨-, hGmon, hGdeg, -⟩ := hGf.shape
  obtain ⟨hGFt, hPkn, hBl, hDqe, hresC⟩ := resDivCheckRF_spec hchk
  set ιq := algebraMap ℚ (TE.F 0) with hιq
  set Kb := AlgebraicClosure (TE.F 0) with hKb
  set φ := algebraMap (TE.F 0) Kb with hφ
  set φF := algebraMap ℚ (RFC.RatFuncC N) with hφF
  have hιmem : ∀ a : (RFC.RatFuncC N), ψ (T.psiN ιC a) ∈ TE.F 0 := fun a ↦ hTEmem 0 _ (T.psiN_mem ιC a)
  set ι : (RFC.RatFuncC N) →+* TE.F 0 := RingHom.codRestrict ((algebraMap L E₁).comp (T.psiN ιC))
    (TE.F 0) hιmem with hιdef
  set ψ₀ : (RFC.RatFuncC N) →+* Kb := φ.comp ι with hψ₀
  have hιq : ι.comp φF = ιq := ratHom_eq _ _
  have hφι' : ∀ a : (RFC.RatFuncC N), φ (ι a) = ψ₀ a := fun a ↦ rfl
  have hι0 : ∀ c : N, (ι (RFC.mk [c] [1]))′ = 0 := fun c ↦ by
    apply Subtype.ext
    rw [MTower.coe_deriv]
    change (ψ (T.psiN ιC (RFC.mk [c] [1])))′ = 0
    rw [T.psiN_const, deriv_algebraMap, deriv_algebraMap, T.hC, map_zero, map_zero]
  have hιsem : ∀ q : LC 0, ι (trRF N q) = (TE.MP 0 hTEm).sem q := fun q ↦ Subtype.ext (by
    change ψ (T.psiN ιC (trRF N q)) = _
    rw [T.psiN_trRF ιC hyx, TE.sem_MP 0 hTEm, hTEev 0 q])
  have hSF : S₁.F = (toB G.Fc).map (mapRingHom ι) := by
    rw [hGFt, show S₁.F = TE.nkF 0 hTEm Pc from rfl]
    exact nkF_trCurve TE hTEm ι hιsem Pk
  obtain ⟨-, hαnd, hpt⟩ := ptCheck_spec ψ₀ hGmon hGdeg hGf.pt
  -- the branches at the points
  have hY0 : ∀ j : Fin G.αL.length, ∃ Y : Fin G.n → PowerSeries Kb,
      (∀ k, PowerSeries.constantCoeff (Y k) = ψ₀ ((G.yL.getD j []).getD k 0)) ∧
      ((toB G.Fc).map (mapRingHom ψ₀)).map (branchSub (C := Kb) (K := Kb) 1 (ψ₀ (G.αL.getD j 0))) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ Kb (Y k))) := fun j ↦ by
    obtain ⟨Y, hYc, hYs, -⟩ := (hpt j j.2).2
    exact ⟨Y, hYc, hYs⟩
  choose Y0 hY0c hY0s using hY0
  set Y : Fin G.αL.length → Fin S₁.F.natDegree → PowerSeries Kb :=
    fun j k ↦ Y0 j (Fin.cast hnS k) with hYdef
  set α : Fin G.αL.length → TE.F 0 := fun j ↦ ι (G.αL.getD j 0) with hαdef
  set ys : Fin G.αL.length → Fin S₁.F.natDegree → TE.F 0 :=
    fun j k ↦ ι ((G.yL.getD j []).getD k 0) with hysdef
  have hbr : ∀ (Nb : ℕ) (a : RFC.RatFuncC N), S₁.F.map (branchSub (C := TE.F 0) (K := Kb) Nb (ψ₀ a)) =
      ((toB G.Fc).map (mapRingHom ψ₀)).map (branchSub (C := Kb) (K := Kb) Nb (ψ₀ a)) := by
    intro Nb a
    rw [hSF, Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun P ↦ ?_
    change branchSub Nb (ψ₀ a) (P.map ι) = branchSub (C := Kb) (K := Kb) Nb (ψ₀ a) (P.map ψ₀)
    rw [← Differential.SuperData.branchSub_map, Polynomial.map_map]
  have hY : ∀ j, S₁.F.map (branchSub 1 (φ (α j))) =
      ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ Kb (Y j k))) := fun j ↦ by
    rw [hφι', hbr, hY0s j,
      ← prod_cast hnS (fun k ↦ X - Polynomial.C (HahnSeries.ofPowerSeries ℤ Kb (Y0 j k)))]
  have hYc : ∀ j k, PowerSeries.constantCoeff (Y j k) = φ (ys j k) := fun j k ↦ by
    rw [hYdef, hY0c, hysdef, hφι']
    rfl
  have hα : Function.Injective α := fun j j' h ↦ by
    by_contra hne
    exact nodup_getD_ne hαnd j.2 j'.2 (Fin.val_ne_of_ne hne) 0 (ι.injective h)
  have hys : ∀ j, Function.Injective (ys j) := fun j k k' h ↦ by
    have hl := (hpt j j.2).1
    by_contra hne
    exact nodup_getD_ne hl.2 (by rw [hl.1, ← hnS]; exact k.2) (by rw [hl.1, ← hnS]; exact k'.2)
      (Fin.val_ne_of_ne hne) 0 (ι.injective h)
  ------------------------------------------------------------------------------------------------
  -- the integrand as `B(x, y)/D(x)`
  set QB : (TE.F 0)[X][X] := Polynomial.C (Polynomial.C η₁) * (toB B).map (mapRingHom ιq)
    with hQB
  set MD : (TE.F 0)[X] := (toPoly Dq).map ιq with hMD
  have hevB : S₁.evXY ((toB B).map (mapRingHom ιq)) =
      ∑ j ∈ Finset.range G.n, TE.evP 0 (liftQC Fc ks 0 (B.getD j [])) * (ψ θ) ^ j := by
    rw [toB_eq_sum B G.n hBl, CurveData.evXY, Polynomial.map_sum, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_X, eval_mul, eval_C, eval_pow, eval_X,
      coe_mapRingHom, ← TE.toPoly_liftQC 0 hTEm]
    congr 1
    exact TE.aeval_toPoly (TE.MP 0 hTEm) (TE.sem_MP 0 hTEm) _
  have hDv : aeval S₁.x MD = TE.evP 0 (liftQC Fc ks 0 Dq) := by
    rw [hMD, ← TE.toPoly_liftQC 0 hTEm]
    exact TE.aeval_toPoly (TE.MP 0 hTEm) (TE.sem_MP 0 hTEm) _
  have hfval : ψ f = S₁.evXY QB / aeval S₁.x MD := by
    rw [hQB, hDv]
    have e1 : S₁.evXY (Polynomial.C (Polynomial.C η₁) * (toB B).map (mapRingHom ιq)) =
        (η₁ : E₁) * S₁.evXY ((toB B).map (mapRingHom ιq)) := by
      rw [CurveData.evXY, CurveData.evXY, Polynomial.map_mul, eval_mul, Polynomial.map_C, eval_C]
      congr 1
      exact aeval_C _ _
    rw [e1, hevB, hfdef, map_mul, map_sum, ← hTEev 0 η, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_div₀, map_pow, ← hPE, ← hPE]
    rw [show ((η₁ : TE.F 0) : E₁) = TE.ev 0 η from rfl]
    ring
  set fE := S₁.evXY QB / aeval S₁.x MD with hfE
  have hfT : fE ∈ T₁ := by rw [← hfval]; exact hLT f
  ------------------------------------------------------------------------------------------------
  -- the Liouville form over `T₁`
  have heq₁ : fE = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [← hfval, heqL, add_comm]
  obtain ⟨k, d, w, ⟨hd', hw, -⟩, hsum⟩ :=
    logSum_qindep T₁.toSubfield s' c u (fun i hi ↦ (hdata i hi).1)
      (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩)
  set d' : ℕ → TE.F 0 := fun jj ↦
    if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0 with hd'def
  have hdd : ∀ jj < k, algebraMap (TE.F 0) E₁ (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dite_cond_eq_true (eq_true hjj)]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
  have hww : ∀ jj < k, w jj ∈ T₁ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : fE = v′ + ∑ jj ∈ Finset.range k,
      algebraMap (TE.F 0) E₁ (d' jj) * ((w jj)′ / w jj) := by
    rw [heq₁, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  ------------------------------------------------------------------------------------------------
  -- the denominator
  have hMDι : MD = (toPoly (denQ G.αL)).map ι := by
    rw [hMD, ← hDqe, toPoly_mapHom, Polynomial.map_map, hιq]
  have hMDφ : MD.map φ = (G.αL.map fun a ↦ X - Polynomial.C (ψ₀ a)).prod := by
    rw [hMDι, Polynomial.map_map, toPoly_denQ, Polynomial.map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun a _ ↦ ?_
    simp [hψ₀]
  have hDb : ∀ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) → (MD.map φ).eval b ≠ 0 := by
    intro b hb h0
    rw [hMDφ, eval_list_prod, List.prod_eq_zero_iff, List.map_map, List.mem_map] at h0
    obtain ⟨a, ha, hab⟩ := h0
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hab
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact hb ⟨⟨i, hi⟩, by
      change φ (ι (G.αL.getD i 0)) = b
      rw [hφι', hab, List.getD_eq_getElem _ _ hi]⟩
  have hMD0 : MD ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ : ∃ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) :=
      (Set.finite_range _).infinite_compl.nonempty
    exact hDb b hb (by rw [h0, Polynomial.map_zero, eval_zero])
  have hD0 : ∀ j : Fin G.αL.length, MD.eval (α j) = 0 := fun j ↦ by
    rw [hMDι, hαdef, eval_map, eval₂_at_apply, toPoly_denQ, eval_list_prod, List.prod_eq_zero,
      map_zero]
    rw [List.map_map, List.mem_map]
    refine ⟨G.αL.getD j 0, ?_, by simp⟩
    rw [List.getD_eq_getElem _ _ j.2]
    exact List.getElem_mem _
  have hD1v : ∀ j : Fin G.αL.length, (derivative MD).eval (α j) =
      ι (Kron.evalC (CPoly.deriv (denQ G.αL)) (G.αL.getD j 0)) := fun j ↦ by
    rw [hMDι, Polynomial.derivative_map, eval_map, eval₂_at_apply, Kron.evalC_eq, toPoly_deriv]
  have hD1 : ∀ j : Fin G.αL.length, (derivative MD).eval (α j) ≠ 0 := fun j ↦ by
    rw [hD1v]
    exact (map_ne_zero_iff _ ι.injective).mpr (hresC j j.2).2.1
  ------------------------------------------------------------------------------------------------
  -- the residues
  set ρ : Fin G.αL.length → Fin S₁.F.natDegree → TE.F 0 :=
    fun j k ↦ ι (resF (mapBQ B) G.αL j ((G.yL.getD j []).getD k 0)) with hρdef
  have hbelow : ∀ j k (i : ℤ), i < -1 → (S₁.embG (branchSub 1 (φ (α j)))
      (branchSub_injective 1 one_pos _) _ (S₁.root_of_split _ _ (hY j) k) ⟨fE, hfT⟩).coeff i = 0 :=
    fun j k ↦ (S₁.embG_simple_pole QB MD (α j) (hD0 j) (hD1 j) (Y j k)
      (S₁.root_of_split _ _ (hY j) k) hfT).1
  have hres : ∀ j k, (S₁.embG (branchSub 1 (φ (α j)))
      (branchSub_injective 1 one_pos _) _ (S₁.root_of_split _ _ (hY j) k) ⟨fE, hfT⟩).coeff (-1) =
        (sBranch (Polynomial.C η₁) (φ (α j)) 1).coeff 0 * φ (ρ j k) := by
    intro j k
    rw [(S₁.embG_simple_pole QB MD (α j) (hD0 j) (hD1 j) (Y j k)
      (S₁.root_of_split _ _ (hY j) k) hfT).2]
    have hs := sBranch_coeff (C := TE.F 0) (Polynomial.C η₁) (φ (α j)) 1 one_pos
    rw [show (1 : ℤ) - ((1 : ℕ) : ℤ) = 0 by norm_num] at hs
    have hα' : (α j)′ = 0 := by
      rw [hαdef]; dsimp only; rw [(hresC j j.2).1]; exact hι0 _
    rw [hs, Polynomial.map_C, eval_C, hK, hα', map_zero, sub_zero, Nat.cast_one, div_one, one_mul]
    have e1 : (QB.map (mapRingHom φ)) =
        Polynomial.C (Polynomial.C (φ η₁)) * (toB (mapBQ (F := RFC.RatFuncC N) B)).map (mapRingHom ψ₀) := by
      rw [hQB, Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, Polynomial.map_C,
        Polynomial.map_map, Polynomial.mapRingHom_comp, mapBQ, toB_mapHom, Polynomial.map_map,
        Polynomial.mapRingHom_comp, ← hιq, hψ₀]
      rfl
    rw [e1, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, coe_evalRingHom, eval_C,
      hYc, hD1v]
    have hφ2 : ∀ a : (RFC.RatFuncC N), algebraMap (TE.F 0) Kb (ι a) = ψ₀ a := hφι'
    simp only [hαdef, hysdef, hρdef, hφι', hφ2]
    rw [evalB_map, resF, map_div₀]
    ring
  ------------------------------------------------------------------------------------------------
  -- no other finite poles
  have hfree : ∀ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S₁.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l) (i : ℤ), i < 1 - (N : ℤ) →
      (S₁.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S₁.root_of_mem hl hr) ⟨fE, hfT⟩).coeff i = 0 := by
    intro b hb N hN l hl r hr i hi
    have hNp := Nat.pos_of_ne_zero hN
    set Φ := S₁.embG (branchSub N b) (branchSub_injective N hNp b) r (S₁.root_of_mem hl hr)
      with hΦ
    set Dm : T₁ := ⟨aeval S₁.x MD, S₁.aeval_mem MD⟩ with hDm
    have e : (⟨fE, hfT⟩ : T₁) = S₁.evT QB / Dm :=
      Subtype.ext (by rw [IntermediateField.coe_div, S₁.coe_evT])
    have hdm : Φ Dm = branchSub N b MD := S₁.embG_polyX _ _ _ _ MD (S₁.aeval_mem MD)
    have hdd0 : branchSub (K := Kb) N b MD ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective N hNp b)).mpr hMD0
    have hdo : (branchSub (K := Kb) N b MD).order = 0 :=
      Curves.CurveData.order_branchSub_eq_zero (C := TE.F 0) MD b N hNp (hDb b hb)
    have hBo : 0 ≤ (Φ (S₁.evT QB)).order := S₁.regularFinite_evT (K := Kb) QB b N hN l hl r hr
    change (Φ ⟨fE, hfT⟩).coeff i = 0
    rw [e, map_div₀, hdm]
    by_cases hb0 : Φ (S₁.evT QB) = 0
    · rw [hb0, zero_div]; rfl
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [div_eq_mul_inv, HahnSeries.order_mul hb0 (inv_ne_zero hdd0), order_inv_nk _ hdd0, hdo]
    have : (1 : ℤ) ≤ N := by exact_mod_cast hNp
    omega
  ------------------------------------------------------------------------------------------------
  -- the divisor `Γ`
  obtain ⟨Λ, hΛ⟩ := exists_proj (TE.F 0) ιq LinearMap.id
  have hΓ : ∀ (j : Fin G.αL.length) (k : Fin S₁.F.natDegree), (((G.ΓL.getD j []).getD k 0 : ℕ) : ℚ) = sc * Λ (ρ j k) + eS.getD j 0 :=
    fun j k ↦ by
      rw [hρdef]
      simp only
      have hk' : (k : ℕ) < G.n := by rw [← hnS]; exact k.2
      rw [← ((hresC j j.2).2.2 k hk').1, show ι (algebraMap ℚ (RFC.RatFuncC N) _) = ιq _ from
        congrArg (fun g : ℚ →+* TE.F 0 ↦ g _) hιq, hΛ]
      exact ((hresC j j.2).2.2 k hk').2
  have hsumΓ : ∑ j : Fin G.αL.length, ∑ k : Fin S₁.F.natDegree, (G.ΓL.getD j []).getD k 0 =
      G.cdeg * Pc.length := by
    have e : ∀ j : ℕ, ∑ k : Fin S₁.F.natDegree, (G.ΓL.getD j []).getD k 0 =
        ∑ k ∈ Finset.range G.n, (G.ΓL.getD j []).getD k 0 := fun j ↦ by
      rw [Fin.sum_univ_eq_sum_range (fun k ↦ (G.ΓL.getD j []).getD k 0), hnS]
    simp only [e]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ∑ k ∈ Finset.range G.n, (G.ΓL.getD j []).getD k 0), hPkn]
    exact hGf.sum
  obtain ⟨M, hM, γ, hγ0, hγ⟩ := S₁.divGEU_of_liouville (K := Kb) (Polynomial.C η₁) hx hK hnd
    Pc.length _ hS₁F hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 k d' w hww v fE (hCT v hv)
    hfT heq' α hα ys hys Y hY hYc ρ hbelow hres hfree Λ sc (fun j ↦ eS.getD j 0)
    (fun j k ↦ (G.ΓL.getD j []).getD k 0) G.cdeg hΓ hsumΓ
  exact not_torsion_of_cert_map (Kb := Kb) S₁ ι G hSF hG hpq Rp φp hRp Cp hCp Rq φq hRq Cq hCq
    Pb Lm htest M hM ⟨γ, hγ0, hγ⟩


end MTower

end Curves.MT
