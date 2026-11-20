import RischTragerBronstein.Mixed.NKInf2UnitLog
import RischTragerBronstein.Mixed.NKInf2Decide
import RischTragerBronstein.Mixed.NKExactC2
import RischTragerBronstein.Mixed.NKLogCert
import RischTragerBronstein.Algebraic.EllQuadOrbit

/-!
# Two places at infinity with a non-constant unit

When `P₁ − P₂` is torsion, a non-constant unit `u₀ = ∑ Uⱼ θʲ` (`Uⱼ ∈ Fₘ[t]`, with inverse
`∑ Vⱼ θʲ`: `unitC`, and `u₀′/u₀` certified by `logDerChk`) exists; then the logarithmic part of an elementary integral is
`κ u₀′/u₀ + ℓ` (`nk_liouville_unit`), and when `τ(u₀′/u₀) = 0` (as for curves over `ℚ`, where the
norm of `u₀` is a rational constant) `∫ f` is elementary iff `f − τ(f)/n − c u₀′/u₀` is exact for
some constant `c` (`exactC2`) and `∫ τ(f)/n` is elementary (`nk_iff2U`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open CPoly Sup GTors

/-- **The place data of a curve over `ℚ`** (over `F ⊇ ℚ`): one fibre at `0`, two places. -/
def TwoPlaceDataP (F : Type*) [Field F] [DecidableEq F] [CharZero F] (Fc0 : BPoly ℚ) : Prop :=
  ∃ (Fc' : BPoly F) (Pc : PlaceCert F),
    toB Fc' = (toB Fc0).map (mapRingHom (algebraMap ℚ F)) ∧ Pc.check Fc' (toB Fc').natDegree = true ∧
    Pc.fib.length = 1 ∧ Pc.pl.length = 2 ∧ Pc.fα 0 = 0

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `(∑ Uⱼ θʲ)(∑ Vⱼ θʲ) ≡ 1` modulo `P` (unnormalized code arithmetic, for cheap kernel checks). -/
def unitC (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  (remP O1 (nkPC Fc ks m Pp) (GPoly.sub O1 (GPoly.mul O1 (nkFl Fc ks m U) (nkFl Fc ks m V))
    [O1.one])).all O1.isZero

/-- `u′/u` modulo `P` for `u = ∑ Uⱼ θʲ`. -/
def nkLogD (m : ℕ) (Pp : List (GPoly (LC m))) (U : List (GPoly (LC m))) :
    Option (GPoly (LC (m + 1))) :=
  match dThetaC (MOr Fc ks (m + 1)) (nkPC Fc ks m Pp) with
  | some dθ => logDerC (MOr Fc ks (m + 1)) (nkPC Fc ks m Pp) dθ (nkFl Fc ks m U)
  | none => none

/-- `p ≡ 0` modulo `P`. -/
def zeroModC (m : ℕ) (Pp : List (GPoly (LC m))) (p : GPoly (LC (m + 1))) : Bool :=
  (remP (MO Fc ks (m + 1)) (nkPC Fc ks m Pp) p).all (MO Fc ks (m + 1)).isZero

/-- **The logarithmic derivative certificate**: `θ′ = dθ` (`P_θ dθ + Pᐞ ≡ 0`, with `w P_θ ≡ 1`) and
`g ≡ (uᐞ + u_θ dθ) v` modulo `P` (with `u v ≡ 1`). No gcd is computed. -/
def logDerChk (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m)))
    (gl dθ wθ : GPoly (LC (m + 1))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let u := nkFl Fc ks m U
  zeroModC Fc ks m Pp (GPoly.add O1 (GPoly.mul O1 dθ (GPoly.derivX O1 P)) (GPoly.mapD O1 P)) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 wθ (GPoly.derivX O1 P)) [O1.one]) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 gl (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 u)
      (GPoly.mul O1 dθ (GPoly.derivX O1 u))) (nkFl Fc ks m V)))

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma evθ_nkFl (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (U : List (GPoly (LC m))) :
    T.evθ m h1 θ (nkFl Fc ks m U) = ∑ j ∈ Finset.range U.length, T.evP m (U.getD j []) * θ ^ j := by
  rw [T.evθ_list m h1 θ, show (nkFl Fc ks m U).length = U.length from List.length_map _]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [T.sem_nkFl m h1 U j]

lemma evθ_MP (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (p : GPoly (LC (m + 1))) :
    T.evθ m h1 θ p = aeval θ (GPoly.toPoly (T.MP (m + 1) h1) p) := by
  unfold evθ
  congr 1
  induction p with
  | nil => simp [GPoly.toPoly_nil]
  | cons a p ih => rw [GPoly.toPoly_cons, GPoly.toPoly_cons, ih, MPr_sem]

lemma evθ_remP_MO (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (P p : GPoly (LC (m + 1)))
    (hP : T.evθ m h1 θ P = 0) :
    T.evθ m h1 θ (remP (MO Fc ks (m + 1)) P p) = T.evθ m h1 θ p := by
  have hs := GPoly.divMod_spec (T.MP (m + 1) h1) p P
  rw [evθ_MP] at hP ⊢
  rw [evθ_MP, remP, hs, map_add, map_mul, hP, mul_zero, zero_add]

lemma deriv_evθ_MO (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (p : GPoly (LC (m + 1))) :
    (T.evθ m h1 θ p)′ = T.evθ m h1 θ (GPoly.mapD (MO Fc ks (m + 1)) p) +
      T.evθ m h1 θ (GPoly.derivX (MO Fc ks (m + 1)) p) * θ′ := by
  rw [evθ_MP, deriv_aeval_coeff (T.hcommF m) θ, evθ_MP, evθ_MP, GPoly.toPoly_mapD,
    GPoly.toPoly_derivX]

lemma zeroModC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (p : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (h : zeroModC Fc ks m Pp p = true) : T.evθ m h1 θ p = 0 := by
  set O1 := MO Fc ks (m + 1)
  set M1 := T.MP (m + 1) h1
  unfold zeroModC at h
  rw [List.all_eq_true] at h
  have h0 : GPoly.toPoly M1 (remP O1 (nkPC Fc ks m Pp) p) = 0 := by
    refine Polynomial.ext fun i ↦ ?_
    rw [coeff_toPoly_sem, Polynomial.coeff_zero]
    by_cases hi : i < (remP O1 (nkPC Fc ks m Pp) p).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact (M1.isZero_iff _).mp (h _ (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (by omega)]; exact M1.sem_zero
  rw [← T.evθ_remP_MO m h1 θ (nkPC Fc ks m Pp) p hP, evθ_MP, h0, map_zero]

lemma evθ_one_MO (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) :
    T.evθ m h1 θ [(MO Fc ks (m + 1)).one] = 1 := by
  rw [evθ_MP]
  simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
  rw [aeval_C, (T.MP (m + 1) h1).sem_one, map_one]

lemma unitC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp U V : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (h : unitC Fc ks m Pp U V = true) :
    T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = 1 := by
  have h0 := T.zeroModC_sound m h1 θ Pp _ hP h
  rw [evθ_MP, GPoly.toPoly_sub, GPoly.toPoly_mul, map_sub, map_mul, sub_eq_zero, ← evθ_MP,
    ← evθ_MP, ← evθ_MP, T.evθ_one_MO m h1 θ] at h0
  exact h0

lemma logDerChk_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp U V : List (GPoly (LC m)))
    (gl dθ wθ : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (huv : T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = 1)
    (h : logDerChk Fc ks m Pp U V gl dθ wθ = true) :
    T.evθ m h1 θ gl = (T.evθ m h1 θ (nkFl Fc ks m U))′ / T.evθ m h1 θ (nkFl Fc ks m U) := by
  set O1 := MO Fc ks (m + 1)
  unfold logDerChk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hd, hw⟩, hg⟩ := h
  have hd' := T.zeroModC_sound m h1 θ Pp _ hP hd
  have hw' := T.zeroModC_sound m h1 θ Pp _ hP hw
  have hg' := T.zeroModC_sound m h1 θ Pp _ hP hg
  have hev : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.add O1 a b) =
      T.evθ m h1 θ a + T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_add, map_add]
  have hem : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.mul O1 a b) =
      T.evθ m h1 θ a * T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_mul, map_mul]
  have hes : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.sub O1 a b) =
      T.evθ m h1 θ a - T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_sub, map_sub]
  rw [hev, hem] at hd'
  rw [hes, hem, T.evθ_one_MO m h1 θ, sub_eq_zero] at hw'
  rw [hes, hem, hev, hem, sub_eq_zero] at hg'
  -- `θ′ = dθ(θ)`
  have hPd := T.deriv_evθ_MO m h1 θ (nkPC Fc ks m Pp)
  rw [hP, Derivation.map_zero] at hPd
  have hθ' : θ′ = T.evθ m h1 θ dθ := by
    have hne : T.evθ m h1 θ (GPoly.derivX O1 (nkPC Fc ks m Pp)) ≠ 0 :=
      right_ne_zero_of_mul_eq_one hw'
    have : T.evθ m h1 θ (GPoly.derivX O1 (nkPC Fc ks m Pp)) * (θ′ - T.evθ m h1 θ dθ) = 0 := by
      linear_combination -hPd - hd'
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
  have hiv : T.evθ m h1 θ (nkFl Fc ks m V) = (T.evθ m h1 θ (nkFl Fc ks m U))⁻¹ :=
    eq_inv_of_mul_eq_one_right huv
  rw [hg', hiv, T.deriv_evθ_MO m h1 θ (nkFl Fc ks m U), hθ', div_eq_mul_inv]
  ring

set_option maxHeartbeats 4000000 in
/-- **`⇐`** (with a non-constant unit). -/
theorem nk_sufficient2U (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L) (U V : List (GPoly (LC m))) (huv : unitC Fc ks m Pp U V = true)
    (gl dθ wθ : GPoly (LC (m + 1))) (hgl : logDerChk Fc ks m Pp U V gl dθ wθ = true)
    (hgllen : gl.length ≤ Pp.length)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC2 Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gl = some res)
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
  have hiff := T.exactC2_correct m (by omega) hTr (hTr m (by omega)) hk (paramLimC Fc ks lv m)
    MSm.lim (nkPC Fc ks m Pp) _ θ hP hind gl res hres
  obtain ⟨c0, Y, hY⟩ := hiff.mp hr
  -- `u₀′/u₀` in coordinates
  have huvL := T.unitC_sound m hTr θ Pp U V hP huv
  have hu0 : T.evθ m hTr θ (nkFl Fc ks m U) ≠ 0 := left_ne_zero_of_mul_eq_one huvL
  have hld := T.logDerChk_sound m hTr θ Pp U V gl dθ wθ hP huvL hgl
  set M1 := T.MPr (m + 1) hTr with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hglsum : T.evθ m hTr θ gl = ∑ j ∈ Finset.range Pp.length,
      ((M1.sem (gl.getD j O1.zero) : T.F (m + 1)) : L) * θ ^ j := by
    rw [T.evθ_list m hTr θ gl, ← Finset.sum_range_add_sum_Ico _ hgllen,
      Finset.sum_eq_zero (s := Finset.Ico gl.length Pp.length) fun j hj ↦ by
        rw [List.getD_eq_default _ _ (by have := (Finset.mem_Ico.mp hj).1; omega), M1.sem_zero]
        simp, add_zero]
  rw [hlen] at hY
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at hY
  rw [T.sum_nkRest m hTr Pp.length hn0, ← hglsum, hld] at hY
  set u0 := T.evθ m hTr θ (nkFl Fc ks m U) with hu0d
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ +
          ([()].map fun _ ↦ algebraMap Cc L c0 * logDeriv u0).sum by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, logDeriv]
    rw [hY]; ring]
  refine (hq.add_in (hasElementaryIntegralIn_deriv _)).add_in ?_
  exact hasElementaryIntegralIn_logSum (fun _ ↦ algebraMap Cc L c0) (fun _ ↦ u0) [()]
    (fun _ _ ↦ ⟨by rw [deriv_algebraMap, T.hC, map_zero], hu0⟩)

set_option maxHeartbeats 16000000 in
/-- **`⇒`**: an elementary `f` has an exact `f − τ(f)/n` and an elementary `τ(f)/n` (the
logarithmic part of a Liouville form lies in `Fₘ`, and `τ` is `n` on `Fₘ`). -/
theorem nk_necessary2U (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (hpd : TwoPlaceDataP F (invB (shiftB Fq 0) k0 M))
    (U V : List (GPoly (LC m))) (hUlen : U.length ≤ Pp.length)
    (huv : unitC Fc ks m Pp U V = true) (j1 : ℕ) (hj1 : 1 ≤ j1 ∧ j1 < Pp.length)
    (hU1 : GPoly.trim (MO Fc ks m) (U.getD j1 []) ≠ [])
    (gl dθ wθ : GPoly (LC (m + 1))) (hgl : logDerChk Fc ks m Pp U V gl dθ wθ = true)
    (hgllen : gl.length ≤ Pp.length)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hτg : (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length gl s) = true)
    (hres : exactC2 Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gl = some res)
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
  obtain ⟨Fc', Pc, hFc', hPcc, hfib1, hpl2, hα0⟩ := hpd
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
  set u0T : T₁ := S₁.evT (∑ j ∈ Finset.range U.length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (U.getD j [])) * X ^ j) with hu0T
  set v0T : T₁ := S₁.evT (∑ j ∈ Finset.range V.length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (V.getD j [])) * X ^ j) with hv0T
  have hu0v : (u0T : E₁) = TE.evθ m hTE (ψ θ) (nkFl Fc ks m U) := by
    rw [hu0T, S₁.coe_evT, hevPol]
  have hv0v : (v0T : E₁) = TE.evθ m hTE (ψ θ) (nkFl Fc ks m V) := by
    rw [hv0T, S₁.coe_evT, hevPol]
  have huvE : (u0T : E₁) * (v0T : E₁) = 1 := by
    rw [hu0v, hv0v]; exact TE.unitC_sound m hTE (ψ θ) Pp U V hPθE huv
  have huv1 : u0T * v0T = 1 := Subtype.ext (by rw [IntermediateField.coe_mul, huvE]; rfl)
  have hu00 : u0T ≠ 0 := left_ne_zero_of_mul_eq_one huv1
  have hfin0 : ∀ (a : AlgebraicClosure (TE.F m)) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l),
      (S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S₁.root_of_mem hl hr) u0T).order = 0 := by
    intro a N hN l hl r hr
    set φ := S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S₁.root_of_mem hl hr)
    have h1 : φ u0T * φ v0T = 1 := by rw [← map_mul, huv1, map_one]
    have hu' : φ u0T ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hv' : φ v0T ≠ 0 := right_ne_zero_of_mul_eq_one h1
    have o1 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m))
      (∑ j ∈ Finset.range U.length, Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (U.getD j [])) * X ^ j)
      a N hN l hl r hr
    have o2 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m))
      (∑ j ∈ Finset.range V.length, Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (V.getD j [])) * X ^ j)
      a N hN l hl r hr
    have ho := congrArg HahnSeries.order h1
    rw [HahnSeries.order_mul hu' hv', HahnSeries.order_one] at ho
    change 0 ≤ (φ u0T).order at o1
    change 0 ≤ (φ v0T).order at o2
    omega
  have hj1U : j1 < U.length := by
    by_contra hcon
    rw [List.getD_eq_default _ _ (by omega)] at hU1
    exact hU1 rfl
  have hnc : ¬ ∃ c : TE.F m, (u0T : E₁) = algebraMap (TE.F m) E₁ c := by
    rintro ⟨c0, hc0⟩
    have hmemU : ∀ j, TE.evP m (U.getD j []) ∈ TE.F (m + 1) := fun j ↦ TE.evP_mem m (TE.ev_mem m) _
    have hmemc : algebraMap (TE.F m) E₁ c0 ∈ TE.F (m + 1) := (TE.mem_F_succ).mpr
      (IntermediateField.algebraMap_mem _ c0)
    set a : ℕ → TE.F (m + 1) := fun j ↦
      (if j < U.length then ⟨TE.evP m (U.getD j []), hmemU j⟩ else 0) -
        (if j = 0 then ⟨algebraMap (TE.F m) E₁ c0, hmemc⟩ else 0) with ha
    have hsum : ∑ j ∈ Finset.range Pp.length, (a j : E₁) * (ψ θ) ^ j = 0 := by
      have e1 : ∑ j ∈ Finset.range Pp.length, (a j : E₁) * (ψ θ) ^ j =
          ∑ j ∈ Finset.range U.length, TE.evP m (U.getD j []) * (ψ θ) ^ j -
            algebraMap (TE.F m) E₁ c0 := by
        simp only [ha, AddSubgroupClass.coe_sub, sub_mul, Finset.sum_sub_distrib]
        congr 1
        · rw [← Finset.sum_range_add_sum_Ico _ hUlen]
          rw [Finset.sum_eq_zero (s := Finset.Ico U.length Pp.length) fun j hj ↦ by
            rw [if_neg (by have := (Finset.mem_Ico.mp hj).1; omega)]; simp, add_zero]
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          rw [if_pos (Finset.mem_range.mp hj)]
        · rw [Finset.sum_eq_single 0 (fun j _ hj ↦ by rw [if_neg hj]; simp)
            (fun h ↦ absurd (Finset.mem_range.mpr hn0) h), if_pos rfl, pow_zero, mul_one]
      rw [e1, ← TE.evθ_nkFl m hTE (ψ θ) U, ← hu0v, hc0, sub_self]
    have h0 := TE.nkCurveG_ind m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE a hsum j1 hj1.2
    have h0' := congrArg Subtype.val h0
    simp only [ha, if_pos hj1U, if_neg (show j1 ≠ 0 by omega), sub_zero,
      ZeroMemClass.coe_zero] at h0'
    have htrm := (TE.MP m hTEm)
    obtain ⟨-, -, hlc⟩ := GPoly.natDegree_toPoly_of_trim_ne_nil (TE.MP m hTEm) hU1
    have hP0 : GPoly.toPoly (TE.MP m hTEm) (U.getD j1 []) ≠ 0 := by
      intro h
      have hc := (GPoly.natDegree_toPoly_of_trim_ne_nil (TE.MP m hTEm) hU1).2.1
      rw [h, Polynomial.coeff_zero] at hc
      exact hlc hc.symm
    apply hP0
    apply (transcendental_iff.mp (hTE m (by omega)))
    rw [TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm)]
    exact h0'
  have hld := TE.logDerChk_sound m hTE (ψ θ) Pp U V gl dθ wθ hPθE
    (TE.unitC_sound m hTE (ψ θ) Pp U V hPθE huv) hgl
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hglsum : TE.evθ m hTE (ψ θ) gl = ∑ j ∈ Finset.range n,
      ((M1.sem (gl.getD j O1.zero) : TE.F (m + 1)) : E₁) * (ψ θ) ^ j := by
    rw [TE.evθ_list m hTE (ψ θ) gl, ← Finset.sum_range_add_sum_Ico _ hgllen,
      Finset.sum_eq_zero (s := Finset.Ico gl.length Pp.length) fun j hj ↦ by
        rw [List.getD_eq_default _ _ (by have := (Finset.mem_Ico.mp hj).1; omega), M1.sem_zero]
        simp, add_zero]
  have hlogu : logDeriv (u0T : E₁) = ∑ j ∈ Finset.range n,
      ((M1.sem (gl.getD j O1.zero) : TE.F (m + 1)) : E₁) * (ψ θ) ^ j := by
    rw [logDeriv, hu0v, ← hld, hglsum]
  -- the logarithmic part is `κ u₀′/u₀ + ℓ`
  obtain ⟨κ, ℓ₀, hκ, hℓ₀⟩ := S₁.nk_liouville_unit (K := AlgebraicClosure (TE.F m))
    (Polynomial.C η₁) hx hK hnd k0 M hMb hGm' hGn' hgeo' ιF Fc' hmon' hSF' Pc hPcd hn0' hfib1 hpl2
    hα0 u0T hu00 hnc hfin0 hconstC (ψ f) hfT hreg s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  set κE : E₁ := algebraMap (TE.F m) E₁ κ with hκE
  have hκE' : κE′ = 0 := by rw [hκE, deriv_algebraMap, hκ, map_zero]
  obtain ⟨c0, hc0⟩ := TE.hconst κE hκE'
  -- the trace
  obtain ⟨hs0, hτ⟩ := TE.traceC_sound m hTE Pp (ψ θ) hPθE s hs
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  have hκx : κE ∈ (TE.F m)⟮S₁.x⟯ := IntermediateField.algebraMap_mem _ κ
  set fc : ℕ → E₁ := fun j ↦ TE.evP m (fp.getD j []) -
    κE * ((M1.sem (gl.getD j O1.zero) : TE.F (m + 1)) : E₁) with hfc
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
      (mul_mem hκx ((TE.mem_F_succ).mp (M1.sem (gl.getD j O1.zero)).2)))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, fc j * (ψ θ) ^ j = _
      simp only [hfc, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      rw [← hψf, ← hlogu, hℓ₀]
      ring)
  rw [hS₁F] at hwe
  -- `τ(u₀′/u₀) = 0`
  have hτ0 : ∑ j ∈ Finset.range n, ((M1.sem (gl.getD j O1.zero) : TE.F (m + 1)) : E₁) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
    have h1 := (M1.isZero_iff _).mp hτg
    rw [TE.sem_nkTau m n hTE gl s] at h1
    have hn' : ((n : ℕ) : TE.F (m + 1)) ≠ 0 := by exact_mod_cast hn0.ne'
    have h2 : ∑ j ∈ Finset.range n, M1.sem (gl.getD j O1.zero) * M1.sem (s.getD j O1.zero) = 0 :=
      (mul_eq_zero.mp h1).resolve_right (inv_ne_zero hn')
    have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) h2
    simpa only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
      ZeroMemClass.coe_zero] using this
  have hτf : ∑ j ∈ Finset.range n, fc j * ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) =
      ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) := by
    simp only [hfc, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hτ0, mul_zero,
      sub_zero]
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
      ∑ i ∈ s', c i * logDeriv (u i) - κE * logDeriv (u0T : E₁) := by
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
    have hiff := TE.exactC2_correct m (by omega) hTE (hTE m (by omega)) hk (paramLimC Fc ks lv m)
      MSEm.lim (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind gl res hres
    refine hiff.mpr ⟨c0, fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [TE.sum_nkRest m hTE n hn0, hTEev (m + 1) q]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hc0, ← hlogu, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map (fun i ↦ (c i, u i)) ++ [(-κE, (u0T : E₁))] with hl0
    have hu0E : (u0T : E₁) ≠ 0 := fun h ↦ hu00 (Subtype.ext h)
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        rw [Finset.mem_toList] at hi
        exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
      · rw [List.mem_singleton] at hp
        subst hp
        exact ⟨by rw [map_neg, hκE', neg_zero], hu0E⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_append, List.sum_append, List.map_map,
        Finset.sum_map_toList]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Function.comp_def]
      ring
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform


/-- **The decision with a non-constant unit** (`τ(u₀′/u₀) = 0`). -/
theorem nk_iff2U (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (hpd : TwoPlaceDataP F (invB (shiftB Fq 0) k0 M))
    (U V : List (GPoly (LC m))) (hUlen : U.length ≤ Pp.length)
    (huv : unitC Fc ks m Pp U V = true) (j1 : ℕ) (hj1 : 1 ≤ j1 ∧ j1 < Pp.length)
    (hU1 : GPoly.trim (MO Fc ks m) (U.getD j1 []) ≠ [])
    (gl dθ wθ : GPoly (LC (m + 1))) (hgl : logDerChk Fc ks m Pp U V gl dθ wθ = true)
    (hgllen : gl.length ≤ Pp.length)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hτg : (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length gl s) = true)
    (hres : exactC2 Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gl = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) :=
  ⟨T.nk_necessary2U hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ ιC k0 M hinv hGm hGn hpd
      U V hUlen huv j1 hj1 hU1 gl dθ wθ hgl hgllen hθ hgen s hs fp res hτg hres,
    fun h ↦ T.nk_sufficient2U hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ U V huv gl dθ wθ hgl
      hgllen
      hθ s fp res hres h.1 h.2⟩

end MTower

end Curves.MT
