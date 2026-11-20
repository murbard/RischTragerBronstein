import RischTragerBronstein.Mixed.NKInfRNTR
import RischTragerBronstein.Mixed.NKWitTR

/-!
# Several places at infinity over `ℚ(α)`, constant curves: the antiderivative

`exactTRL` is the parametric pipeline `exactTLS` with solver `primSysB` (`exactTRL_eq`), so its
witness version `exactTLSW` applies. `nk_integrateRNTR` makes `nk_decidesRNTR` constructive: an
elementary answer carries an antiderivative of the trace part, an exact part `Y` and rational
coefficients `c`, with `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑_{p,i} e_{p,i} u_{p,i}′/u_{p,i}`, where
`u_{p,i}` are the conjugates `U_p(αᵢ)` of the units and `e = c · V(α)⁻¹` (`NKExplRN`).
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors NCodes

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

lemma exactWEL_eq (m : ℕ) (solve : SysSolver m) (N : ℕ) (Mc : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (E : GPoly (LC m)) :
    exactWEL Fc ks m solve N Mc f gs E = exactWLE Fc ks m solve N Mc f gs E := by
  unfold exactWEL exactWLE
  simp only [matFn_matData]
  split_ifs
  · rfl
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

lemma exactWRL_eq (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r : ℕ → ℤ) :
    exactWRL Fc ks m η lim N Mc f gs r =
      exactWRSL Fc ks m η (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) N Mc f gs r := by
  unfold exactWRL exactWRSL
  simp only [matFn_matData, exactWEL_eq]
  split_ifs
  · rfl
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

lemma exactTRL_eq (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (gs : List (List (LC (m + 1)))) :
    exactTRL Fc ks m η lim r P Tc Ti f gs =
      exactTLS Fc ks m η (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) r P Tc Ti f
        gs := by
  unfold exactTRL exactTGL exactTLS
  simp only [exactWRL_eq, List.map_map]
  split_ifs
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h, List.map_map, Function.comp_def]

/-- The exact part of a candidate with parameters, with the witness. -/
def trlExW (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (c : CandTR) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLSW Fc ks m η (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0)
    (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f gs

lemma trlExW_isSome (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (c : CandTR) :
    (trlExW Fc ks m η lim P f gs c).map Option.isSome =
      exactTRL Fc ks m η lim (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f
        gs := by
  rw [exactTRL_eq]; exact exactTLSW_isSome _ _ _ _ _ _ _ _ _ _ _

lemma searchTRL_eq (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (B : ℕ) :
    searchTRL Fc ks m η lim P f gs B = searchPS (fun _ ↦ true)
      (fun c : CandTR ↦ exactTRL Fc ks m η lim (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1)
        (matL Fc ks m c.2.1) f gs) [] B := by
  unfold searchTRL searchPS searchS
  simp only [List.findSome?_nil]
  congr 1
  funext k
  cases (Encodable.decode k : Option CandTR) with
  | none => rfl
  | some c => rfl

/-- **The constructive decision** (constant curves, several places at infinity over `ℚ(α)`,
logarithmic level). -/
def nkRNTRW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (gss : List (List (GPoly (LC (m + 1)))))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (fun _ ↦ true) (trlExW Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
      gss.flatten) [] N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The explicit antiderivative with units over `ℚ(α)`**: the conjugate units `u p i` are
nonzero and `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑_{p,i} e p i · u′/u`. -/
def NKExplRN (m : ℕ) (θ : L) (Pp fp : List (GPoly (LC m))) (s : List (LC (m + 1))) (n ng : ℕ)
    (u : ℕ → Fin n → L) (e : ℕ → Fin n → Cc) (wt : List ℚ × List (LC (m + 1))) : Prop :=
  (∀ p < ng, ∀ i, u p i ≠ 0) ∧
  ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
    T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
    (∑ k ∈ Finset.range Pp.length, T.ev (m + 1) (wt.2.getD k (MOr Fc ks (m + 1)).zero) * θ ^ k)′ +
    ∑ p ∈ Finset.range ng, ∑ i : Fin n, algebraMap Cc L (e p i) * logDeriv (u p i)

/-- **The explicit form from a witness of the parametric exact test.** -/
theorem rn_explicit (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length)
    (θ : L) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1))))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (fp : List (GPoly (LC m))) (wt : List ℚ × List (LC (m + 1)))
    (hY : T.ExW m h1 ((nkPC Fc ks m Pp).length - 1) (fun k ↦ θ ^ k)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
      gss.flatten wt) :
    T.NKExplRN m θ Pp fp s μ.length gss.length
      (fun p i ↦ nVal (T.evθ m h1 θ) (algebraMap Cc L (αs i)) ((Ass.getD p []).map (nkFl Fc ks m)))
      (fun p i ↦ ∑ k : Fin μ.length,
        ((wt.1.getD (p * μ.length + k) 0 : ℚ) : Cc) * (Matrix.vandermonde αs)⁻¹ k i) wt := by
  classical
  obtain ⟨hd, hall⟩ := unitsRNC_spec hU
  have hgl : ∀ i < gss.length, (gss.getD i []).length = μ.length := fun i hi ↦ (hall i hi).2.2.1
  unfold ExW at hY
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set c : ℕ → Cc := fun q ↦ ((wt.1.getD q 0 : ℚ) : Cc) with hc
  have hcL : ∀ q, ((wt.1.getD q 0 : ℚ) : L) = algebraMap Cc L (c q) := fun q ↦ by
    rw [hc]; simp only [map_ratCast]
  simp only [hcL] at hY
  have hS := T.evθ_RSem m h1 θ
  set αL : Fin μ.length → L := fun i ↦ algebraMap Cc L (αs i) with hαL
  have hμL : ∀ i, αL i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : L) * αL i ^ l = 0 :=
    fun i ↦ by
      have := congrArg (algebraMap Cc L) (hαμ i)
      simpa [map_add, map_sum, map_mul, map_pow, map_intCast] using this
  have hαc : ∀ i, (αL i)′ = 0 := fun i ↦ by rw [hαL]; simp only; rw [deriv_algebraMap, T.hC, map_zero]
  set u : ℕ → Fin μ.length → L := fun p i ↦
    nVal (T.evθ m h1 θ) (αL i) ((Ass.getD p []).map (nkFl Fc ks m)) with hu
  have hu0 : ∀ p < gss.length, ∀ i, u p i ≠ 0 := fun p hp i ↦
    left_ne_zero_of_mul_eq_one (T.unitCN_sound m h1 θ Pp hP μ hd (αL i) (hμL i) _ _
      (hall p hp).1)
  refine ⟨hu0, ?_⟩
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
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  rw [hlen] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRest m h1 Pp.length hn0] at hY
  have hlog : ∑ p ∈ Finset.range gss.length, ∑ k : Fin μ.length,
      algebraMap Cc L (c (p * μ.length + k)) * G p k =
      ∑ p ∈ Finset.range gss.length, ∑ i : Fin μ.length,
        algebraMap Cc L (∑ k : Fin μ.length, c (p * μ.length + k) * (Matrix.vandermonde αs)⁻¹ k i) *
        logDeriv (u p i) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    simp only [hGk p (Finset.mem_range.mp hp), Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by rw [map_mul]; ring
  rw [hlog] at hY
  have hev : ∀ k, ((M1.sem (wt.2.getD k O1.zero) : T.F (m + 1)) : L) =
      T.ev (m + 1) (wt.2.getD k O1.zero) := fun k ↦ T.sem_MP (m + 1) h1 _
  simp only [hev] at hY
  rw [hY]
  ring

set_option maxHeartbeats 8000000 in
/-- **The integral with several places at infinity over `ℚ(α)` (constant curves, logarithmic
level), decided and computed.** -/
theorem nk_integrateRNTR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkRNTRW Fc ks lv m η Pp gss s fp N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplRN m θ Pp fp s μ.length gss.length
          (fun p i ↦ nVal (T.evθ m h1 θ) (algebraMap Cc L (αs i)) ((Ass.getD p []).map (nkFl Fc ks m)))
          (fun p i ↦ ∑ k : Fin μ.length,
            ((b.2.1.getD (p * μ.length + k) 0 : ℚ) : Cc) * (Matrix.vandermonde αs)⁻¹ k i) b.2 := by
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (trlExW_isSome Fc ks m η _ _ _ _) [] N).trans
        (searchTRL_eq Fc ks m η _ _ _ _ N).symm)
    _ (T.nk_decidesRNTR hmon hdeg hshF m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ ιC k0 M hinv hGm
      hGn μ Ass Bss gss hpd dθ wθ s hU J H hJH hθ hgen αs hαinj hαμ hs fp F0 hF0 hlen hcoef) _
    fun N w hw h1 ↦ ?_
  obtain ⟨-, hex⟩ := searchPW_src _ _ [] N w hw
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveG_ind m h1 Pp Fq hPp hmonQ hdegQ hgeo θ hθ
  have hY := T.exactTLSW_valid m h1 (by omega) hk (h1 m (by omega)) _
    (T.primSpecB (by omega) h1.of_succ hk _ MSm.lim) _ (nkPC Fc ks m Pp) _ θ hP hind _ _
    gss.flatten w.2 hex
  exact T.rn_explicit m h1 Pp hn0 θ hP μ Ass Bss gss dθ wθ s hU αs hαinj hαμ fp w.2 hY

end MTower

end Curves.MT

