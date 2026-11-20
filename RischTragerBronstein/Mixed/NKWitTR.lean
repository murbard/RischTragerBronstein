import RischTragerBronstein.Mixed.NKWitTV
import RischTragerBronstein.Mixed.NKDecidesTR

/-!
# A single place at infinity, constant curves: the antiderivative

`exactTR` (constant coefficients, solver `primSysB`) is `exactTLS` with no parameters
(`exactTR_eq`); `nk_integrateTR` makes `nk_decidesTR` constructive: an elementary answer carries an
antiderivative of the trace part and an exact part `Y` with `f(θ) = τ + (∑ₖ Yₖ θᵏ)′`.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

lemma exactTR_eq (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) :
    exactTR Fc ks m η lim r P Tc Ti f =
      exactTLS Fc ks m η (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) r P Tc Ti f
        [] := by
  have hWR : ∀ N Mc g, exactWR Fc ks m η lim N Mc g r =
      exactWRS Fc ks m η (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) N Mc g r :=
    fun _ _ _ ↦ rfl
  unfold exactTR exactTG exactTLS
  simp only [hWR, exactWRS_eq, List.map_nil]
  split_ifs
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

/-- The exact part of a candidate, with the witness. -/
def trExW (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (c : CandTR) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLSW Fc ks m η (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0)
    (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f []

lemma trExW_isSome (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (c : CandTR) :
    (trExW Fc ks m η lim P f c).map Option.isSome =
      exactTR Fc ks m η lim (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1) (matL Fc ks m c.2.1) f := by
  rw [exactTR_eq]; exact exactTLSW_isSome _ _ _ _ _ _ _ _ _ _ _

lemma searchTR_eq (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) :
    searchTR Fc ks m η lim P f B = searchPS (fun _ ↦ true)
      (fun c : CandTR ↦ exactTR Fc ks m η lim (fun i ↦ c.2.2.getD i 0) P (matL Fc ks m c.1)
        (matL Fc ks m c.2.1) f) [] B := by
  unfold searchTR searchPS searchS
  simp only [List.findSome?_nil]
  congr 1
  funext k
  cases (Encodable.decode k : Option CandTR) with
  | none => rfl
  | some c => rfl

/-- **The constructive decision** (constant curves, a single place at infinity, logarithmic
level). -/
def nkTRW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (s : List (LC (m + 1)))
    (fp : List (GPoly (LC m))) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (fun _ ↦ true) (trExW Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) [] N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The integral over constant curves with a single place at infinity, decided and
computed.** -/
theorem nk_integrateTR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTRW Fc ks lv m η Pp s fp N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s (fun _ ↦ 1) 0 b.2 := by
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (trExW_isSome Fc ks m η _ _ _) [] N).trans
        (searchTR_eq Fc ks m η _ _ _ N).symm)
    _ (T.nk_decidesTR hmon hdeg hshF m hn hc hk Pp hsh θ hθ hgen s hs fp F0 hF0 hlen hcoef) _
    fun N w hw h1 ↦ ?_
  obtain ⟨-, hex⟩ := searchPW_src _ _ [] N w hw
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurve_ind m h1 Pp hsh θ hθ
  have hY := T.exactTLSW_valid m h1 (by omega) hk (h1 m (by omega)) _
    (T.primSpecB (by omega) h1.of_succ hk _ MSm.lim) _ (nkPC Fc ks m Pp) _ θ hP hind _ _ [] w.2 hex
  exact T.nk_explicit_core m h1 Pp (T.nkShape_spec m h1.of_succ Pp hsh).1 θ [] (fun _ ↦ 1)
    (fun i hi ↦ absurd hi (by simp)) (fun i hi ↦ absurd hi (by simp)) fp s w.2 hY

end MTower

end Curves.MT
