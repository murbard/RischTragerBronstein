import RischTragerBronstein.Mixed.NKDecidesInfVG
import RischTragerBronstein.Mixed.NKInfRVG0

/-!
# Split places at infinity with zero residues: the decision without units

`henselC`: Newton lifting of a simple root `γ` of the residual polynomial to a root
`Θ = γ + a₁ T + ⋯ + a_{M−1} T^{M−1}` of `Q(T, Z) = T^{ns} P(1/T, Z/T^s)` modulo `T^M`
(untrusted: every candidate is checked by `splitResCk`). `splitRes0C` runs the zero-residue
certificate on these lifts.

`searchIVG0 … B` tries the first `B` candidates `(T, T⁻¹, r, C, C⁻¹)` for `exactTLVG` **without
units** (`gls = []`). Every answer is correct, and when the residues vanish
(`nk_decidesInfVG0`) the search answers for every large bound: together with `elM` (for `τ(f)/n`)
this decides `∫ ∑ bⱼ θʲ` on curves split at infinity **whatever the unit rank** (no
Mordell–Weil question arises, since no logarithm is needed).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- Newton lifting: `Θ ↦ Θ + a T^i` with `a = −[T^i] Q(T, Θ) / R′(γ)`, for `i = 1, …, M − 1`. -/
def henselC (m s M : ℕ) (Pp : List (GPoly (LC m))) (γ : LC m) : GPoly (LC m) :=
  let O := MO Fc ks m
  let Qc := invCoeffsC Fc ks m s Pp
  let d := O.inv (evalLC Fc ks m (GPoly.derivX O (residualC Fc ks m s Pp)) γ)
  ((List.range M).drop 1).foldl (fun Θ i ↦
    Θ ++ [O.neg (O.mul d ((evalPolyC Fc ks m Qc Θ).getD i O.zero))]) [γ]

/-- The zero-residue certificate on the Newton lifts of `γs`. -/
def splitRes0C (m s M : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m))
    (fp : List (GPoly (LC m))) : Bool :=
  splitResCk Fc ks lv m s M Pp γs (γs.map (henselC Fc ks m s M Pp)) fp

/-- A candidate without units: basis, inverse, shifts, gauge and its inverse. -/
abbrev CandIVG0 (m : ℕ) :=
  List (List (LC (m + 1))) × List (List (LC (m + 1))) × List ℤ × List (List (LC m)) ×
    List (List (LC m))

/-- One candidate: run `exactTLVG` without units. -/
def ivg0Try (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandIVG0 m) : Option Bool :=
  exactTLVG Fc ks m η rde [] c.2.2.2.1 c.2.2.2.2 (fun i ↦ c.2.2.1.getD i 0) (nkPC Fc ks m Pp)
    c.1 c.2.1 f []

/-- **The search** over the first `B` candidates. -/
def searchIVG0 (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandIVG0 m)) with
    | none => none
    | some c => ivg0Try Fc ks m η rde Pp f c

lemma searchIVG0_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchIVG0 Fc ks m η rde Pp f B = some b) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m))),
      exactTLVG Fc ks m η rde [] C Ci r (nkPC Fc ks m Pp) Tc Ti f [] = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, _, _, hk⟩

lemma searchIVG0_complete (m : ℕ) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (hex : (exactTLVG Fc ks m η rde [] C Ci r (nkPC Fc ks m Pp) Tc Ti f []).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchIVG0 Fc ks m η rde Pp f B).isSome := by
  set c : CandIVG0 m := (Tc, Ti, (List.range ((nkPC Fc ks m Pp).length - 1)).map r, C, Ci) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchIVG0
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  unfold ivg0Try
  rw [exactTLVG_congr_r Fc ks m η rde [] C Ci _ r (nkPC Fc ks m Pp) Tc Ti f [] (fun k hk ↦ by
    simp [List.getD_eq_getElem?_getD, hk])]
  exact hex

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision for curves split at infinity with zero residues, no units** (logarithmic
level): if the zero-residue certificate passes, then for every large bound `elM` decides `τ(f)/n`,
`searchIVG0` decides the exact part, and together they decide `f`. -/
theorem nk_decidesInfVG0 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (sR MR : ℕ) (γR : List (LC m)) (Θs : List (GPoly (LC m)))
    (hres0 : splitResCk Fc ks lv m sR MR Pp γR Θs fp = true) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVG0 Fc ks m η (prdeC Fc ks lv m) Pp
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hn0 : 0 < Pp.length := by
    unfold splitShapeC at hsplit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsplit
    exact hsplit.1.1.1.1
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
  obtain ⟨Tc, Ti, r, C, Ci, hex⟩ := T.exactTLVG_exists m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp qE csE sE tE s2E t2E hck sp γs hsplit θ hθ (nkRest Fc ks m (nkFl Fc ks m fp) q) []
  obtain ⟨B0, hB0⟩ := searchIVG0_complete Fc ks m η (prdeC Fc ks lv m) Pp
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Tc Ti r C Ci hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨Tc', Ti', r', C', Ci', hex'⟩ := searchIVG0_sound Fc ks m η _ Pp _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVG0 hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck θ hn0 dθ wθ s hθ hgen hs fp
    sR MR γR Θs hres0 Tc' Ti' res [] C' Ci' r' hex', h0, hiff]

end MTower

end Curves.MT
