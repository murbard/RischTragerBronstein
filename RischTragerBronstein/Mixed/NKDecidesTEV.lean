import RischTragerBronstein.Mixed.NKExactTEVExists
import RischTragerBronstein.Mixed.NKDecidesTV
import RischTragerBronstein.Mixed.NKSearchTRE
import RischTragerBronstein.Mixed.NKExpDecideTEV

/-!
# Non-constant curves over an exponential: the exact part is decided

`searchTEV … B`: tries the first `B` candidates `(T, T⁻¹, r, dg, C, C⁻¹, dg₀)` — code matrices,
integer shifts, diagonal data at infinity, a gauge at `t = 0` and its diagonal data, an `Encodable`
enumeration — with `exactTEV`. Every answer is correct (`searchTEV_sound`, `nk_iffTEV`), and **the
search answers for every large `B`** (`searchTEV_complete`, from `exactTEV_exists`).

**`nk_decidesTEV`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over an exponential level `t = eᵃ` with coefficients
`aᵢ ∈ Fₘ[t]` (any codes, not necessarily constant), a single place at infinity and a single place
above `t = 0`, and `f = ∑ bⱼ θʲ`: for every large bound `N`, `elM` decides `τ(f)/n` and
`searchTEV` decides the exact part, and together they decide whether `f` has an elementary
integral — Risch's mixed case for these curves over an exponential, with nothing supplied.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

lemma exactWREV_congr_r (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (r r' : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (h : ∀ k < N, r k = r' k) :
    exactWREV Fc ks m a rde dg N Mc f r C Ci dg0 = exactWREV Fc ks m a rde dg N Mc f r' C Ci dg0 := by
  have hR : ((List.range N).map fun i ↦ (-r i).toNat) = (List.range N).map fun i ↦ (-r' i).toNat :=
    List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.mp hi)]
  have hM : ∀ bc, rescaleME Fc ks m bc N Mc r = rescaleME Fc ks m bc N Mc r' := fun bc ↦
    rescaleME_congr Fc ks m bc N Mc r r' h
  unfold exactWREV
  simp only [hM, rescaleF_congr Fc ks m N f r r' h, hR]

lemma exactTEV_congr_r (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (r r' : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m)) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (h : ∀ k < P.length - 1, r k = r' k) :
    exactTEV Fc ks m a rde dg r C Ci dg0 P Tc Ti f =
      exactTEV Fc ks m a rde dg r' C Ci dg0 P Tc Ti f := by
  have hc : ∀ (Mc : List (List (LC (m + 1)))) (fw : List (LC (m + 1))), exactWREV Fc ks m a rde dg (P.length - 1)
      (Mc.map fun l ↦ l.map (redC Fc ks m)) (fw.map (redC Fc ks m)) r C Ci dg0 =
      exactWREV Fc ks m a rde dg (P.length - 1)
      (Mc.map fun l ↦ l.map (redC Fc ks m)) (fw.map (redC Fc ks m)) r' C Ci dg0 := fun Mc fw ↦
    exactWREV_congr_r Fc ks m a rde dg _ _ _ r r' C Ci dg0 h
  unfold exactTEV exactTG
  simp only [hc]

/-- A candidate: `T`, `T⁻¹`, shifts, diagonal data, the gauge at `0` and its diagonal data. -/
abbrev CandTEV (m : ℕ) :=
  List (List (LC (m + 1))) × List (List (LC (m + 1))) × List ℤ × List (ℚ × ℚ × LC m) ×
    List (List (LC m)) × List (List (LC m)) × List (ℚ × ℚ × LC m)

/-- **The search** over the first `B` candidates. -/
def searchTEV (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandTEV m)) with
    | none => none
    | some c => exactTEV Fc ks m a rde c.2.2.2.1 (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.2.1
        c.2.2.2.2.2.1 c.2.2.2.2.2.2 P c.1 c.2.1 f

lemma searchTEV_sound (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchTEV Fc ks m a rde P f B = some b) :
    ∃ (dg : List (ℚ × ℚ × LC m)) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg0 : List (ℚ × ℚ × LC m)) (Tc Ti : List (List (LC (m + 1)))),
      exactTEV Fc ks m a rde dg r C Ci dg0 P Tc Ti f = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, _, _, _, _, hk⟩

/-- **Completeness of the search**: if some `exactTEV` answers, the search answers for every
large bound. -/
lemma searchTEV_complete (m : ℕ) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (dg : List (ℚ × ℚ × LC m)) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (Tc Ti : List (List (LC (m + 1))))
    (h : (exactTEV Fc ks m a rde dg r C Ci dg0 P Tc Ti f).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchTEV Fc ks m a rde P f B).isSome := by
  set c : CandTEV m := (Tc, Ti, (List.range (P.length - 1)).map r, dg, C, Ci, dg0) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchTEV
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  rw [exactTEV_congr_r Fc ks m a rde dg _ r C Ci dg0 P _ _ f (fun k hk ↦ by
    simp [List.getD_eq_getElem?_getD, hk])]
  exact h

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision for curves with any coefficients in `Fₘ[t]` over an exponential** (Risch's
mixed case for a single place at infinity and a single place above `t = 0`): for every large
bound, `elM` decides `τ(f)/n`, `searchTEV` decides the exact part, and together they decide `f`. -/
theorem nk_decidesTEV (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchTEV Fc ks m a (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
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
  -- the search answers for large bounds
  obtain ⟨Tc, Ti, r, dg, C, Ci, dg0, hex⟩ := T.exactTEV_exists m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) MSm.rde Pp hsh hsh0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q)
  obtain ⟨B0, hB0⟩ := searchTEV_complete Fc ks m a (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
    (nkRest Fc ks m (nkFl Fc ks m fp) q) dg r C Ci dg0 Tc Ti hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨dg', r', C', Ci', dg0', Tc', Ti', hex'⟩ := searchTEV_sound Fc ks m a _ _ _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffTEV hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp dg' r' C' Ci' dg0' Tc' Ti'
    res hex', h0, hiff]

end MTower

end Curves.MT
