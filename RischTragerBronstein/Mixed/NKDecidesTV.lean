import RischTragerBronstein.Mixed.NKExactTVExists
import RischTragerBronstein.Mixed.NKSearchTV

/-!
# Non-constant curves over a logarithm: the exact part is decided

`searchTV … B`: tries the first `B` candidates `(T, T⁻¹, r, dg)` — code matrices, integer shifts and
diagonal representations, an `Encodable` enumeration of codes — with `exactTV`. Every answer is
correct (`searchTV_sound`, `nk_iffTV`), and **the search answers for every large `B`**
(`searchTV_complete`, from `exactTV_exists`).

**`nk_decidesTV`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithmic level with coefficients
`aᵢ ∈ Fₘ[t]` (any codes, not necessarily constant) and a single place at infinity, and
`f = ∑ bⱼ θʲ`: for every large bound `N`, `elM` decides `τ(f)/n` and `searchTV` decides the exact
part, and together they decide whether `f` has an elementary integral — Risch's mixed case for
these curves, with nothing supplied.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

/-- Codes are encodable. -/
@[instance_reducible] def encLC : (m : ℕ) → Encodable (LC m)
  | 0 => (inferInstance : Encodable (List (List ℚ × List ℚ)))
  | m + 1 =>
    letI := encLC m
    (inferInstance : Encodable (List (LC m) × List (LC m)))

instance instEncodableLC (m : ℕ) : Encodable (LC m) := encLC m

instance instEncodableFRep (α : Type) [Encodable α] : Encodable (FRep α) :=
  Encodable.ofEquiv (α × List (α × α))
    ⟨fun fr ↦ (fr.h, fr.logs), fun p ↦ ⟨p.1, p.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- A candidate: `T`, `T⁻¹`, shifts and diagonal representations. -/
abbrev CandTV (m : ℕ) :=
  List (List (LC (m + 1))) × List (List (LC (m + 1))) × List ℤ × List (FRep (LC m))

/-- **The search** over the first `B` candidates. -/
def searchTV (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandTV m)) with
    | none => none
    | some c => exactTV Fc ks m η rde c.2.2.2 (fun i ↦ c.2.2.1.getD i 0) P c.1 c.2.1 f

lemma searchTV_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchTV Fc ks m η rde P f B = some b) :
    ∃ (dg : List (FRep (LC m))) (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))),
      exactTV Fc ks m η rde dg r P Tc Ti f = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, _, hk⟩

lemma exactWRS_congr_r (m : ℕ) (η : LC m) (solve : SysSolver m) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r r' : ℕ → ℤ)
    (h : ∀ k < N, r k = r' k) :
    exactWRS Fc ks m η solve N Mc f r = exactWRS Fc ks m η solve N Mc f r' := by
  have hR : ((List.range N).map fun i ↦ (-r i).toNat) = (List.range N).map fun i ↦ (-r' i).toNat :=
    List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.mp hi)]
  unfold exactWRS
  rw [rescaleM_congr Fc ks m η N Mc r r' h, rescaleF_congr Fc ks m N f r r' h, hR]

lemma exactTV_congr_r (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (r r' : ℕ → ℤ) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (h : ∀ k < P.length - 1, r k = r' k) :
    exactTV Fc ks m η rde dg r P Tc Ti f = exactTV Fc ks m η rde dg r' P Tc Ti f := by
  have hc : ∀ Mc fw, exactWRV Fc ks m η rde dg (P.length - 1) Mc fw r =
      exactWRV Fc ks m η rde dg (P.length - 1) Mc fw r' := fun Mc fw ↦
    exactWRS_congr_r Fc ks m η _ _ Mc fw r r' h
  unfold exactTV exactTG
  simp only [hc]

/-- **Completeness of the search**: if some `exactTV` answers, the search answers for every
large bound. -/
lemma searchTV_complete (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (dg : List (FRep (LC m))) (r : ℕ → ℤ)
    (Tc Ti : List (List (LC (m + 1))))
    (h : (exactTV Fc ks m η rde dg r P Tc Ti f).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchTV Fc ks m η rde P f B).isSome := by
  set c : CandTV m := (Tc, Ti, (List.range (P.length - 1)).map r, dg) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchTV
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  rw [exactTV_congr_r Fc ks m η rde dg _ r P _ _ f (fun k hk ↦ by
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
/-- **The decision for curves with any coefficients in `Fₘ[t]` over a logarithm** (Risch's mixed
case for a single place at infinity): for every large bound, `elM` decides `τ(f)/n`, `searchTV`
decides the exact part, and together they decide `f`. -/
theorem nk_decidesTV (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchTV Fc ks m η (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
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
  obtain ⟨Tc, Ti, r, dg, hex⟩ := T.exactTV_exists m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp hsh θ hθ (nkRest Fc ks m (nkFl Fc ks m fp) q)
  obtain ⟨B0, hB0⟩ := searchTV_complete Fc ks m η (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
    (nkRest Fc ks m (nkFl Fc ks m fp) q) dg r Tc Ti hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨dg', r', Tc', Ti', hex'⟩ := searchTV_sound Fc ks m η _ _ _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffTV hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp dg' r' Tc' Ti' res hex', h0, hiff]

end MTower

end Curves.MT
