import RischTragerBronstein.Mixed.NKLogDecideTV
import RischTragerBronstein.Mixed.NKDecidesTR
import RischTragerBronstein.Mixed.NKExpDecide

/-!
# Non-constant curves over a logarithm: candidates and the decision

For `θⁿ + ∑ aᵢ θⁱ = 0` over a logarithmic level `t′ = η` with coefficients `aᵢ ∈ Fₘ[t]` (not
necessarily constant) and a single place at infinity (`nkShape`), the derivation matrix of the
basis `nkTc` (`wᵣ = θ^{π r}/t^{⌊π(r) d/n⌋}`) tends at infinity to a triangular matrix with
diagonal `(π(r)/n) c′/c`, `c = lc(a₀)` (the branch `θ ∼ (−c tᵈ)^{1/n}`): `nkDg`. The search
`searchTVP` tries a list of candidates `(Tc, Ti, r, dg)` with `exactTV`; **`nk_decidesTVP`**:
whenever it answers, with `elM` for `τ(f)/n`, the answers decide whether `f` has an elementary
integral (`nk_iffTV`). The candidate built from the shape (`nkCandV`) is checked at run time.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The diagonal of the limit matrix for the basis `nkTc`: `(π(r)/n) c′/c`, `c = lc(a₀)`. -/
def nkDg (m : ℕ) (Pp : List (GPoly (LC m))) : List (FRep (LC m)) :=
  let O := MO Fc ks m
  let n := Pp.length
  let d := degG O (Pp.getD 0 [])
  let π := nkOrd n d
  (List.range n).map fun r ↦
    ⟨O.zero, [(mcst Fc ks m ((π.getD r 0 : ℚ) / n), leadG O (Pp.getD 0 []))]⟩

/-- The candidate from the shape: `nkTc`, `nkTi`, shifts `0`, `nkDg`. -/
def nkCandV (m : ℕ) (Pp : List (GPoly (LC m))) :
    List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ) × List (FRep (LC m)) :=
  (nkTc Fc ks m Pp, nkTi Fc ks m Pp, fun _ ↦ 0, nkDg Fc ks m Pp)

/-- **The search over candidates** `(Tc, Ti, r, dg)`. -/
def searchTVP (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1)))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ) ×
      List (FRep (LC m)))) : Option Bool :=
  pre.findSome? fun c ↦ exactTV Fc ks m η rde c.2.2.2 c.2.2.1 P c.1 c.2.1 f

lemma searchTVP_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1)))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ) ×
      List (FRep (LC m)))) (b : Bool) (h : searchTVP Fc ks m η rde P f pre = some b) :
    ∃ (dg : List (FRep (LC m))) (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))),
      exactTV Fc ks m η rde dg r P Tc Ti f = some b := by
  obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨_, _, _, _, hc⟩

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision for curves over a logarithm with any coefficients in `Fₘ[t]`**: whenever the
candidate search `searchTVP` answers `res`, for every large bound `N` `elM` answers `b` for
`τ(f)/n`, and `f` has an elementary integral iff `res ∧ b`. -/
theorem nk_decidesTVP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m)))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ) ×
      List (FRep (LC m)))) (res : Bool)
    (hres : searchTVP Fc ks m η (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre =
        some res) :
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
  obtain ⟨dg, r', Tc, Ti, hex'⟩ := searchTVP_sound Fc ks m η _ _ _ pre res hres
  refine ⟨b, hb, ?_⟩
  rw [T.nk_iffTV hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp dg r' Tc Ti res hex', h0, hiff]

end MTower

end Curves.MT
