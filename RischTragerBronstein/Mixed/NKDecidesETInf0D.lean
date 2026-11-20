import RischTragerBronstein.Mixed.NKDecidesETInf0
import RischTragerBronstein.Mixed.NKDecidesETInfVGD
import RischTragerBronstein.Mixed.NKInf0ExpD

/-!
# Several places at infinity and above `t = 0` (exponential level): the decision

`searchET0D … B`: as `searchETVG`, with candidates carrying S-units (`uᵢ vᵢ = t^{kᵢ}`, `unitsC0`,
`2n − 2` of them, independent together with `t` by the Wronskian certificate `indepWC`). Every answer is correct
(`searchET0_soundD`, `nk_iffETInf0D`), and when the units exist the search answers for every large
bound (`searchET0_completeD`, from `exactTLEVG_exists0`).

**`nk_decidesETInf0D`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over an exponential level `t = eᵃ` with any
coefficients in `Fₘ[t]` (Eisenstein certificate), split at infinity (`splitShapeC`) and with a split
fibre above `t = 0` (`split0C`), and `2n − 2` S-units independent together with `t` modulo `Fₘ`:
`elM` and `searchET0D` decide whether `∑ bⱼ θʲ` has an elementary integral.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- Candidates with denominators for the S-units. -/
abbrev CandET0D (m : ℕ) : Type :=
  CandET0 m × List (GPoly (LC m)) × List (List (GPoly (LC m))) × List (List (GPoly (LC m))) ×
    List (GPoly (LC (m + 1)))

/-- One candidate: check the S-units, then run `exactTLEVG`. -/
def et0TryD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (cc : CandET0D m) : Option Bool :=
  let c := cc.1.2.2.2
  if (decide (c.2.2.1.length + 2 = 2 * Pp.length) &&
      unitsC0D Fc ks m Pp c.1 c.2.1 cc.1.1 cc.1.2.1 cc.2.1 cc.2.2.1 cc.2.2.2.1 cc.2.2.2.2 ((MO Fc ks m).deriv a) c.2.2.1 dθ wθ s &&
      indepWC Fc ks m c.2.2.1 c.2.2.2.1 cc.1.2.2.1 c.2.2.2.2.1) = true then
    exactTLEVG Fc ks m a rde [] c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.1
      (fun i ↦ c.2.2.2.2.2.2.2.1.getD i 0) c.2.2.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.2.2.1
      c.2.2.2.2.2.2.2.2.2.2.2.2 (nkPC Fc ks m Pp) c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 f c.2.2.1
  else none

/-- **The search** over the first `B` candidates. -/
def searchET0D (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandET0D m)) with
    | none => none
    | some c => et0TryD Fc ks m a rde Pp dθ wθ s f c

lemma searchET0_soundD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchET0D Fc ks m a rde Pp dθ wθ s f B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1)))) (gls : List (GPoly (LC (m + 1))))
      (J D : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ)
      (Cg Cgi C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true ∧
      exactTLEVG Fc ks m a rde [] Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · rename_i c _
    unfold et0TryD at hk
    dsimp only at hk
    split_ifs at hk with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc.1.1, hc.1.2, hc.2, hk⟩

/-- **Completeness of the search**: if units and an answering basis exist, the search answers for
every large bound. -/
lemma searchET0_completeD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
    (gls : List (GPoly (LC (m + 1))))
    (J D : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (Cg Cgi C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (hk1 : gls.length + 2 = 2 * Pp.length)
    (hU : unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ((MO Fc ks m).deriv a) gls dθ wθ s = true)
    (hJH : indepWC Fc ks m gls J D H = true)
    (hex : (exactTLEVG Fc ks m a rde [] Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchET0D Fc ks m a rde Pp dθ wθ s f B).isSome := by
  set c : CandET0D m := ((kk, jj, D, Us, Vs, gls, J, H, Tc, Ti,
    (List.range ((nkPC Fc ks m Pp).length - 1)).map r, Cg, Cgi, C, Ci, dg0), ds, cUs, cVs, Es) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchET0D
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  unfold et0TryD
  dsimp only
  rw [if_pos (by simp [hk1, hU, hJH])]
  rw [exactTLEVG_congr_r Fc ks m a rde [] Cg Cgi _ r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls
    (fun k hk ↦ by simp [List.getD_eq_getElem?_getD, hk])]
  exact hex

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision for curves with any coefficients split at infinity and above `t = 0`, with
`2n − 2` S-units** (exponential level): for every large bound, `elM` decides `τ(f)/n`, `searchET0D`
decides the exact part (finding the units, the basis and both gauges), and together they decide
`f`. -/
theorem nk_decidesETInf0D (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ) (H : List (List (LC (m + 1)))),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true)
    (fp : List (GPoly (LC m))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0D Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
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
  obtain ⟨Us, Vs, kk, jj, ds, cUs, cVs, Es, gls, J, D, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg0, hex⟩ := T.exactTLEVG_exists0 m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck sp γs hsplit βs hsp0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchET0_completeD Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs kk jj ds cUs cVs Es gls J D H Tc Ti r Cg Cgi C Ci dg0 hk1 hU hJH
    hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨Us', Vs', kk', jj', ds', cUs', cVs', Es', gls', J', D', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg0', hk1', hU',
    hJH', hex'⟩ := searchET0_soundD Fc ks m a _ Pp dθ wθ s _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInf0D hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck θ Us' Vs' kk' jj' ds' cUs' cVs' Es' gls' hk1'
    dθ wθ s hU' J' D' H' hJH' hθ hgen hs fp Tc' Ti' res [] Cg' Cgi' r' C' Ci' dg0' hex', h0, hiff]

end MTower

end Curves.MT

