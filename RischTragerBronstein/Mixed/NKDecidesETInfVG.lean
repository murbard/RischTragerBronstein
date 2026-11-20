import RischTragerBronstein.Mixed.NKExactTLEVGExists
import RischTragerBronstein.Mixed.NKInfRVExpG
import RischTragerBronstein.Mixed.NKDecidesInfVG
import RischTragerBronstein.Mixed.NKDecidesTEV

/-!
# Several places at infinity over an exponential level, non-constant coefficients: the decision

`searchETVG … B`: tries the first `B` candidates `(U, V, g, J, H, T, T⁻¹, r, Cg, Cg⁻¹, C, C⁻¹, dg₀)`
— units with inverses and logarithmic derivatives, an independence certificate, a basis, shifts,
a gauge at infinity, a gauge at `t = 0` with its diagonal data, an `Encodable` enumeration of
codes — checking the units (`unitsC`, `indepC`) and running `exactTLEVG`. Every answer is correct
(`searchETVG_sound`, `nk_iffETInfVG`), and **when the units exist the search answers for every
large `B`** (`searchETVG_complete`, from `exactTLEVG_exists`).

**`nk_decidesETInfVG`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over an exponential level `t = eᵃ` with any
coefficients in `Fₘ[t]` (Eisenstein certificate), split at infinity (`splitShapeC`), a single
place above `t = 0` (`nkShape0`), and `n − 1` units multiplicatively independent modulo `Fₘ`:
`elM` and `searchETVG` decide whether `∑ bⱼ θʲ` has an elementary integral, the basis, gauges and
units being found by the search.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

lemma exactWREVLS_congr_r (m : ℕ) (a : LC m) (solve : SysSolver m) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (r r' : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (h : ∀ k < N, r k = r' k) :
    exactWREVLS Fc ks m a solve N Mc f gs r C Ci dg0 =
      exactWREVLS Fc ks m a solve N Mc f gs r' C Ci dg0 := by
  have hR : ((List.range N).map fun i ↦ (-r i).toNat) = (List.range N).map fun i ↦ (-r' i).toNat :=
    List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.mp hi)]
  have hM : ∀ bc, rescaleME Fc ks m bc N Mc r = rescaleME Fc ks m bc N Mc r' := fun bc ↦
    rescaleME_congr Fc ks m bc N Mc r r' h
  have hg : (gs.map fun g ↦ (rescaleF Fc ks m N g r).map (redC Fc ks m)) =
      gs.map fun g ↦ (rescaleF Fc ks m N g r').map (redC Fc ks m) :=
    List.map_congr_left fun g _ ↦ by rw [rescaleF_congr Fc ks m N g r r' h]
  unfold exactWREVLS
  simp only [hM, rescaleF_congr Fc ks m N f r r' h, hR, hg]

lemma exactTLEVG_congr_r (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r r' : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1))))
    (h : ∀ k < P.length - 1, r k = r' k) :
    exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 P Tc Ti f gs =
      exactTLEVG Fc ks m a rde dg Cg Cgi r' C Ci dg0 P Tc Ti f gs := by
  unfold exactTLEVG exactTLEVS
  simp only [exactWREVLS_congr_r Fc ks m a _ _ _ _ _ r r' C Ci dg0 h]

/-- A candidate: units, inverses, logarithmic derivatives, independence certificate, basis,
inverse, shifts, the gauge at infinity and its inverse, the gauge at `t = 0`, its inverse and its
diagonal data. -/
abbrev CandETVG (m : ℕ) :=
  List (List (GPoly (LC m))) × List (List (GPoly (LC m))) × List (GPoly (LC (m + 1))) × List ℕ ×
    List (List (LC (m + 1))) × List (List (LC (m + 1))) × List (List (LC (m + 1))) × List ℤ ×
    List (List (LC m)) × List (List (LC m)) × List (List (LC m)) × List (List (LC m)) ×
    List (ℚ × ℚ × LC m)

/-- One candidate: check the units, then run `exactTLEVG`. -/
def etvgTry (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandETVG m) : Option Bool :=
  if (decide (c.2.2.1.length + 1 = Pp.length) &&
      unitsC Fc ks m Pp c.1 c.2.1 c.2.2.1 dθ wθ s && indepC Fc ks m c.2.2.1 c.2.2.2.1 c.2.2.2.2.1)
    = true then
    exactTLEVG Fc ks m a rde [] c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.1
      (fun i ↦ c.2.2.2.2.2.2.2.1.getD i 0) c.2.2.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.2.2.1
      c.2.2.2.2.2.2.2.2.2.2.2.2 (nkPC Fc ks m Pp) c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 f c.2.2.1
  else none

/-- **The search** over the first `B` candidates. -/
def searchETVG (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandETVG m)) with
    | none => none
    | some c => etvgTry Fc ks m a rde Pp dθ wθ s f c

lemma searchETVG_sound (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchETVG Fc ks m a rde Pp dθ wθ s f B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (Cg Cgi C Ci : List (List (LC m)))
      (dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 1 = Pp.length ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLEVG Fc ks m a rde [] Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · rename_i c _
    unfold etvgTry at hk
    split_ifs at hk with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc.1.1, hc.1.2, hc.2, hk⟩

/-- **Completeness of the search**: if units and an answering basis exist, the search answers for
every large bound. -/
lemma searchETVG_complete (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (J : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (Cg Cgi C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (hk1 : gls.length + 1 = Pp.length) (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (hJH : indepC Fc ks m gls J H = true)
    (hex : (exactTLEVG Fc ks m a rde [] Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchETVG Fc ks m a rde Pp dθ wθ s f B).isSome := by
  set c : CandETVG m := (Us, Vs, gls, J, H, Tc, Ti,
    (List.range ((nkPC Fc ks m Pp).length - 1)).map r, Cg, Cgi, C, Ci, dg0) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchETVG
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  unfold etvgTry
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
/-- **The decision for curves with any coefficients split at infinity, with `n − 1` units**
(exponential level, a single place above `t = 0`): for every large bound, `elM` decides
`τ(f)/n`, `searchETVG` decides the exact part (finding the units, the basis and both gauges),
and together they decide `f`. -/
theorem nk_decidesETInfVG (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length ∧
      unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVG Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
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
  obtain ⟨Us, Vs, gls, J, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg0, hex⟩ := T.exactTLEVG_exists m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck sp γs hsplit hsh0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchETVG_complete Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs gls J H Tc Ti r Cg Cgi C Ci dg0 hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨Us', Vs', gls', J', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg0', hk1', hU', hJH', hex'⟩ :=
    searchETVG_sound Fc ks m a _ Pp dθ wθ s _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInfVG hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck hsh0 θ Us' Vs' gls' hk1'
    dθ wθ s hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res [] Cg' Cgi' r' C' Ci' dg0' hex', h0, hiff]

end MTower

end Curves.MT
