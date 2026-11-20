import RischTragerBronstein.Mixed.NKDecidesETInf0
import RischTragerBronstein.Mixed.NKSplitCand

/-!
# Several places above `t = 0`: computed candidates

`searchET0P`: the search `searchET0` with precomputed candidates tried first (sound,
`searchET0P_sound`; answering whenever `searchET0` does, `searchET0P_isSome`), and
`nk_decidesETInf0P`, the decision with any list of candidates.

`split0Cands`: candidates from given S-units `Uᵢ/t^{jᵢ}` (`Uᵢ Vᵢ = t^{kᵢ}`): the logarithmic
derivatives `Uᵢ′ Vᵢ / t^{kᵢ} − jᵢ η` (`η` the code of `t′/t`, no inversion modulo `P`), a Wronskian certificate (positions `1 + p mod (n − 1)`,
derivative orders `⌊p/(n − 1)⌋`, inverse by Gauss–Jordan), the basis `θʲ` with shifts `j s`, the
Vandermonde gauges `(γₐᵇ)` at infinity and `(βₐᵇ)` at `t = 0` (or the identity), zero diagonal data
at `0`. `split0CandsA` computes the units too (`split0Units`: `n − 1` units at infinity by
`splitUnits`, and `n − 1` S-units with divisors `μ (P0ᵢ − P∞_{n−1})` by `unitSearch0S`, kernels of
the order conditions at infinity and along the Hensel branches above `0` (`expand0S`), normalized to
norm `1` as `uⁿ/(c t^μ)`). Everything is re-checked by `et0Try`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The search with precomputed candidates** (several places above `t = 0`), tried first. -/
def searchET0P (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0 m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (et0Try Fc ks m a rde Pp dθ wθ s f) with
  | some b => some b
  | none => searchET0 Fc ks m a rde Pp dθ wθ s f B

lemma searchET0P_sound (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0 m)) (B : ℕ) (b : Bool)
    (h : searchET0P Fc ks m a rde Pp dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (gls : List (GPoly (LC (m + 1))))
      (J D : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ)
      (Cg Cgi C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true ∧
      exactTLEVG Fc ks m a rde [] Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchET0P at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold et0Try at hc
    dsimp only at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchET0_sound Fc ks m a rde Pp dθ wθ s f B b h

lemma searchET0P_isSome (m : ℕ) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0 m)) (B : ℕ)
    (h : (searchET0 Fc ks m a rde Pp dθ wθ s f B).isSome) :
    (searchET0P Fc ks m a rde Pp dθ wθ s f pre B).isSome := by
  unfold searchET0P
  split
  · rfl
  · exact h

/-- **Candidates from given S-units** `Uᵢ/t^{jᵢ}` with `Uᵢ Vᵢ = t^{kᵢ}` (see the module doc). -/
def split0Cands (m s : ℕ) (Pp : List (GPoly (LC m))) (γs βs : List (LC m)) (ηc : LC m)
    (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) : List (CandET0 m) :=
  let n := Pp.length
  let O := MO Fc ks m
  let O1 := MOr Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  match dThetaC O1 P with
  | none => []
  | some dθ =>
    -- `g = U′ V / tᵏ − j η` (no inversion modulo `P`)
    let glOf : ℕ → GPoly (LC (m + 1)) := fun i ↦
      let u := nkFl Fc ks m (Us.getD i [])
      let r := (remP O1 P (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 u)
        (GPoly.mul O1 dθ (GPoly.derivX O1 u))) (nkFl Fc ks m (Vs.getD i [])))).map
          (O1.mul (tInvPowC Fc ks m (kk.getD i 0)))
      let jη : LC (m + 1) := ([O.mul (O.natCast (jj.getD i 0)) ηc], [O.one])
      ((List.range (max r.length 1)).map fun l ↦
        if l = 0 then O1.add (r.getD 0 O1.zero) (O1.neg jη) else r.getD l O1.zero)
    match (some ((List.range Us.length).map glOf) : Option (List (GPoly (LC (m + 1))))) with
    | none => []
    | some gls =>
      let k := gls.length
      let J := (List.range k).map fun p ↦ 1 + p % (n - 1)
      let D := (List.range k).map fun p ↦ p / (n - 1)
      let W := (List.range k).map fun i ↦ (List.range k).map fun p ↦
        iterDC Fc ks m (D.getD p 0) ((gls.getD i []).getD (J.getD p 0) O1.zero)
      match gjInvO (MO Fc ks (m + 1)) k W with
      | none => []
      | some H =>
        let I1 := idMatC O1 n
        let r := (List.range n).map fun j ↦ ((j * s : ℕ) : ℤ)
        let gI := (match splitGaugeS Fc ks m γs with | some g => [g] | none => []) ++
          [(idMatC O n, idMatC O n)]
        let g0 := (match splitGaugeS Fc ks m βs with | some g => [g, (g.2, g.1)] | none => []) ++
          [(idMatC O n, idMatC O n)]
        let dg0 := (List.range n).map fun _ ↦ ((0 : ℚ), (0 : ℚ), O.one)
        gI.flatMap fun gi ↦ g0.map fun gz ↦
          (kk, jj, D, Us, Vs, gls, J, H, I1, I1, r, gi.1, gi.2, gz.1, gz.2, dg0)

/-- **The branch above `t = 0` through the simple root `β` of the fibre** (Newton iteration,
`R` coefficients in `t`). -/
def expand0S (m n R : ℕ) (Pp : List (GPoly (LC m))) (β : LC m) : List (LC m) :=
  let O := MOr Fc ks m
  let aS : ℕ → List (LC m) := fun i ↦ if i = n then [O.one] else Pp.getD i []
  let evalP : ℕ → List (LC m) → List (LC m) := fun R' z ↦
    let pw := serPowsO O R' (n + 1) z
    (List.range R').map fun k ↦ lsumC O ((List.range (n + 1)).map fun i ↦
      (serMulO O R' (aS i) (pw.getD i [])).getD k O.zero)
  let Ld := lsumC O ((List.range (n + 1)).map fun i ↦
    O.mul (O.natCast i) (O.mul ((aS i).getD 0 O.zero)
      ((serPowsO O 1 n [β]).getD (i - 1) [O.one] |>.getD 0 O.one)))
  let iv := O.inv Ld
  (List.range R).foldl (fun z j ↦
    if j = 0 then [β] else
      let e := (evalP (j + 1) z).getD j O.zero
      z ++ [O.neg (O.mul e iv)]) []

/-- **The linear S-unit search**: a non-zero `u = ∑_{j<n, l≤B} u_{jl} tˡ θʲ` with `ord_{P∞ₖ} u ≥ cₖ`
(branches `zs` at infinity, slope `s`) and `ord_{P0ₖ} u ≥ μₖ` (branches `ys` above `0`). -/
def unitSearch0S (m n s B : ℕ) (zs ys : List (List (LC m))) (c : List ℤ) (μs : List ℕ) :
    Option (List (LC m)) :=
  let O := MOr Fc ks m
  let D : ℤ := B + (n - 1) * s
  let R : ℕ := ((c.foldr max 0) + D + 1).toNat
  let rowsI := (List.range zs.length).flatMap fun k ↦
    let pw := serPowsO O R n (zs.getD k [])
    (List.range (c.getD k 0 + D).toNat).map fun idx ↦
      let e : ℤ := (idx : ℤ) - D
      (List.range n).flatMap fun (j : ℕ) ↦ (List.range (B + 1)).map fun (l : ℕ) ↦
        let i : ℤ := e + (l : ℤ) + ((j * s : ℕ) : ℤ)
        if i < 0 then O.zero else (pw.getD j []).getD i.toNat O.zero
  let R0 := μs.foldr max 0 + 1
  let rows0 := (List.range ys.length).flatMap fun k ↦
    let pw := serPowsO O R0 n (ys.getD k [])
    (List.range (μs.getD k 0)).map fun e ↦
      (List.range n).flatMap fun (j : ℕ) ↦ (List.range (B + 1)).map fun (l : ℕ) ↦
        if e < l then O.zero else (pw.getD j []).getD (e - l) O.zero
  kerVecO O (n * (B + 1)) (rowsI ++ rows0)

/-- An S-unit with divisor `μ (P0ᵢ − P∞_{n−1})` normalized to norm `1`: `(U, V, k, j)` with
`U V = tᵏ`, the unit being `U/tʲ` (`k = n μ`, `j = μ`). -/
def findUnit0S (m n s Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (zs ys : List (List (LC m)))
    (i0 : ℕ) : Option (List (GPoly (LC m)) × List (GPoly (LC m)) × ℕ × ℕ) :=
  let O := MO Fc ks m
  (List.range mmax).findSome? fun μ0 ↦ (List.range (Bmax + 1)).findSome? fun B ↦ do
    let μ : ℕ := μ0 + 1
    let cu : List ℤ := (List.range n).map fun k ↦ if k = n - 1 then -(μ : ℤ) else 0
    let mu : List ℕ := (List.range n).map fun k ↦ if k = i0 then μ else 0
    let x ← unitSearch0S Fc ks m n s B zs ys cu mu
    let cv : List ℤ := (List.range n).map fun k ↦ if k = n - 1 then 0 else -(μ : ℤ)
    let mv : List ℕ := (List.range n).map fun k ↦ if k = i0 then 0 else μ
    let (B', y) ← (List.range (Bmax + 1)).findSome? fun B' ↦
      (unitSearch0S Fc ks m n s B' zs ys cv mv).map fun y ↦ (B', y)
    let R : ℕ := (μ + B + B' + (n - 1) * s + 2)
    let pws := zs.map (serPowsO O R n)
    let lead : ℕ → LC m := fun k ↦ coeffUS Fc ks m n s B x (pws.getD k []) (cu.getD k 0)
    let κ := O.mul (lead 0) (coeffUS Fc ks m n s B' y (pws.getD 0 []) (cv.getD 0 0))
    if O.isZero κ then none else
    let cN := (List.range zs.length).foldr (fun k acc ↦ O.mul (lead k) acc) O.one
    if O.isZero cN then none else
    let u := unitPolyS Fc ks m n B x
    let v := (unitPolyS Fc ks m n B' y).map (GPoly.smul O (O.inv κ))
    pure ((thPowS Fc ks m Pp u n).map (GPoly.smul O (O.inv cN)),
      (thPowS Fc ks m Pp v n).map (GPoly.smul O cN), n * μ, μ)

/-- **The S-units of a curve split at infinity and above `0`**: `n − 1` units at infinity
(`splitUnits`) and `n − 1` units with divisors `μ (P0ᵢ − P∞_{n−1})`, as `(Us, Vs, kk, jj)`. -/
def split0Units (m s R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs βs : List (LC m)) :
    Option (List (List (GPoly (LC m))) × List (List (GPoly (LC m))) × List ℕ × List ℕ) := do
  let n := Pp.length
  let (Us1, Vs1, _) ← splitUnits Fc ks m s R Bmax mmax Pp γs
  let zs := γs.map (expandInfS Fc ks m n s R Pp)
  let ys := βs.map (expand0S Fc ks m n R Pp)
  let u0 ← (List.range (n - 1)).mapM fun i ↦ findUnit0S Fc ks m n s Bmax mmax Pp zs ys i
  pure (Us1 ++ u0.map (·.1), Vs1 ++ u0.map (·.2.1),
    Us1.map (fun _ ↦ 0) ++ u0.map (·.2.2.1), Us1.map (fun _ ↦ 0) ++ u0.map (·.2.2.2))

/-- **Candidates with computed S-units** (`split0Units`, then `split0Cands`). -/
def split0CandsA (m s R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs βs : List (LC m))
    (ηc : LC m) : List (CandET0 m) :=
  match split0Units Fc ks m s R Bmax mmax Pp γs βs with
  | none => []
  | some (Us, Vs, kk, jj) => split0Cands Fc ks m s Pp γs βs ηc Us Vs kk jj

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`nk_decidesETInf0` with precomputed candidates tried first** (`pre` arbitrary, e.g.
`split0Cands`). -/
theorem nk_decidesETInf0P (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ) (H : List (List (LC (m + 1)))),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandET0 m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0P Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
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
  obtain ⟨Us, Vs, kk, jj, gls, J, D, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg0, hex⟩ := T.exactTLEVG_exists0 m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck sp γs hsplit βs hsp0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchET0_complete Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs kk jj gls J D H Tc Ti r Cg Cgi C Ci dg0 hk1 hU hJH
    hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchET0P_isSome Fc ks m a _ Pp dθ wθ s _ pre N
    (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', kk', jj', gls', J', D', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg0', hk1', hU',
    hJH', hex'⟩ := searchET0P_sound Fc ks m a _ Pp dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInf0 hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck θ Us' Vs' kk' jj' gls' hk1'
    dθ wθ s hU' J' D' H' hJH' hθ hgen hs fp Tc' Ti' res [] Cg' Cgi' r' C' Ci' dg0' hex', h0, hiff]

end MTower

end Curves.MT
