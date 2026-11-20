import RischTragerBronstein.Mixed.NKDecidesETInfVG
import RischTragerBronstein.Mixed.NKUnitFind

/-!
# Candidates for curves split at infinity (untrusted)

For `θⁿ + ∑ aᵢ(t) θⁱ = 0` with coefficients in `Fₘ[t]`, split at infinity (`deg aᵢ ≤ (n − i) s`,
leading polynomial with distinct roots `γₖ ∈ Fₘ`), the data that the decisions `nk_decidesInfVG`
and `nk_decidesETInfVG` search for are computed here directly, over the code field `Fₘ`. Every
output is re-checked by the kernel checks of those decisions (`unitsC`, `indepC`, `traceW` and
the runtime checks of `exactTLVG`/`exactTLEVG`), so nothing here needs a proof; the enumeration
stays as the fallback that makes the search complete.

* `expandInfS`: the branches `θₖ = tˢ ∑ⱼ cₖⱼ t⁻ʲ` at the places at infinity (`cₖ₀ = γₖ`,
  `cₖⱼ = −[wʲ] Q(w, z_{<j})/L′(γₖ)` for `Q(w, z) = w^{ns} P(1/w, z/w^s)`).
* `unitSearchS`: the units `u = ∑ u_{jl} tˡ θʲ` with divisor `∑ cₖ Pₖ` (`∑ cₖ = 0`) as the kernel
  of the linear conditions `ord_{Pₖ} u ≥ cₖ` (`rrefO`, `kerVecO`: Gauss–Jordan over any code field).
* `splitUnits`: units with divisors `μ (Pᵢ − P_{n−1})`, their inverses (normalized so that
  `u v = 1`), logarithmic derivatives `u′/u` (`logDerC`), the independence certificate.
* `splitCandsL`, `splitCandsE`: complete candidates — basis `θʲ/t^{⌊j d₀/n⌋}` (shifts
  `j s − ⌊j d₀/n⌋`), the gauge at infinity `Vᵀ` (`V` the Vandermonde matrix of the `γₖ`) and its
  inverse, at `t = 0` the permutation sorting by `j d₀ mod n` with diagonal data
  `((j d₀ mod n)/n, j/n, c₀)` (exponential level).
* `searchIVGP`, `searchETVGP`: try the candidates first, then enumerate; sound and complete as
  `searchIVG`, `searchETVG`, and the decisions hold for them (`nk_decidesInfVGP`,
  `nk_decidesETInfVGP`).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Generic

variable {α : Type} (O : COps α)

/-- Truncated product of two series (coefficient lists), `R` coefficients. -/
def serMulO (R : ℕ) (a b : List α) : List α :=
  (List.range R).map fun k ↦ lsumC O ((List.range (k + 1)).map fun i ↦
    O.mul (a.getD i O.zero) (b.getD (k - i) O.zero))

/-- Truncated powers `[1, z, z², …]` (`n` of them). -/
def serPowsO (R n : ℕ) (z : List α) : List (List α) :=
  (List.range n).foldl (fun acc _ ↦ acc ++ [serMulO O R (acc.getLast?.getD [O.one]) z])
    [(List.range R).map fun k ↦ if k = 0 then O.one else O.zero] |>.take n

/-- One Gauss–Jordan pass: reduced rows (pivot `1`, eliminated elsewhere) and pivot columns. -/
def rrefO (ncols : ℕ) (rows : List (List α)) : List (List α) × List ℕ :=
  let st := (List.range ncols).foldl (fun (st : List (List α) × List ℕ × List (List α)) c ↦
    let (done, pivs, rest) := st
    match rest.findIdx? fun r ↦ !O.isZero (r.getD c O.zero) with
    | none => st
    | some p =>
      let rp := rest.getD p []
      let iv := O.inv (rp.getD c O.zero)
      let rp' := (List.range ncols).map fun j ↦ O.mul iv (rp.getD j O.zero)
      let elim : List α → List α := fun r ↦
        let f := r.getD c O.zero
        (List.range ncols).map fun j ↦ O.add (r.getD j O.zero) (O.neg (O.mul f (rp'.getD j O.zero)))
      (done.map elim ++ [rp'], pivs ++ [c], (rest.eraseIdx p).map elim)) ([], [], rows)
  (st.1, st.2.1)

/-- A non-zero kernel vector (first free column `1`), if any. -/
def kerVecO (ncols : ℕ) (rows : List (List α)) : Option (List α) :=
  let (red, pivs) := rrefO O ncols rows
  match (List.range ncols).find? fun c ↦ !pivs.contains c with
  | none => none
  | some f => some ((List.range ncols).map fun c ↦
      if c = f then O.one else
      match pivs.idxOf? c with
      | some k => O.neg ((red.getD k []).getD f O.zero)
      | none => O.zero)

/-- Gauss–Jordan inverse of a square matrix over any code field (untrusted). -/
def gjInvO (n : ℕ) (A : List (List α)) : Option (List (List α)) :=
  let aug : List (List α) := (List.range n).map fun i ↦
    ((List.range n).map fun j ↦ (A.getD i []).getD j O.zero) ++
      (List.range n).map fun j ↦ if i = j then O.one else O.zero
  let (red, pivs) := rrefO O (2 * n) aug
  if pivs = List.range n then some (red.map fun r ↦ r.drop n) else none

end Generic

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `bᵢ(w) = w^{(n−i)s} aᵢ(1/w)` (and `b_n = 1`), as coefficient lists in `w`. -/
def bCoeffS (m n s : ℕ) (Pp : List (GPoly (LC m))) (i : ℕ) : List (LC m) :=
  let O := MO Fc ks m
  if i = n then [O.one] else
    (List.range ((n - i) * s + 1)).map fun l ↦ (Pp.getD i []).getD ((n - i) * s - l) O.zero

/-- `Q(w, z) = ∑ bᵢ(w) zⁱ`, truncated. -/
def evalQS (m n s R : ℕ) (Pp : List (GPoly (LC m))) (z : List (LC m)) : List (LC m) :=
  let O := MO Fc ks m
  let pw := serPowsO O R (n + 1) z
  (List.range R).map fun k ↦ lsumC O ((List.range (n + 1)).map fun i ↦
    (serMulO O R (bCoeffS Fc ks m n s Pp i) (pw.getD i [])).getD k O.zero)

/-- **The branch `z = θ/tˢ` at the place at infinity with leading value `γ`** (`R` coefficients
in `w = 1/t`). -/
def expandInfS (m n s R : ℕ) (Pp : List (GPoly (LC m))) (γ : LC m) : List (LC m) :=
  let O := MO Fc ks m
  let Ld := lsumC O ((List.range (n + 1)).map fun i ↦
    O.mul (O.natCast i) (O.mul ((bCoeffS Fc ks m n s Pp i).getD 0 O.zero)
      ((serPowsO O 1 n [γ]).getD (i - 1) [O.one] |>.getD 0 O.one)))
  let iv := O.inv Ld
  (List.range R).foldl (fun z j ↦
    if j = 0 then [γ] else
      let e := (evalQS Fc ks m n s (j + 1) Pp z).getD j O.zero
      z ++ [O.neg (O.mul e iv)]) []

/-- The coefficient of `wᵉ` of `u = ∑ u_{jl} tˡ θʲ` along a branch (powers `pw` of `z`). -/
def coeffUS (m n s B : ℕ) (x : List (LC m)) (pw : List (List (LC m))) (e : ℤ) : LC m :=
  let O := MO Fc ks m
  lsumC O ((List.range n).flatMap fun (j : ℕ) ↦ (List.range (B + 1)).map fun (l : ℕ) ↦
    let i : ℤ := e + (l : ℤ) + ((j * s : ℕ) : ℤ)
    if i < 0 then O.zero else O.mul (x.getD (j * (B + 1) + l) O.zero) ((pw.getD j []).getD i.toNat O.zero))

/-- **The linear unit search**: a non-zero `u = ∑_{j<n, l≤B} u_{jl} tˡ θʲ` with `ord_{Pₖ} u ≥ cₖ`. -/
def unitSearchS (m n s B : ℕ) (zs : List (List (LC m))) (c : List ℤ) : Option (List (LC m)) :=
  let O := MO Fc ks m
  let D : ℤ := B + (n - 1) * s
  let R : ℕ := ((c.foldr max 0) + D + 1).toNat
  let rows := (List.range zs.length).flatMap fun k ↦
    let pw := serPowsO O R n (zs.getD k [])
    (List.range (c.getD k 0 + D).toNat).map fun idx ↦
      let e : ℤ := (idx : ℤ) - D
      (List.range n).flatMap fun (j : ℕ) ↦ (List.range (B + 1)).map fun (l : ℕ) ↦
        let i : ℤ := e + (l : ℤ) + ((j * s : ℕ) : ℤ)
        if i < 0 then O.zero else (pw.getD j []).getD i.toNat O.zero
  kerVecO O (n * (B + 1)) rows

/-- The `θ`-coefficients (polynomials in `t`) of `u`. -/
def unitPolyS (m n B : ℕ) (x : List (LC m)) : List (GPoly (LC m)) :=
  (List.range n).map fun j ↦ (List.range (B + 1)).map fun l ↦ x.getD (j * (B + 1) + l) (MO Fc ks m).zero

/-- The product of two `θ`-polynomials with coefficients in `Fₘ[t]`, reduced modulo
`θⁿ + ∑ aᵢ θⁱ`. -/
def thMulS (m : ℕ) (Pp : List (GPoly (LC m))) (a b : List (GPoly (LC m))) : List (GPoly (LC m)) :=
  let O := MO Fc ks m
  let n := Pp.length
  let L := a.length + b.length
  let c := (List.range L).map fun k ↦ GPoly.trim O ((List.range (k + 1)).foldr (fun i acc ↦
    GPoly.add O acc (GPoly.mul O (a.getD i []) (b.getD (k - i) []))) [])
  let red := (List.range L).reverse.foldl (fun c k ↦
    if k < n then c else
      let ck := c.getD k []
      (List.range L).map fun i ↦
        if i = k then [] else
        if k - n ≤ i ∧ i < k then
          GPoly.trim O (GPoly.sub O (c.getD i []) (GPoly.mul O ck (Pp.getD (i + n - k) [])))
        else c.getD i []) c
  (List.range n).map fun i ↦ red.getD i []

/-- `uᵏ` modulo `P`. -/
def thPowS (m : ℕ) (Pp : List (GPoly (LC m))) (u : List (GPoly (LC m))) (k : ℕ) :
    List (GPoly (LC m)) :=
  (List.range k).foldl (fun acc _ ↦ thMulS Fc ks m Pp acc u) [[(MO Fc ks m).one]]

/-- A unit with divisor `μ c`, its inverse (`u v = 1`) and its norm, for the first `μ ≤ mmax`,
`B ≤ Bmax`. -/
def findUnitS (m n s Bmax mmax : ℕ) (zs : List (List (LC m))) (c : List ℤ) :
    Option (List (GPoly (LC m)) × List (GPoly (LC m)) × LC m) :=
  let O := MO Fc ks m
  (List.range mmax).findSome? fun μ ↦ (List.range (Bmax + 1)).findSome? fun B ↦ do
    let cμ := c.map (((μ + 1 : ℕ) : ℤ) * ·)
    let x ← unitSearchS Fc ks m n s B zs cμ
    let (B', y) ← (List.range (Bmax + 1)).findSome? fun B' ↦
      (unitSearchS Fc ks m n s B' zs (cμ.map (- ·))).map fun y ↦ (B', y)
    let R : ℕ := ((cμ.foldr (fun a b ↦ max |a| b) 0) + B + B' + (n - 1) * s + 2).toNat
    let pws := zs.map (serPowsO O R n)
    let lead : ℕ → LC m := fun k ↦ coeffUS Fc ks m n s B x (pws.getD k []) (cμ.getD k 0)
    let e := cμ.getD 0 0
    let κ := O.mul (lead 0) (coeffUS Fc ks m n s B' y (pws.getD 0 []) (-e))
    if O.isZero κ then none else
    let N := (List.range zs.length).foldr (fun k acc ↦ O.mul (lead k) acc) O.one
    pure (unitPolyS Fc ks m n B x, unitPolyS Fc ks m n B' (y.map (O.mul (O.inv κ))), N)

/-- **The units of a split curve**: divisors `μ (Pᵢ − P_{n−1})`, their inverses, logarithmic
derivatives, `θ′`, `1/P_θ`, the trace codes and the independence certificate. -/
def splitUnits (m s R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m)) :
    Option (List (List (GPoly (LC m))) × List (List (GPoly (LC m))) ×
      List (GPoly (LC (m + 1))) × List ℕ × List (List (LC (m + 1))) ×
      GPoly (LC (m + 1)) × GPoly (LC (m + 1)) × List (LC (m + 1))) := do
  let n := Pp.length
  let O1 := MOr Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let zs := γs.map (expandInfS Fc ks m n s R Pp)
  let us0 ← (List.range (n - 1)).mapM fun i ↦
    findUnitS Fc ks m n s Bmax mmax zs ((List.range n).map fun k ↦
      if k = i then 1 else if k = n - 1 then -1 else 0)
  -- `uⁿ/N(u)` has norm `1`, so its logarithmic derivative has trace `0`
  let O := MO Fc ks m
  let us := us0.map fun uvN ↦
    ((thPowS Fc ks m Pp uvN.1 n).map (GPoly.smul O (O.inv uvN.2.2)),
      (thPowS Fc ks m Pp uvN.2.1 n).map (GPoly.smul O uvN.2.2))
  let dθ ← dThetaC O1 P
  let wθ ← invModC O1 P (GPoly.derivX O1 P)
  let gls ← us.mapM fun uv ↦ logDerC O1 P dθ (nkFl Fc ks m uv.1)
  let J := (List.range (n - 1)).map (· + 1)
  let A := (List.range (n - 1)).map fun i ↦ J.map fun j ↦ (gls.getD i []).getD j O1.zero
  let H ← gjInvO O1 (n - 1) A
  pure (us.map (·.1), us.map (·.2), gls, J, H, dθ, wθ, traceCodes Fc ks m P)

/-- The gauge at infinity `Vᵀ` (`V a b = γ_aᵇ`) and its inverse. -/
def splitGaugeS (m : ℕ) (γs : List (LC m)) : Option (List (List (LC m)) × List (List (LC m))) :=
  let O := MO Fc ks m
  let n := γs.length
  let V := γs.map fun γ ↦ serPowsO O 1 n [γ] |>.map fun p ↦ p.getD 0 O.one
  (gjInvO O n V).map fun Vi ↦ (V, Vi)

/-- The identity matrix of codes. -/
def idMatC {α : Type} (O : COps α) (n : ℕ) : List (List α) :=
  (List.range n).map fun i ↦ (List.range n).map fun j ↦ if i = j then O.one else O.zero

/-- **The candidates at a logarithmic level** (basis `θʲ`, shifts `j s`, gauge `Vᵀ` or `1`). -/
def splitCandsL (m s R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m)) :
    List (CandIVG m) :=
  match splitUnits Fc ks m s R Bmax mmax Pp γs with
  | none => []
  | some (Us, Vs, gls, J, H, _) =>
    let n := Pp.length
    let I1 := idMatC (MOr Fc ks (m + 1)) n
    let r := (List.range n).map fun j ↦ ((j * s : ℕ) : ℤ)
    let gs := (match splitGaugeS Fc ks m γs with | some g => [g] | none => []) ++
      [(idMatC (MO Fc ks m) n, idMatC (MO Fc ks m) n)]
    gs.map fun g ↦ (Us, Vs, gls, J, H, I1, I1, r, g.1, g.2)

/-- The permutation matrix `δ_{b, τ a}`. -/
def permMatC {α : Type} (O : COps α) (n : ℕ) (τ : List ℕ) : List (List α) :=
  (List.range n).map fun a ↦ (List.range n).map fun b ↦ if b = τ.getD a 0 then O.one else O.zero

/-- **The candidates at an exponential level** (single place above `t = 0` of trailing degree
`d₀`): basis `θʲ/t^{⌊j d₀/n⌋}`, shifts `j s − ⌊j d₀/n⌋`, gauge `Vᵀ` or `1` at infinity, the
permutation sorting by `j d₀ mod n` (or its inverse) at `t = 0`, diagonal data
`((j d₀ mod n)/n, j/n, c₀)`. -/
def splitCandsE (m s R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m)) :
    List (CandETVG m) :=
  match splitUnits Fc ks m s R Bmax mmax Pp γs with
  | none => []
  | some (Us, Vs, gls, J, H, _) =>
    let n := Pp.length
    let O := MO Fc ks m
    let O1 := MOr Fc ks (m + 1)
    let a0 := Pp.getD 0 []
    let d0 := trailG O a0
    let c0 := a0.getD d0 O.zero
    let fl : ℕ → ℕ := fun j ↦ j * d0 / n
    let Tc := (List.range n).map fun i ↦ (List.range n).map fun j ↦
      if i = j then tInvPowC Fc ks m (fl j) else O1.zero
    let Ti := (List.range n).map fun i ↦ (List.range n).map fun j ↦
      if i = j then tPowC Fc ks m (fl j) else O1.zero
    let r := (List.range n).map fun j ↦ ((j * s : ℕ) : ℤ) - (fl j : ℤ)
    let gs := (match splitGaugeS Fc ks m γs with | some g => [g] | none => []) ++
      [(idMatC O n, idMatC O n)]
    let τ := (List.range n).insertionSort fun i j ↦ j * d0 % n ≤ i * d0 % n
    let τi := (List.range n).map fun a ↦ τ.idxOf a
    let zs : List (List ℕ) := [τ, τi, List.range n, (List.range n).reverse]
    let z0 := zs.flatMap fun σ ↦
      let σi := (List.range n).map fun a ↦ σ.idxOf a
      [(permMatC O n σ, permMatC O n σi, σ), (permMatC O n σi, permMatC O n σ, σ)]
    gs.flatMap fun g ↦ z0.map fun c ↦
      (Us, Vs, gls, J, H, Tc, Ti, r, g.1, g.2, c.1, c.2.1,
        (List.range n).map fun a ↦
          let j := c.2.2.getD a 0
          (((j * d0 % n : ℕ) : ℚ) / n, ((j : ℕ) : ℚ) / n, c0))

/-- **The search with precomputed candidates** (logarithmic level), tried first. -/
def searchIVGP (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVG m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (ivgTry Fc ks m η rde Pp dθ wθ s f) with
  | some b => some b
  | none => searchIVG Fc ks m η rde Pp dθ wθ s f B

lemma searchIVGP_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVG m)) (B : ℕ) (b : Bool)
    (h : searchIVGP Fc ks m η rde Pp dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m))),
      gls.length + 1 = Pp.length ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLVG Fc ks m η rde [] C Ci r (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchIVGP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold ivgTry at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchIVG_sound Fc ks m η rde Pp dθ wθ s f B b h

lemma searchIVGP_isSome (m : ℕ) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVG m)) (B : ℕ)
    (h : (searchIVG Fc ks m η rde Pp dθ wθ s f B).isSome) :
    (searchIVGP Fc ks m η rde Pp dθ wθ s f pre B).isSome := by
  unfold searchIVGP
  split
  · rfl
  · exact h

/-- **The search with precomputed candidates** (exponential level), tried first. -/
def searchETVGP (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVG m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (etvgTry Fc ks m a rde Pp dθ wθ s f) with
  | some b => some b
  | none => searchETVG Fc ks m a rde Pp dθ wθ s f B

lemma searchETVGP_sound (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVG m)) (B : ℕ) (b : Bool)
    (h : searchETVGP Fc ks m a rde Pp dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (Cg Cgi C Ci : List (List (LC m)))
      (dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 1 = Pp.length ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLEVG Fc ks m a rde [] Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchETVGP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold etvgTry at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchETVG_sound Fc ks m a rde Pp dθ wθ s f B b h

lemma searchETVGP_isSome (m : ℕ) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVG m)) (B : ℕ)
    (h : (searchETVG Fc ks m a rde Pp dθ wθ s f B).isSome) :
    (searchETVGP Fc ks m a rde Pp dθ wθ s f pre B).isSome := by
  unfold searchETVGP
  split
  · rfl
  · exact h

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`nk_decidesInfVG` with precomputed candidates tried first** (logarithmic level;
`pre` arbitrary, e.g. `splitCandsL`): for every large bound, `elM` decides `τ(f)/n`, `searchIVG` decides the
exact part (finding the units, the basis and the gauge), and together they decide `f`. -/
theorem nk_decidesInfVGP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length ∧
      unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandIVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVGP Fc ks m η (prdeC Fc ks lv m) Pp dθ wθ s
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
  obtain ⟨Us, Vs, gls, J, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, C, Ci, hex⟩ := T.exactTLVG_exists m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp qE csE sE tE s2E t2E hck sp γs hsplit θ hθ (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchIVG_complete Fc ks m η (prdeC Fc ks lv m) Pp dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs gls J H Tc Ti r C Ci hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchIVGP_isSome Fc ks m η _ Pp dθ wθ s _ pre N
    (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', gls', J', H', Tc', Ti', r', C', Ci', hk1', hU', hJH', hex'⟩ :=
    searchIVGP_sound Fc ks m η _ Pp dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVG hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck θ Us' Vs' gls' hk1' dθ wθ s
    hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res [] C' Ci' r' hex', h0, hiff]

set_option maxHeartbeats 4000000 in
/-- **`nk_decidesETInfVG` with precomputed candidates tried first** (exponential level;
`pre` arbitrary, e.g. `splitCandsE`): for every large bound, `elM` decides
`τ(f)/n`, `searchETVG` decides the exact part (finding the units, the basis and both gauges),
and together they decide `f`. -/
theorem nk_decidesETInfVGP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (fp : List (GPoly (LC m))) (pre : List (CandETVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVGP Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
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
  obtain ⟨Us, Vs, gls, J, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg0, hex⟩ := T.exactTLEVG_exists m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck sp γs hsplit hsh0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchETVG_complete Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs gls J H Tc Ti r Cg Cgi C Ci dg0 hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchETVGP_isSome Fc ks m a _ Pp dθ wθ s _ pre N
    (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', gls', J', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg0', hk1', hU', hJH', hex'⟩ :=
    searchETVGP_sound Fc ks m a _ Pp dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInfVG hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck hsh0 θ Us' Vs' gls' hk1'
    dθ wθ s hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res [] Cg' Cgi' r' C' Ci' dg0' hex', h0, hiff]

end MTower

end Curves.MT
