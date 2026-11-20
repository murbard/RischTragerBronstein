import RischTragerBronstein.Mixed.NKLogCert

/-!
# Searching for logarithm certificates (untrusted)

Computable, unverified search for the certificate `(uⱼ, cⱼ)` of `nk_iffC`: everything found here is
checked afterwards by `logCert` and `resCert`, whose soundness is proved, so the search itself carries
no proof obligations.

* truncated power series over code operations (`serMul`, `serInv`, `polyEvalSer`);
* the branch `θ(T)` of the curve at an unramified point `(a, b)` over `Fₘ` by Newton's method
  (`branchSer`).
-/

namespace Curves.MT.Search

variable {α : Type} (O : COps α)

/-- Pad/truncate a series to `L` coefficients. -/
def serT (L : ℕ) (s : List α) : List α := (List.range L).map fun k ↦ s.getD k O.zero

/-- The product of two series modulo `T^L`. -/
def serMul (L : ℕ) (a b : List α) : List α :=
  (List.range L).map fun k ↦ (List.range (k + 1)).foldr
    (fun j acc ↦ O.add (O.mul (a.getD j O.zero) (b.getD (k - j) O.zero)) acc) O.zero

/-- The sum of two series modulo `T^L`. -/
def serAdd (L : ℕ) (a b : List α) : List α :=
  (List.range L).map fun k ↦ O.add (a.getD k O.zero) (b.getD k O.zero)

/-- The inverse of a series with invertible constant term, modulo `T^L`. -/
def serInv (L : ℕ) (a : List α) : List α :=
  let i0 := O.inv (a.getD 0 O.zero)
  (List.range L).foldl (fun (b : List α) k ↦
    if k = 0 then [i0] else
      b ++ [O.mul (O.neg i0) ((List.range k).foldr
        (fun j acc ↦ O.add (O.mul (a.getD (k - j) O.zero) (b.getD j O.zero)) acc) O.zero)]) []

/-- `p(s)` for a polynomial `p` and a series `s`, modulo `T^L` (Horner). -/
def polyEvalSer (L : ℕ) (p : GPoly α) (s : List α) : List α :=
  p.foldr (fun c acc ↦ serAdd O L (serT O L [c]) (serMul O L s acc)) (serT O L [])

/-- Coefficients `cᵢ(T) = aᵢ(a + T)` of `P(a + T, Y) = Yⁿ + ∑ aᵢ(a + T) Yⁱ`, modulo `T^L`. -/
def coeffsAt (L : ℕ) (Pp : List (GPoly α)) (a : α) : List (List α) :=
  Pp.map fun p ↦ polyEvalSer O L p [a, O.one]

/-- `P(a+T, y)` and `P_Y(a+T, y)` for a series `y`, modulo `T^L`. -/
def evalPY (L : ℕ) (cs : List (List α)) (y : List α) : List α × List α :=
  let n := cs.length
  let pows := (List.range (n + 1)).foldl (fun (acc : List (List α)) _ ↦
    acc ++ [serMul O L y (acc.getD (acc.length - 1) (serT O L [O.one]))]) [serT O L [O.one]]
  let pv := (List.range n).foldr (fun i acc ↦ serAdd O L (serMul O L (cs.getD i []) (pows.getD i []))
    acc) (pows.getD n [])
  let pdy := (List.range n).foldr (fun i acc ↦
    if i = 0 then acc else
      serAdd O L (serMul O L (serT O L [O.natCast i]) (serMul O L (cs.getD i []) (pows.getD (i - 1) [])))
        acc) (serMul O L (serT O L [O.natCast n]) (pows.getD (n - 1) []))
  (pv, pdy)

/-- **The branch at an unramified point** `(a, b)`: Newton's iteration `y ↦ y − P/P_Y` modulo `T^L`. -/
def branchSer (L : ℕ) (Pp : List (GPoly α)) (a b : α) (steps : ℕ) : List α :=
  let cs := coeffsAt O L Pp a
  (List.range steps).foldl (fun y _ ↦
    let (pv, pdy) := evalPY O L cs y
    serAdd O L y (serMul O L (serT O L [O.neg O.one]) (serMul O L pv (serInv O L pdy))))
    (serT O L [b])

/-- The order of a series (index of the first non-zero coefficient among the first `L`). -/
def serOrd (L : ℕ) (s : List α) : ℕ := ((List.range L).find? fun k ↦ !(O.isZero (s.getD k O.zero))).getD L

/-- A Laurent series `T^v ∑ cₖ Tᵏ` (`v` may be negative), modulo `T^{v+L}`. -/
structure Laur (α : Type) where
  v : ℤ
  c : List α

/-- `num(a + T)/den(a + T)` as a Laurent series with `L` coefficients. -/
def fracAt (L : ℕ) (num den : GPoly α) (a : α) : Laur α :=
  let d := polyEvalSer O (2 * L) den [a, O.one]
  let k := serOrd O (2 * L) d
  let d' := serT O L (d.drop k)
  let nS := polyEvalSer O L num [a, O.one]
  ⟨-(k : ℤ), serMul O L nS (serInv O L d')⟩

/-- The coefficient of `T^e` of a Laurent series. -/
def laurCoeff (s : Laur α) (e : ℤ) : α :=
  if e < s.v then O.zero else s.c.getD (e - s.v).toNat O.zero

/-- `∑ⱼ fⱼ(a+T) y(T)ʲ` at `T⁻¹`: the coefficient `f₋₁` along the branch `y` (`fⱼ = numⱼ/denⱼ`). -/
def resAt (L : ℕ) (fl : List (GPoly α × GPoly α)) (a : α) (y : List α) : α :=
  let pows := (List.range fl.length).foldl (fun (acc : List (List α)) _ ↦
    acc ++ [serMul O L y (acc.getD (acc.length - 1) (serT O L [O.one]))]) [serT O L [O.one]]
  (List.range fl.length).foldr (fun j acc ↦
    let fj := fracAt O L (fl.getD j ([], [O.one])).1 (fl.getD j ([], [O.one])).2 a
    -- coefficient of T^{-1} in fⱼ · yʲ
    let pj := pows.getD j []
    let term := (List.range L).foldr (fun (i : ℕ) acc2 ↦
      O.add (O.mul (laurCoeff O fj (-1 - (i : ℤ))) (pj.getD i O.zero)) acc2) O.zero
    O.add term acc) O.zero

/-- **A kernel vector** of the matrix with the given rows (`ncols` columns), by Gaussian
elimination with the zero test; `none` if the kernel is zero. -/
def nullVec (ncols : ℕ) (rows : List (List α)) : Option (List α) :=
  -- reduce: list of (pivot column, normalized row)
  let red := rows.foldl (fun (piv : List (ℕ × List α)) r ↦
    -- eliminate existing pivots from r
    let r' := piv.foldl (fun r (pc, pr) ↦
      let f := r.getD pc O.zero
      (List.range ncols).map fun j ↦ O.add (r.getD j O.zero) (O.neg (O.mul f (pr.getD j O.zero)))) r
    match (List.range ncols).find? fun j ↦ !(O.isZero (r'.getD j O.zero)) with
    | none => piv
    | some pc =>
      let iv := O.inv (r'.getD pc O.zero)
      let nr := (List.range ncols).map fun j ↦ O.mul iv (r'.getD j O.zero)
      -- eliminate the new pivot from old rows
      (piv.map fun (qc, qr) ↦
        let f := qr.getD pc O.zero
        (qc, (List.range ncols).map fun j ↦
          O.add (qr.getD j O.zero) (O.neg (O.mul f (nr.getD j O.zero)))))
        ++ [(pc, nr)]) []
  let pcs := red.map Prod.fst
  match (List.range ncols).find? fun j ↦ !(pcs.contains j) with
  | none => none
  | some fc =>
    some ((List.range ncols).map fun j ↦
      if j = fc then O.one else
        match red.find? fun (pc, _) ↦ pc == j with
        | some (_, pr) => O.neg (pr.getD fc O.zero)
        | none => O.zero)

end Curves.MT.Search

namespace Curves.MT.Search

open Curves.LT

variable (Fc : Sup.BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The rational gcd of a list of rationals. -/
def ratGcd (l : List ℚ) : ℚ :=
  ((l.map fun q ↦ q.num.natAbs).foldr Nat.gcd 0 : ℕ) / ((l.map (·.den)).foldr Nat.lcm 1 : ℕ)

/-- `(t − a)ᴱ` over level-`m` codes. -/
def linPow (m : ℕ) (a : LC m) (E : ℕ) : GPoly (LC m) :=
  sysPowC (MO Fc ks m) [(MO Fc ks m).neg a, (MO Fc ks m).one] E

/-- **The order-conditions search**: `W = ∑ cᵢₖ tᵏ θⁱ` over the monomials of weight
`n k + i d ≤ Wb` (the pole order at the single place at infinity), with `ord_{(a,b)} W ≥ τ` at each
`(a, b, τ)`; returns the coefficients `pᵢ(t)`. -/
def searchW (m n d Wb : ℕ) (Pp : List (GPoly (LC m))) (pts : List (LC m × LC m × ℕ)) :
    Option (List (GPoly (LC m))) :=
  let O := MO Fc ks m
  let M := Wb / n
  let L := (pts.map fun p ↦ p.2.2).foldr max 0 + 1
  let cols := (List.range (n * (M + 1))).filter fun col ↦ n * (col % (M + 1)) + (col / (M + 1)) * d ≤ Wb
  let rows := pts.flatMap fun (a, b, τ) ↦
    let y := branchSer O L Pp a b 6
    let ypow := (List.range n).foldl (fun (acc : List (List (LC m))) _ ↦
      acc ++ [serMul O L y (acc.getD (acc.length - 1) (serT O L [O.one]))]) [serT O L [O.one]]
    let tpow := (List.range (M + 1)).foldl (fun (acc : List (List (LC m))) _ ↦
      acc ++ [serMul O L [a, O.one] (acc.getD (acc.length - 1) (serT O L [O.one]))]) [serT O L [O.one]]
    (List.range τ).map fun l ↦ cols.map fun col ↦
      (serMul O L (tpow.getD (col % (M + 1)) []) (ypow.getD (col / (M + 1)) [])).getD l O.zero
  (nullVec O cols.length rows).map fun v ↦
    (List.range n).map fun i ↦ (List.range (M + 1)).map fun k ↦
      match cols.idxOf? (i * (M + 1) + k) with
      | some j => v.getD j O.zero
      | none => O.zero

/-- The `resCert` data for `g = ∑ gpⱼ θʲ / D`: the least `k ≤ kmax` with `Bᵏ ≡ U D mod P`. -/
def findResCert (m : ℕ) (Pp gp : List (GPoly (LC m))) (D : GPoly (LC m)) (kmax : ℕ) :
    Option (ℕ × List (GPoly (LC m))) :=
  let O := MO Fc ks m
  let O1 := MOr Fc ks (m + 1)
  (List.range kmax).findSome? fun k0 ↦
    let k := k0 + 1
    let R := remP O1 (nkPC Fc ks m Pp) (sysPowC O1 (gp.map (polyCode Fc ks m)) k)
    let us := R.map fun c ↦ cofC O c.1 (GPoly.mul O D c.2)
    if us.all Prod.fst && resCert Fc ks m Pp gp D k (us.map Prod.snd) then
      some (k, us.map Prod.snd) else none

/-- **The certificate search.** `roots`: the roots `a` of the denominator of `f` with their full
fibres `b`; `sDen a = ω(a) − a′`. Returns `(u, c, gp, D, k, U)` with `logCert` and `resCert` checked. -/
def findCert (m : ℕ) (sDen : LC m → LC m) (Pp : List (GPoly (LC m))) (fl : List (LC (m + 1)))
    (roots : List (LC m × List (LC m))) (prec Kmax Mmax : ℕ) :
    Option (GPoly (LC (m + 1)) × ℚ × List (GPoly (LC m)) × GPoly (LC m) × ℕ × List (GPoly (LC m))) :=
  let O := MO Fc ks m
  let O1 := MOr Fc ks (m + 1)
  let n := Pp.length
  let P := nkPC Fc ks m Pp
  let fr : List (GPoly (LC m) × GPoly (LC m)) := (List.range n).map fun j ↦ fl.getD j O1.zero
  -- the residues
  let pts : List (LC m × LC m × Option ℚ) := roots.flatMap fun (a, bs) ↦ bs.map fun b ↦
    let y := branchSer O prec Pp a b 6
    (a, b, ratValC Fc ks m (O.mul (resAt O prec fr a y) (O.inv (sDen a))))
  if !(pts.all fun p ↦ p.2.2.isSome) then none else
  let rs := pts.map fun p ↦ p.2.2.getD 0
  let nz := rs.filter (· ≠ 0)
  if nz = [] then none else
  let c := ratGcd nz
  let ns : List ℤ := rs.map fun r ↦ (r / c).num
  let nmin := ns.foldr min 0
  match dThetaC O1 P with
  | none => none
  | some dθ =>
  (List.range Kmax).findSome? fun κ0 ↦
    let κ := κ0 + 1
    let E := (κ * (-nmin)).toNat
    let tg := (pts.zip ns).map fun (p, k) ↦ (p.1, p.2.1, ((κ : ℤ) * k + E).toNat)
    let den := roots.foldr (fun (a, _) acc ↦ GPoly.mul O (linPow Fc ks m a E) acc) [O.one]
    let d := Tower.NestM.degG O (Pp.getD 0 [])
    (List.range (Mmax + 1)).findSome? fun Wb ↦
      match searchW Fc ks m n d Wb Pp tg with
      | none => none
      | some ps =>
        let u : GPoly (LC (m + 1)) := ps.map fun p ↦ ((p, den) : LC (m + 1))
        match logDerC O1 P dθ u with
        | none => none
        | some ld =>
          let cq : ℚ := c / κ
          let g := (List.range n).map fun j ↦
            O1.add (fl.getD j O1.zero) (O1.neg (O1.mul (mcst Fc ks (m + 1) cq) (ld.getD j O1.zero)))
          let D := lcmGL O (g.map Prod.snd)
          let cofs := g.map fun e ↦ cofC O D e.2
          if !(cofs.all Prod.fst) then none else
          let gp := (g.zip cofs).map fun (e, cf) ↦ GPoly.mul O e.1 cf.2
          if !(GPoly.squarefreeCheck O D) then none else
          match findResCert Fc ks m Pp gp D 4 with
          | none => none
          | some (k, U) =>
            if logCert Fc ks m P fl (nkFlR m gp D) [u] [cq] then some (u, cq, gp, D, k, U) else none

end Curves.MT.Search
