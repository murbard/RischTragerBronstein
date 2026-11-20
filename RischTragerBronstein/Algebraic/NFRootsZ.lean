import RischTragerBronstein.Algebraic.NFRootFinder

/-!
# A fast root finder in number fields (Zassenhaus)

`ZF.factorZ`: factorization over `ℤ` by Zassenhaus's method (factorization modulo a prime by
distinct- and equal-degree splitting, multifactor Hensel lifting, recombination by trial
division). It is **unverified** and only produces candidates: `rfNFZ` is Trager's norm method
(`rootsIn`) with `factorZ` in place of Kronecker's exponential search, and — like `rfNF` — it only
returns a list when the candidate roots are roots whose multiplicities add up to the degree, so the
answer is all the roots. Every use of a `RootFinder` is re-checked by certificates anyway
(`certCheck`), so no correctness proof is needed; `rfNF` remains the root finder that is proved
complete.
-/

open Polynomial CPoly

namespace ZF

abbrev ZP := List Int

def trimZ (f : ZP) : ZP := (f.reverse.dropWhile (· == 0)).reverse

def degZ (f : ZP) : Int := (trimZ f).length - 1

def lcZ (f : ZP) : Int := (trimZ f).getLastD 0

def addZ : ZP → ZP → ZP
  | [], g => g
  | f, [] => f
  | a :: f, b :: g => (a + b) :: addZ f g

def negZ (f : ZP) : ZP := f.map (- ·)
def subZ (f g : ZP) : ZP := addZ f (negZ g)
def scaleZ (c : Int) (f : ZP) : ZP := f.map (c * ·)

def mulZ (f g : ZP) : ZP :=
  f.foldr (fun a acc ↦ addZ (scaleZ a g) (0 :: acc)) []

/-- Exact division by a polynomial with leading coefficient dividing (returns none if inexact). -/
def divExactZ (f g : ZP) : Option ZP := Id.run do
  let g := trimZ g
  let dg := g.length - 1
  let lg := g.getLastD 1
  let mut r := (trimZ f).toArray
  if r.size < g.length then
    return (if r.all (· == 0) then some [] else none)
  let dq := r.size - g.length
  let mut q := Array.replicate (dq + 1) (0 : Int)
  for ii in [0:dq + 1] do
    let i := dq - ii
    let c := r[i + dg]!
    if c % lg != 0 then return none
    let qc := c / lg
    q := q.set! i qc
    for j in [0:g.length] do
      r := r.set! (i + j) (r[i + j]! - qc * g[j]!)
  if r.all (· == 0) then some q.toList else none

def derivZ (f : ZP) : ZP := ((f.drop 1).zipIdx.map fun (a, i) ↦ a * (i + 1 : Int))

def contZ (f : ZP) : Int := f.foldl (fun g a ↦ Int.ofNat (Nat.gcd g.natAbs a.natAbs)) 0

def primZ (f : ZP) : ZP :=
  let c := contZ f
  let f := if c == 0 then f else f.map (· / c)
  if lcZ f < 0 then negZ f else f

/-! ### Arithmetic modulo `m` -/

def md (m a : Int) : Int := a % m  -- Int.emod: nonnegative for m > 0

def normM (m : Int) (f : ZP) : ZP := trimZ (f.map (md m))

def addM (m : Int) (f g : ZP) : ZP := normM m (addZ f g)
def subM (m : Int) (f g : ZP) : ZP := normM m (subZ f g)
def mulM (m : Int) (f g : ZP) : ZP := normM m (mulZ f g)

/-- Modular inverse (extended Euclid); `m` need not be prime, `a` must be a unit. -/
partial def invM (m a : Int) : Int :=
  let rec go (r0 r1 s0 s1 : Int) : Int :=
    if r1 == 0 then md m s0 else go r1 (r0 - (r0 / r1) * r1) s1 (s0 - (r0 / r1) * s1)
  go (md m a) m 1 0

/-- Division with remainder modulo `m` (leading coefficient of `g` a unit). -/
def divModM (m : Int) (f g : ZP) : ZP × ZP := Id.run do
  let g := normM m g
  if g.isEmpty then return ([], normM m f)
  let dg := g.length - 1
  let il := invM m (g.getLastD 1)
  let mut r := (normM m f).toArray
  if r.size < g.length then return ([], r.toList)
  let dq := r.size - g.length
  let mut q := Array.replicate (dq + 1) (0 : Int)
  for ii in [0:dq + 1] do
    let i := dq - ii
    let c := md m (r[i + dg]! * il)
    q := q.set! i c
    for j in [0:g.length] do
      r := r.set! (i + j) (md m (r[i + j]! - c * g[j]!))
  (normM m q.toList, normM m r.toList)

def remM (m : Int) (f g : ZP) : ZP := (divModM m f g).2

def monicM (m : Int) (f : ZP) : ZP :=
  let f := normM m f
  if f.isEmpty then f else normM m (f.map (· * invM m (f.getLastD 1)))

partial def gcdM (p : Int) (f g : ZP) : ZP :=
  let g := normM p g
  if g.isEmpty then monicM p f else gcdM p g (remM p f g)

/-- Extended gcd modulo a prime: `s f + t g = gcd`. -/
partial def xgcdM (p : Int) (f g : ZP) : ZP × ZP × ZP :=
  let rec go (r0 r1 s0 s1 t0 t1 : ZP) : ZP × ZP × ZP :=
    if (normM p r1).isEmpty then
      let c := invM p ((normM p r0).getLastD 1)
      (normM p (r0.map (· * c)), normM p (s0.map (· * c)), normM p (t0.map (· * c)))
    else
      let (q, r) := divModM p r0 r1
      go r1 r (s1) (subM p s0 (mulM p q s1)) t1 (subM p t0 (mulM p q t1))
  go f g [1] [] [] [1]

def powModM (p : Int) (b : ZP) (e : Nat) (f : ZP) : ZP := Id.run do
  let mut result : ZP := [1]
  let mut base := remM p b f
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then result := remM p (mulM p result base) f
    base := remM p (mulM p base base) f
    e := e / 2
  result

/-! ### Factoring modulo `p` (distinct-degree, then equal-degree with deterministic trials) -/

/-- Distinct-degree factorization of a monic squarefree `f` modulo `p`. -/
def ddf (p : Nat) (f : ZP) : List (Nat × ZP) := Id.run do
  let pp : Int := p
  let mut res : List (Nat × ZP) := []
  let mut f := monicM pp f
  let mut h : ZP := [0, 1]
  let mut i := 0
  while (f.length - 1) ≥ 2 * (i + 1) do
    i := i + 1
    h := powModM pp h p f
    let g := gcdM pp f (subM pp h [0, 1])
    if g.length > 1 then
      res := (i, g) :: res
      f := (divModM pp f g).1
      h := remM pp h f
  if f.length > 1 then res := (f.length - 1, f) :: res
  res

/-- Equal-degree splitting (Cantor–Zassenhaus, odd `p`) with trial elements `x + a`, `x² + a`,…. -/
partial def edf (p : Nat) (d : Nat) (f : ZP) (seed : Nat) : List ZP :=
  let pp : Int := p
  let f := monicM pp f
  if f.length - 1 ≤ d then [f] else
  -- trial element
  let a : ZP := normM pp [Int.ofNat (seed % p), Int.ofNat ((seed / p) % p + 1), Int.ofNat (seed / (p * p))]
  let e := (p ^ d - 1) / 2
  let b := subM pp (powModM pp a e f) [1]
  let g := gcdM pp f b
  if g.length > 1 && g.length < f.length then
    edf p d g (seed + 1) ++ edf p d ((divModM pp f g).1) (seed + 1)
  else edf p d f (seed + 1)

def factorModP (p : Nat) (f : ZP) : List ZP :=
  (ddf p f).flatMap fun (d, g) ↦ edf p d g 1

/-! ### Hensel lifting (quadratic, multifactor by recursion on a factor tree) -/

/-- Lift `f ≡ lc·g·h (mod p)` (`g`, `h` monic, coprime) to modulus `p^k` (linear steps). -/
def henselStep (m p : Int) (f g h s t : ZP) : ZP × ZP :=
  -- f ≡ g h (mod m); s g + t h ≡ 1 (mod p)
  let e := normM (m * p) (subZ f (mulZ g h))
  let e := e.map (· / m)  -- exact division
  let (q, r) := divModM p (mulM p s e) h
  let g' := addZ g (scaleZ m (normM p (addZ (mulM p t e) (mulM p q g))))
  let h' := addZ h (scaleZ m r)
  (normM (m * p) g', normM (m * p) h')

partial def liftPair (p : Int) (k : Nat) (f g h : ZP) : ZP × ZP := Id.run do
  let (_, s, t) := xgcdM p g h
  let mut m := p
  let mut g := g
  let mut h := h
  for _ in [1:k] do
    let r := henselStep m p f g h s t
    g := r.1; h := r.2
    m := m * p
  (g, h)

/-- Lift all monic factors `fs` of the monic `f` modulo `p^k`. -/
partial def liftAll (p : Int) (k : Nat) (f : ZP) (fs : List ZP) : List ZP :=
  match fs with
  | [] => []
  | [_] => [normM (p ^ k) f]
  | _ =>
    let n := fs.length / 2
    let fs1 := fs.take n
    let fs2 := fs.drop n
    let g := fs1.foldl (mulM p) [1]
    let h := fs2.foldl (mulM p) [1]
    let (G, H) := liftPair p k f g h
    liftAll p k G fs1 ++ liftAll p k H fs2

/-! ### Recombination -/

def symmM (m : Int) (a : Int) : Int := let a := md m a; if 2 * a > m then a - m else a

def sublistsOfSize {α} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | k + 1, x :: xs => (sublistsOfSize k xs).map (x :: ·) ++ sublistsOfSize (k + 1) xs

/-- Mignotte-type bound on the coefficients of factors. -/
def bound (f : ZP) : Nat :=
  let n := f.length
  let norm2 := Nat.sqrt ((f.map fun a ↦ a.natAbs ^ 2).foldl (· + ·) 0) + 1
  2 ^ n * norm2 * (lcZ f).natAbs

/-- Factor a squarefree primitive `f ∈ ℤ[x]` (positive degree). -/
partial def factorSqfree (f : ZP) : List ZP := Id.run do
  let f := primZ f
  if f.length ≤ 2 then return [f]
  let lc := lcZ f
  -- a prime with `f mod p` squarefree of full degree
  let isPrime (n : Nat) : Bool := n ≥ 2 && (List.range (Nat.sqrt n + 1)).all fun d ↦ d < 2 || n % d != 0
  let mut p : Nat := 3
  while lc % (p : Int) == 0 || (gcdM (p : Int) (normM p f) (normM p (derivZ f))).length > 1 do
    p := p + 2
    while !(isPrime p) do p := p + 2
  let pp : Int := p
  let fm := monicM pp f
  let facs := factorModP p fm
  if facs.length ≤ 1 then return [f]
  let B := 2 * bound f + 1
  let mut k := 1
  while pp ^ k ≤ B do k := k + 1
  let mk := pp ^ k
  -- lift `f / lc` (monic mod p^k)
  let fmk := normM mk (f.map (· * invM mk lc))
  let lifted := liftAll pp k fmk facs
  -- recombination
  let mut remaining := lifted
  let mut g := f
  let mut out : List ZP := []
  let mut s := 1
  while 2 * s ≤ remaining.length do
    let mut found := false
    for S in sublistsOfSize s remaining do
      if !found then
        let lcg := lcZ g
        let prod := S.foldl (mulM mk) [lcg]
        let cand := primZ (prod.map (symmM mk))
        match divExactZ g cand with
        | some q =>
          out := cand :: out
          g := primZ q
          remaining := remaining.filter (fun h ↦ !(S.contains h))
          found := true
        | none => pure ()
    if !found then s := s + 1
  out := g :: out
  out

/-- Squarefree part and factorization of a non-zero polynomial over ℤ (irreducible factors,
without multiplicities). -/
partial def factorZ (f : ZP) : List ZP :=
  let f := primZ f
  if f.length ≤ 2 then (if f.length == 2 then [f] else []) else
  -- squarefree part over ℤ: f / gcd(f, f') via rational gcd (monic mod large prime is unsafe);
  -- use repeated exact division by the primitive gcd computed by subresultants (simple Euclid over ℚ)
  let rec gcdQ (a b : ZP) (fuel : Nat) : ZP :=
    match fuel with
    | 0 => a
    | fuel + 1 =>
      if (trimZ b).isEmpty then primZ a else
      -- pseudo-remainder
      let a := trimZ a
      let b := trimZ b
      if a.length < b.length then gcdQ b a fuel else
      let lb := b.getLastD 1
      let d := a.length - b.length
      let a' := scaleZ (lb ^ (d + 1)) a
      let r := Id.run do
        let mut r := a'.toArray
        for ii in [0:d + 1] do
          let i := d - ii
          let c := r[i + b.length - 1]! / lb
          for j in [0:b.length] do
            r := r.set! (i + j) (r[i + j]! - c * b[j]!)
        trimZ r.toList
      gcdQ b (primZ r) fuel
  let g := gcdQ f (derivZ f) (f.length + 2)
  let sf := if g.length ≤ 1 then f else (divExactZ f g).getD f
  factorSqfree sf

end ZF

namespace NFC

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

/-- A rational polynomial as a primitive integer polynomial (same roots). -/
def toZP (N : CPoly ℚ) : ZF.ZP :=
  let L := N.foldl (fun l q ↦ Nat.lcm l q.den) 1
  ZF.primZ (N.map fun q ↦ q.num * ((L / q.den : ℕ) : ℤ))

/-- The roots read off the (Zassenhaus) factors of the norm. -/
def rootsFromNZ (g : CPoly (NF f)) (s : ℚ) (N : CPoly ℚ) : List (NF f) :=
  (ZF.factorZ (toZP N)).filterMap fun Mz ↦
    let M : CPoly ℚ := Mz.map fun a : ℤ ↦ (a : ℚ)
    let G := trim (egcd g (shiftQ f M ((s : NF f) * gen f))).1
    if degT G = 1 then some (-(G.getD 0 0) / G.getD 1 0) else none

/-- The roots of `g` in `K` (fast candidates). -/
def rootsInZ (g : CPoly (NF f)) : Option (List (NF f)) :=
  (List.range (sBound f g)).findSome? fun i : ℕ ↦
    if squarefreeCheck (normPoly f g ((i : ℚ) + 1)) then
      some (rootsFromNZ f g ((i : ℚ) + 1) (normPoly f g ((i : ℚ) + 1)))
    else none

/-- **The fast root finder**: all roots in `K` (checked by multiplicities), or `none`. -/
def rfNFZ : Curves.RootFinder (NF f) := fun P ↦
  let P := trim P
  if isZero P then none else
  match rootsInZ f (sqfreePart P) with
  | none => none
  | some rs =>
    let rs := rs.dedup
    if (rs.map fun r ↦ Curves.multAt P r (P.length + 1) P).sum + 1 = P.length then some rs
    else none

end NFC
