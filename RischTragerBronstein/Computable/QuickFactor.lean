import RischTragerBronstein.Computable.KronCert

/-!
# A quick (untrusted) factor finder over `ℚ`

`quickFactor N` looks for a proper factor of `N ∈ ℚ[x]` by factoring modulo a prime
(distinct-degree and equal-degree splitting), Hensel lifting of the products of few modular
factors, and trial division. Nothing is proved about it: the callers check the result (division
and `irredQ`). All recursions are structural, so the kernel can evaluate it.
-/

namespace CPoly

namespace Kron

open DegCert

section Mod

variable {p : ℕ} [Fact p.Prime]

/-- The monic associate. -/
def monicP (g : CPoly (ZMod p)) : CPoly (ZMod p) :=
  let g := trim g
  smul (lead g)⁻¹ g

/-- The monic gcd. -/
def gcdP (a b : CPoly (ZMod p)) : CPoly (ZMod p) := monicP (egcd a b).1

/-- Distinct-degree pieces `(d, h_d)`. -/
def ddfP (f : CPoly (ZMod p)) : ℕ → ℕ → CPoly (ZMod p) → CPoly (ZMod p) →
    List (ℕ × CPoly (ZMod p))
  | 0, _, _, _ => []
  | n + 1, d, w, cur =>
    if (trim cur).length ≤ 1 then [] else
      let w' := powMod f w p
      let g := gcdP cur (sub w' [0, 1])
      if (trim g).length ≤ 1 then ddfP f n (d + 1) w' cur
      else (d, g) :: ddfP f n (d + 1) w' (divMod cur g).1

/-- Equal-degree splitting of products of irreducibles of degree `d` (`p` odd). -/
def edf (d : ℕ) : ℕ → ℕ → List (CPoly (ZMod p)) → List (CPoly (ZMod p))
  | 0, _, todo => todo
  | _ + 1, _, [] => []
  | fuel + 1, a, h :: todo =>
    if (trim h).length ≤ d + 1 then h :: edf d fuel a todo
    else
      let w := sub (powMod h [(a : ZMod p), 1] ((p ^ d - 1) / 2)) [1]
      let g := gcdP h w
      if 1 < (trim g).length ∧ (trim g).length < (trim h).length then
        edf d fuel (a + 1) (g :: (divMod h g).1 :: todo)
      else edf d fuel (a + 1) (h :: todo)

/-- The monic irreducible factors modulo `p` of a monic integral polynomial (`none` if it is not
squarefree modulo `p`). -/
def modFactors (Ft : CPoly ℤ) : Option (List (CPoly (ZMod p))) :=
  let f : CPoly (ZMod p) := Ft.map (Int.castRingHom (ZMod p))
  if (trim (egcd f (deriv f)).1).length = 1 then
    some ((ddfP f Ft.length 1 [0, 1] f).flatMap fun dh ↦ edf dh.1 (40 * Ft.length) 0 [dh.2])
  else none

/-- Lift to `[0, p)`. -/
def liftZ (g : CPoly (ZMod p)) : CPoly ℤ := g.map fun c ↦ (c.val : ℤ)

/-- Linear Hensel lifting of `Ft ≡ G H`. -/
def hensel (Ft : CPoly ℤ) (G0 H0 t : CPoly (ZMod p)) : ℕ → ℤ → CPoly ℤ → CPoly ℤ →
    CPoly ℤ × CPoly ℤ
  | 0, _, G, H => (G, H)
  | k + 1, pk, G, H =>
    let E : CPoly ℤ := (sub Ft (mul G H)).map (· / pk)
    let e : CPoly (ZMod p) := E.map (Int.castRingHom (ZMod p))
    let dG := (divMod (mul t e) G0).2
    let dH := (divMod (sub e (mul dG H0)) G0).1
    hensel Ft G0 H0 t k (pk * p) (add G (smul pk (liftZ dG))) (add H (smul pk (liftZ dH)))

/-- The product of a list of polynomials. -/
def prodP (l : List (CPoly (ZMod p))) : CPoly (ZMod p) := l.foldr (fun g acc ↦ mul g acc) [1]

/-- A monic integral factor of the monic `Ft` from the modular factors `S` (`steps` lifting
steps), if the lift divides `Ft`. -/
def trySubset (Ft : CPoly ℤ) (f : CPoly (ZMod p)) (steps : ℕ) (S : List (CPoly (ZMod p))) :
    Option (CPoly ℤ) :=
  let G0 := monicP (prodP S)
  let H0 := (divMod f G0).1
  let e := egcd G0 H0
  let c := (trim e.1).getD 0 0
  let t := smul c⁻¹ e.2.2
  let GH := hensel Ft G0 H0 t steps p (liftZ G0) (liftZ H0)
  let pK : ℤ := (p : ℤ) ^ (steps + 1)
  let G : CPoly ℤ := GH.1.map fun c ↦ let r := c % pK; if 2 * r > pK then r - pK else r
  let Gq : CPoly ℚ := G.map fun c ↦ (c : ℚ)
  let Fq : CPoly ℚ := Ft.map fun c ↦ (c : ℚ)
  if isZero (divMod Fq Gq).2 then some G else none

/-- A proper monic factor of the monic `Ft`, trying the products of at most half of the modular
factors, fewest first. -/
def factorMod (Ft : CPoly ℤ) (steps : ℕ) : Option (CPoly ℤ) :=
  match modFactors (p := p) Ft with
  | none => none
  | some fs =>
    let f : CPoly (ZMod p) := Ft.map (Int.castRingHom (ZMod p))
    (List.range (fs.length / 2)).findSome? fun k ↦
      (List.sublistsLen (k + 1) fs).findSome? fun S ↦ trySubset Ft f steps S

end Mod

/-- The number of modular factors at `p` (`none`: unusable prime). -/
def nModFactors (Ft : CPoly ℤ) (p : ℕ) : Option ℕ :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    (modFactors (p := p) Ft).map List.length
  else none

/-- `factorMod` at `p`. -/
def factorAt (Ft : CPoly ℤ) (p steps : ℕ) : Option (CPoly ℤ) :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    factorMod (p := p) Ft steps
  else none

/-- The monic polynomial `lcⁿ⁻¹ F(x/lc)` of an integral `F`. -/
def monicZ (F : CPoly ℤ) : CPoly ℤ :=
  let n := F.length - 1
  let lc := F.getLastD 1
  (List.range n).map (fun i ↦ F.getD i 0 * lc ^ (n - 1 - i)) ++ [1]

/-- **A proper factor of `N`, if the search finds one** (untrusted). -/
def quickFactor (N : CPoly ℚ) : Option (CPoly ℚ) :=
  let F := primInt (trim N)
  let FZ : CPoly ℤ := F.map Rat.num
  if FZ.length < 3 then none else
    let lc := FZ.getLastD 1
    let Ft := monicZ FZ
    -- a prime with few modular factors among the first usable ones
    let cands := (certPrimes.filterMap fun p ↦ (nModFactors Ft p).map fun k ↦ (k, p)).take 8
    match cands.foldl (fun (best : Option (ℕ × ℕ)) kp ↦
        match best with
        | none => some kp
        | some b => if kp.1 < b.1 then some kp else some b) none with
    | none => none
    | some (k, p) =>
      if k ≤ 1 then none else
        let B : ℕ := 2 ^ (Ft.length + 1) * (Ft.foldr (fun c acc ↦ c.natAbs + acc) 0)
        let steps := (B.log2 + 1) / p.log2 + 2
        (factorAt Ft p steps).map fun G ↦
          primInt ((List.range G.length).map fun i ↦ ((G.getD i 0 * lc ^ i : ℤ) : ℚ))

/-- Iterate `quickFactor` down to a polynomial without a factor found (`N` itself if none). -/
def quickIrr : ℕ → CPoly ℚ → CPoly ℚ
  | 0, N => N
  | k + 1, N =>
    match quickFactor N with
    | some M => quickIrr k M
    | none => primInt (trim N)

end Kron

end CPoly

