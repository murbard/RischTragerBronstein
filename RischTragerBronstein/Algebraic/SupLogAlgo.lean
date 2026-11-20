import RischTragerBronstein.Algebraic.SupLift
import RischTragerBronstein.Jacobian.HypDecideK

/-!
# The superelliptic logarithmic-part procedure

`superLogDecide f n ζ tors B B₁ a b G` decides `∫ (B(x, y) + B₁(x, y)/f(x) + ∑ᵢ Gᵢ(x, y)/(x − aᵢ)) dx` on
`yⁿ = f(x)` (with `bᵢⁿ = f(aᵢ)`, `ζ` a primitive `n`-th root of unity, all data in a field `F` with a
computable `ℚ`-basis):

1. the residues `rᵢₖ = Gᵢ(aᵢ, ζᵏ bᵢ)` are split along the `ℚ`-basis of `F`; the `j`-th component has
   integer multiplicities `zᵢₖ = Lⱼ coordⱼ(rᵢₖ)`, whose positive-part divisor
   `Γⱼ⁺ = ∑ max(zᵢₖ, 0) Pᵢₖ + ∑_{zᵢₖ<0} |zᵢₖ| (fibre − Pᵢₖ)` is handed to the torsion oracle `tors`;
2. a non-torsion component means non-elementary;
3. otherwise `supPrincipalC` finds `Wⱼ` with divisor `Nⱼ Γⱼ⁺ − deg ∞`, and `exactTest` decides whether
   `h − ∑ⱼ cⱼ (Wⱼ/Dⱼ)′/(Wⱼ/Dⱼ)` is exact (`Dⱼ = ∏ (x − aᵢ)^{Nⱼ ∑_{z<0}|z|}`, `cⱼ = κⱼ/(NⱼLⱼ)`).
-/

open Polynomial CPoly

namespace Sup

section Comp

variable {F : Type*} [Field F] [DecidableEq F]

/-- The value of `W` at `(a, b)`. -/
def evalB (W : BPoly F) (a b : F) : F := W.foldr (fun c acc ↦ Kron.evalC c a + b * acc) 0

/-- `∑ cₖ x^{aₖ} y^{lₖ}`. -/
def lsumB : List F → List (ℕ × ℕ) → BPoly F
  | c :: cs, al :: B => addB (smulB [c] (monoB al.1 al.2)) (lsumB cs B)
  | _, _ => []

/-- Products and sums. -/
def prodC (l : List (CPoly F)) : CPoly F := l.foldr CPoly.mul [1]
def prodB (l : List (BPoly F)) : BPoly F := l.foldr mulB [[1]]
def sumB (l : List (BPoly F)) : BPoly F := l.foldr addB []

/-- A torsion oracle: `some (some N)` with `N Γ` principal, `some none` if `Γ` is not torsion,
`none` if it cannot tell. -/
def TorsSpecN (f : CPoly F) (n : ℕ) (tors : List (F × F × ℕ) → Option (Option ℕ)) : Prop :=
  ∀ (r : ℕ) (α β : Fin r → F) (mq : Fin r → ℕ), (∀ q, β q ≠ 0 ∧ β q ^ n = (toPoly f).eval (α q)) →
    Function.Injective (fun q ↦ (α q, β q)) →
    (∀ N, tors (gammaL α β mq 1) = some (some N) →
      1 ≤ N ∧ PrincipalMulN (toPoly f) n (f.length - 1) α β mq N) ∧
    (tors (gammaL α β mq 1) = some none →
      ∀ N, 1 ≤ N → ¬ PrincipalMulN (toPoly f) n (f.length - 1) α β mq N)

/-- The witness of `N Γ`. -/
def witW (f : CPoly F) (n d : ℕ) {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (N : ℕ) :
    Option (BPoly F) :=
  match supPrincipalC f n d (gammaL α β mq N) (N * ∑ q, mq q) with
  | some (jj, cs) => some (lsumB (cs.set jj 1) (basisN n d (N * ∑ q, mq q)))
  | none => none

/-- The fibre index of a point. -/
def fibI {m n : ℕ} (q : Fin (m * n)) : Fin m := (finProdFinEquiv.symm q).1
/-- The root-of-unity index of a point. -/
def fibK {m n : ℕ} (q : Fin (m * n)) : Fin n := (finProdFinEquiv.symm q).2

/-- The points `(aᵢ, ζᵏ bᵢ)`. -/
def ptA {m : ℕ} (n : ℕ) (a : Fin m → F) (q : Fin (m * n)) : F := a (fibI q)
def ptB {m : ℕ} (n : ℕ) (ζ : F) (b : Fin m → F) (q : Fin (m * n)) : F :=
  ζ ^ (fibK q : ℕ) * b (fibI q)

/-- `(x − a)` as a list. -/
def linC (a : F) : CPoly F := [-a, 1]

/-- `∏ᵢ (x − aᵢ)^{eᵢ}`. -/
def denC {m : ℕ} (a : Fin m → F) (e : Fin m → ℕ) : CPoly F :=
  prodC ((List.finRange m).map fun i ↦ prodC (List.replicate (e i) (linC (a i))))

/-- `∏_{i' ≠ i} (x − aᵢ')`. -/
def prodExc {m : ℕ} (a : Fin m → F) (i : Fin m) : CPoly F :=
  prodC ((List.finRange m).map fun i' ↦ if i' = i then [1] else linC (a i'))

/-- The bound `n (max length) + d (length)`. -/
def boundB (n d : ℕ) (W : BPoly F) : ℕ := n * maxLenB W + d * W.length

variable [CharZero F] [EllQuad.QCoords F]

open EllQuad.QCoords

/-- The residues `rᵢₖ = Gᵢ(aᵢ, ζᵏ bᵢ)`. -/
def resK {m : ℕ} (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (i : Fin m) (k : ℕ) : F :=
  evalB (G i) (a i) (ζ ^ k * b i)

/-- The common denominator of the `j`-th coordinates. -/
def denJ {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (j : Fin (dim F)) : ℕ :=
  EllQuad.denL ((List.finRange m).flatMap fun i ↦
    (List.range n).map fun k ↦ coord j (resK ζ a b G i k))

/-- The integer multiplicities `Lⱼ coordⱼ(rᵢₖ)`. -/
def zJ {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (j : Fin (dim F))
    (i : Fin m) (k : ℕ) : ℤ :=
  (coord j (resK ζ a b G i k) * denJ n ζ a b G j).num

/-- `∑_{zᵢₖ < 0} |zᵢₖ|` on the fibre `i`. -/
def negJ {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (j : Fin (dim F))
    (i : Fin m) : ℕ :=
  ∑ k : Fin n, (-(zJ n ζ a b G j i k)).toNat

/-- The multiplicities of `Γⱼ⁺`. -/
def mqJ {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (j : Fin (dim F))
    (q : Fin (m * n)) : ℕ :=
  (zJ n ζ a b G j (fibI q) (fibK q) + negJ n ζ a b G j (fibI q)).toNat

/-- The oracle's answer for component `j`. -/
def torsJ {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (j : Fin (dim F)) : Option (Option ℕ) :=
  tors (gammaL (ptA n a) (ptB n ζ b) (mqJ n ζ a b G j) 1)

/-- The logarithm data of component `j`: `(Nⱼ, Wⱼ)`. -/
def logJ {m : ℕ} (f : CPoly F) (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (j : Fin (dim F)) : Option (ℕ × BPoly F) :=
  match torsJ n ζ a b G tors j with
  | some (some N) =>
    (witW f n (f.length - 1) (ptA n a) (ptB n ζ b) (mqJ n ζ a b G j) N).map fun W ↦ (N, W)
  | _ => none

/-- The constant `cⱼ = κⱼ / (Nⱼ Lⱼ)`. -/
def cJ {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (j : Fin (dim F)) (N : ℕ) :
    F :=
  bvec j / ((N : F) * (denJ n ζ a b G j : F))

/-- The multiplier `M = P ∏ Wⱼ` and the target
`T = U (f P (B + ∑ Gᵢ/(x − aᵢ) + ∑ⱼ cⱼ Dⱼ′/Dⱼ) + P B₁) − ∑ⱼ cⱼ P (f Wⱼ′) ∏_{k ≠ j} W_k` of the
exactness test (`M f v′ = T`). -/
def logMT {m : ℕ} (f : CPoly F) (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (B B₁ : BPoly F) (NW : Fin (dim F) → ℕ × BPoly F) : BPoly F × BPoly F :=
  let P : CPoly F := prodC ((List.finRange m).map fun i ↦ linC (a i))
  let U : BPoly F := prodB ((List.finRange (dim F)).map fun j ↦ (NW j).2)
  -- `P (B + ∑ Gᵢ/(x − aᵢ) + ∑ⱼ cⱼ Dⱼ′/Dⱼ)`
  let hP : BPoly F := sumB (smulB P B :: (List.finRange m).map fun i ↦
    addB (smulB (prodExc a i) (G i)) [smul (((List.finRange (dim F)).map fun j ↦
      cJ n ζ a b G j (NW j).1 * (((NW j).1 * negJ n ζ a b G j i : ℕ) : F)).sum) (prodExc a i)])
  -- `∑ⱼ cⱼ P (f Wⱼ′) ∏_{k ≠ j} W_k`
  let S : BPoly F := sumB ((List.finRange (dim F)).map fun j ↦
    smulB (smul (cJ n ζ a b G j (NW j).1) P)
      (mulB (derivB f n (NW j).2)
        (prodB ((List.finRange (dim F)).map fun k ↦ if k = j then [[1]] else (NW k).2))))
  (smulB P U, addB (mulB U (addB (smulB f hP) (smulB P B₁))) (smulB [-1] S))

/-- The bound `H`. -/
def boundH {m : ℕ} (f : CPoly F) (n : ℕ) (B B₁ : BPoly F) (G : Fin m → BPoly F) : ℕ :=
  max (max (boundB n (f.length - 1) B) (boundB n (f.length - 1) B₁))
    (((List.finRange m).map fun i ↦ boundB n (f.length - 1) (G i)).foldr max 0)

/-- **The procedure** (`none`: invalid data, or the oracle cannot tell). -/
def superLogDecide {m : ℕ} (f : CPoly F) (n : ℕ) (ζ : F)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (B B₁ : BPoly F) (a b : Fin m → F)
    (G : Fin m → BPoly F) : Option Bool :=
  if hn : 0 < n then
    if (List.finRange (dim F)).any fun j ↦ (torsJ n ζ a b G tors j).isNone then none
    else if (List.finRange (dim F)).any fun j ↦ torsJ n ζ a b G tors j == some none then some false
    else if (List.finRange (dim F)).all fun j ↦ (logJ f n ζ a b G tors j).isSome then
      let NW : Fin (dim F) → ℕ × BPoly F := fun j ↦ (logJ f n ζ a b G tors j).getD (1, [[1]])
      let MT := logMT f n ζ a b G B B₁ NW
      some (exactTest f n hn MT.1 MT.2 (basisN n (f.length - 1) (boundH f n B B₁ G + n))).isSome
    else none
  else none

end Comp

end Sup
