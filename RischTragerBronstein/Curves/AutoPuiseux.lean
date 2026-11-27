import RischTragerBronstein.Curves.CertBranch
import RischTragerBronstein.Curves.BranchEval

/-!
# Computing Puiseux expansions (Newton polygons)

`puiseuxAt rf Fc a L`: the branches of `F(x, Y) = 0` above `x = a`, as truncated series
`y(T)`, `x = a + T^E`, computed by the Newton polygon method. At each step the lower hull of
`(j, ord_T Hⱼ)` gives an edge of slope `p/q`, a non-zero root `c` of its edge polynomial gives the
substitution `T ↦ Tᵠ`, `Y ↦ Tᵖ (c + Y)`; a simple root ends the recursion with Newton's iteration.
`rf` finds all roots of a polynomial in the field (`none` if some root is missing: the result is then
`.error g` with the polynomial `g` to adjoin). `branchCert` puts the branches in a common system
`x = a + Tᴺ`. Nothing here needs proofs: the output is checked by `certCheck`.
-/

namespace Curves

open CPoly Sup

section Series

variable {F : Type*} [Field F] [DecidableEq F]

/-- Truncated product. -/
def sMulT (p q : CPoly F) (L : ℕ) : CPoly F :=
  (List.range L).map fun m ↦ ∑ i ∈ Finset.range (m + 1), p.getD i 0 * q.getD (m - i) 0

/-- Truncated quotient (`q₀ ≠ 0`). -/
def sDivT (p q : CPoly F) (L : ℕ) : CPoly F := divTrunc p q L

/-- `∑ Hⱼ(T) Zʲ` truncated. -/
def evalBT (H : BPoly F) (Z : CPoly F) (L : ℕ) : CPoly F :=
  H.foldr (fun c acc ↦ (List.range L).map fun m ↦ c.getD m 0 + (sMulT Z acc L).getD m 0) []

/-- `evalBT` with each truncated product computed once: the compiled code. -/
def evalBTF (H : BPoly F) (Z : CPoly F) (L : ℕ) : CPoly F :=
  H.foldr (fun c acc ↦
    let s := sMulT Z acc L
    (List.range L).map fun m ↦ c.getD m 0 + s.getD m 0) []

@[csimp] theorem evalBT_eq_evalBTF : @evalBT = @evalBTF := rfl

/-- `P(Tᵍ)`. -/
def subsPow (P : CPoly F) (q : ℕ) : CPoly F :=
  (List.range ((P.length - 1) * q + 1)).map fun m ↦ if m % q = 0 then P.getD (m / q) 0 else 0

/-- `Tᵐ P`. -/
def shiftT (m : ℕ) (P : CPoly F) : CPoly F := List.replicate m 0 ++ P

/-- `H(T, c + Y)`. -/
def shiftYB (H : BPoly F) (c : F) : BPoly F :=
  H.foldr (fun h acc ↦ addB [h] (addB (smulB [c] acc) ([] :: acc))) []

/-- `H(Tᵍ, Tᵖ Y)` divided by `Tᵐ`. -/
def substB (H : BPoly F) (q p m : ℕ) : BPoly F :=
  (List.range H.length).map fun j ↦ (shiftT (p * j) (subsPow (H.getD j []) q)).drop m

/-- Newton's iteration for the simple root `Z(0) = 0` of `H(T, Z)`. -/
def newtonT (H : BPoly F) (L : ℕ) : ℕ → CPoly F → CPoly F
  | 0, Z => Z
  | k + 1, Z =>
    let V := evalBT H Z L
    let D := evalBT (derivYB H) Z L
    newtonT H L k ((List.range L).map fun m ↦ Z.getD m 0 - (sDivT V D L).getD m 0)

/-- `newtonT` with each truncated quotient computed once: the compiled code. -/
def newtonTF (H : BPoly F) (L : ℕ) : ℕ → CPoly F → CPoly F
  | 0, Z => Z
  | k + 1, Z =>
    let V := evalBT H Z L
    let D := evalBT (derivYB H) Z L
    let q := sDivT V D L
    newtonTF H L k ((List.range L).map fun m ↦ Z.getD m 0 - q.getD m 0)

omit [DecidableEq F] in
theorem newtonT_eq_newtonTF' (H : BPoly F) (L : ℕ) :
    ∀ (k : ℕ) (Z : CPoly F), newtonT H L k Z = newtonTF H L k Z
  | 0, _ => rfl
  | k + 1, Z => by
    rw [newtonT, newtonTF]
    exact newtonT_eq_newtonTF' H L k _

@[csimp] theorem newtonT_eq_newtonTF : @newtonT = @newtonTF := by
  funext F _ H L k Z
  exact newtonT_eq_newtonTF' H L k Z

end Series

section NP

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `T`-orders of the coefficients (`none` for a zero coefficient). -/
def ordsB (H : BPoly F) : List (Option ℕ) :=
  H.map fun h ↦ if isZero h then none else some (ordC h)

/-- The order of `Hⱼ` (`none` if `Hⱼ = 0`). -/
def ordAt (H : BPoly F) (j : ℕ) : Option ℕ := (ordsB H).getD j none

/-- The next vertex of the lower hull after `(j₁, v₁)` among the points below `v₁`: the largest
slope `(v₁ − vⱼ)/(j − j₁)`, the largest `j` among ties. -/
def nextVertex (H : BPoly F) (j1 v1 : ℕ) : Option (ℕ × ℕ) :=
  (((List.range H.length).filter (j1 < ·)).filterMap fun j ↦
    match ordAt H j with
    | some vj => if vj < v1 then some (j, vj) else none
    | none => none).foldl (fun (best : Option (ℕ × ℕ)) jv ↦
      match best with
      | none => some jv
      | some b =>
        if (v1 - jv.2) * (b.1 - j1) > (v1 - b.2) * (jv.1 - j1) ∨
          ((v1 - jv.2) * (b.1 - j1) = (v1 - b.2) * (jv.1 - j1) ∧ jv.1 > b.1) then some jv
        else some b) none

/-- **The edges of negative slope** of the Newton polygon, from `(0, v₀)` down to the order `0`:
`(j₁, v₁, j₂, p, q)` with slope `p/q`. -/
def edgesFrom (H : BPoly F) : ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)
  | 0, _, _ => []
  | k + 1, j1, v1 =>
    if v1 = 0 then [] else
    match nextVertex H j1 v1 with
    | none => []
    | some (j2, v2) =>
      let g := Nat.gcd (v1 - v2) (j2 - j1)
      (j1, v1, j2, (v1 - v2) / g, (j2 - j1) / g) :: edgesFrom H k j2 v2

/-- The edge polynomial in `c` of the edge `(j₁, v₁) → (j₂, ·)` of slope `p/q`. -/
def edgePoly (H : BPoly F) (j1 v1 j2 p q : ℕ) : CPoly F :=
  (List.range (j2 - j1 + 1)).map fun i ↦
    match ordAt H (j1 + i) with
    | some vj => if vj * q + (j1 + i) * p = v1 * q + j1 * p then (H.getD (j1 + i) []).getD vj 0
      else 0
    | none => 0

/-- The multiplicity of the root `c` of `P`. -/
def multAt (P : CPoly F) (c : F) : ℕ → CPoly F → ℕ
  | 0, _ => 0
  | k + 1, Q =>
    let d := synthDiv' c Q
    if d.2 = 0 ∧ ¬ isZero Q then 1 + multAt P c k d.1 else 0
where
  /-- Horner division by `X − c`. -/
  synthDiv' (c : F) : CPoly F → CPoly F × F
    | [] => ([], 0)
    | x :: P => ((synthDiv' c P).2 :: (synthDiv' c P).1, x + c * (synthDiv' c P).2)

/-- A partial branch: `x − a = T^E`, `y = pre(T) + T^o Y`, `Y` a root of `H`. -/
structure PState (F : Type*) where
  E : ℕ
  pre : CPoly F
  o : ℕ
  H : BPoly F

/-- A computed branch: `x − a = T^E`, `y = ser(T)`. -/
structure PBranch (F : Type*) where
  E : ℕ
  ser : CPoly F

/-- The roots of `P` in the field: `rf` returns all roots of `P` or `none`. -/
abbrev RootFinder (F : Type*) := CPoly F → Option (List F)

/-- **A root finder from candidate roots** (from any untrusted source): the candidates that are
roots, provided their multiplicities add up to the degree (so the list is then all the roots). -/
def rfHint (hints : List F) : RootFinder F := fun P ↦
  let P := trim P
  if isZero P then none else
  let rs := (hints.filter fun r ↦ Kron.evalC P r = 0).dedup
  if (rs.map fun r ↦ multAt P r (P.length + 1) P).sum + 1 = P.length then some rs else none

/-- **The Newton polygon recursion** (fuel `k`). Returns the branches or the polynomial whose roots
are missing. -/
def npRec (rf : RootFinder F) (L : ℕ) : ℕ → PState F → Except (CPoly F) (List (PBranch F))
  | 0, _ => .error []
  | k + 1, st =>
    if isZero (st.H.getD 0 []) then
      -- `Y = 0` is an exact root
      .ok [⟨st.E, (List.range L).map fun m ↦ st.pre.getD m 0⟩]
    else
    (edgesFrom st.H st.H.length 0 (ordC (st.H.getD 0 []))).foldr (fun ed acc ↦
      match acc with
      | .error e => .error e
      | .ok bs =>
        let (j1, v1, j2, p, q) := ed
        let φ := edgePoly st.H j1 v1 j2 p q
        match rf φ with
        | none => .error φ
        | some cs =>
          (cs.filter (· ≠ 0)).foldr (fun c acc2 ↦ match acc2 with
            | .error e => .error e
            | .ok bs2 =>
              let H2 := shiftYB (substB st.H q p (v1 * q + j1 * p)) c
              let pre' := (List.range (L + 1)).map fun m ↦
                (subsPow st.pre q).getD m 0 + (if m = st.o * q + p then c else 0)
              let st' : PState F := ⟨st.E * q, pre', st.o * q + p, H2⟩
              if multAt φ c (φ.length + 1) φ = 1 then
                let Z := newtonT H2 L (Nat.log2 L + 3) []
                .ok (⟨st'.E, (List.range L).map fun m ↦
                    pre'.getD m 0 + (if st'.o ≤ m then Z.getD (m - st'.o) 0 else 0)⟩ :: bs2)
              else
                match npRec rf L k st' with
                | .error e => .error e
                | .ok bs' => .ok (bs' ++ bs2)) (.ok bs)) (.ok [])

/-- **The branches above `x = a`**: the roots `y₀` of `F(a, Y)` and the Newton polygon recursion
at each. -/
def puiseuxAt (rf : RootFinder F) (Fc : BPoly F) (a : F) (L fuel : ℕ) :
    Except (CPoly F) (List (PBranch F)) :=
  let H0 := Fc.map fun c ↦ compC c [a, 1]
  let f0 := H0.map fun c ↦ c.getD 0 0
  match rf f0 with
  | none => .error f0
  | some ys => ys.foldr (fun y0 acc ↦ match acc with
      | .error e => .error e
      | .ok bs =>
        let H1 := shiftYB H0 y0
        let st : PState F := ⟨1, [y0], 0, H1⟩
        if multAt f0 y0 (f0.length + 1) f0 = 1 then
          let Z := newtonT H1 L (Nat.log2 L + 3) []
          .ok (⟨1, (List.range L).map fun m ↦ (if m = 0 then y0 else 0) + Z.getD m 0⟩ :: bs)
        else
          match npRec rf L fuel st with
          | .error e => .error e
          | .ok bs' => .ok (bs' ++ bs)) (.ok [])

/-- The branches in a common system `x = a + Tᴺ`, `N = lcm E`. -/
def branchCert (bs : List (PBranch F)) (prec : ℕ) : BranchCert F :=
  let N := bs.foldr (fun b n ↦ Nat.lcm b.E n) 1
  ⟨N, bs.map fun b ↦ subsPow b.ser (N / b.E), prec⟩

end NP

end Curves
