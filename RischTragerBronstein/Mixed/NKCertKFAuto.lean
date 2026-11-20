import RischTragerBronstein.Mixed.NKCertKF

/-!
# Searching the primes of a two-place certificate

Untrusted search (the certificate built from its answer is checked by `primeCheck`,
`PlaceCert.primeCheck`, `nonPrincOK`): for a curve `y² = Q(T)` over a computable field `F` with a
global certificate `T`, place certificate `Pc` and reductions `redAt p x₀` (e.g. `redAtKF` with all
residues `x₀`), `primeCandsK` lists the triples `(p, x₀, m_p)` for which the prime certificate
(`primeCertG`: `Q` split modulo `p` with square derivatives at its roots) and the multiplier `m_p ≤ B`
(`autoPlaceData`) exist, and `pickPairK` returns the first pair `p ≠ q` (by increasing
`pairMult p q m_p m_q`) for which the test over `F` fails (`autoLm` + `nonPrincOK`): the data of a
`TwoPlaceCertK`.
-/

namespace Curves

open CPoly Sup GTors

variable {F : Type*} [Field F] [DecidableEq F]

/-- The cheap test first: `Q = −F(T, 0)` splits completely modulo `p` (distinct roots) and the
ramified branches exist at its roots (square derivatives). -/
def splitSqK {p : ℕ} [Fact p.Prime] (R : RedFns p F) (T : GlobalCert F) : Bool :=
  let Q : CPoly (ZMod p) := ((redBL R T.Fc).getD 0 []).map (- ·)
  let rs := (zElems p).filter fun a ↦ Kron.evalC Q a = 0
  decide (rs.length + 1 = (CPoly.trim Q).length) && rs.all fun a ↦ (ramCertG Q a 2 1).isSome

/-- The admissible `(p, x₀, m_p)` for the primes in `ps` (first admissible `x₀ < p` per prime). -/
def primeCandsK (redAt : (p : ℕ) → ℕ → Option (RedFns p F)) (T : GlobalCert F) (Pc : PlaceCert F)
    (B : ℕ) (ps : List ℕ) : List (ℕ × ℕ × ℕ) :=
  ps.filterMap fun p ↦
    if hp : p.Prime then
      haveI : Fact p.Prime := ⟨hp⟩
      (List.range p).findSome? fun x0 ↦
        match redAt p x0 with
        | none => none
        | some R =>
          if !splitSqK R T then none else
          match primeCertG R T (Pc.fib.map Prod.fst) with
          | none => none
          | some P =>
            if primeCheck R T P then
              (autoPlaceData R T Pc B).bind fun Q ↦
                if Pc.primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc P.xs Q then some (p, x0, Q.mp)
                else none
            else none
    else none

/-- The failed test at `M = pairMult · cΓ` over `F` (`autoLm` + `nonPrincOK`). -/
def testFailsK (T : GlobalCert F) (Pc : PlaceCert F) (pm : ℕ) : Bool :=
  match autoLm T.n (pm * Pc.cΓ) pm T.I.δL T.I.Bc T.I.Dc Pc with
  | none => false
  | some L => nonPrincOK T.n (pm * Pc.cΓ) L.1 T.I.δL T.I.Bc T.I.Dc Pc.αs (Pc.fcerts T.n)
      (Pc.bL T.n pm) L.2

/-- **The pair of primes**: `((p, x₀ₚ, mₚ), (q, x₀_q, m_q))` with a failing test, smallest
`pairMult` first. -/
def pickPairK (T : GlobalCert F) (Pc : PlaceCert F) (cs : List (ℕ × ℕ × ℕ)) :
    Option ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  let prs := (cs.flatMap fun a ↦ cs.filterMap fun b ↦
    if a.1 < b.1 then some (pairMult a.1 b.1 a.2.2 b.2.2, a, b) else none).mergeSort
      fun u v ↦ u.1 ≤ v.1
  (prs.find? fun u ↦ testFailsK T Pc u.1).map fun u ↦ u.2

/-- The global certificate of `y² = Q` above `T = 0`'s model `Fm` (weight `k`): special points at the
rational roots of the discriminant found by `rf` (none needed at simple roots, `ibCheckR`). -/
def autoGlobalK (rf : RootFinder F) (Fm : BPoly F) (n k : ℕ) :
    Option (GlobalCert F) := do
  let ci ← certAtAuto rf (invB Fm k (k * n)) 0 (2 * n * n + 2) (2 * n * n)
  let I ← autoIntBasis Fm n k [] ci 30
  pure ⟨Fm, n, k, kDOf Fm, I, 0, [], [], [], [], 0⟩

/-- The place certificate of the two places `(0, ±√Q(0))`, `Q(0) = 1`, `Γ = 2 P₊`, precision `L`,
test precision `tp`. -/
def placeSqrtK (Fm : BPoly F) (L tp : ℕ) : PlaceCert F :=
  let ser := sqrtSerG ((Fm.getD 0 []).map (- ·)) 1 L
  ⟨[(0, 1)], [(0, (1, (ser, L - 1))), (0, (1, (ser.map (- ·), L - 1)))],
    [[(0, (1, 1)), (1, (1, 1))]], [2, 0], [2], [2], 1, [tp]⟩

/-- **The whole search**: global and place certificates, and the pair of primes. -/
def autoTwoK (rf : RootFinder F)
    (redAt : (p : ℕ) → ℕ → Option (RedFns p F)) (Fm : BPoly F) (L tp B : ℕ) (ps : List ℕ) :
    Option (GlobalCert F × PlaceCert F × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  match autoGlobalK rf Fm 2 2 with
  | none => none
  | some T =>
    let Pc := placeSqrtK Fm L tp
    if !(T.globalCheckR && Pc.check T.Fc T.n) then none else
    match pickPairK T Pc (primeCandsK redAt T Pc B ps) with
    | none => none
    | some pr => some (T, Pc, pr)

end Curves
