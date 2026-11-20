import RischTragerBronstein.Mixed.KXCodes
import RischTragerBronstein.Algebraic.Ramanujan
import RischTragerBronstein.Algebraic.SupRedNFK
import RischTragerBronstein.Algebraic.SupLocalCert

/-!
# Radicals `θⁿ = A(t)` over an exponential level: the algorithm

`krDecide`: for a certified mixed tower whose top level `t = tₘ` is an exponential (`t′ = η t`),
`θⁿ = A(t)` (`A` squarefree of degree prime to `n`, `A(0) ≠ 0`), `0 < j < n` prime to `n`, and the
integrand `B(t) θʲ / (tᵏ Aˡ)`:

1. Search `z ∈ Fₘ` with `z′ + (1/n)(a₀′/a₀) z = 0` (`a₀ = A(0)`). Without one, `ⁿ√a₀ ∉ Fₘ` even after
   adjoining constants, the logarithms have no `yʲ`-part, and the answer is the Risch equation
   `y′ + (j/n)(A′/A) y = B/(tᵏ Aˡ)`.
2. Otherwise `κ = zⁿ a₀ ∈ ℚ`; on the twist `ỹⁿ = Â = (zⁿ/κ) A` the points over `t = 0` are `(0, ζᵏ)`.
   Over the cyclotomic extension `Kₘ(ζ)` of the code field (`NFz`, `ζ` a root of `Φₙ`) the torsion
   oracle is asked about `Γ = ∑_k (c_n(k) + M₀)(0, ζᵏ)` (Ramanujan sums `c_n(k)`). Not torsion: the
   Risch equation as in 1. Torsion of order `N`: the witness `W` over `Kₘ(ζ)`, its norm to `Kₘ`
   (checked to have coefficients in `Kₘ`), and the `ỹʲ`-coordinate `E` of `W′/W` (extended gcd
   modulo `Yⁿ − Â`) give the column `zʲ E`; the answer is the parametric Risch equation.
-/

open Polynomial CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- `Xⁿ − 1`. -/
def xnSub1 (n : ℕ) : CPoly ℚ := (-1 : ℚ) :: (List.replicate (n - 1) 0 ++ [1])

/-- **The cyclotomic polynomial** `Φₙ`, by division of `Xⁿ − 1` by `∏_{d ∣ n, d < n} Φ_d`. -/
def cycloQ (n : ℕ) : CPoly ℚ :=
  if n = 0 then [1] else
    (CPoly.divMod (xnSub1 n) (((List.range n).filter (fun d ↦ decide (0 < d ∧ d ∣ n))).attach.foldr
      (fun d acc ↦ CPoly.mul (cycloQ d.1) acc) [1])).1
termination_by n
decreasing_by exact List.mem_range.mp (List.mem_filter.mp d.2).1

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- `Φₙ` over the code field `Kₘ`. -/
def cycK (m n : ℕ) : CPoly (KF Fc m) := CPoly.trim (List.map (fun q : ℚ ↦ (Rat.cast q : KF Fc m)) (cycloQ n))

section NFsec

variable (m n : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))]

/-- The cyclotomic extension `Kₘ(ζ)` of the code field. -/
abbrev NFz : Type := NFK.NF (cycK Fc m n)

/-- `ζ`. -/
def zetaN : NFz Fc m n := NFK.mk _ [0, 1]

/-- `Kₘ → Kₘ(ζ)`. -/
def embNF (a : KF Fc m) : NFz Fc m n := NFK.mk _ [a]

/-- **The reductions of `Kₘ(ζ)`**: a reduction of `Kₘ` and a simple root of `Φₙ` modulo `p`. -/
def redAtNF (rs : ℕ → ℕ) (p : ℕ) : Option (RedFns p (NFz Fc m n)) :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    match redAtKF Fc m rs p with
    | none => none
    | some R =>
      if (cycK Fc m n).all R.ok then
        ((List.range p).find? fun i ↦
          evalC ((cycK Fc m n).map R.red) (i : ZMod p) == 0 &&
          evalC (CPoly.deriv ((cycK Fc m n).map R.red)) (i : ZMod p) != 0).map fun i ↦
            nfkFns R (cycK Fc m n) (i : ZMod p)
      else none
  else none

/-- The shift making the Ramanujan multiplicities non-negative. -/
def ramM0 (n : ℕ) : ℤ := ((List.range n).map fun k ↦ |ramC n k|).sum

/-- The multiplicities `c_n(k) + M₀` at the points `(0, ζᵏ)`. -/
def ramMult (n : ℕ) : Fin n → ℕ := fun k ↦ (ramC n k + ramM0 n).toNat

/-- The twisted polynomial `Â = (zⁿ/κ) A`, a code of level `m`. -/
def krAh (A : GPoly (LC m)) (z : LC m) (κ : ℚ) : GPoly (LC m) :=
  A.map ((MO Fc ks m).mul ((MO Fc ks m).mul (powC (MO Fc ks m) z n) (mcst Fc ks m κ⁻¹)))

/-- `Â` over `Kₘ(ζ)`. -/
def krFK (A : GPoly (LC m)) (z : LC m) (κ : ℚ) : CPoly (NFz Fc m n) :=
  CPoly.trim (((krAh Fc ks m n A z κ).map (trC Fc m)).map (embNF Fc m n))

/-- The torsion answer for `Γ = ∑_k (c_n(k) + M₀)(0, ζᵏ)`. -/
def krTorsC (A : GPoly (LC m)) (z : LC m) (κ : ℚ) (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option (Option ℕ) :=
  torsOracleC (redAtNF Fc m n rs) (cpf (krFK Fc ks m n A z κ)) ps bound (krFK Fc ks m n A z κ) n
    (gammaL (fun _ : Fin n ↦ (0 : NFz Fc m n)) (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (ramMult n) 1)

/-- The witness of `N Γ` over `Kₘ(ζ)`. -/
def krWit (A : GPoly (LC m)) (z : LC m) (κ : ℚ) (N : ℕ) : Option (BPoly (NFz Fc m n)) :=
  witW (krFK Fc ks m n A z κ) n ((krFK Fc ks m n A z κ).length - 1)
    (fun _ : Fin n ↦ (0 : NFz Fc m n)) (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (ramMult n) N

/-- `a(X) ↦ a(Xᵘ)` on codes. -/
def expandC {R : Type*} [Zero R] (u : ℕ) : List R → List R
  | [] => []
  | a :: l => a :: (List.replicate (u - 1) 0 ++ expandC u l)

/-- The Galois action `ζ ↦ ζᵘ` on `Kₘ(ζ)`. -/
def tauN (u : ℕ) (a : NFz Fc m n) : NFz Fc m n := NFK.mk _ (expandC u a.1)

/-- **The norm** `∏_{u unit} τ_u W` of a bivariate polynomial over `Kₘ(ζ)`. -/
def normNF (W : BPoly (NFz Fc m n)) : BPoly (NFz Fc m n) :=
  ((List.range n).filter fun u ↦ Nat.Coprime u n).foldr
    (fun u acc ↦ mulB (W.map fun c ↦ c.map (tauN Fc m n u)) acc) [[1]]

/-- Descend to `Kₘ` when every coefficient lies there. -/
def descendNF (W : BPoly (NFz Fc m n)) : Option (BPoly (KF Fc m)) :=
  if W.all (·.all fun a ↦ decide (a.1.length ≤ 1)) then
    some (W.map fun c ↦ c.map fun a ↦ a.1.getD 0 0)
  else none

end NFsec

section Column

variable (m n : ℕ)

/-- A polynomial in `t` as a code of level `m + 1`. -/
def pcP (P : GPoly (LC m)) : LC (m + 1) := (P, [(MO Fc ks m).one])

/-- **The column** `zʲ E`, `E` the `ỹʲ`-coordinate of `W′/W` on `ỹⁿ = Â`: derivatives on the tower
codes, the extended gcd modulo `Yⁿ − Â` over the normalized code field `K_{m+1}` (`none` if the gcd
is not a non-zero constant). -/
def krCol (Ah : GPoly (LC m)) (z : LC m) (j : ℕ) (W : BPoly (KF Fc m)) : Option (LC (m + 1)) :=
  let O := MO Fc ks (m + 1)
  let tr := trC Fc (m + 1)
  let Wc : List (LC (m + 1)) := W.map fun c ↦ pcP Fc ks m (c.map (unTr Fc m))
  let Ahc := pcP Fc ks m Ah
  let r := O.mul (mcst Fc ks (m + 1) (1 / n)) (O.mul (O.deriv Ahc) (O.inv Ahc))
  let Wd : List (LC (m + 1)) := (List.range Wc.length).map fun i ↦
    O.add (O.deriv (Wc.getD i O.zero)) (O.mul (O.mul (mcst Fc ks (m + 1) i) r) (Wc.getD i O.zero))
  let WK : CPoly (KF Fc (m + 1)) := Wc.map tr
  let WdK : CPoly (KF Fc (m + 1)) := Wd.map tr
  let MK : CPoly (KF Fc (m + 1)) := (-(tr Ahc)) :: (List.replicate (n - 1) 0 ++ [1])
  let e := CPoly.egcd WK MK
  let g := CPoly.trim e.1
  if g.length = 1 then
    let D := (CPoly.divMod (CPoly.mul WdK e.2.1) MK).2
    some (normC Fc (m + 1) (O.mul (pcP Fc ks m [powC (MO Fc ks m) z j])
      (unTr Fc (m + 1) (D.getD j 0 * (g.getD 0 1)⁻¹))))
  else none

end Column

/-- The potential `(1/n) a₀′/a₀`. -/
def halfFrN (m n : ℕ) (a0 : LC m) : FRep (LC m) := ⟨(MO Fc ks m).zero, [(mcst Fc ks m (1 / n), a0)]⟩

/-- A non-zero `z` with `zⁿ A(0)` constant, if any. -/
def krZ (m n : ℕ) (A : GPoly (LC m)) : Option (LC m) :=
  ((prdeC Fc ks lv m (halfFrN Fc ks m n (A.getD 0 (MO Fc ks m).zero)) []).find?
    (fun r ↦ !(MO Fc ks m).isZero r.2)).map (·.2)

/-- **The decision** (`none`: data not accepted, the torsion oracle did not answer within its bounds,
or a runtime check on the witness failed). -/
def krDecideC (m n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (A B : GPoly (LC m))
    (kt l : ℕ) (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  let O := MO Fc ks m
  let rhs : LC (m + 1) := (B, denC Fc ks m kt l A)
  let frA := kpFr Fc ks m j n A
  let plain := rdeOKFr Fc ks lv (m + 1) frA rhs
  if !(decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) then none
  else if O.isZero (A.getD 0 O.zero) then none
  else
    match krZ Fc ks lv m n A with
    | none => some plain
    | some z =>
      let κ := (ratValC Fc ks m (O.mul (powC O z n) (A.getD 0 O.zero))).getD 0
      if κ = 0 then none
      else
        match krTorsC Fc ks m n A z κ cpf ps bound rs with
        | none => none
        | some none => some plain
        | some (some N) =>
          match krWit Fc ks m n A z κ N with
          | none => none
          | some Wb =>
            match descendNF Fc m n (normNF Fc m n Wb) with
            | none => none
            | some W0 =>
              match krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0 with
              | none => none
              | some col => some ((prdeC Fc ks lv (m + 1) frA [rhs, col]).any
                  fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- **The decision** (certificates by search modulo `p`). -/
def krDecide (m n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (A B : GPoly (LC m))
    (kt l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  krDecideC Fc ks lv m n j A B kt l (fun fK ↦ searchCert fK n) ps bound rs

/-- **The decision with local torsion certificates** (`kr_decided`). -/
def krDecideL (m n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (A B : GPoly (LC m))
    (kt l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  krDecideC Fc ks lv m n j A B kt l (fun fK ↦ localCert fK n) ps bound rs

/-- The torsion answer (certificates by search modulo `p`). -/
def krTors (m n : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (A : GPoly (LC m)) (z : LC m)
    (κ : ℚ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option (Option ℕ) :=
  krTorsC Fc ks m n A z κ (fun fK ↦ searchCert fK n) ps bound rs

end Curves.MT
