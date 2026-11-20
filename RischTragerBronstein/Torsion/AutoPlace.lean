import RischTragerBronstein.Torsion.AutoIntBasis
import RischTragerBronstein.Torsion.RamRes

/-!
# Computing the place certificate of a residue component

From the Puiseux branches at the fibres with residues, `autoPlaceCert` builds a `PlaceCert` for
the component `j₀` of the residues (scaled by `s`, the lcm of the denominators): conjugate branches
are grouped into places, the residue `r_π` of each place gives `Γ_π = s r_π + e_α e_π` with the
smallest `e_α` making `Γ ≥ 0`, and the roots above `α` are the rotations `T ↦ ωⁱ T` of the
reparametrized representatives (`ω` a primitive `N`-th root of unity). Everything is checked
afterwards (`PlaceCert.check`, `torsResCheckP`); no proof is needed here.
-/

namespace Curves

open CPoly Sup EllQuad.QCoords

section Place

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Tᴺ − 1`. -/
def xnm1 (N : ℕ) : CPoly F := (List.replicate N (0 : F) ++ [1]).set 0 (-1)

/-- `ρ(ζ T)` truncated to the length of `ρ`. -/
def rotC (ζ : F) (ρ : CPoly F) : CPoly F := (List.range ρ.length).map fun m ↦ ζ ^ m * ρ.getD m 0

/-- Group conjugate branches (same `E`, `b(T) = r(ζ T)` for an `E`-th root of unity `ζ`, compared
below `L`) into places, keeping one representative each. -/
def placeReps (rf : RootFinder F) (L : ℕ) (bs : List (PBranch F)) : List (PBranch F) :=
  bs.foldl (fun reps b ↦
    let zs := (rf (xnm1 b.E)).getD [1]
    if reps.any (fun r ↦ r.E = b.E && zs.any fun ζ ↦ decide ((rotC ζ r.ser).take L = b.ser.take L))
    then reps else reps ++ [b]) []

/-- A primitive `N`-th root of unity among the roots of `T^N − 1`. -/
def primRoot (rf : RootFinder F) (N : ℕ) : Option F :=
  ((rf (xnm1 N)).getD []).find? fun ζ ↦
    (List.range N).all fun i ↦ decide (i = 0 ∨ ζ ^ i ≠ 1)

end Place

section Auto

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- The lcm of the denominators of a list of rationals. -/
def denLcm (qs : List ℚ) : ℕ := qs.foldr (fun q m ↦ Nat.lcm q.den m) 1

/-- **The place certificate** of the component `j₀` at the fibres `fibs` (with their branches),
test precision `tp`. Returns the certificate, the exponents `e_α` and the scale `s`. -/
def autoPlaceCert (rf : RootFinder F) (P : CurveProb F) (j₀ : Fin (dim F)) (L tp : ℕ)
    (fibs : List (F × List (PBranch F))) : Option (PlaceCert F × List ℤ × ℕ) := do
  -- the places above each fibre, with their residues
  let fr := fibs.map fun ab ↦
    let reps := placeReps rf L ab.2
    (ab.1, reps.map fun r ↦ (r, coord j₀ (P.resFin ab.1 ⟨r.E, [], L⟩ r.ser)))
  let s := denLcm (fr.flatMap fun f ↦ f.2.map Prod.snd)
  -- `Γ_π = s r_π + e e_π` with the smallest `e ≥` all `−s r_π / e_π`
  let eL : List ℤ := fr.map fun f ↦
    (f.2.map fun rr ↦ -((((s : ℚ) * rr.2) / rr.1.E).floor)).foldr max 0
  let places := (List.range fr.length).flatMap fun j ↦
    ((fr.getD j (0, [])).2).map fun rr ↦ (j, rr.1, rr.2)
  let Γp : List ℕ := places.map fun q ↦
    (((s : ℚ) * q.2.2).num + eL.getD q.1 0 * q.2.1.E).toNat
  let Ns : List ℕ := fr.map fun f ↦ f.2.foldr (fun rr m ↦ Nat.lcm rr.1.E m) 1
  let rtL ← (List.range fr.length).mapM fun j ↦ do
    let N := Ns.getD j 1
    let ω ← primRoot rf N
    pure ((List.range places.length).flatMap fun π ↦
      let q := places.getD π (0, ⟨1, []⟩, 0)
      if q.1 = j then (List.range q.2.1.E).map fun i ↦ (π, N / q.2.1.E, ω ^ i) else [])
  let cf : List ℕ := (List.range fr.length).map fun j ↦
    (List.range places.length).foldr (fun π m ↦
      let q := places.getD π (0, ⟨1, []⟩, 0)
      if q.1 = j then max m ((Γp.getD π 0 + q.2.1.E - 1) / q.2.1.E) else m) 0
  let dΓ : List ℕ := (List.range fr.length).map fun j ↦
    (List.range places.length).foldr (fun π m ↦
      if (places.getD π (0, ⟨1, []⟩, 0)).1 = j then m + Γp.getD π 0 else m) 0
  let n := (rtL.getD 0 []).length
  let cΓ := (dΓ.foldr (· + ·) 0) / (if n = 0 then 1 else n)
  pure (⟨(fr.map Prod.fst).zip Ns,
      places.map fun q ↦ (q.1, q.2.1.E, q.2.1.ser, L - 1), rtL, Γp, cf, dΓ, cΓ,
      fr.map fun _ ↦ tp⟩, eL, s)

end Auto

end Curves
