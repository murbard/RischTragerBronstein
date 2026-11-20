import RischTragerBronstein.Mixed.SysPrim
import RischTragerBronstein.Mixed.SysExp
import RischTragerBronstein.Mixed.SysExpT
import RischTragerBronstein.Mixed.MTRed

/-!
# The exact part over an algebraic extension of a primitive level: codes

For `θ` algebraic over `Fₘ₊₁ = Fₘ(t)` (`t′ = η`, a primitive level) with monic minimal polynomial
`P` (codes of level `m + 1`), and `f = ∑ fⱼ θʲ`, `exactC` decides whether `f = v′` for some
`v = ∑ Yᵢ θⁱ` with `Yᵢ ∈ Fₘ₊₁`:
* `θ′` from `P(θ) = 0` and a Bezout identity `s P_Y + t' P = g` (`g` a nonzero constant):
  `θ′ = −g⁻¹ s(θ) P^δ(θ)` reduced mod `P` (`dThetaC`);
* the matrix `(θⁱ)′ = ∑ⱼ Mᵢⱼ θʲ` (`derivMatC`);
* the system `Yⱼ′ + ∑ᵢ Mᵢⱼ Yᵢ = fⱼ`, with common denominators `q`, `h` (monic lcm, divisions checked),
  handed to `primSysC`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

section Codes

variable {α : Type} (O : COps α)

/-- `p mod P`. -/
def remP (P p : GPoly α) : GPoly α := (GPoly.divMod O p P).2

/-- `θ′` as a polynomial in `θ` (`none` if `P_Y` is not invertible mod `P` by the check). -/
def dThetaC (P : GPoly α) : Option (GPoly α) :=
  let e := GPoly.egcd O (GPoly.derivX O P) P
  let g := GPoly.trim O e.1
  if g.length = 1 then
    some (remP O P (GPoly.smul O (O.neg (O.inv (g.getD 0 O.zero)))
      (GPoly.mul O e.2.1 (GPoly.mapD O P))))
  else none

/-- `(θⁱ)′ mod P`. -/
def dPowC (P dθ : GPoly α) (i : ℕ) : GPoly α :=
  if i = 0 then [] else remP O P (GPoly.mul O (GPoly.monomial O (i - 1) (O.natCast i)) dθ)

/-- `lcm(a, b)` (up to a unit). -/
def lcmG (a b : GPoly α) : GPoly α :=
  GPoly.mul O a (GPoly.divMod O b (GPoly.egcd O a b).1).1

/-- Monic lcm of a list. -/
def lcmGL (ds : List (GPoly α)) : GPoly α := monicG O (ds.foldr (lcmG O) [O.one])

/-- Does `d` divide `q` (by the check), and the cofactor. -/
def cofC (q d : GPoly α) : Bool × GPoly α :=
  let r := GPoly.divMod O q d
  (GPoly.isZero O r.2, r.1)

end Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test** at a primitive level `m + 1` (`t′ = η`): `some true` if `f = v′` for
some `v ∈ Fₘ₊₁[θ]`, `some false` if not, `none` if a check fails. -/
def exactC (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) : Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  let N := P.length - 1
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten ++ f
    let q := lcmGL O (ent.map Prod.snd)
    let cofs := ent.map fun c ↦ cofC O q c.2
    if !(cofs.all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((M.getD i []).getD j O1.zero)
    let G : Fin N → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero)
    match primSysC Fc ks m η lim N A0 q q [G] with
    | none => none
    | some r => some (r.2.any fun b ↦ b.1.getD 0 0 != 0)

/-- **The exact-part test** at an exponential level `m + 1` (`t = exp a`): `some true` if `f = v′` for
some `v ∈ Fₘ₊₁[θ]`, `some false` if not, `none` if a check fails. -/
def exactCE (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) : Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  let N := P.length - 1
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten ++ f
    let q := lcmGL O (ent.map Prod.snd)
    let cofs := ent.map fun c ↦ cofC O q c.2
    if !(cofs.all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((M.getD i []).getD j O1.zero)
    let G : Fin N → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero)
    match expSysC Fc ks m a rdeD N A0 q q [G] with
    | none => none
    | some r => some (r.2.any fun b ↦ b.1.getD 0 0 != 0)

/-- **The exact-part test** at an exponential level `m + 1` (`t = exp a`), triangular limit at infinity: `some true` if `f = v′` for
some `v ∈ Fₘ₊₁[θ]`, `some false` if not, `none` if a check fails. -/
def exactCT (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) : Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  let N := P.length - 1
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten ++ f
    let q := lcmGL O (ent.map Prod.snd)
    let cofs := ent.map fun c ↦ cofC O q c.2
    if !(cofs.all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((M.getD i []).getD j O1.zero)
    let G : Fin N → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero)
    match expSysT Fc ks m a rdeD N A0 q q [G] with
    | none => none
    | some r => some (r.2.any fun b ↦ b.1.getD 0 0 != 0)

end Curves.MT
