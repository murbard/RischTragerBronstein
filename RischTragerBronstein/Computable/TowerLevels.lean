import RischTragerBronstein.Computable.GIntegrateHermite

/-!
# Towers of arbitrary height, uniformly

The foundation for a recursive integrator: codes, operations and models for towers
`ℚ ⊂ ℚ(t₁) ⊂ ℚ(t₁)(t₂) ⊂ …` of **any height `n`**, defined by recursion on `n`.

* `Tower.Code n` — the type of codes at height `n` (`Code 0 = ℚ`, `Code (n+1) = GFrac (Code n)`);
* `Tower.Spec n` — a tower specification: for each step, the code `w` of `tᵢ′ ∈ Kᵢ₋₁[tᵢ]`
  (`Spec (n+1) = Spec n × GPoly (Code n)`; no induction-recursion is needed, since `Spec (n+1)`
  only refers to `Code n`);
* `Tower.ops n sp : COps (Code n)` — the executable operations;
* `Tower.Level n sp` / `Tower.level n sp` — the differential field `K` of the tower (iterated
  `RatFunc` with `ratFuncOfDeriv`), of characteristic zero, together with the proof that
  `ops n sp` models it (`CField`).

Every algorithm written against `COps`/`CField` (`divMod`, `egcd`, `solveBezout`, `hermite`,
`integrateByHermite`, `linearPole`, …) is thereby available, with its correctness theorem, at every
height.
-/

open Polynomial Differential

namespace Tower

/-- Codes at height `n`. -/
def Code : ℕ → Type
  | 0 => ℚ
  | n + 1 => GFrac (Code n)

/-- Tower specifications: the derivative `tᵢ′ = wᵢ(tᵢ)` of each generator. -/
def Spec : ℕ → Type
  | 0 => Unit
  | n + 1 => Spec n × GPoly (Code n)

/-- Executable operations at height `n`. -/
def ops : (n : ℕ) → Spec n → COps (Code n)
  | 0, _ => COps.ofDecidableField ℚ
  | n + 1, sp => (ops n sp.1).monomial sp.2

/-- The semantic side of a level: the differential field and the model. -/
structure Level (n : ℕ) (sp : Spec n) where
  /-- the differential field of the tower -/
  K : Type
  [instField : Field K]
  [instDiff : Differential K]
  [instChar : CharZero K]
  /-- `ops n sp` models `K` -/
  M : CField (Code n) K (ops n sp)

attribute [instance] Level.instField Level.instDiff Level.instChar

/-- The tower of height `n`: iterated `RatFunc`, with the derivations prescribed by `sp`. -/
noncomputable def level : (n : ℕ) → (sp : Spec n) → Level n sp
  | 0, _ => { K := ℚ, M := CField.ofDecidableField ℚ fun _ ↦ rfl }
  | n + 1, sp =>
    let L := level n sp.1
    letI : Differential (RatFunc L.K) := ratFuncOfDeriv (GPoly.toPoly L.M sp.2)
    { K := RatFunc L.K
      instChar := charZero_of_injective_algebraMap (algebraMap L.K (RatFunc L.K)).injective
      M := L.M.monomial sp.2 }

/-- Hermite-only integration at the top step of any tower is certified:
a returned answer is an antiderivative in the tower's differential field. -/
theorem integrateByHermite_sound_level (n : ℕ) (sp : Spec (n + 1)) {A D : GPoly (Code n)}
    {g : GPoly (Code n) × GPoly (Code n)}
    (h : GPoly.integrateByHermite (ops n sp.1) sp.2 A D = some g) :
    letI := ratFuncOfDeriv (GPoly.toPoly (level n sp.1).M sp.2)
    (algebraMap (level n sp.1).K[X] (RatFunc (level n sp.1).K) (GPoly.toPoly (level n sp.1).M g.1) /
        algebraMap (level n sp.1).K[X] (RatFunc (level n sp.1).K)
          (GPoly.toPoly (level n sp.1).M g.2))′ =
      algebraMap (level n sp.1).K[X] (RatFunc (level n sp.1).K) (GPoly.toPoly (level n sp.1).M A) /
        algebraMap (level n sp.1).K[X] (RatFunc (level n sp.1).K)
          (GPoly.toPoly (level n sp.1).M D) :=
  GPoly.integrateByHermite_sound (level n sp.1).M h

end Tower

namespace Tower

/-- `1 / (x t₁)` as an element of height 2. -/
def invXT : Code 2 :=
  ([(([1], [1]) : GFrac ℚ)], [(([0], [1]) : GFrac ℚ), (([0, 1], [1]) : GFrac ℚ)])

/-- The tower `ℚ(x)(log x)(log log x)` of height three: `x′ = 1`, `t₁′ = 1/x`, `t₂′ = 1/(x t₁)`. -/
def spec₃ : Spec 3 :=
  ((((), ([1] : GPoly ℚ)), ([(([1], [0, 1]) : GFrac ℚ)] : GPoly (Code 1))), ([invXT] : GPoly (Code 2)))

/-- `t₂ = log log x` as an element of height 3. -/
def t₂ : Code 3 :=
  ([(ops 2 spec₃.1).zero, (ops 2 spec₃.1).one], [(ops 2 spec₃.1).one])

end Tower

open Tower in
-- at height three: (t₂²)′ is not zero …
#eval (ops 3 spec₃).isZero ((ops 3 spec₃).deriv ((ops 3 spec₃).mul t₂ t₂))
open Tower in
-- … while t₂′ - 1/(x t₁) tests as zero
#eval (ops 3 spec₃).isZero ((ops 3 spec₃).add ((ops 3 spec₃).deriv t₂)
  ((ops 3 spec₃).neg ([invXT], [(ops 2 spec₃.1).one])))
