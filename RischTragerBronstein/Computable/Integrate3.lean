import RischTragerBronstein.Computable.IntegratePrim2Concrete
import RischTragerBronstein.Computable.IntegrateNestedLogConcrete
import RischTragerBronstein.Computable.IntegrateLiConcrete
import RischTragerBronstein.Computable.IntegrateExpPrimConcrete
import RischTragerBronstein.Computable.IntegrateExpExpConcrete
import RischTragerBronstein.Computable.IntegratePrimExpConcrete
import RischTragerBronstein.Computable.IntegrateLiExpConcrete
import RischTragerBronstein.Computable.IntegrateExpArgPrimConcrete
import RischTragerBronstein.Computable.IntegrateExpArgExpConcrete
import RischTragerBronstein.Computable.IntegrateHexpPrimConcrete
import RischTragerBronstein.Computable.IntegratePrimHexpConcrete
import RischTragerBronstein.Computable.IntegrateLiHexpConcrete
import RischTragerBronstein.Computable.IntegrateExpHexpConcrete
import RischTragerBronstein.Computable.IntegrateHexpHexpConcrete
import RischTragerBronstein.Computable.IntegrateExpArgHexpConcrete
import RischTragerBronstein.Computable.Integrate2

/-!
# One entry point for all decided towers of height three over `R(x)`

`Tower3Spec R` describes a tower `R(x)(t₁)(t₂)` by the data of its two monomials; `certs` are the
executable side conditions (all decidable by `decide +kernel` on `ℚ`); `w₂`, `w₃` the codes of
`t₁′`, `t₂′`; `integrate3` dispatches to the integrator of the shape. `integrate3_decides`: for
every shape with valid certificates and every element `A / D` of the field, the answer is `true`
iff `A / D` has an elementary integral.
-/

open Polynomial

namespace Tower

open Differential CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- The decided shapes of height three. -/
inductive Tower3Spec (R : Type*) [Field R]
  /-- two independent primitives `t₁′ = η₁`, `t₂′ = η₂` (`log x`, `log (x + 1)`, …) -/
  | prim2 (En₁ Ed₁ En₂ Ed₂ : CPoly R) (Iη₁ Iη₂ : RationalIntegral R)
  /-- `t₁′ = η₁`, `t₂ = log U` with `U ∈ R(x)(t₁)`, `t₂′ = W = U′ / U` -/
  | nestedLog (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (W U : GFrac (GFrac R))
  /-- `t₁′ = η₁`, `t₂′ = W ∈ R(x)(t₁)` with non-constant residues (`li x`) -/
  | li (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (W : GFrac (GFrac R))
  /-- `t₁′ = η₁`, `t₂ = exp a(x)` -/
  | expPrim (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (a : CPoly R)
  /-- `t₁ = exp a₁(x)`, `t₂ = exp a(x)`, independent -/
  | expExp (a₁ a : CPoly R)
  /-- `t₁ = exp a₁(x)`, `t₂ = log U` with `U ∈ R(x)(t₁)` -/
  | primExp (a₁ : CPoly R) (W U : GFrac (GFrac R))
  /-- `t₁ = exp a₁(x)`, `t₂′ = W ∈ R(x)(t₁)` with non-constant residues -/
  | liExp (a₁ : CPoly R) (W : GFrac (GFrac R))
  /-- `t₁′ = η₁`, `t₂ = exp a` with `a ∈ R(x)[t₁]` (`x^x`) -/
  | expArgPrim (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (a : GPoly (GFrac R))
  /-- `t₁ = exp a₁(x)`, `t₂ = exp a` with `a ∈ R(x)[t₁]` (`e^{eˣ}`) -/
  | expArgExp (a₁ : CPoly R) (a : GPoly (GFrac R))
  /-- `t₁′ = η₁`, `t₂′ = η t₂` with `η = Gn / Gd ∈ R(x)` arbitrary (`exp (arctan x)` over `log x`),
  `μ` an annihilator of the residues of `η` -/
  | hexpPrim (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (Gn Gd μ : CPoly R)
  /-- `t₁′ = η t₁` with `η = Hn / Hd ∈ R(x)` arbitrary, `t₂ = log U` with `U ∈ R(x)(t₁)`
  (`log (exp (arctan x) + x)`) -/
  | primHexp (Hn Hd μ : CPoly R) (W U : GFrac (GFrac R))
  /-- `t₁′ = η t₁` with `η = Hn / Hd ∈ R(x)` arbitrary, `t₂′ = W ∈ R(x)(t₁)` with non-constant
  residues (`∫ dx / (exp (arctan x) + x)`) -/
  | liHexp (Hn Hd μ : CPoly R) (W : GFrac (GFrac R))
  /-- `t₁′ = η t₁` with `η = Hn / Hd ∈ R(x)` arbitrary, `t₂ = exp a(x)`, `a ∈ R[x]`, independent
  (`ℚ(x, exp (arctan x), eˣ)`; certified by `hexpExpIndep`) -/
  | expHexp (Hn Hd μ a : CPoly R)
  /-- `t₁′ = η₁ t₁`, `t₂′ = η₂ t₂`, `ηᵢ ∈ R(x)` arbitrary, independent (`hexpHexpIndep`;
  `ℚ(x, exp (arctan x), exp (1/x))`) -/
  | hexpHexp (Hn Hd μ Hn₂ Hd₂ μ₂ : CPoly R)
  /-- `t₁′ = η t₁`, `η ∈ R(x)` arbitrary, `t₂ = exp a` with `a ∈ R(x)[t₁]`, `a′` of positive
  `t₁`-degree (`exp (exp (arctan x))`) -/
  | expArgHexp (Hn Hd μ : CPoly R) (a : GPoly (GFrac R))

namespace Tower3Spec

/-- The operations of `R(x)(t₁)`. -/
def ops₂ : Tower3Spec R → COps (GFrac (GFrac R))
  | prim2 En₁ Ed₁ _ _ _ _ => ops₂p En₁ Ed₁
  | nestedLog En₁ Ed₁ _ _ _ => ops₂p En₁ Ed₁
  | li En₁ Ed₁ _ _ => ops₂p En₁ Ed₁
  | expPrim En₁ Ed₁ _ _ => ops₂p En₁ Ed₁
  | expExp a₁ _ => ops₂e a₁
  | primExp a₁ _ _ => ops₂e a₁
  | liExp a₁ _ => ops₂e a₁
  | expArgPrim En₁ Ed₁ _ _ => ops₂p En₁ Ed₁
  | expArgExp a₁ _ => ops₂e a₁
  | hexpPrim En₁ Ed₁ _ _ _ _ => ops₂p En₁ Ed₁
  | primHexp Hn Hd _ _ _ => ops₂h Hn Hd
  | liHexp Hn Hd _ _ => ops₂h Hn Hd
  | expHexp Hn Hd _ _ => ops₂h Hn Hd
  | hexpHexp Hn Hd _ _ _ _ => ops₂h Hn Hd
  | expArgHexp Hn Hd _ _ => ops₂h Hn Hd

/-- The executable certificates of a shape. -/
def certs [HasNatTest R] [HasRatRoots R] : Tower3Spec R → Bool
  | prim2 En₁ Ed₁ En₂ Ed₂ Iη₁ Iη₂ =>
    rationalCheck En₁ Ed₁ Iη₁ && rationalCheck En₂ Ed₂ Iη₂ && !isZero Iη₁.r &&
      (limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s).isNone
  | nestedLog En₁ Ed₁ Iη₁ W U =>
    rationalCheck En₁ Ed₁ Iη₁ && !isZero Iη₁.r && !GPoly.isZero (ops₁g R) W.2 &&
      !GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 &&
      !isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 && !(ops₂p En₁ Ed₁).isZero U &&
      (ops₂p En₁ Ed₁).isZero ((ops₂p En₁ Ed₁).add ((ops₂p En₁ Ed₁).mul W U)
        ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).deriv U)))
  | li En₁ Ed₁ Iη₁ W =>
    rationalCheck En₁ Ed₁ Iη₁ && !isZero Iη₁.r && !GPoly.isZero (ops₁g R) W.2 &&
      !GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 &&
      !isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 &&
      !GPoly.residueCheck (ops₁g R) [(En₁, Ed₁)]
        (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
          (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s
  | expPrim En₁ Ed₁ Iη₁ a =>
    rationalCheck En₁ Ed₁ Iη₁ && !isZero Iη₁.r && decide (trim (deriv a) ≠ [])
  | expExp a₁ a =>
    decide (trim (deriv a₁) ≠ []) && decide (trim (deriv a) ≠ []) && expIndep a₁ a
  | primExp a₁ W U =>
    decide (trim (deriv a₁) ≠ []) && !GPoly.isZero (ops₁g R) W.2 && !isDerivExp a₁ W.1 W.2 &&
      !(ops₂e a₁).isZero U &&
      (ops₂e a₁).isZero ((ops₂e a₁).add ((ops₂e a₁).mul W U)
        ((ops₂e a₁).neg ((ops₂e a₁).deriv U)))
  | liExp a₁ W =>
    decide (trim (deriv a₁) ≠ []) && !GPoly.isZero (ops₁g R) W.2 && !isDerivExp a₁ W.1 W.2 &&
      !GPoly.residueCheck (ops₁g R) (expW a₁) (expReduce a₁ W.1 W.2).r (expReduce a₁ W.1 W.2).s
  | expArgPrim En₁ Ed₁ Iη₁ a =>
    rationalCheck En₁ Ed₁ Iη₁ && !isZero Iη₁.r &&
      decide (2 ≤ (GPoly.trim (ops₁g R) (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] a)).length)
  | expArgExp a₁ a =>
    decide (trim (deriv a₁) ≠ []) &&
      decide (2 ≤ (GPoly.trim (ops₁g R) (GPoly.derivT (ops₁g R) (expW a₁) a)).length)
  | hexpPrim En₁ Ed₁ Iη₁ Gn Gd μ =>
    rationalCheck En₁ Ed₁ Iη₁ && !isZero Iη₁.r && !isZero Gn && !isZero Gd &&
      Tower2Spec.coprimeCheck Gn Gd && hyperexpMonomialCheck Gn Gd μ
  | primHexp Hn Hd μ W U =>
    !isZero Hn && !isZero Hd && Tower2Spec.coprimeCheck Hn Hd && hyperexpMonomialCheck Hn Hd μ &&
      !GPoly.isZero (ops₁g R) W.2 && !isDerivHexp Hn Hd μ W.1 W.2 && !(ops₂h Hn Hd).isZero U &&
      (ops₂h Hn Hd).isZero ((ops₂h Hn Hd).add ((ops₂h Hn Hd).mul W U)
        ((ops₂h Hn Hd).neg ((ops₂h Hn Hd).deriv U)))
  | liHexp Hn Hd μ W =>
    !isZero Hn && !isZero Hd && Tower2Spec.coprimeCheck Hn Hd && hyperexpMonomialCheck Hn Hd μ &&
      !GPoly.isZero (ops₁g R) W.2 && !isDerivHexp Hn Hd μ W.1 W.2 &&
      !GPoly.residueCheck (ops₁g R) (hexpW Hn Hd) (hexpReduce Hn Hd W.1 W.2).r
        (hexpReduce Hn Hd W.1 W.2).s
  | expHexp Hn Hd μ a =>
    !isZero Hn && !isZero Hd && Tower2Spec.coprimeCheck Hn Hd && hyperexpMonomialCheck Hn Hd μ &&
      decide (trim (deriv a) ≠ []) && hexpExpIndep Hn Hd μ a
  | hexpHexp Hn Hd μ Hn₂ Hd₂ μ₂ =>
    !isZero Hn && !isZero Hd && Tower2Spec.coprimeCheck Hn Hd && hyperexpMonomialCheck Hn Hd μ &&
      !isZero Hn₂ && !isZero Hd₂ && Tower2Spec.coprimeCheck Hn₂ Hd₂ &&
      hyperexpMonomialCheck Hn₂ Hd₂ μ₂ && hexpHexpIndepAll Hn Hd μ Hn₂ Hd₂ μ₂
  | expArgHexp Hn Hd μ a =>
    !isZero Hn && !isZero Hd && Tower2Spec.coprimeCheck Hn Hd && hyperexpMonomialCheck Hn Hd μ &&
      decide (2 ≤ (GPoly.trim (ops₁g R) (GPoly.derivT (ops₁g R) (hexpW Hn Hd) a)).length)

/-- The code of `t₁′` (a polynomial over `R(x)` in `t₁`). -/
noncomputable def w₂ : Tower3Spec R → (RatFunc R)[X]
  | prim2 En₁ Ed₁ _ _ _ _ => C (primEta En₁ Ed₁)
  | nestedLog En₁ Ed₁ _ _ _ => C (primEta En₁ Ed₁)
  | li En₁ Ed₁ _ _ => C (primEta En₁ Ed₁)
  | expPrim En₁ Ed₁ _ _ => C (primEta En₁ Ed₁)
  | expExp a₁ _ => C (algebraMap R[X] (RatFunc R) (derivative (toPoly a₁))) * X
  | primExp a₁ _ _ => C (algebraMap R[X] (RatFunc R) (derivative (toPoly a₁))) * X
  | liExp a₁ _ => C (algebraMap R[X] (RatFunc R) (derivative (toPoly a₁))) * X
  | expArgPrim En₁ Ed₁ _ _ => C (primEta En₁ Ed₁)
  | expArgExp a₁ _ => C (algebraMap R[X] (RatFunc R) (derivative (toPoly a₁))) * X
  | hexpPrim En₁ Ed₁ _ _ _ _ => C (primEta En₁ Ed₁)
  | primHexp Hn Hd _ _ _ =>
    C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X
  | liHexp Hn Hd _ _ =>
    C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X
  | expHexp Hn Hd _ _ =>
    C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X
  | hexpHexp Hn Hd _ _ _ _ =>
    C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X
  | expArgHexp Hn Hd _ _ =>
    C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X

/-- The code of `t₂′` (a polynomial over `R(x)(t₁)` in `t₂`). -/
noncomputable def w₃ : Tower3Spec R → (RatFunc (RatFunc R))[X]
  | prim2 _ _ En₂ Ed₂ _ _ => C (RatFunc.C (primEta En₂ Ed₂))
  | nestedLog _ _ _ W _ => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W)
  | li _ _ _ W => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W)
  | expPrim _ _ _ a => C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
      (algebraMap R[X] (RatFunc R) (derivative (toPoly a)))) * X
  | expExp _ a => C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
      (algebraMap R[X] (RatFunc R) (derivative (toPoly a)))) * X
  | primExp _ W _ => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W)
  | liExp _ W => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W)
  | expArgPrim En₁ Ed₁ _ a => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) (expEtaG En₁ Ed₁ a)) * X
  | expArgExp a₁ a => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) (expEtaE a₁ a)) * X
  | hexpPrim _ _ _ Gn Gd _ => C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
      (algebraMap R[X] (RatFunc R) (toPoly Gn) / algebraMap R[X] (RatFunc R) (toPoly Gd))) * X
  | primHexp _ _ _ W _ => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W)
  | liHexp _ _ _ W => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W)
  | expHexp _ _ _ a => C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
      (algebraMap R[X] (RatFunc R) (derivative (toPoly a)))) * X
  | hexpHexp _ _ _ Hn₂ Hd₂ _ => C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
      (algebraMap R[X] (RatFunc R) (toPoly Hn₂) / algebraMap R[X] (RatFunc R) (toPoly Hd₂))) * X
  | expArgHexp Hn Hd _ a => C (val₂ (RatFunc R) (RatFunc (RatFunc R)) (expEtaH Hn Hd a)) * X

/-- **The integrator**: dispatch on the shape. -/
def integrate3 [HasNatTest R] [HasRatRoots R] : Tower3Spec R → GPoly (GFrac (GFrac R)) →
    GPoly (GFrac (GFrac R)) → Bool
  | prim2 En₁ Ed₁ En₂ Ed₂ Iη₁ Iη₂, A, D => integratePrim2 En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A D
  | nestedLog En₁ Ed₁ Iη₁ W _, A, D => integrateNestedLog En₁ Ed₁ Iη₁ W A D
  | li En₁ Ed₁ Iη₁ W, A, D => integrateLi En₁ Ed₁ Iη₁ W A D
  | expPrim En₁ Ed₁ Iη₁ a, A, D => integrateExpPrim En₁ Ed₁ Iη₁ a A D
  | expExp a₁ a, A, D => integrateExpExp a₁ a A D
  | primExp a₁ W _, A, D => integratePrimExp a₁ W A D
  | liExp a₁ W, A, D => integrateLiExp a₁ W A D
  | expArgPrim En₁ Ed₁ Iη₁ a, A, D => integrateExpArgPrim En₁ Ed₁ Iη₁ a A D
  | expArgExp a₁ a, A, D => integrateExpArgExp a₁ a A D
  | hexpPrim En₁ Ed₁ Iη₁ Gn Gd μ, A, D => integrateHexpPrim En₁ Ed₁ Iη₁ Gn Gd μ A D
  | primHexp Hn Hd μ W _, A, D => integratePrimHexp Hn Hd μ W A D
  | liHexp Hn Hd μ W, A, D => integrateLiHexp Hn Hd μ W A D
  | expHexp Hn Hd μ a, A, D => integrateExpHexp Hn Hd μ a A D
  | hexpHexp Hn Hd μ Hn₂ Hd₂ _, A, D => integrateHexpHexp Hn Hd μ Hn₂ Hd₂ A D
  | expArgHexp Hn Hd μ a, A, D => integrateExpArgHexp Hn Hd μ a A D

end Tower3Spec

variable [CharZero R] [HasNatTest R] [HasRatRoots R] [Differential R]

set_option maxHeartbeats 1600000 in
/-- **Every decided height-three tower, one theorem.** -/
theorem integrate3_decides (h0 : ∀ r : R, r′ = 0) (s : Tower3Spec R) (hc : s.certs = true)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero s.ops₂ D = false) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv s.w₂
    letI : Differential (RatFunc (RatFunc (RatFunc R))) := ratFuncOfDeriv s.w₃
    HasElementaryIntegral
        (val₃ (RatFunc R) (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) A D) ↔
      s.integrate3 A D = true := by
  cases s with
  | prim2 En₁ Ed₁ En₂ Ed₂ Iη₁ Iη₂ =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none]
      at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    exact integratePrim2_decides_concrete h0 En₁ Ed₁ En₂ Ed₂ Iη₁ Iη₂ h1 h2 h3 h4 A D hD0
  | nestedLog En₁ Ed₁ Iη₁ W U =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
    exact integrateNestedLog_decides_concrete h0 En₁ Ed₁ W U Iη₁ h1 h2 h3 h4 h5 h6 h7 A D hD0
  | li En₁ Ed₁ Iη₁ W =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    exact integrateLi_decides_concrete h0 En₁ Ed₁ W Iη₁ h1 h2 h3 h4 h5 h6 A D hD0
  | expPrim En₁ Ed₁ Iη₁ a =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    exact integrateExpPrim_decides_concrete h0 En₁ Ed₁ a h3 Iη₁ h1 h2 A D hD0
  | expExp a₁ a =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    exact integrateExpExp_decides_concrete h0 a₁ a h1 h2 h3 A D hD0
  | primExp a₁ W U =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    exact integratePrimExp_decides_concrete h0 a₁ h1 W U h2 h3 h4 h5 A D hD0
  | liExp a₁ W =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    exact integrateLiExp_decides_concrete h0 a₁ h1 W h2 h3 h4 A D hD0
  | expArgPrim En₁ Ed₁ Iη₁ a =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    exact integrateExpArgPrim_decides_concrete h0 En₁ Ed₁ a h3 Iη₁ h1 h2 A D hD0
  | expArgExp a₁ a =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    exact integrateExpArgExp_decides_concrete h0 a₁ a h1 h2 A D hD0
  | hexpPrim En₁ Ed₁ Iη₁ Gn Gd μ =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    refine integrateHexpPrim_decides_concrete h0 En₁ Ed₁ Gn Gd μ ?_ ?_ (coprimeCheck_sound h5) h6
      Iη₁ h1 h2 A D hD0
    · intro h; rw [← isZero_iff] at h; rw [h] at h3; exact absurd h3 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h4; exact absurd h4 (by decide)
  | primHexp Hn Hd μ W U =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
    refine integratePrimHexp_decides_concrete h0 Hn Hd μ ?_ ?_ (coprimeCheck_sound h3) h4 W U
      h5 h6 h7 h8 A D hD0
    · intro h; rw [← isZero_iff] at h; rw [h] at h1; exact absurd h1 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h2; exact absurd h2 (by decide)
  | liHexp Hn Hd μ W =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
    refine integrateLiHexp_decides_concrete h0 Hn Hd μ ?_ ?_ (coprimeCheck_sound h3) h4 W
      h5 h6 h7 A D hD0
    · intro h; rw [← isZero_iff] at h; rw [h] at h1; exact absurd h1 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h2; exact absurd h2 (by decide)
  | expHexp Hn Hd μ a =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    refine integrateExpHexp_decides_concrete h0 Hn Hd μ a ?_ ?_ (coprimeCheck_sound h3) h4 h5 h6
      A D hD0
    · intro h; rw [← isZero_iff] at h; rw [h] at h1; exact absurd h1 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h2; exact absurd h2 (by decide)

  | hexpHexp Hn Hd μ Hn₂ Hd₂ μ₂ =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
    refine integrateHexpHexp_decides_concrete h0 Hn Hd μ ?_ ?_ (coprimeCheck_sound h3) h4
      Hn₂ Hd₂ μ₂ ?_ ?_ (coprimeCheck_sound h7) h8 h9 A D hD0
    · intro h; rw [← isZero_iff] at h; rw [h] at h1; exact absurd h1 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h2; exact absurd h2 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h5; exact absurd h5 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h6; exact absurd h6 (by decide)

  | expArgHexp Hn Hd μ a =>
    simp only [Tower3Spec.certs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    refine integrateExpArgHexp_decides_concrete h0 Hn Hd μ a ?_ ?_ (coprimeCheck_sound h3) h4 h5
      A D hD0
    · intro h; rw [← isZero_iff] at h; rw [h] at h1; exact absurd h1 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h2; exact absurd h2 (by decide)

end Tower
