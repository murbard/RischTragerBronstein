import RischTragerBronstein.Computable.GIntegrateHermite
import RischTragerBronstein.Liouville.ResidueTest

/-!
# The residue test, executable at any tower level

For a computable model `M` of `K`, a monomial step `t′ = w` and an integrand `b / s`
(`s` coprime to `s′`), `GPoly.residueCheck O w b s` computes

* the residue polynomial `r` with `r s′ ≡ b (mod s)` (Bézout, `solveBezout`),
* `T = r^κ ∂ₜ s - ∂ₜ r s^κ`,
* and tests `s ∣ T` by division, using only the model's zero test.

`residueCheck_spec`: the computed `r` is a residue polynomial and the check is `true` iff
`s ∣ residueTest r s`. No resultants, no factorisation, no algebraic numbers.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

/-- The residue polynomial `r`: `r s′ ≡ b (mod s)`. -/
def residuePoly (O : COps α) (w b s : GPoly α) : GPoly α :=
  (solveBezout O (derivT O w s) s b).1

/-- The residue test: `s ∣ r^κ ∂ₜ s - ∂ₜ r s^κ`. -/
def residueCheck (O : COps α) (w b s : GPoly α) : Bool :=
  let r := residuePoly O w b s
  let T := sub O (mul O (mapD O r) (derivX O s)) (mul O (derivX O r) (mapD O s))
  isZero O (divMod O T s).2

variable {O : COps α} (M : CField α K O)

theorem residuePoly_spec (w b s : GPoly α) (hs : toPoly M s ≠ 0)
    (hcop : IsCoprime (implicitDeriv (toPoly M w) (toPoly M s)) (toPoly M s)) :
    toPoly M s ∣ toPoly M (residuePoly O w b s) * implicitDeriv (toPoly M w) (toPoly M s) -
      toPoly M b := by
  have h := solveBezout_spec M (derivT O w s) s b hs (by rwa [toPoly_derivT])
  rw [toPoly_derivT] at h
  refine ⟨-toPoly M (solveBezout O (derivT O w s) s b).2, ?_⟩
  rw [residuePoly, ← h]
  ring

theorem residueCheck_iff (w b s : GPoly α) (hs : toPoly M s ≠ 0) :
    residueCheck O w b s = true ↔
      toPoly M s ∣ residueTest (toPoly M (residuePoly O w b s)) (toPoly M s) := by
  simp only [residueCheck]
  rw [isZero_iff M]
  set T := sub O (mul O (mapD O (residuePoly O w b s)) (derivX O s))
    (mul O (derivX O (residuePoly O w b s)) (mapD O s)) with hT
  have hTpoly : toPoly M T = residueTest (toPoly M (residuePoly O w b s)) (toPoly M s) := by
    rw [hT, residueTest, toPoly_sub, toPoly_mul, toPoly_mul, toPoly_mapD, toPoly_mapD,
      toPoly_derivX, toPoly_derivX]
  rw [← hTpoly]
  constructor
  · intro h0
    have := divMod_spec M T s
    rw [h0, add_zero] at this
    exact ⟨toPoly M (divMod O T s).1, by rw [this]; ring⟩
  · exact divMod_exact M T s hs

end GPoly

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

/-- Certificate that `s` is coprime to `s′` (derivation `t′ = w`). -/
def coprimeDerivCheck (O : COps α) (w s : GPoly α) : Bool :=
  (trim O (egcd O (derivT O w s) s).1).length == 1

variable {O : COps α} (M : CField α K O)

theorem coprimeDerivCheck_sound {w s : GPoly α} (h : coprimeDerivCheck O w s = true) :
    IsCoprime (implicitDeriv (toPoly M w) (toPoly M s)) (toPoly M s) := by
  rw [coprimeDerivCheck, beq_iff_eq] at h
  have hne : trim O (egcd O (derivT O w s) s).1 ≠ [] := fun h0 ↦ by simp [h0] at h
  have hdeg : (toPoly M (egcd O (derivT O w s) s).1).natDegree = 0 := by
    have := length_trim M hne
    omega
  have hg0 : toPoly M (egcd O (derivT O w s) s).1 ≠ 0 := fun h0 ↦
    hne ((trim_eq_nil_iff M _).mpr h0)
  obtain ⟨γ, hγ⟩ : ∃ γ : K, toPoly M (egcd O (derivT O w s) s).1 = C γ :=
    ⟨_, eq_C_of_natDegree_eq_zero hdeg⟩
  have hγ0 : γ ≠ 0 := fun h0 ↦ hg0 (by rw [hγ, h0, C_0])
  have hbez := egcd_spec M (derivT O w s) s
  rw [hγ, toPoly_derivT] at hbez
  refine ⟨C γ⁻¹ * toPoly M (egcd O (derivT O w s) s).2.1,
    C γ⁻¹ * toPoly M (egcd O (derivT O w s) s).2.2, ?_⟩
  have : C γ⁻¹ * C γ = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  linear_combination C γ⁻¹ * hbez + this

/-- Degrees from trimmed lengths, in every model. -/
theorem degree_lt_of_trim_length_lt {b s : GPoly α}
    (h : (trim O b).length < (trim O s).length) :
    (toPoly M b).degree < (toPoly M s).degree := by
  have hs : trim O s ≠ [] := fun h0 ↦ by simp [h0] at h
  have hs0 : toPoly M s ≠ 0 := fun h0 ↦ hs ((trim_eq_nil_iff M s).mpr h0)
  by_cases hb : trim O b = []
  · rw [(trim_eq_nil_iff M b).mp hb, degree_zero]
    exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hs0)
  · have hb0 : toPoly M b ≠ 0 := fun h0 ↦ hb ((trim_eq_nil_iff M b).mpr h0)
    rw [degree_eq_natDegree hb0, degree_eq_natDegree hs0]
    have h1 := length_trim M hb
    have h2 := length_trim M hs
    exact_mod_cast (by omega : (toPoly M b).natDegree < (toPoly M s).natDegree)

/-- The certificate always passes when `s` is coprime to `s′`: together with
`coprimeDerivCheck_sound`, the check decides coprimality. -/
theorem coprimeDerivCheck_complete {w s : GPoly α}
    (h : IsCoprime (implicitDeriv (toPoly M w) (toPoly M s)) (toPoly M s)) :
    coprimeDerivCheck O w s = true := by
  have hcop : IsCoprime (toPoly M (derivT O w s)) (toPoly M s) := by rwa [toPoly_derivT]
  obtain ⟨hga, hgb⟩ := egcd_dvd M (derivT O w s) s
  have hunit : IsUnit (toPoly M (egcd O (derivT O w s) s).1) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact isUnit_of_dvd_one (huv ▸ dvd_add (Dvd.dvd.mul_left hga u) (Dvd.dvd.mul_left hgb v))
  have hne : trim O (egcd O (derivT O w s) s).1 ≠ [] := fun h' ↦
    hunit.ne_zero ((trim_eq_nil_iff M _).mp h')
  rw [coprimeDerivCheck, beq_iff_eq, length_trim M hne, natDegree_eq_zero_of_isUnit hunit]

theorem coprimeDerivCheck_iff {w s : GPoly α} :
    coprimeDerivCheck O w s = true ↔
      IsCoprime (implicitDeriv (toPoly M w) (toPoly M s)) (toPoly M s) :=
  ⟨coprimeDerivCheck_sound M, coprimeDerivCheck_complete M⟩

end GPoly

open Tower in
-- `∫ dx / (x (log² x + 1)) = arctan (log x)`: residues `± 1 / 2i`, constants — test passes
#eval GPoly.residueCheck ops₁ [invX] [invX] [ops₁.one, ops₁.zero, ops₁.one]
open Tower in
-- `∫ dx / log x`: residue `x`, not a constant — test fails
#eval GPoly.residueCheck ops₁ [invX] [ops₁.one] [ops₁.zero, ops₁.one]
open Tower in
-- `∫ dx / (log² x + x)`: test fails
#eval GPoly.residueCheck ops₁ [invX] [ops₁.one]
  [(([0, 1] : GPoly ℚ), ([1] : GPoly ℚ)), ops₁.zero, ops₁.one]
open Tower in
-- `∫ 2 log x / (x (log² x - 2))`: residues `1, 1` at `± √2` — test passes without `√2`
#eval GPoly.residueCheck ops₁ [invX] [ops₁.zero, (([2] : GPoly ℚ), ([0, 1] : GPoly ℚ))]
  [(([-2] : GPoly ℚ), ([1] : GPoly ℚ)), ops₁.zero, ops₁.one]
