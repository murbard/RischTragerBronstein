import RischTragerBronstein.Computable.NestedConst
import RischTragerBronstein.Computable.PrimHexpStepW
import RischTragerBronstein.Computable.NestedConstE

/-!
# The nested constant for a primitive over `R(x)(t₁)`, `t₁′ = η t₁` with `η ∈ R(x)` arbitrary

The analogue of `nestedConstH` / `laurent_const_eq_zero_H` over a general hyperexponential base.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- The constant `c` for which `ρ - c W` can have constant residues at `t₁`. -/
def nestedConstH (Hn Hd : CPoly R) (ρ W : GFrac (GFrac R)) : Option R :=
  let eρ := hexpReduce Hn Hd ρ.1 ρ.2
  let eW := hexpReduce Hn Hd W.1 W.2
  let g := GPoly.gcd (ops₁g R) eρ.s eW.s
  let m := GPoly.div (ops₁g R) eρ.s g
  let wq := GPoly.div (ops₁g R) eW.s g
  let r₁ := (GPoly.solveBezout (ops₁g R)
    (GPoly.mul (ops₁g R) (GPoly.derivT (ops₁g R) (hexpW Hn Hd) eW.s) m) eW.s
    (GPoly.mul (ops₁g R) eρ.r wq)).1
  let rWs := GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s
  constQuot (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R) r₁ eW.s) eW.s).2
    (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R) rWs eW.s) eW.s).2

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [DecidableEq S]
variable [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
variable [CPoly.HasRatRoots R] [HasNatTest R]

set_option maxHeartbeats 3200000 in
theorem nestedConstH_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {Hn Hd μ : CPoly R}
    (M : ModelHW (K₁ := K₁) (K₂ := K₂) ι Hn Hd μ) (ρ W : GFrac (GFrac R))
    (hρ0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) ρ.2 ≠ 0)
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) W.2 ≠ 0)
    (hresW : GPoly.residueCheck (ops₁g R) (hexpW Hn Hd) (hexpReduce Hn Hd W.1 W.2).r
      (hexpReduce Hn Hd W.1 W.2).s = false)
    (c : S) {κ : Type*} (Sx : Finset κ) (cs : κ → K₁) (hcs : ∀ i ∈ Sx, (cs i)′ = 0)
    (u : κ → K₂) (hu : ∀ i ∈ Sx, u i ≠ 0) (v : K₂)
    (h : (M.cf ι h0).sem ρ - φ₂ (C (φ (C c))) * (M.cf ι h0).sem W =
      ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) + v′) :
    ∃ c', nestedConstH Hn Hd ρ W = some c' ∧ ι c' = c := by
  set M₁ := M₁In (K₁ := K₁) ι h0 M.hD with hM₁
  have hWη : GPoly.toPoly M₁ (hexpW Hn Hd) = C (ηh ι Hn Hd) * X := toPoly_hexpW_In ι h0 M.hD Hn Hd
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ (hexpW Hn Hd)) P := fun P ↦ by
    rw [hWη]; exact M.hD₂ P
  have hnorm' := normal_of_hconst (ηh ι Hn Hd) M.hD₂ M.hconst
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφ : ∀ {P : K₁[X]}, P ≠ 0 → φ₂ P ≠ 0 := fun hP ↦ (map_ne_zero_iff _ hinj₂).mpr hP
  -- reduction of `ρ` and `W`
  obtain ⟨hidρ, hsqρ, hXρ, -⟩ := hexpReduce_spec (K₂ := K₂) ι h0 M.hD Hn Hd M.hD₂ M.hconst ρ.1 ρ.2 hρ0
  obtain ⟨hidW, hsqW, hXW, -⟩ := hexpReduce_spec (K₂ := K₂) ι h0 M.hD Hn Hd M.hD₂ M.hconst W.1 W.2 hW0
  unfold nestedConstH
  simp only
  generalize hexpReduce Hn Hd ρ.1 ρ.2 = eρ at hidρ hsqρ hXρ ⊢
  generalize hexpReduce Hn Hd W.1 W.2 = eW at hidW hsqW hXW hresW ⊢
  set Sρ := GPoly.toPoly M₁ eρ.s with hSρ
  set SW := GPoly.toPoly M₁ eW.s with hSW
  have hSρ0 : Sρ ≠ 0 := hsqρ.ne_zero
  have hSW0 : SW ≠ 0 := hsqW.ne_zero
  -- normality of the primes of `SW` (they are not `X`)
  have hnormW : ∀ p : K₁[X], Irreducible p → p ∣ SW → ¬p ∣ p′ := fun p hp hpS hpd ↦
    hXW ((dvd_X_of_irreducible_special (ηh ι Hn Hd) M.hD₂ M.hconst hp hpd).trans hpS)
  -- the gcd of the two denominators
  obtain ⟨hGρ, hGW⟩ := GPoly.egcd_dvd M₁ eρ.s eW.s
  have hGuniv : ∀ p : K₁[X], p ∣ Sρ → p ∣ SW → p ∣ GPoly.toPoly M₁ (GPoly.gcd (ops₁g R) eρ.s eW.s) :=
    fun p h1 h2 ↦ by rw [GPoly.toPoly_gcd]; exact GPoly.dvd_egcd M₁ eρ.s eW.s h1 h2
  rw [← GPoly.toPoly_gcd] at hGρ hGW
  generalize GPoly.gcd (ops₁g R) eρ.s eW.s = g at hGρ hGW hGuniv ⊢
  set G := GPoly.toPoly M₁ g with hG
  have hG0 : G ≠ 0 := fun h0' ↦ hSρ0 (by
    obtain ⟨a, ha⟩ := hGρ
    rw [hSρ, ha, h0', zero_mul])
  have hm : Sρ = GPoly.toPoly M₁ (GPoly.div (ops₁g R) eρ.s g) * G := by
    have := GPoly.divMod_spec M₁ eρ.s g
    rw [GPoly.divMod_exact M₁ eρ.s g hG0 hGρ, add_zero] at this
    exact this
  have hw : SW = GPoly.toPoly M₁ (GPoly.div (ops₁g R) eW.s g) * G := by
    have := GPoly.divMod_spec M₁ eW.s g
    rw [GPoly.divMod_exact M₁ eW.s g hG0 hGW, add_zero] at this
    exact this
  generalize GPoly.div (ops₁g R) eρ.s g = m at hm ⊢
  generalize GPoly.div (ops₁g R) eW.s g = wq at hw ⊢
  set Mm := GPoly.toPoly M₁ m with hMm
  set Wq := GPoly.toPoly M₁ wq with hWq
  have hMm0 : Mm ≠ 0 := fun h0' ↦ hSρ0 (by rw [hm, h0', zero_mul])
  have hWq0 : Wq ≠ 0 := fun h0' ↦ hSW0 (by rw [hw, h0', zero_mul])
  have hmcop : ∀ p : K₁[X], Irreducible p → p ∣ SW → ¬p ∣ Mm := fun p hp hpS hpM ↦ by
    have hpρ : p ∣ Sρ := by rw [hm]; exact hpM.mul_right G
    have hpG : p ∣ G := hGuniv p hpρ hpS
    have : p * p ∣ Sρ := by rw [hm]; exact mul_dvd_mul hpM hpG
    exact hp.not_isUnit (hsqρ p this)
  -- the Laurent cofactor `X ^ K`
  set K := eρ.k + eW.k with hK
  have hXcop : ∀ p : K₁[X], Irreducible p → p ∣ SW → ¬p ∣ X ^ K := fun p hp hpS hpX ↦ by
    have hpX' : p ∣ X := hp.prime.dvd_of_dvd_pow hpX
    have hXp : X ∣ p := hp.dvd_symm irreducible_X hpX'
    exact hXW (hXp.trans hpS)
  have hmXcop : ∀ p : K₁[X], Irreducible p → p ∣ SW → ¬p ∣ Mm * X ^ K := fun p hp hpS hpd ↦
    (hp.prime.dvd_or_dvd hpd).elim (hmcop p hp hpS) (hXcop p hp hpS)
  -- the residue polynomials
  have hcopS : IsCoprime (SW′) SW := isCoprime_deriv_of_squarefree hsqW hnormW
  have hcopM : IsCoprime Mm SW :=
    isCoprime_of_irreducible_dvd (fun h' ↦ hSW0 h'.2) fun p hp h1 h2 ↦ hmcop p hp h2 h1
  have ha : GPoly.toPoly M₁ (GPoly.mul (ops₁g R)
      (GPoly.derivT (ops₁g R) (hexpW Hn Hd) eW.s) m) = SW′ * Mm := by
    rw [GPoly.toPoly_mul, GPoly.toPoly_derivT, ← hDW]
  have hbez := GPoly.solveBezout_spec M₁ (GPoly.mul (ops₁g R)
    (GPoly.derivT (ops₁g R) (hexpW Hn Hd) eW.s) m) eW.s (GPoly.mul (ops₁g R) eρ.r wq) hSW0
    (by rw [ha]; exact hcopS.mul_left hcopM)
  rw [ha, GPoly.toPoly_mul] at hbez
  generalize GPoly.solveBezout (ops₁g R) (GPoly.mul (ops₁g R)
    (GPoly.derivT (ops₁g R) (hexpW Hn Hd) eW.s) m) eW.s (GPoly.mul (ops₁g R) eρ.r wq) = sol
    at hbez ⊢
  have hr₁ : SW ∣ GPoly.toPoly M₁ sol.1 * (SW′ * Mm) - GPoly.toPoly M₁ eρ.r * Wq :=
    ⟨-GPoly.toPoly M₁ sol.2, by linear_combination hbez⟩
  have hcopS' : IsCoprime (implicitDeriv (GPoly.toPoly M₁ (hexpW Hn Hd)) SW) SW := by
    rw [← hDW]; exact hcopS
  have hrWs := GPoly.residuePoly_spec M₁ (hexpW Hn Hd) eW.r eW.s hSW0 hcopS'
  rw [← hDW] at hrWs
  -- the Liouville identity over the denominator `SW * (Mm * X ^ K)`
  set ct : K₁ := φ (C c) with hct
  have hct' : ct′ = 0 := by rw [hct, deriv_algebraMap, M.hD, derivative_C, map_zero]
  have hct₂ : (φ₂ (C ct))′ = 0 := by
    rw [deriv_algebraMap, M.hD₂, implicitDeriv_C, hct', C_0, map_zero]
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := hφ X_ne_zero
  set B : K₁[X] := (GPoly.toPoly M₁ eρ.Λ * X ^ eW.k - C ct * (GPoly.toPoly M₁ eW.Λ * X ^ eρ.k)) *
    (SW * Mm) + (GPoly.toPoly M₁ eρ.r * Wq * X ^ K - C ct * GPoly.toPoly M₁ eW.r * (Mm * X ^ K))
    with hB
  have hliou : φ₂ B / φ₂ (SW * (Mm * X ^ K)) =
      ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) +
        (v - φ₂ (GPoly.toPoly M₁ eρ.gn) / φ₂ (GPoly.toPoly M₁ eρ.gd) +
          φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ eW.gn) / φ₂ (GPoly.toPoly M₁ eW.gd)))′ := by
    have hsum : ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) =
        (M.cf ι h0).sem ρ - φ₂ (C ct) * (M.cf ι h0).sem W - v′ := by rw [h]; ring
    have hder : (v - φ₂ (GPoly.toPoly M₁ eρ.gn) / φ₂ (GPoly.toPoly M₁ eρ.gd) +
        φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ eW.gn) / φ₂ (GPoly.toPoly M₁ eW.gd)))′ =
        v′ - (φ₂ (GPoly.toPoly M₁ eρ.gn) / φ₂ (GPoly.toPoly M₁ eρ.gd))′ +
          φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ eW.gn) / φ₂ (GPoly.toPoly M₁ eW.gd))′ := by
      rw [map_add, map_sub, Derivation.leibniz, hct₂]
      simp only [smul_eq_mul, mul_zero, add_zero]
    have h4 := hφ hSW0
    have h5 := hφ hMm0
    have h6 := hφ hWq0
    have h7 := hφ hG0
    have hSρ' : φ₂ Sρ = φ₂ Mm * φ₂ G := by rw [hm, map_mul]
    have hSW' : φ₂ SW = φ₂ Wq * φ₂ G := by rw [hw, map_mul]
    rw [hsum, ModelHW.cf, sem_M₂H, sem_M₂H, hidρ, hidW, hder, hB, hK]
    simp only [map_add, map_sub, map_mul, map_pow]
    rw [hSρ', hSW']
    field_simp
    ring
  -- necessity of the residue test for `r₁ - c r_W*`
  have hB' : SW ∣ B - (GPoly.toPoly M₁ sol.1 * SW′ - C ct * GPoly.toPoly M₁ eW.r) * (Mm * X ^ K) := by
    have e : B - (GPoly.toPoly M₁ sol.1 * SW′ - C ct * GPoly.toPoly M₁ eW.r) * (Mm * X ^ K) =
        SW * ((GPoly.toPoly M₁ eρ.Λ * X ^ eW.k - C ct * (GPoly.toPoly M₁ eW.Λ * X ^ eρ.k)) * Mm) -
          (GPoly.toPoly M₁ sol.1 * (SW′ * Mm) - GPoly.toPoly M₁ eρ.r * Wq) * X ^ K := by
      rw [hB]; ring
    rw [e]
    exact dvd_sub (dvd_mul_right _ _) (hr₁.mul_right _)
  have hr' : SW ∣ (GPoly.toPoly M₁ sol.1 - C ct * GPoly.toPoly M₁
      (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) * SW′ -
      (GPoly.toPoly M₁ sol.1 * SW′ - C ct * GPoly.toPoly M₁ eW.r) := by
    have e : (GPoly.toPoly M₁ sol.1 - C ct * GPoly.toPoly M₁
        (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) * SW′ -
        (GPoly.toPoly M₁ sol.1 * SW′ - C ct * GPoly.toPoly M₁ eW.r) =
        -(C ct) * (GPoly.toPoly M₁ (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s) * SW′ -
          GPoly.toPoly M₁ eW.r) := by ring
    rw [e]
    exact hrWs.mul_left _
  have haff := dvd_residueTest_mul (K := K₂) hsqW hnormW hmXcop hB' hr' Sx cs hcs u hu _ hliou
  rw [residueTest_sub_C_mul hct'] at haff
  -- reduce modulo `SW`
  have hd1 := GPoly.divMod_spec M₁ (GPoly.residueTestCode (ops₁g R) sol.1 eW.s) eW.s
  have hl1 := GPoly.divMod_degree_lt M₁ (GPoly.residueTestCode (ops₁g R) sol.1 eW.s) eW.s hSW0
  have hd2 := GPoly.divMod_spec M₁ (GPoly.residueTestCode (ops₁g R)
    (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s) eW.s) eW.s
  have hl2 := GPoly.divMod_degree_lt M₁ (GPoly.residueTestCode (ops₁g R)
    (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s) eW.s) eW.s hSW0
  rw [GPoly.toPoly_residueTestCode] at hd1 hd2
  have htW0 : GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R)
      (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s) eW.s) eW.s).2 ≠ 0 := fun hz ↦ by
    have hdvd : SW ∣ residueTest (GPoly.toPoly M₁
        (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) SW := by
      rw [hd2, hz, add_zero]
      exact dvd_mul_left _ _
    have := (GPoly.residueCheck_iff M₁ (hexpW Hn Hd) eW.r eW.s hSW0).mpr hdvd
    rw [hresW] at this
    exact Bool.noConfusion this
  refine constQuot_complete (K₁ := K₁) ι h0 M.hD _ _ c htW0 ?_
  have hdvd : SW ∣ GPoly.toPoly M₁ (GPoly.divMod (ops₁g R)
      (GPoly.residueTestCode (ops₁g R) sol.1 eW.s) eW.s).2 - C ct * GPoly.toPoly M₁
      (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R)
        (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s) eW.s) eW.s).2 := by
    have := haff
    rw [hd1, hd2] at this
    have h3 : ∀ a b t₁ t₂ : K₁[X], a * SW + t₁ - C ct * (b * SW + t₂) =
        (t₁ - C ct * t₂) + SW * (a - C ct * b) := fun a b t₁ t₂ ↦ by ring
    rw [h3] at this
    exact (dvd_add_left (dvd_mul_right _ _)).mp this
  have hdeg : (GPoly.toPoly M₁ (GPoly.divMod (ops₁g R)
      (GPoly.residueTestCode (ops₁g R) sol.1 eW.s) eW.s).2 - C ct * GPoly.toPoly M₁
      (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R)
        (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s) eW.s) eW.s).2).degree <
      SW.degree := by
    refine (degree_sub_le _ _).trans_lt (max_lt hl1 ?_)
    rw [C_mul']
    exact (degree_smul_le _ _).trans_lt hl2
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg)

set_option maxHeartbeats 3200000 in
/-- **A Laurent polynomial minus `c W` has a Liouville form only for `c = 0`** when the proper part
of `W` fails the residue test. -/
theorem laurent_const_eq_zero_H (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {Hn Hd μ : CPoly R}
    (M : ModelHW (K₁ := K₁) (K₂ := K₂) ι Hn Hd μ) (W : GFrac (GFrac R))
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) W.2 ≠ 0)
    (hresW : GPoly.residueCheck (ops₁g R) (hexpW Hn Hd) (hexpReduce Hn Hd W.1 W.2).r
      (hexpReduce Hn Hd W.1 W.2).s = false)
    (P : K₁[X]) (n : ℕ) (c : S) {κ : Type*} (Sx : Finset κ) (cs : κ → K₁)
    (hcs : ∀ i ∈ Sx, (cs i)′ = 0) (u : κ → K₂) (hu : ∀ i ∈ Sx, u i ≠ 0) (v : K₂)
    (h : φ₂ P / φ₂ X ^ n - φ₂ (C (φ (C c))) * (M.cf ι h0).sem W =
      ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) + v′) :
    c = 0 := by
  set M₁ := M₁In (K₁ := K₁) ι h0 M.hD with hM₁
  have hWη : GPoly.toPoly M₁ (hexpW Hn Hd) = C (ηh ι Hn Hd) * X := toPoly_hexpW_In ι h0 M.hD Hn Hd
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ (hexpW Hn Hd)) P := fun P ↦ by
    rw [hWη]; exact M.hD₂ P
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hinj₁ : Function.Injective φ := IsFractionRing.injective S[X] K₁
  have hφ : ∀ {P : K₁[X]}, P ≠ 0 → φ₂ P ≠ 0 := fun hP ↦ (map_ne_zero_iff _ hinj₂).mpr hP
  obtain ⟨hidW, hsqW, hXW, -⟩ := hexpReduce_spec (K₂ := K₂) ι h0 M.hD Hn Hd M.hD₂ M.hconst W.1 W.2 hW0
  generalize hexpReduce Hn Hd W.1 W.2 = eW at hidW hsqW hXW hresW
  set SW := GPoly.toPoly M₁ eW.s with hSW
  have hSW0 : SW ≠ 0 := hsqW.ne_zero
  have hnormW : ∀ p : K₁[X], Irreducible p → p ∣ SW → ¬p ∣ p′ := fun p hp hpS hpd ↦
    hXW ((dvd_X_of_irreducible_special (ηh ι Hn Hd) M.hD₂ M.hconst hp hpd).trans hpS)
  set K := n + eW.k with hK
  have hXcop : ∀ p : K₁[X], Irreducible p → p ∣ SW → ¬p ∣ X ^ K := fun p hp hpS hpX ↦ by
    have hpX' : p ∣ X := hp.prime.dvd_of_dvd_pow hpX
    have hXp : X ∣ p := hp.dvd_symm irreducible_X hpX'
    exact hXW (hXp.trans hpS)
  have hcopS : IsCoprime (SW′) SW := isCoprime_deriv_of_squarefree hsqW hnormW
  have hcopS' : IsCoprime (implicitDeriv (GPoly.toPoly M₁ (hexpW Hn Hd)) SW) SW := by
    rw [← hDW]; exact hcopS
  have hrWs := GPoly.residuePoly_spec M₁ (hexpW Hn Hd) eW.r eW.s hSW0 hcopS'
  rw [← hDW] at hrWs
  set ct : K₁ := φ (C c) with hct
  have hct' : ct′ = 0 := by rw [hct, deriv_algebraMap, M.hD, derivative_C, map_zero]
  have hct₂ : (φ₂ (C ct))′ = 0 := by
    rw [deriv_algebraMap, M.hD₂, implicitDeriv_C, hct', C_0, map_zero]
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := hφ X_ne_zero
  set B : K₁[X] := (P * X ^ eW.k - C ct * (GPoly.toPoly M₁ eW.Λ * X ^ n)) * SW -
    C ct * GPoly.toPoly M₁ eW.r * X ^ K with hB
  have hliou : φ₂ B / φ₂ (SW * X ^ K) =
      ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) +
        (v + φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ eW.gn) / φ₂ (GPoly.toPoly M₁ eW.gd)))′ := by
    have hsum : ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) =
        φ₂ P / φ₂ X ^ n - φ₂ (C ct) * (M.cf ι h0).sem W - v′ := by rw [h]; ring
    have hder : (v + φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ eW.gn) / φ₂ (GPoly.toPoly M₁ eW.gd)))′ =
        v′ + φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ eW.gn) / φ₂ (GPoly.toPoly M₁ eW.gd))′ := by
      rw [map_add, Derivation.leibniz, hct₂]
      simp only [smul_eq_mul, mul_zero, add_zero]
    have h4 := hφ hSW0
    rw [hsum, ModelHW.cf, sem_M₂H, hidW, hder, hB, hK]
    simp only [map_add, map_sub, map_mul, map_pow]
    field_simp
    ring
  have hB' : SW ∣ B - (-(C ct) * GPoly.toPoly M₁ eW.r) * X ^ K := by
    have e : B - (-(C ct) * GPoly.toPoly M₁ eW.r) * X ^ K =
        SW * (P * X ^ eW.k - C ct * (GPoly.toPoly M₁ eW.Λ * X ^ n)) := by rw [hB]; ring
    rw [e]
    exact dvd_mul_right _ _
  have hr' : SW ∣ (-(C ct) * GPoly.toPoly M₁ (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) *
      SW′ - (-(C ct) * GPoly.toPoly M₁ eW.r) := by
    have e : (-(C ct) * GPoly.toPoly M₁ (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) *
        SW′ - (-(C ct) * GPoly.toPoly M₁ eW.r) =
        -(C ct) * (GPoly.toPoly M₁ (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s) * SW′ -
          GPoly.toPoly M₁ eW.r) := by ring
    rw [e]
    exact hrWs.mul_left _
  have haff := dvd_residueTest_mul (K := K₂) hsqW hnormW hXcop hB' hr' Sx cs hcs u hu _ hliou
  have hT0 : residueTest (0 : K₁[X]) SW = 0 := by simp [residueTest]
  have hT : residueTest (-(C ct) * GPoly.toPoly M₁ (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s))
      SW = -(C ct) * residueTest (GPoly.toPoly M₁
        (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) SW := by
    have := residueTest_sub_C_mul hct' 0
      (GPoly.toPoly M₁ (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) SW
    rw [zero_sub, hT0, zero_sub] at this
    rw [neg_mul, this, neg_mul]
  rw [hT] at haff
  by_contra hne
  have hct0 : ct ≠ 0 := by
    rw [hct, Ne, map_eq_zero_iff φ hinj₁, C_eq_zero]
    exact hne
  have hunit : IsUnit (-(C ct)) := (isUnit_C.mpr hct0.isUnit).neg
  have hdvd : SW ∣ residueTest (GPoly.toPoly M₁
      (GPoly.residuePoly (ops₁g R) (hexpW Hn Hd) eW.r eW.s)) SW :=
    (hunit.dvd_mul_left).mp haff
  have := (GPoly.residueCheck_iff M₁ (hexpW Hn Hd) eW.r eW.s hSW0).mpr hdvd
  rw [hresW] at this
  exact Bool.noConfusion this

end Tower
