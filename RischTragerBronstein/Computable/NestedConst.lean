import RischTragerBronstein.Computable.ConstQuot
import RischTragerBronstein.Computable.Prim2StepW
import RischTragerBronstein.Liouville.ResidueTestAffine

/-!
# The constant of Liouville's theorem at a non-elementary nested primitive

`t₂′ = W ∈ R(x)(t₁)` where the simple part of `W` fails the residue test (`li x`-type). If
`ρ - c W` has a Liouville form over `S(x)(t₁)` for a constant `c` of some extension `S ⊇ R`, then
`c` is determined by `ρ` and `W`: the residue test is affine in `c`
(`dvd_residueTest_affine`), and `Tower.nestedConst` computes it — in particular `c ∈ R`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

/-- Code of the residue-test polynomial `T(r, s) = r^κ ∂s - ∂r s^κ`. -/
def residueTestCode (O : COps α) (r s : GPoly α) : GPoly α :=
  sub O (mul O (mapD O r) (derivX O s)) (mul O (derivX O r) (mapD O s))

lemma toPoly_residueTestCode {O : COps α} (M : CField α K O) (r s : GPoly α) :
    toPoly M (residueTestCode O r s) = residueTest (toPoly M r) (toPoly M s) := by
  rw [residueTestCode, residueTest, toPoly_sub, toPoly_mul, toPoly_mul, toPoly_mapD, toPoly_mapD,
    toPoly_derivX, toPoly_derivX]

end GPoly

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The constant `c` for which `ρ - c W` can have constant residues. -/
def nestedConst (En₁ Ed₁ : CPoly R) (ρ W : GFrac (GFrac R)) : Option R :=
  let hρ := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] ρ.1 ρ.2
  let rρ := (GPoly.divMod (ops₁g R) hρ.b hρ.s).2
  let hW := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2
  let rW := (GPoly.divMod (ops₁g R) hW.b hW.s).2
  let g := GPoly.gcd (ops₁g R) hρ.s hW.s
  let m := GPoly.div (ops₁g R) hρ.s g
  let wq := GPoly.div (ops₁g R) hW.s g
  let r₁ := (GPoly.solveBezout (ops₁g R)
    (GPoly.mul (ops₁g R) (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] hW.s) m) hW.s
    (GPoly.mul (ops₁g R) rρ wq)).1
  let rWs := GPoly.residuePoly (ops₁g R) [(En₁, Ed₁)] rW hW.s
  constQuot (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R) r₁ hW.s) hW.s).2
    (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R) rWs hW.s) hW.s).2

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

set_option maxHeartbeats 3200000 in
theorem nestedConst_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ : CPoly R}
    (M : ModelW (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁) (ρ W : GFrac (GFrac R))
    (hρ0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) ρ.2 ≠ 0)
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) W.2 ≠ 0)
    (hresW : GPoly.residueCheck (ops₁g R) [(En₁, Ed₁)]
      (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s = false)
    (c : S) {κ : Type*} (Sx : Finset κ) (cs : κ → K₁) (hcs : ∀ i ∈ Sx, (cs i)′ = 0)
    (u : κ → K₂) (hu : ∀ i ∈ Sx, u i ≠ 0) (v : K₂)
    (h : (M.cf ι h0).sem ρ - φ₂ (C (φ (C c))) * (M.cf ι h0).sem W =
      ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) + v′) :
    ∃ c', nestedConst En₁ Ed₁ ρ W = some c' ∧ ι c' = c := by
  set M₁ := M₁In (K₁ := K₁) ι h0 M.hD with hM₁
  have hWη : GPoly.toPoly M₁ [(En₁, Ed₁)] = C (CPoly.ev K₁ ι (En₁, Ed₁)) := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, sem_M₁In]
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) P := fun P ↦ by
    rw [hWη]; exact M.hD₂ P
  have hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive (CPoly.ev K₁ ι (En₁, Ed₁)) M.hD₂ M.hconst₂ hp
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφ : ∀ {P : K₁[X]}, P ≠ 0 → φ₂ P ≠ 0 := fun hP ↦ (map_ne_zero_iff _ hinj₂).mpr hP
  -- Hermite reduction of `ρ` and `W`
  have hchkρ := GPoly.hermiteCheck_hermite M₁ [(En₁, Ed₁)] ρ.1 ρ.2
    (fun p hp _ hdvd ↦ hnorm p hp (by rw [hDW]; exact hdvd)) hρ0
  obtain ⟨hidρ, hsqρ⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ [(En₁, Ed₁)] ρ.1 ρ.2 _ hDW hchkρ
  have hchkW := GPoly.hermiteCheck_hermite M₁ [(En₁, Ed₁)] W.1 W.2
    (fun p hp _ hdvd ↦ hnorm p hp (by rw [hDW]; exact hdvd)) hW0
  obtain ⟨hidW, hsqW⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ [(En₁, Ed₁)] W.1 W.2 _ hDW hchkW
  unfold nestedConst
  simp only
  generalize GPoly.hermite (ops₁g R) [(En₁, Ed₁)] ρ.1 ρ.2 = hρ at hidρ hsqρ ⊢
  generalize GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2 = hW at hidW hsqW hresW ⊢
  set Sρ := GPoly.toPoly M₁ hρ.s with hSρ
  set SW := GPoly.toPoly M₁ hW.s with hSW
  have hSρ0 : Sρ ≠ 0 := hsqρ.ne_zero
  have hSW0 : SW ≠ 0 := hsqW.ne_zero
  have hdmρ := GPoly.divMod_spec M₁ hρ.b hρ.s
  have hdmW := GPoly.divMod_spec M₁ hW.b hW.s
  generalize GPoly.divMod (ops₁g R) hρ.b hρ.s = qrρ at hdmρ ⊢
  generalize GPoly.divMod (ops₁g R) hW.b hW.s = qrW at hdmW hresW ⊢
  -- the gcd of the two denominators
  obtain ⟨hGρ, hGW⟩ := GPoly.egcd_dvd M₁ hρ.s hW.s
  have hGuniv : ∀ p : K₁[X], p ∣ Sρ → p ∣ SW → p ∣ GPoly.toPoly M₁ (GPoly.gcd (ops₁g R) hρ.s hW.s) :=
    fun p h1 h2 ↦ by rw [GPoly.toPoly_gcd]; exact GPoly.dvd_egcd M₁ hρ.s hW.s h1 h2
  rw [← GPoly.toPoly_gcd] at hGρ hGW
  generalize GPoly.gcd (ops₁g R) hρ.s hW.s = g at hGρ hGW hGuniv ⊢
  set G := GPoly.toPoly M₁ g with hG
  have hG0 : G ≠ 0 := fun h0' ↦ hSρ0 (by
    obtain ⟨a, ha⟩ := hGρ
    rw [hSρ, ha, h0', zero_mul])
  have hm : Sρ = GPoly.toPoly M₁ (GPoly.div (ops₁g R) hρ.s g) * G := by
    have := GPoly.divMod_spec M₁ hρ.s g
    rw [GPoly.divMod_exact M₁ hρ.s g hG0 hGρ, add_zero] at this
    exact this
  have hw : SW = GPoly.toPoly M₁ (GPoly.div (ops₁g R) hW.s g) * G := by
    have := GPoly.divMod_spec M₁ hW.s g
    rw [GPoly.divMod_exact M₁ hW.s g hG0 hGW, add_zero] at this
    exact this
  generalize GPoly.div (ops₁g R) hρ.s g = m at hm ⊢
  generalize GPoly.div (ops₁g R) hW.s g = wq at hw ⊢
  set Mm := GPoly.toPoly M₁ m with hMm
  set Wq := GPoly.toPoly M₁ wq with hWq
  have hMm0 : Mm ≠ 0 := fun h0' ↦ hSρ0 (by rw [hm, h0', zero_mul])
  have hmcop : ∀ p : K₁[X], Irreducible p → p ∣ SW → ¬p ∣ Mm := fun p hp hpS hpM ↦ by
    have hpρ : p ∣ Sρ := by rw [hm]; exact hpM.mul_right G
    have hpG : p ∣ G := hGuniv p hpρ hpS
    have : p * p ∣ Sρ := by rw [hm]; exact mul_dvd_mul hpM hpG
    exact hp.not_isUnit (hsqρ p this)
  -- the residue polynomials
  have hcopS : IsCoprime (SW′) SW := isCoprime_deriv_of_squarefree hsqW fun p hp _ ↦ hnorm p hp
  have hcopM : IsCoprime Mm SW :=
    isCoprime_of_irreducible_dvd (fun h' ↦ hSW0 h'.2) fun p hp h1 h2 ↦ hmcop p hp h2 h1
  have ha : GPoly.toPoly M₁ (GPoly.mul (ops₁g R)
      (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] hW.s) m) = SW′ * Mm := by
    rw [GPoly.toPoly_mul, GPoly.toPoly_derivT, ← hDW]
  have hbez := GPoly.solveBezout_spec M₁ (GPoly.mul (ops₁g R)
    (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] hW.s) m) hW.s (GPoly.mul (ops₁g R) qrρ.2 wq) hSW0
    (by rw [ha]; exact hcopS.mul_left hcopM)
  rw [ha, GPoly.toPoly_mul] at hbez
  generalize GPoly.solveBezout (ops₁g R) (GPoly.mul (ops₁g R)
    (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] hW.s) m) hW.s (GPoly.mul (ops₁g R) qrρ.2 wq) = sol
    at hbez ⊢
  have hr₁ : SW ∣ GPoly.toPoly M₁ sol.1 * (SW′ * Mm) - GPoly.toPoly M₁ qrρ.2 * Wq :=
    ⟨-GPoly.toPoly M₁ sol.2, by linear_combination hbez⟩
  have hcopS' : IsCoprime (implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) SW) SW := by
    rw [← hDW]; exact hcopS
  have hrWs := GPoly.residuePoly_spec M₁ [(En₁, Ed₁)] qrW.2 hW.s hSW0 hcopS'
  rw [← hDW] at hrWs
  -- the Liouville identity over the denominator `SW * Mm`
  set ct : K₁ := φ (C c) with hct
  have hct' : ct′ = 0 := by rw [hct, deriv_algebraMap, M.hD, derivative_C, map_zero]
  have hct₂ : (φ₂ (C ct))′ = 0 := by
    rw [deriv_algebraMap, M.hD₂, implicitDeriv_C, hct', C_0, map_zero]
  have e1 : φ₂ (GPoly.toPoly M₁ hρ.b) / φ₂ Sρ = φ₂ (GPoly.toPoly M₁ qrρ.1) +
      φ₂ (GPoly.toPoly M₁ qrρ.2 * Wq) / φ₂ (SW * Mm) := by
    have hprod : Sρ * Wq = SW * Mm := by rw [hm, hw]; ring
    have h1 := hφ hSρ0
    have h2 : φ₂ (SW * Mm) ≠ 0 := hφ (mul_ne_zero hSW0 hMm0)
    rw [hdmρ, map_add, map_mul, add_div, mul_div_assoc, div_self h1, mul_one, ← hprod, map_mul,
      map_mul]
    have h3 : φ₂ Wq ≠ 0 := hφ fun h0' ↦ hSW0 (by rw [hw, h0', zero_mul])
    field_simp
  have e2 : φ₂ (GPoly.toPoly M₁ hW.b) / φ₂ SW = φ₂ (GPoly.toPoly M₁ qrW.1) +
      φ₂ (GPoly.toPoly M₁ qrW.2 * Mm) / φ₂ (SW * Mm) := by
    have h1 := hφ hSW0
    have h3 := hφ hMm0
    rw [hdmW, map_add, map_mul, add_div, mul_div_assoc, div_self h1, mul_one, map_mul, map_mul]
    field_simp
  have hliou : φ₂ ((GPoly.toPoly M₁ qrρ.1 - C ct * GPoly.toPoly M₁ qrW.1) * (SW * Mm) +
      (GPoly.toPoly M₁ qrρ.2 * Wq - C ct * GPoly.toPoly M₁ qrW.2 * Mm)) / φ₂ (SW * Mm) =
      ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) +
        (v - φ₂ (GPoly.toPoly M₁ hρ.gn) / φ₂ (GPoly.toPoly M₁ hρ.gd) +
          φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ hW.gn) / φ₂ (GPoly.toPoly M₁ hW.gd)))′ := by
    have h2 : φ₂ (SW * Mm) ≠ 0 := hφ (mul_ne_zero hSW0 hMm0)
    have hsum : ∑ i ∈ Sx, φ₂ (C (cs i)) * logDeriv (u i) =
        (M.cf ι h0).sem ρ - φ₂ (C ct) * (M.cf ι h0).sem W - v′ := by rw [h]; ring
    have hder : (v - φ₂ (GPoly.toPoly M₁ hρ.gn) / φ₂ (GPoly.toPoly M₁ hρ.gd) +
        φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ hW.gn) / φ₂ (GPoly.toPoly M₁ hW.gd)))′ =
        v′ - (φ₂ (GPoly.toPoly M₁ hρ.gn) / φ₂ (GPoly.toPoly M₁ hρ.gd))′ +
          φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ hW.gn) / φ₂ (GPoly.toPoly M₁ hW.gd))′ := by
      rw [map_add, map_sub, Derivation.leibniz, hct₂]
      simp only [smul_eq_mul, mul_zero, add_zero]
    have h4 := hφ hSW0
    have h5 := hφ hMm0
    rw [hsum, sem_M₂W, sem_M₂W, hidρ, hidW, e1, e2, hder, div_eq_iff h2]
    simp only [map_add, map_sub, map_mul]
    field_simp
    ring
  have haff := dvd_residueTest_affine (K := K₂) hct' hsqW (fun p hp _ ↦ hnorm p hp) hmcop hr₁ hrWs
    Sx cs hcs u hu _ hliou
  -- reduce modulo `SW`
  have hd1 := GPoly.divMod_spec M₁ (GPoly.residueTestCode (ops₁g R) sol.1 hW.s) hW.s
  have hl1 := GPoly.divMod_degree_lt M₁ (GPoly.residueTestCode (ops₁g R) sol.1 hW.s) hW.s hSW0
  have hd2 := GPoly.divMod_spec M₁ (GPoly.residueTestCode (ops₁g R)
    (GPoly.residuePoly (ops₁g R) [(En₁, Ed₁)] qrW.2 hW.s) hW.s) hW.s
  have hl2 := GPoly.divMod_degree_lt M₁ (GPoly.residueTestCode (ops₁g R)
    (GPoly.residuePoly (ops₁g R) [(En₁, Ed₁)] qrW.2 hW.s) hW.s) hW.s hSW0
  rw [GPoly.toPoly_residueTestCode] at hd1 hd2
  have htW0 : GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R)
      (GPoly.residuePoly (ops₁g R) [(En₁, Ed₁)] qrW.2 hW.s) hW.s) hW.s).2 ≠ 0 := fun hz ↦ by
    have hdvd : SW ∣ residueTest (GPoly.toPoly M₁
        (GPoly.residuePoly (ops₁g R) [(En₁, Ed₁)] qrW.2 hW.s)) SW := by
      rw [hd2, hz, add_zero]
      exact dvd_mul_left _ _
    have := (GPoly.residueCheck_iff M₁ [(En₁, Ed₁)] qrW.2 hW.s hSW0).mpr hdvd
    rw [hresW] at this
    exact Bool.noConfusion this
  refine constQuot_complete (K₁ := K₁) ι h0 M.hD _ _ c htW0 ?_
  have hdvd : SW ∣ GPoly.toPoly M₁ (GPoly.divMod (ops₁g R)
      (GPoly.residueTestCode (ops₁g R) sol.1 hW.s) hW.s).2 - C ct * GPoly.toPoly M₁
      (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R)
        (GPoly.residuePoly (ops₁g R) [(En₁, Ed₁)] qrW.2 hW.s) hW.s) hW.s).2 := by
    have := haff
    rw [hd1, hd2] at this
    have h3 : ∀ a b t₁ t₂ : K₁[X], a * SW + t₁ - C ct * (b * SW + t₂) =
        (t₁ - C ct * t₂) + SW * (a - C ct * b) := fun a b t₁ t₂ ↦ by ring
    rw [h3] at this
    exact (dvd_add_left (dvd_mul_right _ _)).mp this
  have hdeg : (GPoly.toPoly M₁ (GPoly.divMod (ops₁g R)
      (GPoly.residueTestCode (ops₁g R) sol.1 hW.s) hW.s).2 - C ct * GPoly.toPoly M₁
      (GPoly.divMod (ops₁g R) (GPoly.residueTestCode (ops₁g R)
        (GPoly.residuePoly (ops₁g R) [(En₁, Ed₁)] qrW.2 hW.s) hW.s) hW.s).2).degree <
      SW.degree := by
    refine (degree_sub_le _ _).trans_lt (max_lt hl1 ?_)
    rw [C_mul']
    exact (degree_smul_le _ _).trans_lt hl2
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg)

end Tower
