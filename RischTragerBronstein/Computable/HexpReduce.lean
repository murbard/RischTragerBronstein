import RischTragerBronstein.Computable.HexpBase

/-!
# The reduction of an element of `R(x)(t)`, `t′ = η t` with `η ∈ R(x)` arbitrary

`hexpReduce Hn Hd Gn Gd`: `expSplit`, Hermite reduction and Euclidean division for the
hyperexponential `t′ = (Hn / Hd) t` — the analogue of `expReduce`, with the same output type
`ExpRed`. `hexpReduce_spec` is the reduction identity.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- `expSplit`, Hermite reduction, Euclidean division, for `t′ = (Hn / Hd) t`. -/
def hexpReduce (Hn Hd : CPoly R) (Gn Gd : GPoly (GFrac R)) : ExpRed R :=
  let sp := GPoly.expSplit (ops₁g R) Gn Gd
  let h := GPoly.hermite (ops₁g R) (hexpW Hn Hd) sp.1 sp.2.2.2
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  let Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1
  ⟨h.gn, h.gd, Λ, sp.2.2.1, qr.2, h.s⟩

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

set_option maxHeartbeats 800000 in
/-- **The reduction identity.** -/
theorem hexpReduce_spec (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) (Hn Hd : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gd ≠ 0) :
    φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gn) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gd) =
      (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).gn) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).gd))′ +
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).Λ) /
          φ₂ X ^ (hexpReduce Hn Hd Gn Gd).k +
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).r) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).s) ∧
    Squarefree (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).s) ∧
    ¬X ∣ GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).s ∧
    (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).r).degree <
      (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpReduce Hn Hd Gn Gd).s).degree := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hW : GPoly.toPoly M₁ (hexpW Hn Hd) = C (ηh ι Hn Hd) * X := toPoly_hexpW_In ι h0 hD Hn Hd
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ (hexpW Hn Hd)) P := fun P ↦ by
    rw [hW]; exact hD₂ P
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M₁ Gn Gd hGd
  simp only [hexpReduce]
  generalize GPoly.expSplit (ops₁g R) Gn Gd = sp at hsp1 hsp2 hsp3 ⊢
  have hd₁0 : GPoly.toPoly M₁ sp.2.2.2 ≠ 0 := fun h ↦ hGd (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : K₁[X], Irreducible p → p ∣ GPoly.toPoly M₁ sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₁ (hexpW Hn Hd)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special (ηh ι Hn Hd) hD₂ hconst hp (by rw [hDW]; exact hsp')).trans hpd)
  have hchk := GPoly.hermiteCheck_hermite M₁ (hexpW Hn Hd) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ (hexpW Hn Hd) sp.1 sp.2.2.2 _ hDW hchk
  have hsdvd := GPoly.hermite_s_dvd M₁ (hexpW Hn Hd) sp.1 sp.2.2.2 hd₁0
  generalize GPoly.hermite (ops₁g R) (hexpW Hn Hd) sp.1 sp.2.2.2 = h at hchk hid hsq hsdvd ⊢
  have hS0 : GPoly.toPoly M₁ h.s ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ GPoly.toPoly M₁ h.s := fun hX ↦ hsp3 (hX.trans hsdvd)
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₁ h.b h.s hS0
  generalize GPoly.divMod (ops₁g R) h.b h.s = qr at hdm hdeglt ⊢
  refine ⟨?_, hsq, hXS, hdeglt⟩
  have hΛpoly : GPoly.toPoly M₁ (GPoly.add (ops₁g R)
      (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1) =
      GPoly.toPoly M₁ qr.1 * X ^ sp.2.2.1 + GPoly.toPoly M₁ sp.2.1 := by
    rw [GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M₁.sem_one, C_1, one_mul]
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
  have hXk : φ₂ (X : K₁[X]) ^ sp.2.2.1 ≠ 0 := pow_ne_zero _ hX0
  have hφS : φ₂ (GPoly.toPoly M₁ h.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hS0
  have hφd₁ : φ₂ (GPoly.toPoly M₁ sp.2.2.2) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hd₁0
  have hAD : φ₂ (GPoly.toPoly M₁ Gn) / φ₂ (GPoly.toPoly M₁ Gd) =
      φ₂ (GPoly.toPoly M₁ sp.1) / φ₂ (GPoly.toPoly M₁ sp.2.2.2) +
        φ₂ (GPoly.toPoly M₁ sp.2.1) / φ₂ X ^ sp.2.2.1 := by
    rw [← hsp1, hsp2, map_add, map_mul, map_mul, map_mul, map_pow]
    field_simp
  rw [hAD, hid, hdm, hΛpoly]
  simp only [map_add, map_mul, map_pow]
  field_simp
  ring

end Tower
