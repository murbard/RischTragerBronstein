import RischTragerBronstein.Torsion.TriExData

/-!
# A non-elementary integral decided by a non-torsion certificate at a ramified place

On the genus-`1` curve `Y³ + 3xY − x² − 8x = 0` (over `ℚ(ζ₁₂)`, `c = ζ₁₂³` a square root of `−1`),
the integrand `f = Y (c / (8 (x + 16)) + 1 / (12 (x − 32)))` has, in its `c`-component, residues
`−1` at the ramified place `P = (−16, −4)` (`e = 2`) and `+1` at the unramified place
`P' = (−16, 8)` of the same fibre, and `0, 1, −1` at the three points above `x = 32`. The
residue divisor is not torsion; this is certified by the witness `twZ` (place certificate `PcZ`,
primes `13` and `109`, a failed principality test over `ℚ(ζ₁₂)`), checked in the kernel (`okZ`),
and `not_elementary_of_torsOKP` gives **`not_elementaryZ`**.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.TriEx

/-- The non-torsion witness: the `ζ³`-component (`j₀ = 3`) of the residues, scale `1`. -/
def twZ : TorsWitP QZ :=
  ⟨TZ, PcZ, [1, 1], 1, ⟨3, by decide +kernel⟩, 13, 109, P13, P109, Q13, Q109, PbZ, LmZ⟩

/-- The reductions of `ℚ(ζ₁₂)`. -/
def redZ : (p : ℕ) → Option (RedFns p QZ) :=
  Sup.nfRedAt (M := ([1, 0, -1, 0, 1] : CPoly ℚ)) [1, 0, -1, 0, 1]

/-! The kernel checks, one conjunct at a time (to bound the memory of each). -/

set_option maxRecDepth 200000 in
lemma okInf : certCheck (invB probZ.Fc probZ.k (probZ.k * probZ.n)) probZ.n 0 probZ.inf = true := by
  decide +kernel

set_option maxRecDepth 200000 in
lemma okV : probZ.valid = true := by
  unfold CurveProb.valid
  rw [okInf]
  decide +kernel

set_option maxRecDepth 200000 in
lemma okG : twZ.T.globalCheck = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okPc : twZ.Pc.check twZ.T.Fc twZ.T.n = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okR : torsResCheckP probZ twZ.T twZ.Pc twZ.eL twZ.s twZ.j₀ = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okP : primeOKP redZ twZ.T twZ.Pc twZ.p twZ.Pp twZ.Qp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okQ : primeOKP redZ twZ.T twZ.Pc twZ.q twZ.Pq twZ.Qq = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okN : nonPrincCheckN twZ.T.n ((twZ.Qp.mp * twZ.Qq.mp) * twZ.Pc.cΓ) twZ.Pb twZ.T.I.δL
    twZ.T.I.Bc twZ.T.I.Dc twZ.Pc.αs (twZ.Pc.fcerts twZ.T.n)
    (twZ.Pc.bL twZ.T.n (twZ.Qp.mp * twZ.Qq.mp)) twZ.Lm = true := by decide +kernel

lemma okN' : nonPrincOK twZ.T.n ((twZ.Qp.mp * twZ.Qq.mp) * twZ.Pc.cΓ) twZ.Pb twZ.T.I.δL
    twZ.T.I.Bc twZ.T.I.Dc twZ.Pc.αs (twZ.Pc.fcerts twZ.T.n)
    (twZ.Pc.bL twZ.T.n (twZ.Qp.mp * twZ.Qq.mp)) twZ.Lm = true := by
  unfold nonPrincOK
  rw [okN, Bool.true_or]

lemma okZ : torsOKP redZ probZ twZ = true := by
  unfold torsOKP
  rw [okV, okG, okPc, okR, okP, okQ, okN']
  decide

lemma hredZ : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p QZ), redZ p = some R →
    ∃ φ : QZ →+* ℚ_[p], RedValid p R φ := fun p _ R h ↦
  Sup.nfRedAt_valid [1, 0, -1, 0, 1] (by simp [toPoly]) p R h

lemma zA0 : z (4/3) 0 0 (-4) = (4 : ℕ) / (3 : ℕ) - (4 : ℕ) * z 0 0 0 1 := by decide +kernel
lemma zA1 : z (1/12) 0 0 (1/8) = 1 / (12 : ℕ) + z 0 0 0 1 / (8 : ℕ) := by decide +kernel
lemma z0 : z 0 0 0 0 = 0 := by decide +kernel
lemma z1 : z 1 0 0 0 = 1 := by decide +kernel
lemma zm16 : z (-16) 0 0 0 = -((16 : ℕ) : QZ) := by decide +kernel
lemma zm512 : z (-512) 0 0 0 = -((512 : ℕ) : QZ) := by decide +kernel
lemma zi : z 0 0 0 1 * z 0 0 0 1 = -1 := by decide +kernel

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- The embedding `ℚ(ζ₁₂) → Kc`. -/
noncomputable def ιZ : QZ →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := QZ) (M := Kc)).toRingHom

/-- The image of `ζ₁₂³`, a square root of `−1`. -/
lemma ιZ_i_sq : ιZ (Kc := Kc) (z 0 0 0 1) ^ 2 = -1 := by
  rw [sq, ← map_mul, zi, map_neg, map_one]

/-- **A non-elementary integral with residues at a ramified place.** On any curve
`Y³ + 3xY − x² − 8x = 0` over an algebraically closed field of constants containing `c`
(`c² = −1`, the image of `ζ₁₂³`), `∫ Y ((4/3 − 4c) + (1/12 + c/8) x) / (x² − 16x − 512) dx`
`= ∫ Y (c / (8 (x + 16)) + 1 / (12 (x − 32))) dx` has no elementary antiderivative. -/
theorem not_elementaryZ (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ w : E, w ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probZ.Fc).map (mapRingHom (ιZ (Kc := Kc)))) :
    ¬ HasElementaryIntegral (S.y * ((4 / 3 - 4 * algebraMap Kc E (ιZ (z 0 0 0 1))) +
      (1 / 12 + algebraMap Kc E (ιZ (z 0 0 0 1)) / 8) * S.x) / (S.x ^ 2 - 16 * S.x - 512)) := by
  have := not_elementary_of_torsOKP hC S hx hgen redZ hredZ probZ ιZ hSF twZ okZ
  convert this using 2
  simp only [CurveData.fE, CurveData.evXY, probZ, toB, CPoly.toPoly]
  rw [zA0, zA1, zm512, zm16, z1]
  have hn : ∀ m : ℕ, ιZ (Kc := Kc) ((m : ℕ) : QZ) = m := fun m ↦ map_natCast _ m
  have h3 : ιZ (Kc := Kc) (3 : QZ) = 3 := by exact_mod_cast hn 3
  have h4 : ιZ (Kc := Kc) (4 : QZ) = 4 := by exact_mod_cast hn 4
  have h8 : ιZ (Kc := Kc) (8 : QZ) = 8 := by exact_mod_cast hn 8
  have h12 : ιZ (Kc := Kc) (12 : QZ) = 12 := by exact_mod_cast hn 12
  have h16 : ιZ (Kc := Kc) (16 : QZ) = 16 := by exact_mod_cast hn 16
  have h512 : ιZ (Kc := Kc) (512 : QZ) = 512 := by exact_mod_cast hn 512
  simp [h3, h4, h8, h12, h16, h512]
  rw [show (algebraMap Kc E) 3 = 3 from map_ofNat _ 3, show (algebraMap Kc E) 4 = 4 from map_ofNat _ 4,
    show (algebraMap Kc E) 8 = 8 from map_ofNat _ 8, show (algebraMap Kc E) 12 = 12 from map_ofNat _ 12,
    show (algebraMap Kc E) 16 = 16 from map_ofNat _ 16,
    show (algebraMap Kc E) 512 = 512 from map_ofNat _ 512]
  ring

end Curves.TriEx
