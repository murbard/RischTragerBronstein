import RischTragerBronstein.Mixed.GeomIrrMob

/-!
# Example: geometric irreducibility by the subset certificate

`Y⁴ − (x² + 3) Y² + x²` has no single place above any rational point or infinity (above `x = 0`
the roots are `0, 0, ±√3`; `deg a₀ = 2` is not prime to `4`) and is not Eisenstein, but it is
geometrically irreducible: at the split point `x = 1` (roots `±(√6 ± √2)/2` in `ℚ(√2, √3)`), no
product of one or two branch factors has polynomial coefficients of degree `≤ 2`
(`irrSubsetCheck`), so `geomIrr_of_subsets` applies.
-/

namespace Curves.MT.GeomIrrSubEx

open Curves Curves.MT CPoly Sup Polynomial

/-- `ℚ(√2 + √3)`. -/
def MM : CPoly ℚ := [1, 0, -10, 0, 1]

theorem hMM : Kron.irredQ MM = true := by decide +kernel

instance : Fact (Irreducible (toPoly MM)) := ⟨Kron.irredQ_sound MM hMM⟩

abbrev KK := NFC.NF MM

/-- `Y⁴ − (x² + 3) Y² + x²`. -/
def Fq : BPoly ℚ := [[0, 0, 1], [], [-3, 0, -1], [], [1]]

/-- The branches above `x = 1`. -/
def bc : BranchCert KK := ⟨1, [[(NFC.mk MM [(-5/4), (9/4), (1/4), (-1/4)]), (NFC.mk MM [(-5/12), 0, (1/12)]), (NFC.mk MM [(-5/144), (9/16), (1/144), (-1/16)]), (NFC.mk MM [(5/432), 0, (-1/432)]), (NFC.mk MM [(-35/10368), (-9/128), (7/10368), (1/128)]), (NFC.mk MM [(25/31104), 0, (-5/31104)]), (NFC.mk MM [(-5/41472), (9/512), (1/41472), (-1/512)]), (NFC.mk MM [(-5/373248), 0, (1/373248)]), (NFC.mk MM [(355/17915904), (-45/8192), (-71/17915904), (5/8192)]), (NFC.mk MM [(-1535/161243136), 0, (307/161243136)])], [(NFC.mk MM [(5/4), (-9/4), (-1/4), (1/4)]), (NFC.mk MM [(5/12), 0, (-1/12)]), (NFC.mk MM [(5/144), (-9/16), (-1/144), (1/16)]), (NFC.mk MM [(-5/432), 0, (1/432)]), (NFC.mk MM [(35/10368), (9/128), (-7/10368), (-1/128)]), (NFC.mk MM [(-25/31104), 0, (5/31104)]), (NFC.mk MM [(5/41472), (-9/512), (-1/41472), (1/512)]), (NFC.mk MM [(5/373248), 0, (-1/373248)]), (NFC.mk MM [(-355/17915904), (45/8192), (71/17915904), (-5/8192)]), (NFC.mk MM [(1535/161243136), 0, (-307/161243136)])], [(NFC.mk MM [(-5/4), (-9/4), (1/4), (1/4)]), (NFC.mk MM [(-5/12), 0, (1/12)]), (NFC.mk MM [(-5/144), (-9/16), (1/144), (1/16)]), (NFC.mk MM [(5/432), 0, (-1/432)]), (NFC.mk MM [(-35/10368), (9/128), (7/10368), (-1/128)]), (NFC.mk MM [(25/31104), 0, (-5/31104)]), (NFC.mk MM [(-5/41472), (-9/512), (1/41472), (1/512)]), (NFC.mk MM [(-5/373248), 0, (1/373248)]), (NFC.mk MM [(355/17915904), (45/8192), (-71/17915904), (-5/8192)]), (NFC.mk MM [(-1535/161243136), 0, (307/161243136)])], [(NFC.mk MM [(5/4), (9/4), (-1/4), (-1/4)]), (NFC.mk MM [(5/12), 0, (-1/12)]), (NFC.mk MM [(5/144), (9/16), (-1/144), (-1/16)]), (NFC.mk MM [(-5/432), 0, (1/432)]), (NFC.mk MM [(35/10368), (-9/128), (-7/10368), (1/128)]), (NFC.mk MM [(-25/31104), 0, (5/31104)]), (NFC.mk MM [(5/41472), (9/512), (-1/41472), (-1/512)]), (NFC.mk MM [(5/373248), 0, (-1/373248)]), (NFC.mk MM [(-355/17915904), (-45/8192), (71/17915904), (5/8192)]), (NFC.mk MM [(1535/161243136), 0, (-307/161243136)])]], 8⟩

-- the earlier criteria do not apply
#guard !eisC Fq 0 && !wtC Fq

lemma Fq_eq : toB Fq = X ^ 4 + C (toPoly [-3, 0, -1]) * X ^ 2 + C (toPoly [0, 0, 1]) := by
  simp only [Fq, toB_cons, toB_nil, toPoly_nil, map_zero, toPoly_cons, map_one, mul_zero,
    add_zero, mul_one]; ring

lemma Fq_mon : (toB Fq).Monic := by rw [Fq_eq]; monicity!

lemma Fq_deg : (toB Fq).natDegree = 4 := by rw [Fq_eq]; compute_degree!

set_option maxRecDepth 200000 in
lemma hsub : irrSubsetCheck (Fq.map (·.map (algebraMap ℚ KK))) 4 2 1 bc = true := by decide +kernel

/-- **`Y⁴ − (x² + 3) Y² + x²` is geometrically irreducible.** -/
theorem geomIrr : GeomIrr.{0} Fq :=
  geomIrr_of_subsets Fq MM Fq_mon 4 2 Fq_deg (by norm_num) 1 bc hsub

end Curves.MT.GeomIrrSubEx
