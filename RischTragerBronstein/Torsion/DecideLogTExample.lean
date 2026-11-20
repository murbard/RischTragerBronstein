import RischTragerBronstein.Torsion.NonTorsionExample
import RischTragerBronstein.Torsion.DecideLogT
import RischTragerBronstein.Curves.ProcLogExampleI

/-!
# A non-elementary integral decided through a non-torsion certificate

On `y² = x (x + 27)(x − 48)` (over `ℚ(i)`), `∫ 72 dx / ((x + 24) y)` has only simple poles, at
`P = (−24, 72)` and `P' = (−24, −72)`, with residues `1` and `−1`. Its residue divisor
`P − P' ∼ 2 P − ∞ₓ` is not torsion (`P` has infinite order), so the integral is not elementary.
`decideLog` alone answers `none` (no logarithm exists); `decideLogT` with the non-torsion witness
`twE` (primes `13` and `193`, see `NonTorsionExample`) answers `some false` in the kernel
(`run`), and `decideLogT_spec` turns this into `not_elementary`.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.NTExample

open Curves.RFExampleI

def probT : CurveProb QI :=
  { Fc := FcE, n := 2, k := 3, A := [[], [cI 72 0]],
    D := [cI 0 0, cI (-31104) 0, cI (-1800) 0, cI 3 0, cI 1 0],
    pts := [(cI (0) (0), ⟨2, [[cI (0) (0), cI (0) (36), cI (0) (0), cI (0) (7/24), cI (0) (0), cI (0) (-625/41472), cI (0) (0), cI (0) (4375/35831808), cI (0) (0), cI (0) (-513125/123834728448), cI (0) (0), cI (0) (9060625/106993205379072), cI (0) (0), cI (0) (-161944375/61628086298345472), cI (0) (0), cI (0) (3769548125/53246666561770487808)], [cI (0) (0), cI (0) (-36), cI (0) (0), cI (0) (-7/24), cI (0) (0), cI (0) (625/41472), cI (0) (0), cI (0) (-4375/35831808), cI (0) (0), cI (0) (513125/123834728448), cI (0) (0), cI (0) (-9060625/106993205379072), cI (0) (0), cI (0) (161944375/61628086298345472), cI (0) (0), cI (0) (-3769548125/53246666561770487808)]], 12⟩),
      (cI (-27) (0), ⟨2, [[cI (0) (0), cI (45) (0), cI (0) (0), cI (-17/15) (0), cI (0) (0), cI (-32/10125) (0), cI (0) (0), cI (-544/6834375) (0), cI (0) (0), cI (-1952/922640625) (0), cI (0) (0), cI (-183328/3113912109375) (0), cI (0) (0), cI (-1192288/700630224609375) (0), cI (0) (0), cI (-23994208/472925401611328125) (0)], [cI (0) (0), cI (-45) (0), cI (0) (0), cI (17/15) (0), cI (0) (0), cI (32/10125) (0), cI (0) (0), cI (544/6834375) (0), cI (0) (0), cI (1952/922640625) (0), cI (0) (0), cI (183328/3113912109375) (0), cI (0) (0), cI (1192288/700630224609375) (0), cI (0) (0), cI (23994208/472925401611328125) (0)]], 12⟩),
      (cI (48) (0), ⟨2, [[cI (0) (0), cI (60) (0), cI (0) (0), cI (41/40) (0), cI (0) (0), cI (-27/64000) (0), cI (0) (0), cI (369/51200000) (0), cI (0) (0), cI (-4083/32768000000) (0), cI (0) (0), cI (285647/131072000000000) (0), cI (0) (0), cI (-24246581/629145600000000000) (0), cI (0) (0), cI (1039846633/1509949440000000000000) (0)], [cI (0) (0), cI (-60) (0), cI (0) (0), cI (-41/40) (0), cI (0) (0), cI (27/64000) (0), cI (0) (0), cI (-369/51200000) (0), cI (0) (0), cI (4083/32768000000) (0), cI (0) (0), cI (-285647/131072000000000) (0), cI (0) (0), cI (24246581/629145600000000000) (0), cI (0) (0), cI (-1039846633/1509949440000000000000) (0)]], 12⟩),
      (cI (-24) (0), ⟨1, [[cI (72) (0), cI (10) (0), cI (-193/144) (0), cI (1001/5184) (0), cI (-117329/2985984) (0), cI (973031/107495424) (0), cI (-7731305/3439853568) (0), cI (217716679/371504185344) (0), cI (-67718445431/427972821516288) (0), cI (2026943325407/46221064723759104) (0), cI (-165110642639911/13311666640442621952) (0), cI (1708789037852935/479219999055934390272) (0), cI (-286755733790239109/276030719456218208796672) (0), cI (3041207694867820523/9937105900423855516680192) (0), cI (-260472208102350875761/2861886499322070388803895296) (0), cI (937078022300172542255/34342637991864844665646743552) (0)], [cI (-72) (0), cI (-10) (0), cI (193/144) (0), cI (-1001/5184) (0), cI (117329/2985984) (0), cI (-973031/107495424) (0), cI (7731305/3439853568) (0), cI (-217716679/371504185344) (0), cI (67718445431/427972821516288) (0), cI (-2026943325407/46221064723759104) (0), cI (165110642639911/13311666640442621952) (0), cI (-1708789037852935/479219999055934390272) (0), cI (286755733790239109/276030719456218208796672) (0), cI (-3041207694867820523/9937105900423855516680192) (0), cI (260472208102350875761/2861886499322070388803895296) (0), cI (-937078022300172542255/34342637991864844665646743552) (0)]], 12⟩)],
    inf := ⟨2, [[cI (0) (0), cI (0) (0), cI (0) (0), cI (1) (0), cI (0) (0), cI (-21/2) (0), cI (0) (0), cI (-5625/8) (0), cI (0) (0), cI (-118125/16) (0), cI (0) (0), cI (-41563125/128) (0), cI (0) (0), cI (-2201731875/256) (0), cI (0) (0), cI (-354172348125/1024) (0), cI (0) (0), cI (-24732005248125/2048) (0), cI (0) (0), cI (-15931984696138125/32768) (0), cI (0) (0), cI (-1241409945464994375/65536) (0), cI (0) (0), cI (-204264642236892654375/262144) (0), cI (0) (0), cI (-16769918069924423866875/524288) (0)], [cI (0) (0), cI (0) (0), cI (0) (0), cI (-1) (0), cI (0) (0), cI (21/2) (0), cI (0) (0), cI (5625/8) (0), cI (0) (0), cI (118125/16) (0), cI (0) (0), cI (41563125/128) (0), cI (0) (0), cI (2201731875/256) (0), cI (0) (0), cI (354172348125/1024) (0), cI (0) (0), cI (24732005248125/2048) (0), cI (0) (0), cI (15931984696138125/32768) (0), cI (0) (0), cI (1241409945464994375/65536) (0), cI (0) (0), cI (204264642236892654375/262144) (0), cI (0) (0), cI (16769918069924423866875/524288) (0)]], 16⟩ }

/-- The non-torsion witness: component `0` (the rational part) of the residues. -/
def twE : TorsWit QI := ⟨TE, [1], 1, ⟨0, by decide +kernel⟩, 13, 193, P13, P193, 12, LmE⟩

set_option maxRecDepth 200000 in
lemma run : decideLogT (nfRedAt [1, 0, 1]) probT [] [twE] = some false := by decide +kernel

lemma c0 : cI 0 0 = 0 := by decide +kernel
lemma c1 : cI 1 0 = 1 := by decide +kernel
lemma c3 : cI 3 0 = ((3 : ℕ) : QI) := by decide +kernel
lemma c72 : cI 72 0 = ((72 : ℕ) : QI) := by decide +kernel
lemma cm1800 : cI (-1800) 0 = -((1800 : ℕ) : QI) := by decide +kernel
lemma cm31104 : cI (-31104) 0 = -((31104 : ℕ) : QI) := by decide +kernel

lemma hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p QI), nfRedAt [1, 0, 1] p = some R →
    ∃ φ : QI →+* ℚ_[p], RedValid p R φ := fun p _ R h ↦
  nfRedAt_valid [1, 0, 1] (by simp [toPoly]) p R h

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **`∫ 72 dx / ((x + 24) √(x (x + 27)(x − 48)))` is not elementary**: on any curve
`y² = x (x + 27)(x − 48)` over an algebraically closed field of constants,
`72 y / (x⁴ + 3x³ − 1800x² − 31104x) = 72 / ((x + 24) y)` has no elementary antiderivative. -/
theorem not_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probT.Fc).map (mapRingHom (ιI (Kc := Kc)))) :
    ¬ HasElementaryIntegral
      (72 * S.y / (S.x ^ 4 + 3 * S.x ^ 3 - 1800 * S.x ^ 2 - 31104 * S.x)) := by
  have := (decideLogT_spec hC S hx hgen (nfRedAt [1, 0, 1]) hred probT ιI hSF [] [twE] false
    run).not.mpr (by simp)
  convert this using 2
  have hι : ∀ n : ℕ, ιI (Kc := Kc) ((n : ℕ) : QI) = n := fun n ↦ map_natCast _ n
  have h72 : ιI (Kc := Kc) (72 : QI) = 72 := by exact_mod_cast hι 72
  have h3 : ιI (Kc := Kc) (3 : QI) = 3 := by exact_mod_cast hι 3
  have h1800 : ιI (Kc := Kc) (1800 : QI) = 1800 := by exact_mod_cast hι 1800
  have h31104 : ιI (Kc := Kc) (31104 : QI) = 31104 := by exact_mod_cast hι 31104
  simp [CurveData.fE, CurveData.evXY, probT, toB, CPoly.toPoly, c0, c1, c3, c72, cm1800,
    cm31104, h72, h3, h1800, h31104]
  rw [show (algebraMap Kc E) 72 = 72 from map_ofNat _ 72,
    show (algebraMap Kc E) 3 = 3 from map_ofNat _ 3,
    show (algebraMap Kc E) 1800 = 1800 from map_ofNat _ 1800,
    show (algebraMap Kc E) 31104 = 31104 from map_ofNat _ 31104]
  ring

end Curves.NTExample
