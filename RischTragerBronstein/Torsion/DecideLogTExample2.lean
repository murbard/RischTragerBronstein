import RischTragerBronstein.Torsion.DecideLogTExample

/-!
# Residues at a ramified point and above infinity

On `y² = x (x + 27)(x − 48)` over `ℚ(i)`: `f = 72/((x + 24) y) + 1/(2x)` has residues `1` at
`P = (−24, 72)`, `−1` at `P' = (−24, −72)`, `1` at the ramified point `Q = (0, 0)` and `−1` at the
single place at infinity. The scaled residue divisor `2 (P − P' + Q − ∞) ∼ 4 P − 2 ∞ₓ` is not
torsion. `decideLogT` (scale `s = 2`, exponents `e = 2` at `x = −24` and `−1` at `x = 0`) answers
`some false` in the kernel. The witnesses are those of `NonTorsionExample`, except that the
reduction modulo `13` now has `m₁₃ = 1` (`4 P̄ = 0`) and a new principal witness modulo `193`.
`run3` certifies irreducibility by specializations without roots modulo `p` instead of
Eisenstein.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.NTExample

open Curves.RFExampleI

def probT2 : CurveProb QI :=
  { Fc := FcE, n := 2, k := 3, A := [[cI (-15552) 0, cI (-900) 0, cI (3/2) 0, cI (1/2) 0], [cI 72 0]],
    D := [cI 0 0, cI (-31104) 0, cI (-1800) 0, cI 3 0, cI 1 0],
    pts := [(cI (0) (0), ⟨2, [[cI (0) (0), cI (0) (36), cI (0) (0), cI (0) (7/24), cI (0) (0), cI (0) (-625/41472), cI (0) (0), cI (0) (4375/35831808), cI (0) (0), cI (0) (-513125/123834728448), cI (0) (0), cI (0) (9060625/106993205379072), cI (0) (0), cI (0) (-161944375/61628086298345472), cI (0) (0), cI (0) (3769548125/53246666561770487808)], [cI (0) (0), cI (0) (-36), cI (0) (0), cI (0) (-7/24), cI (0) (0), cI (0) (625/41472), cI (0) (0), cI (0) (-4375/35831808), cI (0) (0), cI (0) (513125/123834728448), cI (0) (0), cI (0) (-9060625/106993205379072), cI (0) (0), cI (0) (161944375/61628086298345472), cI (0) (0), cI (0) (-3769548125/53246666561770487808)]], 12⟩),
      (cI (-27) (0), ⟨2, [[cI (0) (0), cI (45) (0), cI (0) (0), cI (-17/15) (0), cI (0) (0), cI (-32/10125) (0), cI (0) (0), cI (-544/6834375) (0), cI (0) (0), cI (-1952/922640625) (0), cI (0) (0), cI (-183328/3113912109375) (0), cI (0) (0), cI (-1192288/700630224609375) (0), cI (0) (0), cI (-23994208/472925401611328125) (0)], [cI (0) (0), cI (-45) (0), cI (0) (0), cI (17/15) (0), cI (0) (0), cI (32/10125) (0), cI (0) (0), cI (544/6834375) (0), cI (0) (0), cI (1952/922640625) (0), cI (0) (0), cI (183328/3113912109375) (0), cI (0) (0), cI (1192288/700630224609375) (0), cI (0) (0), cI (23994208/472925401611328125) (0)]], 12⟩),
      (cI (48) (0), ⟨2, [[cI (0) (0), cI (60) (0), cI (0) (0), cI (41/40) (0), cI (0) (0), cI (-27/64000) (0), cI (0) (0), cI (369/51200000) (0), cI (0) (0), cI (-4083/32768000000) (0), cI (0) (0), cI (285647/131072000000000) (0), cI (0) (0), cI (-24246581/629145600000000000) (0), cI (0) (0), cI (1039846633/1509949440000000000000) (0)], [cI (0) (0), cI (-60) (0), cI (0) (0), cI (-41/40) (0), cI (0) (0), cI (27/64000) (0), cI (0) (0), cI (-369/51200000) (0), cI (0) (0), cI (4083/32768000000) (0), cI (0) (0), cI (-285647/131072000000000) (0), cI (0) (0), cI (24246581/629145600000000000) (0), cI (0) (0), cI (-1039846633/1509949440000000000000) (0)]], 12⟩),
      (cI (-24) (0), ⟨1, [[cI (72) (0), cI (10) (0), cI (-193/144) (0), cI (1001/5184) (0), cI (-117329/2985984) (0), cI (973031/107495424) (0), cI (-7731305/3439853568) (0), cI (217716679/371504185344) (0), cI (-67718445431/427972821516288) (0), cI (2026943325407/46221064723759104) (0), cI (-165110642639911/13311666640442621952) (0), cI (1708789037852935/479219999055934390272) (0), cI (-286755733790239109/276030719456218208796672) (0), cI (3041207694867820523/9937105900423855516680192) (0), cI (-260472208102350875761/2861886499322070388803895296) (0), cI (937078022300172542255/34342637991864844665646743552) (0)], [cI (-72) (0), cI (-10) (0), cI (193/144) (0), cI (-1001/5184) (0), cI (117329/2985984) (0), cI (-973031/107495424) (0), cI (7731305/3439853568) (0), cI (-217716679/371504185344) (0), cI (67718445431/427972821516288) (0), cI (-2026943325407/46221064723759104) (0), cI (165110642639911/13311666640442621952) (0), cI (-1708789037852935/479219999055934390272) (0), cI (286755733790239109/276030719456218208796672) (0), cI (-3041207694867820523/9937105900423855516680192) (0), cI (260472208102350875761/2861886499322070388803895296) (0), cI (-937078022300172542255/34342637991864844665646743552) (0)]], 12⟩)],
    inf := ⟨2, [[cI (0) (0), cI (0) (0), cI (0) (0), cI (1) (0), cI (0) (0), cI (-21/2) (0), cI (0) (0), cI (-5625/8) (0), cI (0) (0), cI (-118125/16) (0), cI (0) (0), cI (-41563125/128) (0), cI (0) (0), cI (-2201731875/256) (0), cI (0) (0), cI (-354172348125/1024) (0), cI (0) (0), cI (-24732005248125/2048) (0), cI (0) (0), cI (-15931984696138125/32768) (0), cI (0) (0), cI (-1241409945464994375/65536) (0), cI (0) (0), cI (-204264642236892654375/262144) (0), cI (0) (0), cI (-16769918069924423866875/524288) (0)], [cI (0) (0), cI (0) (0), cI (0) (0), cI (-1) (0), cI (0) (0), cI (21/2) (0), cI (0) (0), cI (5625/8) (0), cI (0) (0), cI (118125/16) (0), cI (0) (0), cI (41563125/128) (0), cI (0) (0), cI (2201731875/256) (0), cI (0) (0), cI (354172348125/1024) (0), cI (0) (0), cI (24732005248125/2048) (0), cI (0) (0), cI (15931984696138125/32768) (0), cI (0) (0), cI (1241409945464994375/65536) (0), cI (0) (0), cI (204264642236892654375/262144) (0), cI (0) (0), cI (16769918069924423866875/524288) (0)]], 16⟩ }
def Gw193b : List (List (ZMod 193)) := [[102, 102, 92, 1, 114, 15, 82], [162, 2, 152, 33, 1, 0, 0]]

/-- The divisor `4 P − 2 ∞ₓ`. -/
def TE2 : GlobalCert QI := { TE with ΓL := [[4, 0]], cdeg := 2 }

def P13b : PrimeCert 13 := { P13 with mp := 1 }

def P193b : PrimeCert 193 := { P193 with Gw := Gw193b }

/-- The non-torsion witness with scale `2`. -/
def twE2 : TorsWit QI := ⟨TE2, [2], 2, ⟨0, by decide +kernel⟩, 13, 193, P13b, P193b, 12, LmE⟩

set_option maxRecDepth 200000 in
lemma run2 : decideLogT (nfRedAt [1, 0, 1]) probT2 [] [twE2] = some false := by decide +kernel

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **`∫ (72 / ((x + 24) y) + 1/(2x)) dx` is not elementary** on any curve
`y² = x (x + 27)(x − 48)` over an algebraically closed field of constants (`f = S.fE probT2 ιI`
is `(72 y + (x³ + 3x² − 1800x − 31104)/2) / (x⁴ + 3x³ − 1800x² − 31104x)`). -/
theorem not_elementary2 (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probT2.Fc).map (mapRingHom (ιI (Kc := Kc)))) :
    ¬ HasElementaryIntegral ((S.fE probT2 ιI : Kc⟮S.x⟯⟮S.y⟯) : E) :=
  (decideLogT_spec hC S hx hgen (nfRedAt [1, 0, 1]) hred probT2 ιI hSF [] [twE2] false
    run2).not.mpr (by simp)

/-- The same witness, with irreducibility certified by specializations without roots modulo `13`
(`x = 3`) and `193` (`x = 1`) instead of Eisenstein. -/
def twE3 : TorsWit QI :=
  ⟨TE2, [2], 2, ⟨0, by decide +kernel⟩, 13, 193, { P13b with aI := some 3 },
    { P193b with aI := some 1 }, 12, LmE⟩

set_option maxRecDepth 200000 in
lemma run3 : decideLogT (nfRedAt [1, 0, 1]) probT2 [] [twE3] = some false := by decide +kernel

/-- `not_elementary2` again, through the specialization certificates. -/
theorem not_elementary2' (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probT2.Fc).map (mapRingHom (ιI (Kc := Kc)))) :
    ¬ HasElementaryIntegral ((S.fE probT2 ιI : Kc⟮S.x⟯⟮S.y⟯) : E) :=
  (decideLogT_spec hC S hx hgen (nfRedAt [1, 0, 1]) hred probT2 ιI hSF [] [twE3] false
    run3).not.mpr (by simp)

end Curves.NTExample
