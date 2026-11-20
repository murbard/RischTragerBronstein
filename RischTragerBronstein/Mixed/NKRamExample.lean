import RischTragerBronstein.Mixed.NKNonTorsP
import RischTragerBronstein.Mixed.NKExactExamples
import RischTragerBronstein.Torsion.Emit

/-!
# Example: residues at a ramified place over `log x`

Tower `x`, `t = log x`, and `θ² = t (t + 27)(t − 48)`. The integrand
`f = (1/x) (θ t/72 + t + 24)/(t (t + 24))`, i.e. `(θ/(72 (t + 24)) + 1/t) dt`, has simple poles at
the unramified points `(−24, ±72)` (residues `±1`) and at the **ramified** place `(0, 0)`
(`t = T²`, residue `2`). The certificates (the data below, up to `okN`) were produced by the
untrusted constant-curve pipeline `emitCurveQ` over `ℚ[γ]/(γ² + 1296) = ℚ(i)` and are checked by
`decide +kernel`; `nk_not_elementary_TW` turns them into: **`∫ f dx` is not elementary**.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.MT.NKRamEx

/-- The coefficient field `ℚ[γ]/(M)`. -/
def MM : CPoly ℚ := [1296, 0, 1]

theorem hMM : Kron.irredQ MM = true := by decide +kernel

instance : Fact (Irreducible (toPoly MM)) := ⟨Kron.irredQ_sound MM hMM⟩

abbrev KK := NFC.NF MM

/-- The integrand over `ℚ`. -/
def P0 : CurveProb ℚ := ⟨[[0, 1296, 21, (-1)], [], [1]], 2, 3, [[24, 1], [0, (1/72)]], [0, 24, 1], [], ⟨1, [], 0⟩⟩

def ptsB : List (KK × BranchCert KK) := [((NFC.mk MM [(-27)]), ⟨2, [[(NFC.mk MM []), (NFC.mk MM [45]), (NFC.mk MM []), (NFC.mk MM [(-17/15)]), (NFC.mk MM []), (NFC.mk MM [(-32/10125)])], [(NFC.mk MM []), (NFC.mk MM [(-45)]), (NFC.mk MM []), (NFC.mk MM [(17/15)]), (NFC.mk MM []), (NFC.mk MM [(32/10125)])]], 4⟩), ((NFC.mk MM [(-24)]), ⟨1, [[(NFC.mk MM [72]), (NFC.mk MM [10]), (NFC.mk MM [(-193/144)]), (NFC.mk MM [(1001/5184)]), (NFC.mk MM [(-117329/2985984)])], [(NFC.mk MM [(-72)]), (NFC.mk MM [(-10)]), (NFC.mk MM [(193/144)]), (NFC.mk MM [(-1001/5184)]), (NFC.mk MM [(117329/2985984)])]], 3⟩), ((NFC.mk MM []), ⟨2, [[(NFC.mk MM []), (NFC.mk MM [0, 1]), (NFC.mk MM []), (NFC.mk MM [0, (7/864)]), (NFC.mk MM []), (NFC.mk MM [0, (-625/1492992)]), (NFC.mk MM []), (NFC.mk MM [0, (4375/1289945088)]), (NFC.mk MM []), (NFC.mk MM [0, (-513125/4458050224128)])], [(NFC.mk MM []), (NFC.mk MM [0, (-1)]), (NFC.mk MM []), (NFC.mk MM [0, (-7/864)]), (NFC.mk MM []), (NFC.mk MM [0, (625/1492992)]), (NFC.mk MM []), (NFC.mk MM [0, (-4375/1289945088)]), (NFC.mk MM []), (NFC.mk MM [0, (513125/4458050224128)])]], 8⟩), ((NFC.mk MM [48]), ⟨2, [[(NFC.mk MM []), (NFC.mk MM [(-60)]), (NFC.mk MM []), (NFC.mk MM [(-41/40)]), (NFC.mk MM []), (NFC.mk MM [(27/64000)])], [(NFC.mk MM []), (NFC.mk MM [60]), (NFC.mk MM []), (NFC.mk MM [(41/40)]), (NFC.mk MM []), (NFC.mk MM [(-27/64000)])]], 4⟩)]

def infY0 : CPoly KK := [(NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM [(21/2)]), (NFC.mk MM []), (NFC.mk MM [(5625/8)]), (NFC.mk MM []), (NFC.mk MM [(118125/16)]), (NFC.mk MM []), (NFC.mk MM [(41563125/128)]), (NFC.mk MM []), (NFC.mk MM [(2201731875/256)]), (NFC.mk MM []), (NFC.mk MM [(354172348125/1024)]), (NFC.mk MM []), (NFC.mk MM [(24732005248125/2048)]), (NFC.mk MM []), (NFC.mk MM [(15931984696138125/32768)])]

def infY1 : CPoly KK := [(NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM [(-21/2)]), (NFC.mk MM []), (NFC.mk MM [(-5625/8)]), (NFC.mk MM []), (NFC.mk MM [(-118125/16)]), (NFC.mk MM []), (NFC.mk MM [(-41563125/128)]), (NFC.mk MM []), (NFC.mk MM [(-2201731875/256)]), (NFC.mk MM []), (NFC.mk MM [(-354172348125/1024)]), (NFC.mk MM []), (NFC.mk MM [(-24732005248125/2048)]), (NFC.mk MM []), (NFC.mk MM [(-15931984696138125/32768)])]

def infB : BranchCert KK := ⟨2, [infY0, infY1], 18⟩

/-- The integrand over `ℚ[γ]/(M)` with its branch data. -/
def Pb : CurveProb KK := P0.baseChange (algebraMap ℚ KK) 3 ptsB infB

def TT : GlobalCert KK := ⟨[[(NFC.mk MM []), (NFC.mk MM [1296]), (NFC.mk MM [21]), (NFC.mk MM [(-1)])], [], [(NFC.mk MM [1])]], 2, 2, 3, ⟨[[[(NFC.mk MM [1])]], [[], [(NFC.mk MM [1])]]], [(NFC.mk MM [1])], [0, 2], [((NFC.mk MM [(-27)]), (⟨2, [[(NFC.mk MM []), (NFC.mk MM [45]), (NFC.mk MM []), (NFC.mk MM [(-17/15)]), (NFC.mk MM []), (NFC.mk MM [(-32/10125)]), (NFC.mk MM []), (NFC.mk MM [(-544/6834375)]), (NFC.mk MM []), (NFC.mk MM [(-1952/922640625)]), (NFC.mk MM []), (NFC.mk MM [(-183328/3113912109375)])], [(NFC.mk MM []), (NFC.mk MM [(-45)]), (NFC.mk MM []), (NFC.mk MM [(17/15)]), (NFC.mk MM []), (NFC.mk MM [(32/10125)]), (NFC.mk MM []), (NFC.mk MM [(544/6834375)]), (NFC.mk MM []), (NFC.mk MM [(1952/922640625)]), (NFC.mk MM []), (NFC.mk MM [(183328/3113912109375)])]], 10⟩, [[(NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [])], [(NFC.mk MM []), (NFC.mk MM [(1/45)]), (NFC.mk MM []), (NFC.mk MM [])]])), ((NFC.mk MM []), (⟨2, [[(NFC.mk MM []), (NFC.mk MM [0, 1]), (NFC.mk MM []), (NFC.mk MM [0, (7/864)]), (NFC.mk MM []), (NFC.mk MM [0, (-625/1492992)]), (NFC.mk MM []), (NFC.mk MM [0, (4375/1289945088)]), (NFC.mk MM []), (NFC.mk MM [0, (-513125/4458050224128)]), (NFC.mk MM []), (NFC.mk MM [0, (9060625/3851755393646592)])], [(NFC.mk MM []), (NFC.mk MM [0, (-1)]), (NFC.mk MM []), (NFC.mk MM [0, (-7/864)]), (NFC.mk MM []), (NFC.mk MM [0, (625/1492992)]), (NFC.mk MM []), (NFC.mk MM [0, (-4375/1289945088)]), (NFC.mk MM []), (NFC.mk MM [0, (513125/4458050224128)]), (NFC.mk MM []), (NFC.mk MM [0, (-9060625/3851755393646592)])]], 10⟩, [[(NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [])], [(NFC.mk MM []), (NFC.mk MM [0, (-1/1296)]), (NFC.mk MM []), (NFC.mk MM [])]])), ((NFC.mk MM [48]), (⟨2, [[(NFC.mk MM []), (NFC.mk MM [(-60)]), (NFC.mk MM []), (NFC.mk MM [(-41/40)]), (NFC.mk MM []), (NFC.mk MM [(27/64000)]), (NFC.mk MM []), (NFC.mk MM [(-369/51200000)]), (NFC.mk MM []), (NFC.mk MM [(4083/32768000000)]), (NFC.mk MM []), (NFC.mk MM [(-285647/131072000000000)])], [(NFC.mk MM []), (NFC.mk MM [60]), (NFC.mk MM []), (NFC.mk MM [(41/40)]), (NFC.mk MM []), (NFC.mk MM [(-27/64000)]), (NFC.mk MM []), (NFC.mk MM [(369/51200000)]), (NFC.mk MM []), (NFC.mk MM [(-4083/32768000000)]), (NFC.mk MM []), (NFC.mk MM [(285647/131072000000000)])]], 10⟩, [[(NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [])], [(NFC.mk MM []), (NFC.mk MM [(-1/60)]), (NFC.mk MM []), (NFC.mk MM [])]]))], ⟨2, [[(NFC.mk MM []), (NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM [(21/2)]), (NFC.mk MM []), (NFC.mk MM [(5625/8)]), (NFC.mk MM []), (NFC.mk MM [(118125/16)]), (NFC.mk MM []), (NFC.mk MM [(41563125/128)]), (NFC.mk MM []), (NFC.mk MM [(2201731875/256)])], [(NFC.mk MM []), (NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM [(-21/2)]), (NFC.mk MM []), (NFC.mk MM [(-5625/8)]), (NFC.mk MM []), (NFC.mk MM [(-118125/16)]), (NFC.mk MM []), (NFC.mk MM [(-41563125/128)]), (NFC.mk MM []), (NFC.mk MM [(-2201731875/256)])]], 10⟩, [[(NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [])], [(NFC.mk MM []), (NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM [])]]⟩, (NFC.mk MM []), [], [], [], [], 0⟩

def PcW : PlaceCert KK := ⟨[((NFC.mk MM [(-24)]), 1), ((NFC.mk MM []), 2)], [(0, (1, ([(NFC.mk MM [72]), (NFC.mk MM [10]), (NFC.mk MM [(-193/144)]), (NFC.mk MM [(1001/5184)]), (NFC.mk MM [(-117329/2985984)]), (NFC.mk MM [(973031/107495424)]), (NFC.mk MM [(-7731305/3439853568)]), (NFC.mk MM [(217716679/371504185344)]), (NFC.mk MM [(-67718445431/427972821516288)]), (NFC.mk MM [(2026943325407/46221064723759104)]), (NFC.mk MM [(-165110642639911/13311666640442621952)]), (NFC.mk MM [(1708789037852935/479219999055934390272)]), (NFC.mk MM [(-286755733790239109/276030719456218208796672)]), (NFC.mk MM [(3041207694867820523/9937105900423855516680192)]), (NFC.mk MM [(-260472208102350875761/2861886499322070388803895296)]), (NFC.mk MM [(937078022300172542255/34342637991864844665646743552)])], 15))), (0, (1, ([(NFC.mk MM [(-72)]), (NFC.mk MM [(-10)]), (NFC.mk MM [(193/144)]), (NFC.mk MM [(-1001/5184)]), (NFC.mk MM [(117329/2985984)]), (NFC.mk MM [(-973031/107495424)]), (NFC.mk MM [(7731305/3439853568)]), (NFC.mk MM [(-217716679/371504185344)]), (NFC.mk MM [(67718445431/427972821516288)]), (NFC.mk MM [(-2026943325407/46221064723759104)]), (NFC.mk MM [(165110642639911/13311666640442621952)]), (NFC.mk MM [(-1708789037852935/479219999055934390272)]), (NFC.mk MM [(286755733790239109/276030719456218208796672)]), (NFC.mk MM [(-3041207694867820523/9937105900423855516680192)]), (NFC.mk MM [(260472208102350875761/2861886499322070388803895296)]), (NFC.mk MM [(-937078022300172542255/34342637991864844665646743552)])], 15))), (1, (2, ([(NFC.mk MM []), (NFC.mk MM [0, 1]), (NFC.mk MM []), (NFC.mk MM [0, (7/864)]), (NFC.mk MM []), (NFC.mk MM [0, (-625/1492992)]), (NFC.mk MM []), (NFC.mk MM [0, (4375/1289945088)]), (NFC.mk MM []), (NFC.mk MM [0, (-513125/4458050224128)]), (NFC.mk MM []), (NFC.mk MM [0, (9060625/3851755393646592)]), (NFC.mk MM []), (NFC.mk MM [0, (-161944375/2218611106740436992)]), (NFC.mk MM []), (NFC.mk MM [0, (3769548125/1916879996223737561088)])], 15)))], [[(0, (1, (NFC.mk MM [1]))), (1, (1, (NFC.mk MM [1])))], [(2, (1, (NFC.mk MM [1]))), (2, (1, (NFC.mk MM [(-1)])))]], [2, 0, 2], [2, 1], [2, 2], 2, [10, 10]⟩

def Pp : PrimeCert 13 := ⟨[(12, (⟨2, [[0, 6, 0, 11, 0, 3, 0, 1, 0, 5, 0, 12], [0, 7, 0, 2, 0, 10, 0, 12, 0, 8, 0, 1]], 10⟩, [[1, 0, 0, 0], [0, 11, 0, 0]])), (0, (⟨2, [[0, 2, 0, 11, 0, 9, 0, 9, 0, 5, 0, 10], [0, 11, 0, 2, 0, 4, 0, 4, 0, 8, 0, 3]], 10⟩, [[1, 0, 0, 0], [0, 7, 0, 0]])), (9, (⟨2, [[0, 5, 0, 11, 0, 1, 0, 3, 0, 5, 0, 4], [0, 8, 0, 2, 0, 12, 0, 10, 0, 8, 0, 9]], 10⟩, [[1, 0, 0, 0], [0, 8, 0, 0]]))], ⟨2, [[0, 12, 0, 4, 0, 6, 0, 11, 0, 10, 0, 2], [0, 1, 0, 9, 0, 7, 0, 2, 0, 3, 0, 11]], 10⟩, [[1, 0, 0, 0], [0, 12, 0, 0]], [1], [[6, 7]], [[0, 1]], [[[7, 7], [12, 1]]], [], 1, [[1]], some 3, 0⟩

def Pq : PrimeCert 17 := ⟨[(7, (⟨2, [[0, 11, 0, 0, 0, 7, 0, 0, 0, 14, 0, 0], [0, 6, 0, 0, 0, 10, 0, 0, 0, 3, 0, 0]], 10⟩, [[1, 0, 0, 0], [0, 14, 0, 0]])), (0, (⟨2, [[0, 8, 0, 4, 0, 15, 0, 1, 0, 12, 0, 7], [0, 9, 0, 13, 0, 2, 0, 16, 0, 5, 0, 10]], 10⟩, [[1, 0, 0, 0], [0, 15, 0, 0]])), (14, (⟨2, [[0, 8, 0, 13, 0, 15, 0, 16, 0, 12, 0, 10], [0, 9, 0, 4, 0, 2, 0, 1, 0, 5, 0, 7]], 10⟩, [[1, 0, 0, 0], [0, 15, 0, 0]]))], ⟨2, [[0, 16, 0, 2, 0, 4, 0, 8, 0, 7, 0, 12], [0, 1, 0, 15, 0, 13, 0, 9, 0, 10, 0, 5]], 10⟩, [[1, 0, 0, 0], [0, 16, 0, 0]], [2], [[1, 16]], [[0, 1]], [[[9, 9], [9, 8]]], [], 1, [[1]], some 1, 0⟩

def Qp : PlaceCert.PrimeData 13 := ⟨2, [[0, 0, 5, 11, 11], [0, 0, 1, 0, 0]]⟩

def Qq : PlaceCert.PrimeData 17 := ⟨5, [[0, 0, 0, 0, 0, 4, 14, 11, 9, 0, 5], [0, 0, 0, 0, 0, 11, 15, 16, 1, 0, 0]]⟩

def LmW : List (List KK) := [[(NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [])], [(NFC.mk MM [(-1/12)]), (NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/12)]), (NFC.mk MM [0, (-1/81)]), (NFC.mk MM []), (NFC.mk MM [])], [(NFC.mk MM [(-1/576)]), (NFC.mk MM [(-1/24)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/576)]), (NFC.mk MM [0, (-13/31104)]), (NFC.mk MM []), (NFC.mk MM [])], [(NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [0, (-1/1296)]), (NFC.mk MM []), (NFC.mk MM [])], [], []]

def tw : TorsWitP KK :=
  ⟨TT, PcW, [1, 0], 1, ⟨0, by decide +kernel⟩, 13, 17, Pp, Pq, Qp, Qq, 2, LmW⟩

/-! The kernel checks, one conjunct at a time. -/

set_option maxRecDepth 200000 in
lemma okInfR0 : rootCheck (invB Pb.Fc Pb.k (Pb.k * Pb.n)) 0 2 18 infY0 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
lemma okInfR1 : rootCheck (invB Pb.Fc Pb.k (Pb.k * Pb.n)) 0 2 18 infY1 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
lemma okInf : certCheck (invB Pb.Fc Pb.k (Pb.k * Pb.n)) Pb.n 0 Pb.inf = true := by
  have e : Pb.inf = infB := rfl
  rw [e, infB, certCheck]
  simp only [List.all_cons, List.all_nil, okInfR0, okInfR1, Bool.and_true]
  decide +kernel

set_option maxRecDepth 200000 in
lemma okV : Pb.valid = true := by
  unfold CurveProb.valid
  rw [okInf]
  decide +kernel

set_option maxRecDepth 200000 in
lemma okG : tw.T.globalCheck = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okPc : tw.Pc.check tw.T.Fc tw.T.n = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okR : torsResCheckP Pb tw.T tw.Pc tw.eL tw.s tw.j₀ = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okP : primeOKP (redAtM MM) tw.T tw.Pc tw.p tw.Pp tw.Qp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okQ : primeOKP (redAtM MM) tw.T tw.Pc tw.q tw.Pq tw.Qq = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okN : nonPrincOK tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp * tw.Pc.cΓ) tw.Pb
    tw.T.I.δL tw.T.I.Bc tw.T.I.Dc tw.Pc.αs (tw.Pc.fcerts tw.T.n)
    (tw.Pc.bL tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp)) tw.Lm = true := by
  decide +kernel

open Curves Curves.LT Curves.MT Tower.Sys Curves.MT.NKExEx

def Fq : BPoly ℚ := [[0, 1296, 21, -1], [], [1]]
def Bq : BPoly ℚ := [[24, 1], [0, 1/72]]
def Dq : CPoly ℚ := [0, 24, 1]

set_option maxRecDepth 200000 in
lemma hcertT : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hshape : nkShape Fc ks 0 (liftCurve Fc ks 0 tw.T.n Fq) = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hresP : resDivCheckP tw.T Fq tw.Pc Bq Dq (EllQuad.QCoords.coord tw.j₀) tw.s tw.eL = true := by
  decide +kernel

lemma hpq : tw.p ≠ tw.q := by decide

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ (θ/(72 (log x + 24)) + 1/log x) dx/x` is not elementary** on `θ² = t (t + 27)(t − 48)`,
`t = log x` (one pole at a ramified place). -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ tw.T.n + ∑ i ∈ Finset.range tw.T.n,
      T.evP 0 ((liftCurve Fc ks 0 tw.T.n Fq).getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ}) :
    ¬ HasElementaryIntegral (T.ev 0 ic * ∑ j ∈ Finset.range tw.T.n,
      T.evP 0 (liftQC Fc ks 0 (Bq.getD j [])) / T.evP 0 (liftQC Fc ks 0 Dq) * θ ^ j) :=
  T.nk_not_elementary_TW (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Cc)).toRingHom hmonF.1
    hmonF.2 0 hn hcertT rfl (redAtM MM) (redAtM_valid MM) tw Fq hshape θ hθ hgen okG okPc hpq
    okP okQ (Or.inr okN) Bq Dq hresP

end Curves.MT.NKRamEx
