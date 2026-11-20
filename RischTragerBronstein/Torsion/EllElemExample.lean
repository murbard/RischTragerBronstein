import RischTragerBronstein.Torsion.Emit

/-!
# An elementary integral with a logarithmic part, decided and certified automatically

`∫ √(x³ + 1)/x dx` on `y² = x³ + 1` (`P0`: `Fc = Y² − x³ − 1`, weight `k = 3`, integrand `Y/x`).
`emitLoop` built the field `ℚ[γ]/(γ⁴ − 2γ³ + 6γ² − 14γ + 13) = ℚ(ζ₁₂)` (the Puiseux coefficients
at the branch points need `ζ₆` and `√3`), found the residues `±1` at `(0, ±1)`, the order `3`
of their divisor (a kernel vector of the principality test at the multiplier `pairMult`, primes
`13` and `37`), the logarithm `u = W/Q` with `div u = 3 ((0, 1) − (0, −1))`, and the exact part;
`emitLog` printed this file. The kernel checks `decideLog` on these witnesses (about 3 minutes,
14 GB), and **`decided`** / **`elementary`** follow from `decideLogTP_baseChange_spec`.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.EllElemExample

/-- The coefficient field `ℚ[γ]/(M)`. -/
def MM : CPoly ℚ := [13, (-14), 6, (-2), 1]

theorem hMM : Kron.irredQ MM = true := by decide +kernel

instance : Fact (Irreducible (toPoly MM)) := ⟨Kron.irredQ_sound MM hMM⟩

abbrev KK := NFC.NF MM

/-- The integrand over `ℚ`. -/
def P0 : CurveProb ℚ := ⟨[[(-1), 0, 0, (-1)], [], [1]], 2, 3, [[], [1]], [0, 1], [], ⟨1, [], 0⟩⟩

def ptsB : List (KK × BranchCert KK) := [((NFC.mk MM [(-1/3), (1/2), 0, (1/6)]), ⟨2, [[(NFC.mk MM []), (NFC.mk MM [(4/3), (-3/2), 0, (-1/6)]), (NFC.mk MM []), (NFC.mk MM [(-11/12), (1/4), (-1/4), (1/12)]), (NFC.mk MM []), (NFC.mk MM [(-19/144), (1/12), (-1/48), (1/72)]), (NFC.mk MM []), (NFC.mk MM [(1/36), (-1/32), 0, (-1/288)]), (NFC.mk MM []), (NFC.mk MM [(121/6912), (-11/2304), (11/2304), (-11/6912)]), (NFC.mk MM []), (NFC.mk MM [(-19/1536), (1/128), (-1/512), (1/768)]), (NFC.mk MM []), (NFC.mk MM [(37/20736), (-37/18432), 0, (-37/165888)])], [(NFC.mk MM []), (NFC.mk MM [(-4/3), (3/2), 0, (1/6)]), (NFC.mk MM []), (NFC.mk MM [(11/12), (-1/4), (1/4), (-1/12)]), (NFC.mk MM []), (NFC.mk MM [(19/144), (-1/12), (1/48), (-1/72)]), (NFC.mk MM []), (NFC.mk MM [(-1/36), (1/32), 0, (1/288)]), (NFC.mk MM []), (NFC.mk MM [(-121/6912), (11/2304), (-11/2304), (11/6912)]), (NFC.mk MM []), (NFC.mk MM [(19/1536), (-1/128), (1/512), (-1/768)]), (NFC.mk MM []), (NFC.mk MM [(-37/20736), (37/18432), 0, (37/165888)])]], 12⟩), ((NFC.mk MM [(4/3), (-1/2), 0, (-1/6)]), ⟨2, [[(NFC.mk MM []), (NFC.mk MM [(19/6), (-2), (1/2), (-1/3)]), (NFC.mk MM []), (NFC.mk MM [(11/12), (-1/4), (1/4), (-1/12)]), (NFC.mk MM []), (NFC.mk MM [(-1/18), (1/16), 0, (1/144)]), (NFC.mk MM []), (NFC.mk MM [(19/288), (-1/24), (1/96), (-1/144)]), (NFC.mk MM []), (NFC.mk MM [(-121/6912), (11/2304), (-11/2304), (11/6912)]), (NFC.mk MM []), (NFC.mk MM [(-1/192), (3/512), 0, (1/1536)]), (NFC.mk MM []), (NFC.mk MM [(703/165888), (-37/13824), (37/55296), (-37/82944)])], [(NFC.mk MM []), (NFC.mk MM [(-19/6), 2, (-1/2), (1/3)]), (NFC.mk MM []), (NFC.mk MM [(-11/12), (1/4), (-1/4), (1/12)]), (NFC.mk MM []), (NFC.mk MM [(1/18), (-1/16), 0, (-1/144)]), (NFC.mk MM []), (NFC.mk MM [(-19/288), (1/24), (-1/96), (1/144)]), (NFC.mk MM []), (NFC.mk MM [(121/6912), (-11/2304), (11/2304), (-11/6912)]), (NFC.mk MM []), (NFC.mk MM [(1/192), (-3/512), 0, (-1/1536)]), (NFC.mk MM []), (NFC.mk MM [(-703/165888), (37/13824), (-37/55296), (37/82944)])]], 12⟩), ((NFC.mk MM [(-1)]), ⟨2, [[(NFC.mk MM []), (NFC.mk MM [(-11/6), (1/2), (-1/2), (1/6)]), (NFC.mk MM []), (NFC.mk MM [(11/12), (-1/4), (1/4), (-1/12)]), (NFC.mk MM []), (NFC.mk MM [(-11/144), (1/48), (-1/48), (1/144)]), (NFC.mk MM []), (NFC.mk MM [(-11/288), (1/96), (-1/96), (1/288)]), (NFC.mk MM []), (NFC.mk MM [(-121/6912), (11/2304), (-11/2304), (11/6912)]), (NFC.mk MM []), (NFC.mk MM [(-11/1536), (1/512), (-1/512), (1/1536)]), (NFC.mk MM []), (NFC.mk MM [(-407/165888), (37/55296), (-37/55296), (37/165888)])], [(NFC.mk MM []), (NFC.mk MM [(11/6), (-1/2), (1/2), (-1/6)]), (NFC.mk MM []), (NFC.mk MM [(-11/12), (1/4), (-1/4), (1/12)]), (NFC.mk MM []), (NFC.mk MM [(11/144), (-1/48), (1/48), (-1/144)]), (NFC.mk MM []), (NFC.mk MM [(11/288), (-1/96), (1/96), (-1/288)]), (NFC.mk MM []), (NFC.mk MM [(121/6912), (-11/2304), (11/2304), (-11/6912)]), (NFC.mk MM []), (NFC.mk MM [(11/1536), (-1/512), (1/512), (-1/1536)]), (NFC.mk MM []), (NFC.mk MM [(407/165888), (-37/55296), (37/55296), (-37/165888)])]], 12⟩), ((NFC.mk MM []), ⟨1, [[(NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1/2)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/8)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1/16)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(5/128)])], [(NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/2)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1/8)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/16)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-5/128)])]], 11⟩)]

def infY0 : CPoly KK := [(NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1/2)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/8)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1/16)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(5/128)])]

def infY1 : CPoly KK := [(NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/2)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1/8)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(1/16)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-5/128)])]

def infB : BranchCert KK := ⟨2, [infY0, infY1], 26⟩

def Pb : CurveProb KK := P0.baseChange (algebraMap ℚ KK) 3 ptsB infB

def ws : List (LogWit KK) := [⟨3, [[(NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [(-1/2)])], [(NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [])]], [(NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM []), (NFC.mk MM [1])]⟩, ⟨1, [[(NFC.mk MM [1])]], [(NFC.mk MM [1])]⟩, ⟨1, [[(NFC.mk MM [1])]], [(NFC.mk MM [1])]⟩, ⟨1, [[(NFC.mk MM [1])]], [(NFC.mk MM [1])]⟩]

set_option maxRecDepth 200000 in
lemma okInfR0 : rootCheck (invB Pb.Fc Pb.k (Pb.k * Pb.n)) 0 2 26 infY0 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
lemma okInfR1 : rootCheck (invB Pb.Fc Pb.k (Pb.k * Pb.n)) 0 2 26 infY1 = true := by
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
lemma okD : Pb.decideLog ws = some true := by
  unfold CurveProb.decideLog
  rw [okV]
  decide +kernel

lemma okT : decideLogTP (redAtM MM) Pb ws [] [] = some true := by
  simp [decideLogTP, decideLogT, okD]

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **The decision** (certificates checked above). -/
theorem decided (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) :
    HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ true = true := by
  set ι : KK →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Kc)).toRingHom
  have hι : ι.comp (algebraMap ℚ KK) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have h := decideLogTP_baseChange_spec hC S hx hgen (redAtM MM) (redAtM_valid MM)
    (algebraMap ℚ KK) P0 3 ptsB infB ι (by rw [hι]; exact hSF) ws [] [] true okT
  rwa [hι] at h

/-- **`∫ √(x³ + 1)/x dx` is elementary.** -/
theorem elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) :
    HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) :=
  (decided hC S hx hgen hSF).mpr rfl

end Curves.EllElemExample
