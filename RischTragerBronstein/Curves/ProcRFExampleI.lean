import RischTragerBronstein.Curves.ProcRFExample
import RischTragerBronstein.Algebraic.NFSplit
import RischTragerBronstein.Algebraic.EllDecideQ

/-!
# A non-elementary elliptic integral, decided by the general-curve procedure

On `y² = x (x − 9)(x − 25)` (branch points chosen so that all Puiseux expansions lie in
`ℚ(i)[[T]]`), `decideRF` runs in the kernel over `ℚ(i) = NF [1, 0, 1]` with certified branches at
`0, 9, 25` and above infinity, and answers `some false`: `∫ dx / y` is not elementary.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.RFExampleI

lemma irr_i : Kron.irredQ ([1, 0, 1] : CPoly ℚ) = true := by decide +kernel

instance : Fact (Irreducible (toPoly ([1, 0, 1] : CPoly ℚ))) := ⟨Kron.irredQ_sound _ irr_i⟩

abbrev QI := NFC.NF ([1, 0, 1] : CPoly ℚ)

/-- `a + b i`. -/
def cI (a b : ℚ) : QI := NFC.mk _ [a, b]

/-- `y² = x (x − 9)(x − 25)`, `∫ dx / y = ∫ y / (x (x − 9)(x − 25)) dx`. -/
def probEll : CurveProb QI :=
  { Fc := [[cI 0 0, cI (-225) 0, cI 34 0, cI (-1) 0], [], [cI 1 0]], n := 2, k := 3,
    A := [[], [cI 1 0]], D := [cI 0 0, cI 225 0, cI (-34) 0, cI 1 0],
    pts := [(0, ⟨2, [[cI (0) (0), cI (15) (0), cI (0) (0), cI (-17/15) (0), cI (0) (0), cI (-32/3375) (0), cI (0) (0), cI (-544/759375) (0), cI (0) (0), cI (-1952/34171875) (0), cI (0) (0)], [cI (0) (0), cI (-15) (0), cI (0) (0), cI (17/15) (0), cI (0) (0), cI (32/3375) (0), cI (0) (0), cI (544/759375) (0), cI (0) (0), cI (1952/34171875) (0), cI (0) (0)]], 8⟩),
      (9, ⟨2, [[cI (0) (0), cI (0) (12), cI (0) (0), cI (0) (7/24), cI (0) (0), cI (0) (-625/13824), cI (0) (0), cI (0) (4375/3981312), cI (0) (0), cI (0) (-513125/4586471424), cI (0) (0)], [cI (0) (0), cI (0) (-12), cI (0) (0), cI (0) (-7/24), cI (0) (0), cI (0) (625/13824), cI (0) (0), cI (0) (-4375/3981312), cI (0) (0), cI (0) (513125/4586471424), cI (0) (0)]], 8⟩),
      (25, ⟨2, [[cI (0) (0), cI (20) (0), cI (0) (0), cI (41/40) (0), cI (0) (0), cI (-81/64000) (0), cI (0) (0), cI (3321/51200000) (0), cI (0) (0), cI (-110241/32768000000) (0), cI (0) (0)], [cI (0) (0), cI (-20) (0), cI (0) (0), cI (-41/40) (0), cI (0) (0), cI (81/64000) (0), cI (0) (0), cI (-3321/51200000) (0), cI (0) (0), cI (110241/32768000000) (0), cI (0) (0)]], 8⟩)],
    inf := ⟨2, [[cI (0) (0), cI (0) (0), cI (0) (0), cI (1) (0), cI (0) (0), cI (-17) (0), cI (0) (0), cI (-32) (0), cI (0) (0), cI (-544) (0), cI (0) (0), cI (-9760) (0), cI (0) (0), cI (-183328) (0), cI (0) (0), cI (-3576864) (0), cI (0) (0), cI (-71982624) (0), cI (0) (0), cI (-1485523488) (0), cI (0) (0), cI (-31292438560) (0), cI (0) (0)], [cI (0) (0), cI (0) (0), cI (0) (0), cI (-1) (0), cI (0) (0), cI (17) (0), cI (0) (0), cI (32) (0), cI (0) (0), cI (544) (0), cI (0) (0), cI (9760) (0), cI (0) (0), cI (183328) (0), cI (0) (0), cI (3576864) (0), cI (0) (0), cI (71982624) (0), cI (0) (0), cI (1485523488) (0), cI (0) (0), cI (31292438560) (0), cI (0) (0)]], 16⟩
 }


set_option maxRecDepth 200000 in
lemma run : probEll.decideRF = some false := by decide +kernel

lemma c0 : cI 0 0 = 0 := by decide +kernel
lemma c1 : cI 1 0 = 1 := by decide +kernel
lemma c225 : cI 225 0 = ((225 : ℕ) : QI) := by decide +kernel
lemma cm34 : cI (-34) 0 = -((34 : ℕ) : QI) := by decide +kernel

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- The embedding `ℚ(i) → Kc`. -/
noncomputable def ιI : QI →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := QI) (M := Kc)).toRingHom

/-- **`∫ dx / √(x (x − 9)(x − 25))` is not elementary**, decided by the general-curve
procedure over `ℚ(i)`: on any curve `y² = x (x − 9)(x − 25)`, `∫ y / (x (x − 9)(x − 25)) dx` has
no elementary antiderivative. -/
theorem ell_not_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probEll.Fc).map (mapRingHom (ιI (Kc := Kc)))) :
    ¬ HasElementaryIntegral (S.y / (S.x ^ 3 - 34 * S.x ^ 2 + 225 * S.x)) := by
  have := (decideRF_spec hC S hx hgen probEll ιI hSF false run).not.mpr (by simp)
  convert this using 2
  have h225 : ιI (Kc := Kc) (225 : QI) = 225 := by
    rw [show (225 : QI) = ((225 : ℕ) : QI) from rfl, map_natCast]; norm_num
  have h34 : ιI (Kc := Kc) (34 : QI) = 34 := by
    rw [show (34 : QI) = ((34 : ℕ) : QI) from rfl, map_natCast]; norm_num
  simp [CurveData.fE, CurveData.evXY, probEll, toB, CPoly.toPoly, c0, c1, c225, cm34, h225, h34]
  rw [show (algebraMap Kc E) 225 = 225 from map_ofNat _ 225,
    show (algebraMap Kc E) 34 = 34 from map_ofNat _ 34]
  ring

end Curves.RFExampleI
