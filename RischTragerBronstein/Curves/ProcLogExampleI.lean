import RischTragerBronstein.Curves.ProcLogDecide
import RischTragerBronstein.Curves.ProcRFExampleI

/-!
# A non-elementary integral with a logarithmic part, over `ℚ(i)`

On `y² = x (x − 9)(x − 25)`: `∫ (1/y + 1/(x − 9)) dx = ∫ (y + x² − 25x)/(x (x − 9)(x − 25)) dx`.
The residue divisor `2·(9, 0) − 2·∞` is principal (`u = x − 9`, verified by `witCheck`), the
remainder `1/y` is a nonzero holomorphic differential: `decideLog … = some false`.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.LogExampleI

open RFExampleI

/-- `A = y + x² − 25x`, `D = x (x − 9)(x − 25)`. -/
def probEllLog : CurveProb QI :=
  { Fc := [[cI 0 0, cI (-225) 0, cI 34 0, cI (-1) 0], [], [cI 1 0]], n := 2, k := 3,
    A := [[cI 0 0, cI (-25) 0, cI 1 0], [cI 1 0]], D := [cI 0 0, cI 225 0, cI (-34) 0, cI 1 0],
    pts := [(0, ⟨2, [[cI (0) (0), cI (15) (0), cI (0) (0), cI (-17/15) (0), cI (0) (0), cI (-32/3375) (0), cI (0) (0), cI (-544/759375) (0), cI (0) (0), cI (-1952/34171875) (0), cI (0) (0)], [cI (0) (0), cI (-15) (0), cI (0) (0), cI (17/15) (0), cI (0) (0), cI (32/3375) (0), cI (0) (0), cI (544/759375) (0), cI (0) (0), cI (1952/34171875) (0), cI (0) (0)]], 8⟩),
      (9, ⟨2, [[cI (0) (0), cI (0) (12), cI (0) (0), cI (0) (7/24), cI (0) (0), cI (0) (-625/13824), cI (0) (0), cI (0) (4375/3981312), cI (0) (0), cI (0) (-513125/4586471424), cI (0) (0)], [cI (0) (0), cI (0) (-12), cI (0) (0), cI (0) (-7/24), cI (0) (0), cI (0) (625/13824), cI (0) (0), cI (0) (-4375/3981312), cI (0) (0), cI (0) (513125/4586471424), cI (0) (0)]], 8⟩),
      (25, ⟨2, [[cI (0) (0), cI (20) (0), cI (0) (0), cI (41/40) (0), cI (0) (0), cI (-81/64000) (0), cI (0) (0), cI (3321/51200000) (0), cI (0) (0), cI (-110241/32768000000) (0), cI (0) (0)], [cI (0) (0), cI (-20) (0), cI (0) (0), cI (-41/40) (0), cI (0) (0), cI (81/64000) (0), cI (0) (0), cI (-3321/51200000) (0), cI (0) (0), cI (110241/32768000000) (0), cI (0) (0)]], 8⟩)],
    inf := ⟨2, [[cI (0) (0), cI (0) (0), cI (0) (0), cI (1) (0), cI (0) (0), cI (-17) (0), cI (0) (0), cI (-32) (0), cI (0) (0), cI (-544) (0), cI (0) (0), cI (-9760) (0), cI (0) (0), cI (-183328) (0), cI (0) (0), cI (-3576864) (0), cI (0) (0), cI (-71982624) (0), cI (0) (0), cI (-1485523488) (0), cI (0) (0), cI (-31292438560) (0), cI (0) (0)], [cI (0) (0), cI (0) (0), cI (0) (0), cI (-1) (0), cI (0) (0), cI (17) (0), cI (0) (0), cI (32) (0), cI (0) (0), cI (544) (0), cI (0) (0), cI (9760) (0), cI (0) (0), cI (183328) (0), cI (0) (0), cI (3576864) (0), cI (0) (0), cI (71982624) (0), cI (0) (0), cI (1485523488) (0), cI (0) (0), cI (31292438560) (0), cI (0) (0)]], 16⟩
 }

/-- The witness `u = x − 9` for the rational component. -/
def wsEllLog : List (LogWit QI) := [⟨1, [[cI (-9) 0, cI 1 0]], [cI 1 0]⟩]

set_option maxRecDepth 200000 in
lemma run : probEllLog.decideLog wsEllLog = some false := by decide +kernel

lemma cm25 : cI (-25) 0 = -((25 : ℕ) : QI) := by decide +kernel

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **`∫ (1/y + 1/(x − 9)) dx` is not elementary** on any curve `y² = x (x − 9)(x − 25)`:
the logarithmic part `log (x − 9)` is found and verified, the remainder `dx/y` is not exact. -/
theorem ell_log_not_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probEllLog.Fc).map (mapRingHom (ιI (Kc := Kc)))) :
    ¬ HasElementaryIntegral ((S.y + S.x ^ 2 - 25 * S.x) / (S.x ^ 3 - 34 * S.x ^ 2 + 225 * S.x)) := by
  have := (decideLog_spec hC S hx hgen probEllLog ιI hSF wsEllLog false run).not.mpr (by simp)
  convert this using 2
  have h225 : ιI (Kc := Kc) (225 : QI) = 225 := by
    rw [show (225 : QI) = ((225 : ℕ) : QI) from rfl, map_natCast]; norm_num
  have h34 : ιI (Kc := Kc) (34 : QI) = 34 := by
    rw [show (34 : QI) = ((34 : ℕ) : QI) from rfl, map_natCast]; norm_num
  have h25 : ιI (Kc := Kc) (25 : QI) = 25 := by
    rw [show (25 : QI) = ((25 : ℕ) : QI) from rfl, map_natCast]; norm_num
  simp [CurveData.fE, CurveData.evXY, probEllLog, toB, CPoly.toPoly, c0, c1, c225, cm34, cm25,
    h225, h34, h25]
  rw [show (algebraMap Kc E) 225 = 225 from map_ofNat _ 225,
    show (algebraMap Kc E) 34 = 34 from map_ofNat _ 34,
    show (algebraMap Kc E) 25 = 25 from map_ofNat _ 25]
  ring

end Curves.LogExampleI
