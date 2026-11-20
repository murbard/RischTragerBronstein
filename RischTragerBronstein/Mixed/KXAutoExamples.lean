import RischTragerBronstein.Mixed.KXAuto
import RischTragerBronstein.Mixed.KXSearchExamples

/-!
# Executable checks for automatic residue selection

The decoding checks include nonzero entries, internal zeros, and an irrelevant tail. The
decision checks exercise a positive encoded stage and an automatic negative search.
-/

namespace Curves.MT

open CPoly

private def sampleResidues (j : ℕ) : ℕ := [2, 5, 0, 7].getD j 99

example : (List.range 4).map (natSeq (natSeqCode 4 sampleResidues)) = [2, 5, 0, 7] := by
  decide +kernel

-- Only the finite prefix is encoded: the original tail value `99` is not retained.
example : natSeq (natSeqCode 4 sampleResidues) 4 = 0 := by decide +kernel

section LevelZero

open KXEx

-- A logarithmic derivative with a dependent Mordell–Weil class: positive encoded stage.
#guard kxAutoStage [0, -1] ks lv 0 xc Adep Bdep 0 1 [c1]
  (Nat.pair (natSeqCode 1 (fun _ ↦ 2)) (Nat.pair 30 (Nat.pair 4 0))) = some true

end LevelZero

section LevelOne

open KXL1

example : kxAuto [0, -1] ks lv 1 g1 A1 [one1] 0 0 [one1] 0 = none := rfl

-- No supplied primes, residues, relation bound, or height bound.
#guard kxAuto [0, -1] ks lv 1 g1 A1 [one1] 0 0 [one1] 1 = some false

end LevelOne

end Curves.MT
