import RischTragerBronstein.Mixed.KXSearch
import RischTragerBronstein.Mixed.KXDepExamples
import RischTragerBronstein.Mixed.KXMWExampleL1M

/-!
# Examples for the unified cubic decider and its persistent search

Both answers at level zero use dependent Mordell–Weil classes. The level-one example uses
a Manin certificate. The small abstract search checks cover a success away from the diagonal
and preservation of a negative answer when later stages fail or disagree.
-/

namespace Curves.MT

open CPoly

section LevelZero

open KXEx

-- A dependent class with a non-elementary remainder.
#guard kxDecideNC [0, -1] ks lv 0 xc Adep [c1] 0 0 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 4 0 = some false

-- The corresponding logarithmic derivative is elementary.
#guard kxDecideNC [0, -1] ks lv 0 xc Adep Bdep 0 1 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 4 0 = some true

example : kxSearch [0, -1] ks lv 0 xc Adep Bdep 0 1 [c1] (fun _ ↦ 2) 0 = none := rfl

end LevelZero

section LevelOne

open KXL1

-- The non-constant level-one example is certified without height iterations.
#guard kxDecideNC [0, -1] ks lv 1 g1 A1 [one1] 0 0 [one1] [17, 19, 23] 30
  (fun _ ↦ 2) 0 0 = some false

-- The Manin branch already answers at the first triple `(0, 0, 0)`.
#guard kxSearch [0, -1] ks lv 1 g1 A1 [one1] 0 0 [one1] (fun _ ↦ 2) 1 = some false

end LevelOne

private def offDiagonal (i : ℕ) : Option Bool :=
  let p := Nat.unpair i
  let q := Nat.unpair p.2
  if p.1 = 1 ∧ q.1 = 2 ∧ q.2 = 0 then some false else none

-- Diagonal trials miss the answer; enumeration reaches it and retains it.
example (n : ℕ) : offDiagonal (Nat.pair n (Nat.pair n n)) = none := by
  simp [offDiagonal, Nat.unpair_pair]
  omega

#guard prefixSearch offDiagonal (Nat.pair 1 (Nat.pair 2 0)) = none
#guard prefixSearch offDiagonal (Nat.pair 1 (Nat.pair 2 0) + 1) = some false
#guard prefixSearch offDiagonal (Nat.pair 1 (Nat.pair 2 0) + 5) = some false

-- `some false` is an answer, including when a later unchecked stage disagrees.
#guard prefixSearch (fun i ↦ if i = 0 then some false else some true) 3 = some false

end Curves.MT
