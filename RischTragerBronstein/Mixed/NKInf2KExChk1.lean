import RischTragerBronstein.Mixed.NKInf2KExData

/-! Kernel checks for `NKInf2KExample` (global certificate, non-principality test); split for memory. -/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial

set_option maxRecDepth 200000 in
lemma okFc : TT.Fc = Fm := by decide +kernel

set_option maxRecDepth 200000 in
lemma okG : TT.globalCheckR = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okN : nonPrincOK TT.n (pairMult 7 37 Q7.mp Q37.mp * Pc2.cΓ) PbL.1 TT.I.δL TT.I.Bc
    TT.I.Dc Pc2.αs (Pc2.fcerts TT.n) (Pc2.bL TT.n (pairMult 7 37 Q7.mp Q37.mp)) PbL.2 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
lemma okshape : Pc2.fib.length = 1 ∧ Pc2.pl.length = 2 ∧ Pc2.fα 0 = 0 := by
  refine ⟨rfl, rfl, ?_⟩
  decide +kernel

end Curves.MT.NKInf2KEx
