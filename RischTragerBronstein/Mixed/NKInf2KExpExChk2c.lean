import RischTragerBronstein.Mixed.NKInf2KExpExChk2b

/-! Kernel checks for `NKInf2KExpExample` (place certificate: separation and assembly); split for memory. -/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial

set_option maxRecDepth 200000 in
lemma okSep : Pc2.sepCheckP TT.n = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma okPls : (List.range Pc2.pl.length).all (fun π ↦ decide (Pc2.pj π < Pc2.fib.length) &&
    decide (0 < Pc2.pe π) && rootCheck TT.Fc (Pc2.fα (Pc2.pj π)) (Pc2.pe π) (Pc2.pp π) (Pc2.py π)) =
    true := by
  rw [List.all_eq_true]
  intro π hπ
  rw [List.mem_range, show Pc2.pl.length = 2 from rfl] at hπ
  rcases π with _ | _ | π
  · rw [okRoot0]; decide +kernel
  · rw [okRoot1]; decide +kernel
  · omega

set_option maxRecDepth 200000 in
lemma okPc : Pc2.check TT.Fc TT.n = true := by
  simp only [PlaceCert.check]
  rw [okPls, okSep]
  decide +kernel

end Curves.MT.NKInf2KExpEx
