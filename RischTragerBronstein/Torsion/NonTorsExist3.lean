import RischTragerBronstein.Torsion.BaseExist2

/-!
# Non-torsion witnesses exist (3): from base points

**`exists_torsOKP_of_base`**: over a number field `ℚ[γ]/(M)` (integral `M`), for a valid problem
with a non-torsion `j₀`-residue divisor (and the side conditions of `exists_torsOKP`), whose curve
is given over the number field, a non-torsion witness accepted by `torsOKP` exists as soon as, for
the integral basis of every global certificate, there are `g ≥ 1` admissible non-special base
fibres away from the special points: the global certificate comes from `exists_globalCert`, the
base-point data from `exists_char0Base`, the place checks in characteristic `0` from `PcE_check`.
-/

open Polynomial HahnSeries Filter EllQuad.QCoords IntermediateField

namespace Curves

open CPoly Sup

section Dne

variable {F : Type*} [Field F] [DecidableEq F]

lemma toPoly_ne_zero_of_getLast {Dc : CPoly F} (h : Dc.getLast? = some 1) : toPoly Dc ≠ 0 := by
  intro h0
  have hlen : 0 < Dc.length := by
    rcases hc : Dc with _ | ⟨c, l⟩
    · rw [hc] at h; simp at h
    · simp
  have h1 : Dc.getD (Dc.length - 1) 0 = 1 := by
    rw [List.getLast?_eq_getElem?] at h
    rw [List.getD_eq_getElem?_getD, h]; rfl
  have := congrArg (fun P ↦ P.coeff (Dc.length - 1)) h0
  simp only [coeff_toPoly, h1, Polynomial.coeff_zero] at this
  exact one_ne_zero this

/-- `D(α + T)` has an order when `D ≠ 0`. -/
lemma muD_lt_of_ne (Dc : CPoly F) (hD : toPoly Dc ≠ 0) (a : F) :
    muD Dc a 1 < (compC Dc (shiftC a 1)).length := by
  have h : toPoly (compC Dc (shiftC a 1)) ≠ 0 := by
    rw [toPoly_compC, toPoly_shiftC, pow_one]
    intro h0
    rcases comp_eq_zero_iff.mp h0 with h1 | ⟨-, h2⟩
    · exact hD h1
    · have := congrArg (fun q ↦ q.coeff 1) h2
      simp at this
  unfold muD ordC
  apply List.findIdx_lt_length_of_exists
  by_contra hall
  push Not at hall
  apply h
  ext i
  rw [coeff_toPoly, Polynomial.coeff_zero]
  by_cases hi : i < (compC Dc (shiftC a 1)).length
  · rw [List.getD_eq_getElem _ _ hi]
    simpa using hall _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]

end Dne

section Witness

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb (NFC.NF M)) {ψ : (NFC.NF M) →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : (NFC.NF M), IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim (NFC.NF M)))

include hSF hV hζ in
/-- **The non-torsion witness from base points.** -/
theorem exists_torsOKP_of_base {mZ : List ℤ} (hint : Curves.intCoeffs M = some mZ)
    (hvalid : P.valid = true)
    (hnd : (P.pts.map Prod.fst).Nodup) (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0)
    (hNT : ∀ m, 0 < m → ∀ Λ : C →ₗ[ℚ] ℚ, (∀ r : NFC.NF M, Λ (ψ r) = coord j₀ r) →
      ∀ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 → ¬ S.TorsOrdStd (K := C) P ψ m w Λ)
    {E : Type*} [Field E] [Algebra (NFC.NF M) E] (SF : CurveData (NFC.NF M) E)
    (hSFF : SF.F = toB P.Fc)
    (hbase : ∀ T : GlobalCert (NFC.NF M), T.globalCheck = true → T.Fc = P.Fc → T.n = P.n →
      T.I.pts.map Prod.fst = P.pts.map Prod.fst →
      ∃ g, 0 < g ∧ (∑ j ∈ Finset.range T.n, T.I.δL.getD j 0) + 1 = g + T.n ∧
      ∃ (hn0 : 0 < T.n) (f : Fin g → AdmFib (fun j : Fin T.n ↦ toB (T.I.Bc.getD j []))),
        Function.Injective (fun l ↦ (f l).x) ∧
        (∀ l k, evalB T.Fc (f l).x ((f l).ys k) = 0) ∧
        (∀ l k, evalB (derivYB T.Fc) (f l).x ((f l).ys k) ≠ 0) ∧
        (∀ l, Kron.evalC T.I.Dc (f l).x ≠ 0) ∧
        kerSp (fun j ↦ T.I.δL.getD j 0) g g f (fun _ ↦ ⟨0, hn0⟩) ≤ (NFC.NF M) ∙ e0 hn0 f ∧
        ∀ l, ∀ ac ∈ P.pts, (f l).x ≠ ac.1) :
    ∃ tw : TorsWitP (NFC.NF M), torsOKP (redAtM M) P tw = true := by
  obtain ⟨T, hT, hTF, hTn, hαL, hyL, hTpts⟩ := exists_globalCert P hvalid hV hnd SF hSFF
  obtain ⟨g, hg0, hg, hn0, f, hinj, hroot, hsimple, hD, hns, havoid⟩ := hbase T hT hTF hTn hTpts
  have hTf := globalCheck_spec hT
  have hSF' : S.F = (toB T.Fc).map (mapRingHom ψ) := by rw [hTF]; exact hSF
  obtain ⟨xs, ys, lam, Ls, irrP, hC, hxs⟩ := exists_char0Base S ψ T hT hαL hyL hSF' hn0 hg0 hg f
    hinj hroot hsimple hD hns
  have hpl : Char0Pl T.Fc T.n T.I.Dc xs (S.PcE P hSF hV hζ j₀) := by
    refine ⟨?_, fun j _ ↦ muD_lt_of_ne _ (toPoly_ne_zero_of_getLast hTf.Dlast) _, fun j hj i hi ↦ ?_⟩
    · rw [hTF, hTn]; exact PlaceCert.check_spec _ (S.PcE_check P hSF hV hζ j₀ hnd hinf0)
    · rw [S.PcE_fib_length P hSF hV hζ j₀ 0] at hj
      rw [S.PcE_fα P hSF hV hζ j₀ 0 hj, hxs, List.getD_eq_getElem _ _ (by simpa [hxs] using hi),
        List.getElem_ofFn]
      exact fun h ↦ havoid _ _ (List.getElem_mem hj) h.symm
  exact S.exists_torsOKP P hSF hV hζ j₀ hint hvalid hnd hinf0 hNT T hT hTF hTn xs ys lam Ls irrP hC
    hpl

end CurveData

end Witness

end Curves
