import RischTragerBronstein.Torsion.PcEFacts

/-!
# Non-torsion witnesses exist (1): the checks at a good prime

**`prime_side`**: at a prime where the finitely many relevant elements are good and `M` is
integral, the reduced prime certificate passes `primeCheck`, and there is one multiplier `m_p`
such that every place certificate `PcE tx` with `tx` above the bound `m_p s Γ_π + N_j μ_j`
passes `PlaceCert.primeCheck` with multiplier `m_p`.
-/

open Polynomial HahnSeries EllQuad.QCoords

namespace Curves

open CPoly Sup

section PrimeSide

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb (NFC.NF M)) {ψ : (NFC.NF M) →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : (NFC.NF M), IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim (NFC.NF M)))

/-- **The checks at a good prime.** -/
theorem prime_side (hnd : (P.pts.map Prod.fst).Nodup) (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0)
    (T : GlobalCert (NFC.NF M)) (hTF : T.Fc = P.Fc) (hTn : T.n = P.n)
    (xs : List (NFC.NF M)) (ys : List (List (NFC.NF M))) (lam : List (List (NFC.NF M))) (Ls : List (List (List (NFC.NF M))))
    (irrP : ℕ) (hC : Char0Base T xs ys lam Ls irrP)
    (hpl : Char0Pl T.Fc T.n T.I.Dc xs (S.PcE P hSF hV hζ j₀))
    {p : ℕ} [Fact p.Prime] (R : RedFns p (NFC.NF M)) (hNF : NFRed p R) (φ : (NFC.NF M) →+* ℚ_[p])
    (hR : RedValid p R φ)
    (hM : toPoly M ∈ lifts (ratSub p).subtype) (hlc : (toPoly M).leadingCoeff⁻¹ ∈ ratSub p)
    (hGB : GoodBase R T xs ys lam Ls irrP)
    (hGP : GoodPl R T.Fc T.n T.I.Dc xs (S.PcE P hSF hV hζ j₀)) :
    primeCheck R T (redPrimeCert R T xs ys lam Ls irrP) = true ∧
    ∃ mm : ℕ, 0 < mm ∧ ∀ tx, (∀ j < P.pts.length, ∀ k < T.n,
        mm * ((S.PcE P hSF hV hζ j₀).rs j k *
          (S.PcE P hSF hV hζ j₀).Γp.getD ((S.PcE P hSF hV hζ j₀).rπ j k) 0) +
          (S.PcE P hSF hV hζ j₀).fN j * muD T.I.Dc ((S.PcE P hSF hV hζ j₀).fα j) 1 ≤ tx) →
      ∃ Q : PlaceCert.PrimeData p, Q.mp = mm ∧
        (S.PcE P hSF hV hζ j₀ tx).primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc (xs.map R.red) Q =
          true := by
  set Ds : ℕ → PlaceCert (NFC.NF M) := fun t ↦ S.PcE P hSF hV hζ j₀ t with hDs
  have hchk : ∀ t, (Ds t).Facts T.Fc T.n := fun t ↦ by
    rw [hTF, hTn]; exact PlaceCert.check_spec _ (S.PcE_check P hSF hV hζ j₀ hnd hinf0 t)
  have hprim := primeCheck_redPrimeCert R hR T xs ys lam Ls irrP hC hGB
  have hPF := primeCheck_spec R hprim
  -- the curve over `K`
  have hirr := (irr_all R φ hR T hC.glob _ hPF).2.2
  obtain ⟨hn0, hmon, hdeg, -⟩ := hC.glob.shape
  set SK := stdCurve (toB T.Fc) hmon (by rw [hdeg]; exact hn0) hirr with hSKdef
  have hSK : SK.F = toB T.Fc := rfl
  have hnSK : SK.F.natDegree = T.n := hdeg
  -- the refinements
  have href : ∀ t t', t ≤ t' → _ := fun t t' htt ↦ S.PcE_refines P hSF hV hζ j₀ htt
  have hfib : ∀ t, (Ds t).fib = (Ds 0).fib := fun t ↦ (href 0 t (Nat.zero_le t)).1
  have hrt : ∀ t, (Ds t).rt = (Ds 0).rt := fun t ↦ (href 0 t (Nat.zero_le t)).2.1
  have hΓp : ∀ t, (Ds t).Γp = (Ds 0).Γp := fun t ↦ (href 0 t (Nat.zero_le t)).2.2.1
  have hcΓ : ∀ t, (Ds t).cΓ = (Ds 0).cΓ := fun t ↦ (href 0 t (Nat.zero_le t)).2.2.2.1
  have hpl' : ∀ t, (Ds t).pl.length = (Ds 0).pl.length := fun t ↦
    (href 0 t (Nat.zero_le t)).2.2.2.2.1
  have hπ : ∀ t, ∀ π < (Ds 0).pl.length, (Ds t).pj π = (Ds 0).pj π ∧ (Ds t).pe π = (Ds 0).pe π ∧
      (Ds 0).pp π ≤ (Ds t).pp π ∧ (Ds 0).py π <+: (Ds t).py π := fun t ↦
    (href 0 t (Nat.zero_le t)).2.2.2.2.2
  have hlen : ∀ π < (Ds 0).pl.length, (Ds 0).pp π ≤ ((Ds 0).py π).length := fun π hπ' ↦
    (S.PcE_pp_facts P hSF hV hζ j₀ 0 π hπ').2
  have hfl : (Ds 0).fib.length = P.pts.length := S.PcE_fib_length P hSF hV hζ j₀ 0
  have htp : ∀ t, ∀ j < (Ds 0).fib.length, (Ds 0).tp.getD j 0 ≤ (Ds t).tp.getD j 0 := fun t j hj ↦
    (S.PcE_tp_ge P hSF hV hζ j₀ t j (by rw [← hfl]; exact hj)).2
  -- the checks without the multiplier
  have hpre0 : (Ds 0).primePre R T.Fc T.n T.I.Dc (xs.map R.red) = true := primePre_of_good R hR hpl hGP
  have hok := py_ok_family R hNF hM hlc (ok_of_goodLL R hGP.F) Ds hchk hfib hpl'
    (fun t π hπ' ↦ (hπ t π hπ').1) (fun t π hπ' ↦ (hπ t π hπ').2.1)
    (fun t π hπ' ↦ ⟨(hπ t π hπ').2.2.1,
      (S.PcE_pp_facts P hSF hV hζ j₀ t π (by rw [hpl' t]; exact hπ')).1⟩) hlen
    (fun t t' htt π hπ' ↦ ((href t t' htt).2.2.2.2.2 π (by rw [hpl' t]; exact hπ')).2.2.2)
    (fun π hπ' ↦ ⟨(hGP.α _ (hpl.facts.pl π hπ').1).1, fun c hc ↦ (hGP.py π hπ' c hc).1,
      (hGP.unit π hπ').2 (getD_ordC _ (rootCheck_spec (hpl.facts.pl π hπ').2.2).2.1)⟩)
  have hpreT : ∀ t, (Ds t).primePre R T.Fc T.n T.I.Dc (xs.map R.red) = true := fun t ↦
    primePre_refine R hpl.facts (hfib t) (hrt t) (hpl' t) (hπ t) hlen (htp t) (hok t) hpre0
  -- one multiplier for the family
  obtain ⟨mm, hmm, hfam⟩ := placeCheck_family R φ hR SK T hSK hC.glob _ hPF Ds
    (fun t ↦ by rw [hnSK]; exact hchk t) hfib hrt hΓp hcΓ hpl' hπ hlen hpreT
  refine ⟨hprim, mm, hmm, fun tx hbound ↦ ?_⟩
  have hDok : ∀ c ∈ T.I.Dc, R.ok c = true := fun c hc ↦ (hGP.Dg c hc).1
  have hNj : ∀ j < (Ds 0).fib.length, 0 < (Ds 0).fN j := fun j hj ↦ by
    obtain ⟨hπj, -, hs, hN, -⟩ := (hpl.facts.rt j hj).2 0 hC.n0
    rw [hN]; exact Nat.mul_pos hs (hpl.facts.pl _ hπj).2.1
  obtain ⟨Q, hQm, hQ⟩ := hfam tx
    (fun j hj ↦ (muD_red R hR hDok (hGP.α j hj).1 (hpl.Dne j hj) (hGP.μ j hj) (hNj j hj)).2)
    (fun j hj k hk ↦ by
      rw [(muD_red R hR hDok (hGP.α j hj).1 (hpl.Dne j hj) (hGP.μ j hj) (hNj j hj)).1,
        (muD_mul T.I.Dc _ (hNj j hj) (hpl.Dne j hj)).1]
      exact le_trans (hbound j (by rw [← hfl]; exact hj) k hk)
        (S.PcE_tp_ge P hSF hV hζ j₀ tx j (by rw [← hfl]; exact hj)).1)
  exact ⟨Q, hQm, hQ⟩

end CurveData

end PrimeSide

end Curves
