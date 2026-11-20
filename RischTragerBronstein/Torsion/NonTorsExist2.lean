import RischTragerBronstein.Torsion.NonTorsExist1
import RischTragerBronstein.Torsion.AutoField

/-!
# Non-torsion witnesses exist (2): the witness

**`exists_torsOKP`**: over a number field `ℚ[γ]/(M)` with integral `M`, a valid problem whose
`j₀`-residue divisor is not torsion (with the primitive roots of unity of the ramification
indices, distinct special points and vanishing computed residues above infinity), a global
certificate `T` without divisor data and characteristic-`0` base-point data (`Char0Base`,
`Char0Pl`) yield a non-torsion witness accepted by `torsOKP`: two large good primes `p ≠ q`, their
multipliers `m_p`, `m_q` (one for all precisions, `prime_side`), the place certificate `PcE tx`
with a precision slack `tx` above all the bounds, and the failed test at `m_p m_q Γ`.
-/

open Polynomial HahnSeries Filter EllQuad.QCoords IntermediateField

namespace Curves

open CPoly Sup

section Primes

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- **Certified reductions exist at arbitrarily large primes.** -/
lemma exists_redAtM_prime {mZ : List ℤ} (hint : Curves.intCoeffs M = some mZ) (T0 : ℕ) :
    ∃ p, T0 < p ∧ p.Prime ∧ ∃ R : RedFns p (NFC.NF M), redAtM M p = some R ∧ NFRed p R := by
  have hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ) := by
    unfold Curves.intCoeffs at hint
    split_ifs at hint with hall
    obtain rfl := Option.some.inj hint
    rw [← Sup.toPoly_mapHom, List.map_map]
    congr 1
    conv_lhs => rw [← List.map_id M]
    refine List.map_congr_left fun q hq ↦ ?_
    have := (List.all_eq_true.mp hall) q hq
    simp only [decide_eq_true_eq] at this
    simp [Function.comp_apply, Rat.coe_int_num_of_den_eq_one this]
  have hdeg : 0 < (toPoly mZ).natDegree := by
    have h := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible (Fact.out : Irreducible (toPoly M)))
    rwa [hmZ, natDegree_map_eq_of_injective (RingHom.injective_int _)] at h
  obtain ⟨p, hpT, hp, s, hs, hs'⟩ := exists_simple_root_prime (M := M) (toPoly mZ) hmZ hdeg T0
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s', hred, -, -⟩ := nfRedAt_eq (M := M) (mZl := mZ) hs hs'
  refine ⟨p, hpT, hp, nfFns p s', ?_, nfRed_nfFns p s'⟩
  simp [redAtM, hint, hred]

end Primes

section Witness

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb (NFC.NF M)) {ψ : (NFC.NF M) →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : (NFC.NF M), IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim (NFC.NF M)))

/-- **The non-torsion witness exists.** -/
theorem exists_torsOKP {mZ : List ℤ} (hint : Curves.intCoeffs M = some mZ) (hvalid : P.valid = true)
    (hnd : (P.pts.map Prod.fst).Nodup) (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0)
    (hNT : ∀ m, 0 < m → ∀ Λ : C →ₗ[ℚ] ℚ, (∀ r : NFC.NF M, Λ (ψ r) = coord j₀ r) →
      ∀ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 → ¬ S.TorsOrdStd (K := C) P ψ m w Λ)
    (T : GlobalCert (NFC.NF M)) (hT : T.globalCheck = true) (hTF : T.Fc = P.Fc) (hTn : T.n = P.n)
    (xs : List (NFC.NF M)) (ys : List (List (NFC.NF M))) (lam : List (List (NFC.NF M)))
    (Ls : List (List (List (NFC.NF M)))) (irrP : ℕ) (hC : Char0Base T xs ys lam Ls irrP)
    (hpl : Char0Pl T.Fc T.n T.I.Dc xs (S.PcE P hSF hV hζ j₀)) :
    ∃ tw : TorsWitP (NFC.NF M), torsOKP (redAtM M) P tw = true := by
  classical
  -- all large primes are good
  have hev := Filter.Eventually.and ((evG_goodBase T xs ys lam Ls irrP).and
    (evG_goodPl T.Fc T.n T.I.Dc xs (S.PcE P hSF hV hζ j₀))) (ev_nfM (M := M))
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hev
  obtain ⟨p, hpT, hp, Rp, hRp, hNFp⟩ := exists_redAtM_prime hint T0
  obtain ⟨q, hqT, hq, Rq, hRq, hNFq⟩ := exists_redAtM_prime hint p
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨φp, hφp⟩ := redAtM_valid M p Rp hRp
  obtain ⟨φq, hφq⟩ := redAtM_valid M q Rq hRq
  have gp := hT0 p hpT.le
  have gq := hT0 q (by omega)
  obtain ⟨hGBp, hGPp⟩ := gp.1 Rp hNFp
  obtain ⟨hMp, hlcp⟩ := gp.2 ⟨hp⟩
  obtain ⟨hGBq, hGPq⟩ := gq.1 Rq hNFq
  obtain ⟨hMq, hlcq⟩ := gq.2 ⟨hq⟩
  obtain ⟨hprimp, mmp, hmmp, hfp⟩ := S.prime_side P hSF hV hζ j₀ hnd hinf0 T hTF hTn xs ys lam Ls
    irrP hC hpl Rp hNFp φp hφp hMp hlcp hGBp hGPp
  obtain ⟨hprimq, mmq, hmmq, hfq⟩ := S.prime_side P hSF hV hζ j₀ hnd hinf0 T hTF hTn xs ys lam Ls
    irrP hC hpl Rq hNFq φq hφq hMq hlcq hGBq hGPq
  -- the precision slack
  set D0 := S.PcE P hSF hV hζ j₀ with hD0
  set bnd : ℕ → ℕ := fun m ↦ ∑ j ∈ Finset.range P.pts.length, ∑ k ∈ Finset.range T.n,
    (m * (D0.rs j k * D0.Γp.getD (D0.rπ j k) 0) + D0.fN j * muD T.I.Dc (D0.fα j) 1) with hbnd
  have hbnd_le : ∀ m, ∀ j < P.pts.length, ∀ k < T.n,
      m * (D0.rs j k * D0.Γp.getD (D0.rπ j k) 0) + D0.fN j * muD T.I.Dc (D0.fα j) 1 ≤ bnd m := by
    intro m j hj k hk
    refine le_trans ?_ (Finset.single_le_sum (f := fun j ↦ ∑ k ∈ Finset.range T.n,
      (m * (D0.rs j k * D0.Γp.getD (D0.rπ j k) 0) + D0.fN j * muD T.I.Dc (D0.fα j) 1))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hj))
    exact Finset.single_le_sum (f := fun k ↦
      m * (D0.rs j k * D0.Γp.getD (D0.rπ j k) 0) + D0.fN j * muD T.I.Dc (D0.fα j) 1)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hk)
  set tx := bnd mmp + bnd mmq + bnd (mmp * mmq) with htx
  obtain ⟨Qp, hQpm, hQp⟩ := hfp tx fun j hj k hk ↦ le_trans (hbnd_le mmp j hj k hk) (by omega)
  obtain ⟨Qq, hQqm, hQq⟩ := hfq tx fun j hj k hk ↦ le_trans (hbnd_le mmq j hj k hk) (by omega)
  obtain ⟨hfib, hrt, hΓp, -, -, -⟩ := S.PcE_refines P hSF hV hζ j₀ (Nat.zero_le tx)
  rw [← hD0] at hfib hrt hΓp
  set Pc := S.PcE P hSF hV hζ j₀ tx with hPc
  -- the failed test over the coefficient field
  have hfl : D0.fib.length = P.pts.length := S.PcE_fib_length P hSF hV hζ j₀ 0
  have hNj : ∀ j < D0.fib.length, 0 < D0.fN j := fun j hj ↦ by
    obtain ⟨hπj, -, hs, hN, -⟩ := (hpl.facts.rt j hj).2 0 hC.n0
    rw [hN]; exact Nat.mul_pos hs (hpl.facts.pl _ hπj).2.1
  have hside : testSideN T.n T.I.Dc Pc.αs (Pc.fcerts T.n) (Pc.bL T.n (mmp * mmq)) = true := by
    have hfα : ∀ j, Pc.fα j = D0.fα j := fun j ↦ by simp only [PlaceCert.fα, hfib]
    have hfN : ∀ j, Pc.fN j = D0.fN j := fun j ↦ by simp only [PlaceCert.fN, hfib]
    have hrs : ∀ j k, Pc.rs j k = D0.rs j k := fun j k ↦ by simp only [PlaceCert.rs, hrt]
    have hrπ : ∀ j k, Pc.rπ j k = D0.rπ j k := fun j k ↦ by simp only [PlaceCert.rπ, hrt]
    refine testSideN_of_tpM _ _ _ _ (fun j hj ↦ ?_) (fun j hj k hk ↦ ?_)
    · rw [hfib] at hj
      rw [hfα, hfN]
      exact (muD_mul T.I.Dc _ (hNj j hj) (hpl.Dne j hj)).2
    · rw [hfib] at hj
      rw [hfα, hfN, hrs, hrπ, hΓp, (muD_mul T.I.Dc _ (hNj j hj) (hpl.Dne j hj)).1]
      have h1 := hbnd_le (mmp * mmq) j (by rw [← hfl]; exact hj) k hk
      have h2 : tx ≤ Pc.tp.getD j 0 := (S.PcE_tp_ge P hSF hV hζ j₀ tx j (by rw [← hfl]; exact hj)).1
      have h3 : bnd (mmp * mmq) ≤ tx := by rw [htx]; omega
      omega
  have hNP := S.nonPrincOK_PcE P hSF hV hζ j₀ tx hnd hinf0 T hT hTF hNT (mmp * mmq)
    (Nat.mul_pos hmmp hmmq) 0 [] hside
  -- the witness
  refine ⟨⟨T, Pc, S.eLE P hSF hV hζ j₀, S.sden P hSF hV hζ j₀, j₀, p, q,
    redPrimeCert Rp T xs ys lam Ls irrP, redPrimeCert Rq T xs ys lam Ls irrP, Qp, Qq, 0, []⟩, ?_⟩
  have hcheck : Pc.check T.Fc T.n = true := by
    rw [hTF, hTn]; exact S.PcE_check P hSF hV hζ j₀ hnd hinf0 tx
  have htors := S.PcE_torsRes P hSF hV hζ j₀ T hnd hinf0 hTF hTn tx
  have hokp : primeOKP (redAtM M) T Pc p (redPrimeCert Rp T xs ys lam Ls irrP) Qp = true := by
    simp only [primeOKP, dif_pos hp, hRp, Bool.and_eq_true]
    exact ⟨hprimp, hQp⟩
  have hokq : primeOKP (redAtM M) T Pc q (redPrimeCert Rq T xs ys lam Ls irrP) Qq = true := by
    simp only [primeOKP, dif_pos hq, hRq, Bool.and_eq_true]
    exact ⟨hprimq, hQq⟩
  simp only [torsOKP, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hvalid, hT⟩, hcheck⟩, htors⟩, by omega⟩, hokp⟩, hokq⟩, Or.inl ?_⟩
  rw [hQpm, hQqm]
  exact hNP

end CurveData

end Witness

end Curves
