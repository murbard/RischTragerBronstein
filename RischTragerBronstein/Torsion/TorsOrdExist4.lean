import RischTragerBronstein.Torsion.TorsOrdExist3

/-!
# Torsion data from principal divisors (4): the failed-test certificate

* `princTest_castN`, `princTest_equivQ`: the principality test is invariant under renaming the
  basis indices (`Fin n = Fin n'`) and the rows (`Q ≃ Q'`);
* **`nonPrincOK_PcE`**: for a non-torsion `j₀`-residue divisor, the failed-test certificate
  `nonPrincOK` passes for every multiple `Mt > 0` of the place divisor of `PcE`, as soon as the
  precisions are large enough (`testSideN`).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Reindex

variable {C : Type*} [Field C]

lemma princTest_castN {n n' : ℕ} (h : n = n') (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} (e : Q → ℕ)
    (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) :
    princTest δ M e a σ b ↔
      princTest (fun i : Fin n' ↦ δ (Fin.cast h.symm i)) M e a (fun q i ↦ σ q (Fin.cast h.symm i)) b := by
  subst h; rfl

lemma princTest_equivQ {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q Q' : Type*} (eq : Q' ≃ Q) (e : Q → ℕ)
    (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) :
    princTest δ M e a σ b ↔ princTest δ M (e ∘ eq) (a ∘ eq) (σ ∘ eq) (b ∘ eq) := by
  constructor
  · rintro ⟨cc, h0, hd, hq⟩; exact ⟨cc, h0, hd, fun q ↦ hq (eq q)⟩
  · rintro ⟨cc, h0, hd, hq⟩
    refine ⟨cc, h0, hd, fun q ↦ ?_⟩
    have := hq (eq.symm q)
    simpa using this

end Reindex

section PcEAcc

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F)) (tx : ℕ)

lemma PcE_fib_length : (S.PcE P hSF hV hζ j₀ tx).fib.length = P.pts.length := by
  simp [PcE, assemble, CurveData.Ls]

lemma PcE_αs_length : (S.PcE P hSF hV hζ j₀ tx).αs.length = P.pts.length := by
  simp [PlaceCert.αs, PcE_fib_length]

variable {j : ℕ} (hj : j < P.pts.length)
include hj

lemma PcE_Ls (hjL : j < (S.Ls P hSF hV hζ j₀ tx).length) :
    (S.Ls P hSF hV hζ j₀ tx).getD j locDef = S.lpj P hSF hV hζ ⟨j, hj⟩ (S.Γj P hSF hV hζ j₀ ⟨j, hj⟩) tx :=
  S.Ls_getD P hSF hV hζ j₀ j hj tx

lemma PcE_fN : (S.PcE P hSF hV hζ j₀ tx).fN j = (S.Φj P hSF hV ⟨j, hj⟩).N := by
  have hjL : j < (S.Ls P hSF hV hζ j₀ tx).length := by rw [S.Ls_length P hSF hV hζ j₀ tx]; exact hj
  rw [PcE, assemble_fN _ j hjL, S.PcE_Ls P hSF hV hζ j₀ tx hj hjL]; rfl

lemma PcE_fα : (S.PcE P hSF hV hζ j₀ tx).fα j = (P.pts[j]).1 := by
  have hjL : j < (S.Ls P hSF hV hζ j₀ tx).length := by rw [S.Ls_length P hSF hV hζ j₀ tx]; exact hj
  rw [PcE, assemble_fα _ j hjL, S.PcE_Ls P hSF hV hζ j₀ tx hj hjL]; rfl

lemma PcE_tp : (S.PcE P hSF hV hζ j₀ tx).tp.getD j 0 =
    (S.Φj P hSF hV ⟨j, hj⟩).tpF + (txj P ⟨j, hj⟩ + tx) := by
  have hjL : j < (S.Ls P hSF hV hζ j₀ tx).length := by rw [S.Ls_length P hSF hV hζ j₀ tx]; exact hj
  rw [PcE, assemble_tp _ j hjL, S.PcE_Ls P hSF hV hζ j₀ tx hj hjL]; rfl

variable {k : ℕ} (hk : k < S.F.natDegree)
include hk

lemma PcE_rts (hjL : j < (S.Ls P hSF hV hζ j₀ tx).length) :
    k < ((S.Ls P hSF hV hζ j₀ tx).getD j locDef).rts.length := by
  rw [S.PcE_Ls P hSF hV hζ j₀ tx hj hjL]
  simp only [lpj, SplitFibre.locPlaces, List.length_map, List.length_finRange]; exact hk

lemma PcE_apx : (S.PcE P hSF hV hζ j₀ tx).apx j k = S.apxj P hSF hV hζ ⟨j, hj⟩ k tx := by
  have hjL : j < (S.Ls P hSF hV hζ j₀ tx).length := by rw [S.Ls_length P hSF hV hζ j₀ tx]; exact hj
  have hkL := S.PcE_rts P hSF hV hζ j₀ tx hj hk hjL
  have hLj := S.PcE_Ls P hSF hV hζ j₀ tx hj hjL
  have hidx : ((S.Ls P hSF hV hζ j₀ tx).getD j locDef).idx k <
      ((S.Ls P hSF hV hζ j₀ tx).getD j locDef).pls.length := by
    rw [hLj]; unfold lpj
    rw [SplitFibre.lp_idx _ _ _ _ _ _ _ k hk, SplitFibre.lp_pls_length]
    exact (S.Φj P hSF hV ⟨j, hj⟩).idxOf_lt _ ⟨k, hk⟩
  rw [PlaceCert.apx, PcE, assemble_rζ _ j hjL k hkL, assemble_rs _ j hjL k hkL,
    assemble_rπ _ j hjL k hkL, assemble_py _ j hjL _ hidx, hLj]
  rfl

lemma PcE_rsΓ : (S.PcE P hSF hV hζ j₀ tx).rs j k * (S.PcE P hSF hV hζ j₀ tx).Γp.getD
      ((S.PcE P hSF hV hζ j₀ tx).rπ j k) 0 =
    (S.Φj P hSF hV ⟨j, hj⟩).sIdx (S.ζj_spec P hSF hV hζ ⟨j, hj⟩)
      ((S.Φj P hSF hV ⟨j, hj⟩).rep (S.ζj_spec P hSF hV hζ ⟨j, hj⟩) ⟨k, hk⟩) *
      S.Γj P hSF hV hζ j₀ ⟨j, hj⟩ ((S.Φj P hSF hV ⟨j, hj⟩).rep (S.ζj_spec P hSF hV hζ ⟨j, hj⟩) ⟨k, hk⟩) := by
  have hjL : j < (S.Ls P hSF hV hζ j₀ tx).length := by rw [S.Ls_length P hSF hV hζ j₀ tx]; exact hj
  have hkL := S.PcE_rts P hSF hV hζ j₀ tx hj hk hjL
  have hLj := S.PcE_Ls P hSF hV hζ j₀ tx hj hjL
  have hlt := (S.Φj P hSF hV ⟨j, hj⟩).idxOf_lt (S.ζj_spec P hSF hV hζ ⟨j, hj⟩) ⟨k, hk⟩
  have hidx : ((S.Ls P hSF hV hζ j₀ tx).getD j locDef).idx k <
      ((S.Ls P hSF hV hζ j₀ tx).getD j locDef).pls.length := by
    rw [hLj]; unfold lpj
    rw [SplitFibre.lp_idx _ _ _ _ _ _ _ k hk, SplitFibre.lp_pls_length]; exact hlt
  have hΓl : ∀ L' ∈ S.Ls P hSF hV hζ j₀ tx, L'.Γ.length = L'.pls.length := by
    intro L' hL'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL'
    simp [lpj, SplitFibre.locPlaces]
  rw [PcE, assemble_rs _ j hjL k hkL, assemble_rπ _ j hjL k hkL, assemble_Γp _ hΓl j hjL _ hidx, hLj]
  unfold lpj
  rw [SplitFibre.lp_s _ _ _ _ _ _ _ k hk, SplitFibre.lp_idx _ _ _ _ _ _ _ k hk,
    SplitFibre.lp_Γ _ _ _ _ _ _ _ _ hlt, (S.Φj P hSF hV ⟨j, hj⟩).getElem_idxOf]

end CurveData

end PcEAcc

section NP

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F)) (tx : ℕ)

/-- **The failed-test certificate for a non-torsion residue divisor.** -/
theorem nonPrincOK_PcE (hnd : (P.pts.map Prod.fst).Nodup)
    (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0) (T : GlobalCert F) (hT : T.globalCheck = true)
    (hTF : T.Fc = P.Fc)
    (hNT : ∀ m, 0 < m → ∀ Λ : C →ₗ[ℚ] ℚ, (∀ r : F, Λ (ψ r) = coord j₀ r) →
      ∀ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 → ¬ S.TorsOrdStd (K := C) P ψ m w Λ)
    (Mt : ℕ) (hMt : 0 < Mt) (Pb : ℕ) (Lm : List (List F))
    (hside : testSideN T.n T.I.Dc (S.PcE P hSF hV hζ j₀ tx).αs ((S.PcE P hSF hV hζ j₀ tx).fcerts T.n)
      ((S.PcE P hSF hV hζ j₀ tx).bL T.n Mt) = true) :
    nonPrincOK T.n (Mt * (S.PcE P hSF hV hζ j₀ tx).cΓ) Pb T.I.δL T.I.Bc T.I.Dc
      (S.PcE P hSF hV hζ j₀ tx).αs ((S.PcE P hSF hV hζ j₀ tx).fcerts T.n)
      ((S.PcE P hSF hV hζ j₀ tx).bL T.n Mt) Lm = true := by
  classical
  have hTf := globalCheck_spec hT
  obtain ⟨-, hmon, hdeg, -⟩ := hTf.shape
  have hTn : S.F.natDegree = T.n := by rw [hSF, ← hTF, hmon.natDegree_map, hdeg]
  set D := S.PcE P hSF hV hζ j₀ tx with hD
  have hαl : D.αs.length = P.pts.length := S.PcE_αs_length P hSF hV hζ j₀ tx
  have hfl : D.fib.length = P.pts.length := S.PcE_fib_length P hSF hV hζ j₀ tx
  set Y : Fin D.αs.length → Fin T.n → PowerSeries C := fun j k ↦
    (S.Φj P hSF hV (Fin.cast hαl j)).y (Fin.cast hTn.symm k) with hY
  have hfc : ∀ j : Fin D.αs.length, (D.fcerts T.n).getD j ⟨1, [], 0⟩ =
      ⟨D.fN j, (List.range T.n).map (D.apx j), D.tp.getD j 0⟩ := fun j ↦
    D.fcerts_getD _ _ (by rw [hfl, ← hαl]; exact j.2)
  have hfcN : ∀ j < P.pts.length, (D.fcerts T.n).getD j ⟨1, [], 0⟩ =
      ⟨D.fN j, (List.range T.n).map (D.apx j), D.tp.getD j 0⟩ := fun j hj ↦
    D.fcerts_getD _ _ (by rw [hfl]; exact hj)
  refine nonPrincOK_complete T.n (Mt * D.cΓ) T.I.δL T.I.Bc T.I.Dc D.αs (D.fcerts T.n) (D.bL T.n Mt)
    ψ Pb Lm hside Y (fun j k ↦ ?_) (fun htest ↦ ?_)
  · -- the approximations
    have hj : (j : ℕ) < P.pts.length := by rw [← hαl]; exact j.2
    have hk : (k : ℕ) < S.F.natDegree := by rw [hTn]; exact k.2
    rw [hfc j]
    have e1 : ((List.range T.n).map (D.apx j)).getD k [] = D.apx j k := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    simp only [e1]
    rw [S.PcE_tp P hSF hV hζ j₀ tx hj, S.PcE_apx P hSF hV hζ j₀ tx hj hk]
    exact (S.Φj P hSF hV ⟨j, hj⟩).lp_approx (S.ζj_spec P hSF hV hζ ⟨j, hj⟩) (S.Φj_a P hSF hV ⟨j, hj⟩)
      (txj P ⟨j, hj⟩ + tx) (S.Γj P hSF hV hζ j₀ ⟨j, hj⟩) rfl (S.hpre_j P hSF hV hζ ⟨j, hj⟩ tx) ⟨k, hk⟩
  · -- the test
    apply S.not_princTest_PcE P hSF hV hζ j₀ hnd hinf0 T hT hTF hNT Mt hMt
    have h1 := (princTest_castN hTn.symm _ _ _ _ _ _).mp htest
    have h2 := (princTest_equivQ _ _ ((finCongr hαl.symm).prodCongr (finCongr hTn)) _ _ _ _).mp h1
    refine princTest_congr (fun i ↦ ?_) (fun q ↦ ?_) (fun q ↦ ?_) (fun q i ↦ ?_) (fun q ↦ ?_) h2
    · rfl
    · simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, finCongr_apply, Fin.val_cast]
      rw [hfcN _ q.1.2]
      exact S.PcE_fN P hSF hV hζ j₀ tx q.1.2
    · simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, finCongr_apply, Fin.val_cast]
      rw [D.αs_getD _ (by rw [hfl]; exact q.1.2), S.PcE_fα P hSF hV hζ j₀ tx q.1.2]
      rfl
    · simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, finCongr_apply, Fin.val_cast]
      rw [hfcN _ q.1.2, S.PcE_fN P hSF hV hζ j₀ tx q.1.2, D.αs_getD _ (by rw [hfl]; exact q.1.2),
        S.PcE_fα P hSF hV hζ j₀ tx q.1.2]
      simp only [hY, Fin.cast_cast, Fin.cast_eq_self]
      rfl
    · simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, finCongr_apply, Fin.val_cast]
      rw [D.bL_getD _ _ _ _ (by rw [hfl]; exact q.1.2) (by rw [← hTn]; exact q.2.2),
        S.PcE_rsΓ P hSF hV hζ j₀ tx q.1.2 q.2.2]

end CurveData

end NP

end Curves
