import RischTragerBronstein.Torsion.PcEFacts

/-!
# Genus zero: every residue divisor is torsion

* **`riemann_places_g0`**: Riemann's inequality in genus `0` (`∑ δ + 1 = n`): the principality
  test at `M Γ` holds with the exact bound `M c` at infinity (the unknowns exceed the conditions);
* **`genus_pos_of_nonTors`**: if the `j₀`-residue divisor is not torsion, the genus
  `∑ δ + 1 − n` is positive (else the test of `not_princTest_PcE` passes at `M = 1`).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section G0

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Riemann's inequality in genus `0`** (`∑ δ + 1 = n`): the principality test at `M Γ` holds
with the exact bound `M c` at infinity. -/
theorem riemann_places_g0 {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J P : Type*} [Fintype J] [Fintype P]
    (α : J → C) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (pj : P → J) (e : P → ℕ) (ρ : P → LaurentSeries C)
    (πr : J → Fin S.F.natDegree → P) (hπr : ∀ j k, pj (πr j k) = j)
    (hsurj : ∀ π, ∃ j k, πr j k = π)
    (sr : J → Fin S.F.natDegree → ℕ) (hsr : ∀ j k, 0 < sr j k)
    (hNr : ∀ j k, N j = sr j k * e (πr j k))
    (ζ : J → Fin S.F.natDegree → C) (hζ0 : ∀ j k, ζ j k ≠ 0) (hζN : ∀ j k, ζ j k ^ N j = 1)
    (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hrC : ∀ j k, rC j k = rot (ζ j k) (hζ0 j k) (lsub (sr j k) (hsr j k) (ρ (πr j k))))
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (ΓP : P → ℕ) (c : ℕ) (hdeg : ∑ π, ΓP π = c * S.F.natDegree) (M : ℕ)
    (hg0 : ∑ i, δ i + 1 = S.F.natDegree) :
    princTest δ (M * c) (Q := J × Fin S.F.natDegree) (fun q ↦ N q.1) (fun q ↦ α q.1)
      (fun q i ↦ basisSer B D (N q.1) (α q.1) (rC q.1 q.2) i)
      (fun q ↦ M * (sr q.1 q.2 * ΓP (πr q.1 q.2))) := by
  classical
  -- the basis series along the representatives have no poles
  have hσP : ∀ π i, LowerBd (basisSer B D (e π) (α (pj π)) (ρ π) i) 0 := by
    intro π i
    obtain ⟨j, k, rfl⟩ := hsurj π
    have h := S.basisSer_lowerBd_N hB (N j) (hN j) (α j) (rC j) (hsC j) k i
    rw [hrC, basisSer_rot_lsub B D (sr j k) (e (πr j k)) (N j) (hsr j k) (hNr j k) (ζ j k)
      (hζ0 j k) (hζN j k), lowerBd_rot_iff, show (0 : ℤ) = (sr j k : ℤ) * 0 by ring,
      lowerBd_lsub_iff] at h
    rwa [hπr]
  have hn : 0 < S.F.natDegree := by
    by_contra h0
    have h1 : S.F = 1 := Polynomial.eq_one_of_monic_natDegree_zero S.monic (by omega)
    have := S.root
    rw [h1, Polynomial.map_one, eval_one] at this
    exact one_ne_zero this
  have hcount : ∑ π, M * ΓP π < ∑ i, (M * c + 1 - δ i) := by
    have h1 : ∀ i, M * c + 1 ≤ (M * c + 1 - δ i) + δ i := fun i ↦ by omega
    have h2 : S.F.natDegree * (M * c + 1) ≤ ∑ i, (M * c + 1 - δ i) + ∑ i, δ i := by
      rw [← Finset.sum_add_distrib]
      calc S.F.natDegree * (M * c + 1) = ∑ _i : Fin S.F.natDegree, (M * c + 1) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ ↦ h1 i
    rw [← Finset.mul_sum, hdeg]
    have e1 : S.F.natDegree * (M * c + 1) = M * (c * S.F.natDegree) + S.F.natDegree := by ring
    omega
  obtain ⟨cc, hc0, hccdeg, hlb⟩ := exists_coords_vanishing δ (M * c) e
    (fun π ↦ α (pj π)) (fun π i ↦ basisSer B D (e π) (α (pj π)) (ρ π) i) hσP (fun π ↦ M * ΓP π)
    hcount
  refine ⟨cc, hc0, hccdeg, fun q ↦ ?_⟩
  obtain ⟨j, k⟩ := q
  -- along a conjugate root: the rotated, reparametrized series
  have hsum : ∑ i, branchSub (C := C) (K := C) (N j) (α j) (cc i) * basisSer B D (N j) (α j) (rC j k) i =
      rot (ζ j k) (hζ0 j k) (lsub (sr j k) (hsr j k) (∑ i, branchSub (C := C) (K := C) (e (πr j k))
        (α j) (cc i) * basisSer B D (e (πr j k)) (α j) (ρ (πr j k)) i)) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_mul, hrC, basisSer_rot_lsub B D (sr j k) (e (πr j k)) (N j) (hsr j k) (hNr j k)
      (ζ j k) (hζ0 j k) (hζN j k), branchSub_rot_lsub (sr j k) (e (πr j k)) (N j) (hsr j k)
      (hNr j k) (ζ j k) (hζ0 j k) (hζN j k)]
  show LowerBd (∑ i, branchSub (C := C) (K := C) (N j) (α j) (cc i) *
    basisSer B D (N j) (α j) (rC j k) i) _
  rw [hsum, lowerBd_rot_iff, show ((M * (sr j k * ΓP (πr j k)) : ℕ) : ℤ) =
    (sr j k : ℤ) * ((M * ΓP (πr j k) : ℕ) : ℤ) by push_cast; ring, lowerBd_lsub_iff]
  have := hlb (πr j k)
  rwa [hπr] at this

end CurveData

end G0

section Pos

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F))

include hSF hV hζ in
/-- **A non-torsion residue divisor forces positive genus.** -/
theorem genus_pos_of_nonTors (hnd : (P.pts.map Prod.fst).Nodup)
    (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0) (T : GlobalCert F) (hT : T.globalCheck = true)
    (hTF : T.Fc = P.Fc)
    (hNT : ∀ m, 0 < m → ∀ Λ : C →ₗ[ℚ] ℚ, (∀ r : F, Λ (ψ r) = coord j₀ r) →
      ∀ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 → ¬ S.TorsOrdStd (K := C) P ψ m w Λ) :
    ∑ i : Fin S.F.natDegree, T.I.δL.getD i 0 + 1 ≠ S.F.natDegree := by
  classical
  intro hg
  apply S.not_princTest_PcE P hSF hV hζ j₀ hnd hinf0 T hT hTF hNT 1 one_pos
  have hTf := globalCheck_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  have hSF' : S.F = (toB T.Fc).map (mapRingHom ψ) := by rw [hSF, hTF]
  have hnS : S.F.natDegree = T.n := by rw [hSF', hmon.natDegree_map, hdeg]
  have hBS : S.IsIntBasis C (fun j ↦ (toB (T.I.Bc.getD j [])).map (mapRingHom ψ))
      ((toPoly T.I.Dc).map ψ) (fun j ↦ T.I.δL.getD j 0) :=
    ibCheckR_spec (K := C) S T.Fc ψ hSF' T.n T.k hnS.symm T.I T.G hTf.ib (dvd_of_eq hTf.G_eq.symm)
  set m := P.pts.length
  set Φ := fun j : Fin m ↦ S.Φj P hSF hV j with hΦ
  have hζs : ∀ j : Fin m, IsPrimitiveRoot (ψ (ζj P hζ j)) (Φ j).N := fun j ↦
    S.ζj_spec P hSF hV hζ j
  set Pl := {q : Fin m × Fin S.F.natDegree // (Φ q.1).rep (hζs q.1) q.2 = q.2} with hPl
  have hn := S.natDegree_F_eq P ψ hSF hV
  refine S.riemann_places_g0 (K := C) hBS (J := Fin m) (P := Pl) (fun j ↦ ψ (P.pts[j]).1)
    (fun j ↦ (Φ j).N) (fun j ↦ (Φ j).hN) (fun q ↦ q.1.1)
    (fun q ↦ (Φ q.1.1).period (hζs q.1.1) q.1.2)
    (fun q ↦ ofPowerSeries ℤ C ((Φ q.1.1).placeSer (hζs q.1.1) q.1.2))
    (fun j k ↦ ⟨(j, (Φ j).rep (hζs j) k), (Φ j).rep_rep (hζs j) k⟩) (fun j k ↦ rfl)
    (fun q ↦ ⟨q.1.1, q.1.2, Subtype.ext (Prod.ext rfl q.2)⟩)
    (fun j k ↦ (Φ j).sIdx (hζs j) ((Φ j).rep (hζs j) k)) (fun j k ↦ (Φ j).sIdx_pos (hζs j) _)
    (fun j k ↦ ((Φ j).sIdx_mul (hζs j) _).symm)
    (fun j k ↦ (ψ (ζj P hζ j)) ^ ((Φ j).cExp (hζs j) k))
    (fun j k ↦ pow_ne_zero _ ((hζs j).ne_zero (Φ j).hN.ne'))
    (fun j k ↦ by
      rw [← pow_mul, mul_comm, pow_mul, show ψ (ζj P hζ j) ^ (Φ j).N = 1 from (hζs j).pow_eq_one,
        one_pow])
    (fun j k ↦ ofPowerSeries ℤ C ((Φ j).y k))
    (fun j k ↦ by rw [(Φ j).cExp_spec (hζs j) k, ofPS_conjPS])
    (fun j ↦ (congrArg (fun G : C[X][X] ↦ G.map (branchSub (K := C) (Φ j).N (ψ (P.pts[j]).1)))
      hSF).trans (Φ j).split)
    (fun q ↦ S.Γj P hSF hV hζ j₀ q.1.1 q.1.2) (∑ j, S.eLj P hSF hV hζ j₀ j) ?_ 1 hg
  -- the degree of the divisor
  have h := S.sum_Γj P hSF hV hζ j₀ hnd hinf0
  simp only [S.lpj_Γ_sum P hSF hV hζ] at h
  rw [← hn] at h
  have e : ∑ q : Pl, S.Γj P hSF hV hζ j₀ q.1.1 q.1.2 = ∑ j : Fin m, ∑ π ∈ Finset.univ.filter
      (fun π ↦ (Φ j).rep (hζs j) π = π), S.Γj P hSF hV hζ j₀ j π := by
    rw [(Finset.sum_subtype (Finset.univ.filter fun q : Fin m × Fin S.F.natDegree ↦
      (Φ q.1).rep (hζs q.1) q.2 = q.2) (fun x ↦ by simp)
      (fun q : Fin m × Fin S.F.natDegree ↦ S.Γj P hSF hV hζ j₀ q.1 q.2)).symm]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_filter]
  rw [e]
  exact_mod_cast h

end CurveData

end Pos

end Curves
