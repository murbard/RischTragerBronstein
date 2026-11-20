import RischTragerBronstein.Torsion.PicTorsion2
import RischTragerBronstein.Torsion.RamStep
import RischTragerBronstein.Torsion.Conj

/-!
# Divisor classes of degree `0` over a finite field have finite order (unramified places)

**Riemann's inequality in the explicit model** (`riemann_unram`): at places with `N = 1`, the
principality test with pole bound `M c + s` (`s = ∑ δᵢ`) and zeros `M Γ` has more unknowns
(`n (M c + s + 1) − ∑ δᵢ`) than conditions (`M c n`), so it passes. With `principal_iff_test` and
`exists_principal_mul`: **`exists_principal_test_unram`** — over a finite field, for every divisor
`Γ − c ∞ₓ` supported at unramified points, some multiple passes the principality test (the
multiplier `m_p` of the non-torsion certificates exists).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Conjugates

variable {C : Type*} [Field C]

/-- `x = a + Tᴺ` along a conjugate `rot ζ (lsub s ρ)` of a branch at level `e` (`N = s e`). -/
lemma branchSub_rot_lsub (s e N : ℕ) (hs : 0 < s) (hN : N = s * e) (ζ : C) (hζ : ζ ≠ 0)
    (hζN : ζ ^ N = 1) (a : C) (P : C[X]) :
    branchSub (C := C) (K := C) N a P = rot ζ hζ (lsub s hs (branchSub (C := C) (K := C) e a P)) := by
  have h1 := lsub_comp_branchSub (C := C) (K := C) s hs e a
  have h2 := rot_branchSub (C := C) ζ hζ N hζN a
  have e1 : lsub s hs (branchSub (C := C) (K := C) e a P) = branchSub (e * s) a P :=
    congrArg (fun φ : C[X] →+* LaurentSeries C ↦ φ P) h1
  rw [e1, show e * s = N by rw [hN, mul_comm]]
  exact (congrArg (fun φ : C[X] →+* LaurentSeries C ↦ φ P) h2).symm

/-- **The basis series along a conjugate branch.** -/
lemma basisSer_rot_lsub {n : ℕ} (B : Fin n → C[X][X]) (D : C[X]) (s e N : ℕ) (hs : 0 < s)
    (hN : N = s * e) (ζ : C) (hζ : ζ ≠ 0) (hζN : ζ ^ N = 1) (a : C) (ρ : LaurentSeries C)
    (i : Fin n) :
    basisSer B D N a (rot ζ hζ (lsub s hs ρ)) i = rot ζ hζ (lsub s hs (basisSer B D e a ρ i)) := by
  set h : LaurentSeries C →+* LaurentSeries C := (rot ζ hζ).comp (lsub s hs) with hh
  have hb : branchSub (C := C) (K := C) N a = h.comp (branchSub e a) :=
    RingHom.ext fun P ↦ branchSub_rot_lsub s e N hs hN ζ hζ hζN a P
  show ((B i).map (branchSub N a)).eval (h ρ) * (branchSub N a D)⁻¹ =
    h (((B i).map (branchSub e a)).eval ρ * (branchSub e a D)⁻¹)
  rw [hb, ← Polynomial.map_map, eval_map, eval₂_at_apply, RingHom.comp_apply, map_mul, map_inv₀]
  rfl

end Conjugates

section Riemann

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Riemann's inequality at unramified places.** -/
theorem riemann_unram {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J : Type*} [Fintype J] (α : J → C)
    (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) 1 (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ)
    (hdeg : ∑ j, ∑ k, ΓC j k = c * S.F.natDegree) (M : ℕ) :
    princTest δ (M * c + ∑ i, δ i) (Q := J × Fin S.F.natDegree) (fun _ ↦ 1) (fun q ↦ α q.1)
      (fun q i ↦ basisSer B D 1 (α q.1) (rC q.1 q.2) i) (fun q ↦ M * ΓC q.1 q.2) := by
  classical
  refine princTest_of_card_lt δ _ _ _ _ _ (fun q i ↦ S.basisSer_lowerBd_N hB 1 one_pos _ _ (hsC q.1)
    q.2 i) ?_
  -- conditions: `M c n`; unknowns: `n (M c + s + 1) − s`
  have hrows : ∑ q : J × Fin S.F.natDegree, M * ΓC q.1 q.2 = M * (c * S.F.natDegree) := by
    rw [Fintype.sum_prod_type, ← hdeg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
  have hcols : ∑ i, (M * c + ∑ i, δ i + 1 - δ i) + ∑ i, δ i =
      S.F.natDegree * (M * c + ∑ i, δ i + 1) := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (by
      have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ Nat.zero_le (δ j))
        (Finset.mem_univ i)
      omega)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hn : 0 < S.F.natDegree := by
    by_contra h0
    have h1 : S.F = 1 := Polynomial.eq_one_of_monic_natDegree_zero S.monic (by omega)
    have := S.root
    rw [h1, Polynomial.map_one, eval_one] at this
    exact one_ne_zero this
  rw [hrows]
  have e : S.F.natDegree * (M * c + ∑ i, δ i + 1) =
      M * (c * S.F.natDegree) + S.F.natDegree * ∑ i, δ i + S.F.natDegree := by ring
  have hle : ∑ i, δ i ≤ S.F.natDegree * ∑ i, δ i := Nat.le_mul_of_pos_left _ hn
  linarith

/-- **Riemann's inequality at arbitrary places**: the roots above `α_j` are conjugates
`rot ζ (lsub s ρ_π)` of place representatives `ρ_π` (at `x = α + T^{e_π}`, `N = s e_π`), with
multiplicities `s · Γ_π`; imposing the conditions along the representatives only (`∑ M Γ_π = M c n`
of them) gives the test. -/
theorem riemann_places {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
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
    (ΓP : P → ℕ) (c : ℕ) (hdeg : ∑ π, ΓP π = c * S.F.natDegree) (M : ℕ) :
    princTest δ (M * c + ∑ i, δ i) (Q := J × Fin S.F.natDegree) (fun q ↦ N q.1) (fun q ↦ α q.1)
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
  have hcount : ∑ π, M * ΓP π < ∑ i, (M * c + ∑ i, δ i + 1 - δ i) := by
    have hcols : ∑ i, (M * c + ∑ i, δ i + 1 - δ i) + ∑ i, δ i =
        S.F.natDegree * (M * c + ∑ i, δ i + 1) := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (by
        have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ Nat.zero_le (δ j))
          (Finset.mem_univ i)
        omega)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← Finset.mul_sum, hdeg]
    have e1 : S.F.natDegree * (M * c + ∑ i, δ i + 1) =
        M * (c * S.F.natDegree) + S.F.natDegree * ∑ i, δ i + S.F.natDegree := by ring
    have hle : ∑ i, δ i ≤ S.F.natDegree * ∑ i, δ i := Nat.le_mul_of_pos_left _ hn
    linarith
  obtain ⟨cc, hc0, hccdeg, hlb⟩ := exists_coords_vanishing δ (M * c + ∑ i, δ i) e
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

variable [IsAlgClosed K] [Fintype C]

/-- **Divisor classes of degree `0` supported at unramified points have finite order** (over a
finite field): some positive multiple passes the principality test. -/
theorem exists_principal_test_unram (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J : Type*} [Fintype J] (α : J → C)
    (hα : Function.Injective α) (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) 1 (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (hinj : ∀ j, Function.Injective fun k ↦ lmap (algebraMap C K) (rC j k))
    (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ)
    (hdeg : ∑ j, ∑ k, ΓC j k = c * S.F.natDegree) :
    ∃ m, 0 < m ∧ princTest δ (m * c) (Q := J × Fin S.F.natDegree) (fun _ ↦ 1) (fun q ↦ α q.1)
      (fun q i ↦ basisSer B D 1 (α q.1) (rC q.1 q.2) i) (fun q ↦ m * ΓC q.1 q.2) := by
  classical
  -- the multiplicities on the roots over `K`
  set Γf : J → LaurentSeries K → ℕ := fun j ↦
    Function.extend (fun k ↦ lmap (algebraMap C K) (rC j k)) (ΓC j) 0 with hΓf
  have hΓk : ∀ j k, Γf j (lmap (algebraMap C K) (rC j k)) = ΓC j k :=
    fun j k ↦ (hinj j).extend_apply _ _ k
  have hdΓ : ∀ j, ((List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k)).map (Γf j)).sum =
      1 * ∑ k, ΓC j k := by
    intro j
    rw [List.map_ofFn, List.sum_ofFn, one_mul]
    exact Finset.sum_congr rfl fun k _ ↦ hΓk j k
  -- Riemann's inequality, as principal functions
  have hR : ∀ M : ℕ, ∃ u : C⟮S.x⟯⟮S.y⟯, u ≠ 0 ∧ S.DivGE α (fun _ ↦ 1) (fun _ ↦ one_pos)
      (fun j ↦ List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k))
      (fun j ↦ S.split_lmap 1 (α j) (rC j) (hsC j)) (fun j r ↦ M * Γf j r) (M * c + ∑ i, δ i) u :=
    fun M ↦ (S.principal_iff_test hB α (fun _ ↦ 1) (fun _ ↦ one_pos) rC hsC (fun j k ↦ M * ΓC j k)
      (fun j r ↦ M * Γf j r) (fun j k ↦ by rw [hΓk]) (M * c + ∑ i, δ i)).mpr
      (S.riemann_unram hB α rC hsC ΓC c hdeg M)
  obtain ⟨m, hm, γ, hγ0, hγ⟩ := S.exists_principal_mul α (fun _ ↦ 1) (fun _ ↦ one_pos)
    (fun j ↦ List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k))
    (fun j ↦ S.split_lmap 1 (α j) (rC j) (hsC j)) hBr hBI hα Γf (fun j ↦ ∑ k, ΓC j k) hdΓ c hdeg
    (∑ i, δ i) hR
  exact ⟨m, hm, (S.principal_iff_test hB α (fun _ ↦ 1) (fun _ ↦ one_pos) rC hsC
    (fun j k ↦ m * ΓC j k) (fun j r ↦ m * Γf j r) (fun j k ↦ by rw [hΓk]) (m * c)).mp
    ⟨γ, hγ0, hγ⟩⟩

/-- **Divisor classes of degree `0` have finite order** (over a finite field, divisors at arbitrary
places): some positive multiple passes the principality test — the multiplier `m_p` of the
non-torsion certificates at places always exists. -/
theorem exists_principal_test_places (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J P : Type*} [Fintype J] [Fintype P]
    (α : J → C) (hα : Function.Injective α) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (pj : P → J) (e : P → ℕ) (ρ : P → LaurentSeries C)
    (πr : J → Fin S.F.natDegree → P) (hπr : ∀ j k, pj (πr j k) = j)
    (hsurj : ∀ π, ∃ j k, πr j k = π)
    (sr : J → Fin S.F.natDegree → ℕ) (hsr : ∀ j k, 0 < sr j k)
    (hNr : ∀ j k, N j = sr j k * e (πr j k))
    (ζ : J → Fin S.F.natDegree → C) (hζ0 : ∀ j k, ζ j k ≠ 0) (hζN : ∀ j k, ζ j k ^ N j = 1)
    (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hrC : ∀ j k, rC j k = rot (ζ j k) (hζ0 j k) (lsub (sr j k) (hsr j k) (ρ (πr j k))))
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (hinj : ∀ j, Function.Injective fun k ↦ lmap (algebraMap C K) (rC j k))
    (ΓP : P → ℕ) (c : ℕ) (hplaces : ∑ π, ΓP π = c * S.F.natDegree) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ∑ k, sr j k * ΓP (πr j k) = N j * dΓ j)
    (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree) :
    ∃ m, 0 < m ∧ princTest δ (m * c) (Q := J × Fin S.F.natDegree) (fun q ↦ N q.1) (fun q ↦ α q.1)
      (fun q i ↦ basisSer B D (N q.1) (α q.1) (rC q.1 q.2) i)
      (fun q ↦ m * (sr q.1 q.2 * ΓP (πr q.1 q.2))) := by
  classical
  set Γf : J → LaurentSeries K → ℕ := fun j ↦
    Function.extend (fun k ↦ lmap (algebraMap C K) (rC j k)) (fun k ↦ sr j k * ΓP (πr j k)) 0
    with hΓf
  have hΓk : ∀ j k, Γf j (lmap (algebraMap C K) (rC j k)) = sr j k * ΓP (πr j k) :=
    fun j k ↦ (hinj j).extend_apply _ _ k
  have hdΓ' : ∀ j, ((List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k)).map (Γf j)).sum =
      N j * dΓ j := by
    intro j
    rw [List.map_ofFn, List.sum_ofFn, ← hdΓ j]
    exact Finset.sum_congr rfl fun k _ ↦ hΓk j k
  have hR : ∀ M : ℕ, ∃ u : C⟮S.x⟯⟮S.y⟯, u ≠ 0 ∧ S.DivGE α N hN
      (fun j ↦ List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k))
      (fun j ↦ S.split_lmap (N j) (α j) (rC j) (hsC j)) (fun j r ↦ M * Γf j r) (M * c + ∑ i, δ i) u :=
    fun M ↦ (S.principal_iff_test hB α N hN rC hsC (fun j k ↦ M * (sr j k * ΓP (πr j k)))
      (fun j r ↦ M * Γf j r) (fun j k ↦ by rw [hΓk]) (M * c + ∑ i, δ i)).mpr
      (S.riemann_places hB α N hN pj e ρ πr hπr hsurj sr hsr hNr ζ hζ0 hζN rC hrC hsC ΓP c hplaces M)
  obtain ⟨m, hm, γ, hγ0, hγ⟩ := S.exists_principal_mul α N hN
    (fun j ↦ List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k))
    (fun j ↦ S.split_lmap (N j) (α j) (rC j) (hsC j)) hBr hBI hα Γf dΓ hdΓ' c hsumΓ
    (∑ i, δ i) hR
  exact ⟨m, hm, (S.principal_iff_test hB α N hN rC hsC (fun j k ↦ m * (sr j k * ΓP (πr j k)))
    (fun j r ↦ m * Γf j r) (fun j k ↦ by rw [hΓk]) (m * c)).mp ⟨γ, hγ0, hγ⟩⟩

end CurveData

end Riemann

end Curves
