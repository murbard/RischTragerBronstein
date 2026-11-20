import RischTragerBronstein.Torsion.DescendRed

/-!
# The norm of the auxiliary function over the fraction field (general curves)

`norm_dvd_sideG`: if `ψ = Ψ(c)(x, y)/D(x)` vanishes on `∑ c'_j F_{α_j} − Γ` and at the points
`(xᵢ, y_{i,k})`, `k ≠ 0`, then `Dⁿ ∏(x − α_j)^{n c'_j − deg Γ_j} ∏(x − xᵢ)^{n−1}` divides the norm
of `Ψ(c)`, whose degree is at most `n (M + deg D)`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section NormSide

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L) [IsAlgClosed K]

/-- **The divisibility of the norm.** -/
theorem norm_dvd_sideG (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) (hDm : D.Monic)
    (c : Fin S.F.natDegree → C[X]) (hc0 : c ≠ 0) (M : ℕ)
    (hdeg : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M)
    {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α) (N : J → ℕ)
    (hN : ∀ j, 0 < N j) (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (c' : J → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hle : ∀ j, dΓ j ≤ S.F.natDegree * c' j)
    {g : ℕ} (xs : Fin g → C) (hxs : Function.Injective xs) (hxα : ∀ i j, xs i ≠ α j)
    (y : Fin g → Fin S.F.natDegree → C) (Y : Fin g → Fin S.F.natDegree → PowerSeries K)
    (hY : ∀ i k, (fibrePS S.F (algebraMap C K (xs i))).eval (Y i k) = 0)
    (hYc : ∀ i k, PowerSeries.constantCoeff (Y i k) = algebraMap C K (y i k))
    (hsx : ∀ i, S.F.map (branchSub 1 (algebraMap C K (xs i))) =
      ((List.ofFn fun k ↦ ofPowerSeries ℤ K (Y i k)).map fun r ↦ X - Polynomial.C r).prod)
    (hDx : ∀ i, D.eval (xs i) ≠ 0) (hn : 0 < S.F.natDegree)
    (hvT : ∀ j r (hr : r ∈ lf j), ((c' j * N j : ℕ) : ℤ) - Γ j r ≤
      (S.embG (branchSub (N j) (algebraMap C K (α j))) (branchSub_injective _ (hN j) _) r
        (S.root_of_mem (hlf j) hr) (S.elt B D c)).order)
    (hvx : ∀ i (k : Fin S.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW (PsiC B c) (xs i) (y i k) = 0)
    (m : ℕ) (hm : (PsiC B c).natDegree ≤ m) :
    (D ^ S.F.natDegree * (∏ j, (X - Polynomial.C (α j)) ^ (S.F.natDegree * c' j - dΓ j)) *
      ∏ i, (X - Polynomial.C (xs i)) ^ (S.F.natDegree - 1)) ∣ S.normW (PsiC B c) m ∧
    (S.normW (PsiC B c) m).natDegree ≤ S.F.natDegree * (M + D.natDegree) := by
  classical
  set ι := algebraMap C K with hι
  set W := PsiC B c with hW_def
  set ψ := S.elt B D c with hψ
  have hψ0 : ψ ≠ 0 := fun h ↦ hc0 (elt_eq_zero hB.hD hB.deg hB.det c h)
  have hψW : ψ = S.fnWQ W D := elt_eq_fnWQ B D c
  have hreg : S.RegularFinite K ψ := regular_elt hB.reg c
  have hWQ : (ψ : L) * aeval S.x D = S.evXY W := by rw [hψW]; exact S.fnWQ_mul W D hB.hD
  have hWne : S.evXY W ≠ 0 := by
    rw [← hWQ]
    exact mul_ne_zero (fun h ↦ hψ0 (Subtype.ext h)) (fun h ↦ hB.hD (transcendental_iff.mp S.htr D h))
  have hordW : ∀ (g' : C[X] →+* LaurentSeries K) (hg : Function.Injective g') (r : LaurentSeries K)
      (hr : (S.F.map g').eval r = 0), ((W.map g').eval r).order =
        (S.embG g' hg r hr ψ).order + (g' D).order :=
    fun g' hg r hr ↦ S.order_W_eq g' hg r hr ψ hψ0 W D hB.hD hWQ
  have hY' : ∀ i k, (S.F.map (branchSub 1 (ι (xs i)))).eval (ofPowerSeries ℤ K (Y i k)) = 0 :=
    fun i k ↦ S.root_of_fibrePS _ _ (hY i k)
  have hDK0 : D.map ι ≠ 0 := (hDm.map ι).ne_zero
  have hαι : Function.Injective fun j ↦ ι (α j) := fun a b h ↦ hα (ι.injective h)
  have hxι : Function.Injective fun i ↦ ι (xs i) := fun a b h ↦ hxs (ι.injective h)
  set P1 : C[X] := ∏ j, (X - Polynomial.C (α j)) ^ (S.F.natDegree * c' j - dΓ j) with hP1
  set P2 : C[X] := ∏ i, (X - Polynomial.C (xs i)) ^ (S.F.natDegree - 1) with hP2
  have hP1m : P1.Monic := monic_prod_of_monic _ _ fun j _ ↦ (monic_X_sub_C _).pow _
  have hP2m : P2.Monic := monic_prod_of_monic _ _ fun j _ ↦ (monic_X_sub_C _).pow _
  have hDpm : (D ^ S.F.natDegree * P1 * P2).Monic := ((hDm.pow S.F.natDegree).mul hP1m).mul hP2m
  have hP1K : P1.map ι = ∏ j, (X - Polynomial.C (ι (α j))) ^ (S.F.natDegree * c' j - dΓ j) := by
    rw [hP1, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun k _ ↦ by
      rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hP2K : P2.map ι = ∏ i, (X - Polynomial.C (ι (xs i))) ^ (S.F.natDegree - 1) := by
    rw [hP2, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun k _ ↦ by
      rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  -- a branch system above `0`, for the non-vanishing of the norm
  obtain ⟨N0, hN0, l0, -, hl0⟩ := hBr 0
  have hl0' : S.F.map (branchSub N0 (0 : K)) =
      ((l0.map (ofPowerSeries ℤ K)).map fun r ↦ X - Polynomial.C r).prod := by
    rw [hl0, List.map_map]; rfl
  have hN0' : S.normW W m ≠ 0 := S.normW_ne_zero W m hm hWne _
    (branchSub_injective N0 (Nat.pos_of_ne_zero hN0) 0) _ hl0'
  have hNK0 : (S.normW W m).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hN0'
  refine ⟨?_, ?_⟩
  · rw [← Polynomial.map_dvd_map ι ι.injective hDpm]
    refine dvd_of_rootMultiplicity_le _ _ (hDpm.map ι).ne_zero hNK0 fun b ↦ ?_
    have hpow : ∀ (p : K[X]), p ≠ 0 → ∀ k : ℕ, (p ^ k).rootMultiplicity b =
        k * p.rootMultiplicity b := by
      intro p hp k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ih]; ring
    have hA : (D.map ι) ^ S.F.natDegree * P1.map ι ≠ 0 := (((hDm.map ι).pow S.F.natDegree).mul (hP1m.map ι)).ne_zero
    have hA' : (D.map ι) ^ S.F.natDegree * P1.map ι * P2.map ι ≠ 0 :=
      ((((hDm.map ι).pow S.F.natDegree).mul (hP1m.map ι)).mul (hP2m.map ι)).ne_zero
    have hmD : ((D ^ S.F.natDegree * P1 * P2).map ι).rootMultiplicity b =
        S.F.natDegree * (D.map ι).rootMultiplicity b + (P1.map ι).rootMultiplicity b +
          (P2.map ι).rootMultiplicity b := by
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, rootMultiplicity_mul hA',
        rootMultiplicity_mul hA, hpow _ hDK0]
    rw [hmD]
    by_cases hbα : ∃ j0, ι (α j0) = b
    · obtain ⟨j0, rfl⟩ := hbα
      have h1 : (P1.map ι).rootMultiplicity (ι (α j0)) = S.F.natDegree * c' j0 - dΓ j0 := by
        rw [hP1K]; exact rootMultiplicity_prodPow_pt _ hαι _ j0
      have h2 : (P2.map ι).rootMultiplicity (ι (α j0)) = 0 := by
        rw [hP2K]; exact rootMultiplicity_prodPow_off _ _ _ (by
          rintro ⟨i, hi⟩; exact hxα i j0 (ι.injective hi))
      rw [h1, h2, add_zero]
      have key := S.le_rootMultiplicity_normW W m hm hWne (N j0) (hN j0) (ι (α j0)) (lf j0) (hlf j0)
        (fun r ↦ (((c' j0 * N j0 + N j0 * (D.map ι).rootMultiplicity (ι (α j0)) : ℕ) : ℤ) - Γ j0 r)) (fun r hr ↦ by
          rw [hordW _ (branchSub_injective _ (hN j0) _) r (S.root_of_mem (hlf j0) hr),
            order_branchSub _ (hN j0) _ _ hB.hD]
          have := hvT j0 r hr
          push_cast at this ⊢
          linarith)
        ((S.F.natDegree * c' j0 - dΓ j0 : ℕ) + S.F.natDegree * (D.map ι).rootMultiplicity (ι (α j0)) : ℤ) (by
          rw [list_sum_const_sub, hdΓ j0, (S.length_of_split (hlf j0))]
          have := hle j0
          push_cast [Nat.cast_sub this]
          ring)
      rw [← hι] at key
      have := hle j0
      push_cast [Nat.cast_sub this] at key ⊢
      omega
    by_cases hbx : ∃ i0, ι (xs i0) = b
    · obtain ⟨i0, rfl⟩ := hbx
      have h1 : (P1.map ι).rootMultiplicity (ι (xs i0)) = 0 := by
        rw [hP1K]; exact rootMultiplicity_prodPow_off _ _ _ (by
          rintro ⟨j, hj⟩; exact hxα i0 j (ι.injective hj).symm)
      have h2 : (P2.map ι).rootMultiplicity (ι (xs i0)) = S.F.natDegree - 1 := by
        rw [hP2K]; exact rootMultiplicity_prodPow_pt _ hxι _ i0
      have h0 : (D.map ι).rootMultiplicity (ι (xs i0)) = 0 := by
        rw [rootMultiplicity_eq_zero]
        rw [IsRoot.def, eval_map, eval₂_at_apply]
        exact (map_ne_zero_iff _ ι.injective).mpr (hDx i0)
      rw [h1, h2, h0, mul_zero, zero_add, zero_add]
      have hs := S.sum_order_fin W m hm hWne 1 one_pos (ι (xs i0)) _ (hsx i0)
      rw [List.map_ofFn, List.sum_ofFn] at hs
      simp only [Function.comp_apply] at hs
      have hge : ∀ k : Fin S.F.natDegree, (if (k : ℕ) = 0 then (0 : ℤ) else 1) ≤
          (((PsiC B c).map (branchSub 1 (ι (xs i0)))).eval (ofPowerSeries ℤ K (Y i0 k))).order := by
        intro k
        rw [S.order_W_eq_fnWQ W D (xs i0) (hDx i0) _ (hY' i0 k) (by rw [← hψW]; exact hψ0), ← hψW]
        split_ifs with hk
        · exact hreg _ 1 one_ne_zero _ (hsx i0) _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
        · rw [hψW]
          exact (S.one_le_order_iff_evalW W D (xs i0) (y i0 k) (hDx i0) (Y i0 k) (hY' i0 k)
            (hYc i0 k) (by rw [← hψW]; exact hψ0)).mpr (hvx i0 k hk)
      have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦ hge k
      rw [hs] at hsum
      have hcnt : ∑ k : Fin S.F.natDegree, (if (k : ℕ) = 0 then (0 : ℤ) else 1) = (S.F.natDegree : ℤ) - 1 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
        have : (Finset.univ.filter fun k : Fin S.F.natDegree ↦ ¬ (k : ℕ) = 0).card = S.F.natDegree - 1 := by
          have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin S.F.natDegree)))
            (fun k : Fin S.F.natDegree ↦ (k : ℕ) = 0)
          have h0 : (Finset.univ.filter fun k : Fin S.F.natDegree ↦ (k : ℕ) = 0).card = 1 := by
            rw [Finset.card_eq_one]
            exact ⟨⟨0, hn⟩, by ext k; simp [Fin.ext_iff]⟩
          rw [h0, Finset.card_univ, Fintype.card_fin] at h
          omega
        rw [this]
        push_cast [Nat.cast_sub (show 1 ≤ S.F.natDegree by omega)]
        ring
      rw [hcnt, Nat.cast_one, one_mul, ← hι] at hsum
      have h1n : 1 ≤ S.F.natDegree := hn
      zify [h1n]
      linarith
    · -- a point off the special fibres
      have h1 : (P1.map ι).rootMultiplicity b = 0 := by
        rw [hP1K]; exact rootMultiplicity_prodPow_off _ _ _ (by rintro ⟨j, hj⟩; exact hbα ⟨j, hj⟩)
      have h2 : (P2.map ι).rootMultiplicity b = 0 := by
        rw [hP2K]; exact rootMultiplicity_prodPow_off _ _ _ (by rintro ⟨i, hi⟩; exact hbx ⟨i, hi⟩)
      rw [h1, h2, add_zero, add_zero]
      obtain ⟨Nb, hNb, lb, -, hlb⟩ := hBr b
      have hlb' : S.F.map (branchSub Nb b) =
          ((lb.map (ofPowerSeries ℤ K)).map fun r ↦ X - Polynomial.C r).prod := by
        rw [hlb, List.map_map]; rfl
      have key := S.le_rootMultiplicity_normW W m hm hWne Nb (Nat.pos_of_ne_zero hNb) b _ hlb'
        (fun _ ↦ ((Nb * (D.map ι).rootMultiplicity b : ℕ) : ℤ)) (fun r hr ↦ by
          rw [hordW _ (branchSub_injective _ (Nat.pos_of_ne_zero hNb) _) r (S.root_of_mem hlb' hr),
            order_branchSub _ (Nat.pos_of_ne_zero hNb) _ _ hB.hD]
          have := hreg b Nb hNb _ hlb' r hr
          push_cast at this ⊢
          linarith)
        ((S.F.natDegree * (D.map ι).rootMultiplicity b : ℕ) : ℤ) (by
          rw [List.map_const', List.sum_replicate, (S.length_of_split hlb'), nsmul_eq_mul]
          push_cast; ring)
      rw [← hι] at key
      exact_mod_cast key
  · obtain ⟨Ni, hNi, li, -, hli⟩ := hBI
    have hNi0 : 0 < Ni := Nat.pos_of_ne_zero hNi
    have hs := S.sum_order_inf W m hm hWne Ni hNi0 li hli
    have hge : ∀ r ∈ li, -((Ni * (M + D.natDegree) : ℕ) : ℤ) ≤ ((W.map (infSub Ni)).eval r).order := by
      intro r hr
      rw [hordW _ (infSub_injective Ni hNi0) r (S.root_of_mem hli hr), order_infSub _ hNi0 _ hB.hD]
      have := le_order_of_lowerBd _ ((map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0) _
        (inf_elt hB.inf c M hdeg Ni hNi li hli r hr)
      push_cast at this ⊢
      linarith
    have hsum : (li.map fun _ ↦ -((Ni * (M + D.natDegree) : ℕ) : ℤ)).sum ≤
        (li.map fun r ↦ ((W.map (infSub Ni)).eval r).order).sum := List.sum_le_sum hge
    rw [hs, List.map_const', List.sum_replicate, (S.length_of_split hli), nsmul_eq_mul] at hsum
    have hNi' : (0 : ℤ) < Ni := by exact_mod_cast hNi0
    have : ((S.normW W m).natDegree : ℤ) ≤ S.F.natDegree * (M + D.natDegree) := by
      push_cast at hsum
      nlinarith
    exact_mod_cast this

end CurveData

end NormSide

end Curves
