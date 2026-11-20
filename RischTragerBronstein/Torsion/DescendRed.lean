import RischTragerBronstein.Torsion.DescendAux

/-!
# The reduced side of the descent (general curves)

`reduced_sideG`: under the hypotheses of `reduced_vanishG`, the auxiliary function `ψ` vanishes
exactly to order `1` at every point of the base fibres: its numerator `W = Ψ(c)` does not vanish to
order `2` there, `W(xᵢ, y_{i,0}) = 0`, and each `xᵢ` is a root of multiplicity `n` of the norm.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Red

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma root_of_fibrePS (a : K) (Yp : PowerSeries K) (hY : (fibrePS S.F a).eval Yp = 0) :
    (S.F.map (branchSub 1 a)).eval (ofPowerSeries ℤ K Yp) = 0 := by
  rw [eval_branchSub_ofPS]
  have : (S.F.map (psSub 1 a)).eval Yp = 0 := hY
  rw [this, map_zero]

/-- Orders of the numerator and of the function agree where the denominator does not vanish. -/
lemma order_W_eq_fnWQ (W : C[X][X]) (D : C[X]) (x : C) (hDx : D.eval x ≠ 0)
    (r : LaurentSeries K) (hr : (S.F.map (branchSub 1 (algebraMap C K x))).eval r = 0)
    (hne : S.fnWQ W D ≠ 0) :
    ((W.map (branchSub 1 (algebraMap C K x))).eval r).order =
      (S.embG (branchSub 1 (algebraMap C K x)) (branchSub_injective 1 one_pos _) r hr
        (S.fnWQ W D)).order := by
  have hD0 : D ≠ 0 := fun h ↦ hDx (by rw [h, eval_zero])
  have hgD : (branchSub (C := C) 1 (algebraMap C K x) D).order = 0 := by
    rw [order_branchSub 1 one_pos _ D hD0, rootMultiplicity_eq_zero]
    · simp
    · rw [IsRoot.def, eval_map, eval₂_at_apply]
      exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr hDx
  have hgD0 : branchSub (C := C) 1 (algebraMap C K x) D ≠ 0 :=
    (map_ne_zero_iff _ (branchSub_injective 1 one_pos _)).mpr hD0
  have hne' := (map_ne_zero_iff _ (S.embG (branchSub 1 (algebraMap C K x))
    (branchSub_injective 1 one_pos _) r hr).injective).mpr hne
  rw [S.embG_fnWQ] at hne' ⊢
  have hW0 : (W.map (branchSub 1 (algebraMap C K x))).eval r ≠ 0 := by
    intro h; rw [h, zero_mul] at hne'; exact hne' rfl
  rw [HahnSeries.order_mul hW0 (inv_ne_zero hgD0), order_inv' _ hgD0, hgD, neg_zero, add_zero]

variable [IsAlgClosed K]

/-- **The reduced side.** -/
theorem reduced_sideG (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ)
    (c : Fin S.F.natDegree → C[X]) (hc0 : c ≠ 0) (M : ℕ)
    (hdeg : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M)
    {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α) (N : J → ℕ)
    (hN : ∀ j, 0 < N j) (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (cΓ : ℕ) (c' : J → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = cΓ * S.F.natDegree)
    {g : ℕ} (xs : Fin g → C) (hxs : Function.Injective xs) (hxα : ∀ i j, xs i ≠ α j)
    (y : Fin g → Fin S.F.natDegree → C) (Y : Fin g → Fin S.F.natDegree → PowerSeries K)
    (hY : ∀ i k, (fibrePS S.F (algebraMap C K (xs i))).eval (Y i k) = 0)
    (hYc : ∀ i k, PowerSeries.constantCoeff (Y i k) = algebraMap C K (y i k))
    (hsx : ∀ i, S.F.map (branchSub 1 (algebraMap C K (xs i))) =
      ((List.ofFn fun k ↦ ofPowerSeries ℤ K (Y i k)).map fun r ↦ X - Polynomial.C r).prod)
    (hFY : ∀ i k, (fibreAt (derivative S.F) (algebraMap C K (xs i))).eval
      (algebraMap C K (y i k)) ≠ 0)
    (hDx : ∀ i, D.eval (xs i) ≠ 0) (hn : 0 < S.F.natDegree)
    (hM : M + cΓ = ∑ j, c' j + g)
    (hvT : ∀ j r (hr : r ∈ lf j), ((c' j * N j : ℕ) : ℤ) - Γ j r ≤
      (S.embG (branchSub (N j) (algebraMap C K (α j))) (branchSub_injective _ (hN j) _) r
        (S.root_of_mem (hlf j) hr) (S.elt B D c)).order)
    (hvx : ∀ i (k : Fin S.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW (PsiC B c) (xs i) (y i k) = 0)
    (γ : C⟮S.x⟯⟮S.y⟯) (hγ0 : γ ≠ 0) (hγ : S.DivGE α N hN lf hlf Γ cΓ γ)
    (hNS : ∀ q : Fin S.F.natDegree → C[X], (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g) →
      (∀ i (k : Fin S.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW (PsiC B q) (xs i) (y i k) = 0) →
      ∀ i, Sup.evalW (PsiC B q) (xs i) (y i ⟨0, hn⟩) = 0)
    (m : ℕ) (hm : (PsiC B c).natDegree ≤ m) :
    (∀ i k, ¬ VanishAtG (S.F.map (mapRingHom (algebraMap C K)))
      ((PsiC B c).map (mapRingHom (algebraMap C K))) (algebraMap C K (xs i))
        (algebraMap C K (y i k)) 2) ∧
    (∀ i, ((S.normW (PsiC B c) m).map (algebraMap C K)).rootMultiplicity
      (algebraMap C K (xs i)) = S.F.natDegree) ∧
    (∀ i, Sup.evalW (PsiC B c) (xs i) (y i ⟨0, hn⟩) = 0) := by
  classical
  set ι := algebraMap C K with hι
  have hY' : ∀ i k, (S.F.map (branchSub 1 (ι (xs i)))).eval (ofPowerSeries ℤ K (Y i k)) = 0 :=
    fun i k ↦ S.root_of_fibrePS _ _ (hY i k)
  have h3 := S.reduced_vanishG hBr hBI hB c hc0 M hdeg α hα N hN lf hlf Γ cΓ c' dΓ hdΓ hsumΓ xs
    hxα y Y hY' hYc (fun i ↦ by rw [hsx i]) hDx hn hM hvT hvx γ hγ0 hγ hNS
  set ψ := S.elt B D c with hψ
  have hψ0 : ψ ≠ 0 := fun h ↦ hc0 (elt_eq_zero hB.hD hB.deg hB.det c h)
  have hψW : ψ = S.fnWQ (PsiC B c) D := elt_eq_fnWQ B D c
  have hreg : S.RegularFinite K ψ := regular_elt hB.reg c
  -- `ψ` vanishes at every base point
  have hvall : ∀ i k, 1 ≤ (S.embG (branchSub 1 (ι (xs i))) (branchSub_injective 1 one_pos _)
      (ofPowerSeries ℤ K (Y i k)) (hY' i k) ψ).order := by
    intro i k
    rw [hψW]
    refine (S.one_le_order_iff_evalW (PsiC B c) D (xs i) (y i k) (hDx i) (Y i k) (hY' i k)
      (hYc i k) (by rw [← hψW]; exact hψ0)).mpr ?_
    by_cases hk : (k : ℕ) = 0
    · have e : k = ⟨0, hn⟩ := Fin.ext hk
      rw [e]; exact h3 i
    · exact hvx i k hk
  obtain ⟨n, hnn⟩ : ∃ n, n = S.F.natDegree := ⟨_, rfl⟩
  -- the exact divisor of `ψ`
  set pt : J ⊕ Fin g → K := Sum.elim (fun j ↦ ι (α j)) (fun i ↦ ι (xs i)) with hpt
  have hptI : Function.Injective pt := Function.Injective.sumElim
    (fun a b h ↦ hα (ι.injective h)) (fun a b h ↦ hxs (ι.injective h))
    (fun a b h ↦ hxα b a (ι.injective h).symm)
  set NI : J ⊕ Fin g → ℕ := Sum.elim N (fun _ ↦ 1) with hNI
  have hNI0 : ∀ k, 0 < NI k := fun k ↦ by cases k <;> simp [hNI, hN]
  set lI : J ⊕ Fin g → List (LaurentSeries K) :=
    Sum.elim lf (fun i ↦ List.ofFn fun k ↦ ofPowerSeries ℤ K (Y i k)) with hlI
  have hlI' : ∀ k, S.F.map (branchSub (NI k) (pt k)) = ((lI k).map fun r ↦ X - Polynomial.C r).prod :=
    fun k ↦ by cases k with
      | inl j => exact hlf j
      | inr i => exact hsx i
  set zI : J ⊕ Fin g → LaurentSeries K → ℤ :=
    Sum.elim (fun j r ↦ ((c' j * N j : ℕ) : ℤ) - Γ j r) (fun _ _ ↦ 1) with hzI
  set dI : J ⊕ Fin g → ℤ := Sum.elim (fun j ↦ (n : ℤ) * c' j - dΓ j) (fun _ ↦ (n : ℤ)) with hdI
  have hlenT : ∀ j, (lf j).length = n := fun j ↦ (S.length_of_split (hlf j)).trans hnn.symm
  have hlenx : ∀ i, (List.ofFn fun k ↦ ofPowerSeries ℤ K (Y i k)).length = n :=
    fun i ↦ (S.length_of_split (hsx i)).trans hnn.symm
  obtain ⟨Ni, hNi, li, -, hli⟩ := hBI
  have hleni : li.length = n := (S.length_of_split hli).trans hnn.symm
  obtain ⟨hE1, -, -⟩ := S.exact_fn hBr ψ hψ0 pt hptI NI hNI0 lI hlI' zI
    (fun k r hr ↦ by
      cases k with
      | inl j => exact hvT j r hr
      | inr i =>
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
        exact hvall i k)
    (fun b _ N' hN' l hl r hr ↦ hreg b N' hN' l hl r hr) (Ni) (Nat.pos_of_ne_zero hNi) li hli
    (fun _ ↦ -((Ni * M : ℕ) : ℤ))
    (fun r hr ↦ le_order_of_lowerBd _ ((map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0) _
      (inf_elt hB.inf c M hdeg Ni hNi li hli r hr))
    dI (fun k ↦ by
      cases k with
      | inl j =>
        simp only [hzI, hNI, hdI, Sum.elim_inl, hlI]
        rw [list_sum_const_sub, hdΓ j, hlenT j]
        push_cast; ring
      | inr i =>
        simp only [hzI, hNI, hdI, Sum.elim_inr, hlI]
        rw [List.map_const', List.sum_replicate, hlenx i]
        simp)
    (-((n : ℤ) * M)) (by rw [List.map_const', List.sum_replicate, hleni]; push_cast; ring)
    (by
      rw [Fintype.sum_sum_type]
      simp only [hdI, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h1 : ((∑ j, dΓ j : ℕ) : ℤ) = cΓ * n := by rw [hsumΓ, ← hnn]; push_cast; ring
      have h2 : ((M + cΓ : ℕ) : ℤ) = ((∑ j, c' j + g : ℕ) : ℤ) := by rw [hM]
      push_cast at h1 h2
      rw [h1]
      linear_combination (-(n : ℤ)) * h2)
  -- orders exactly `1` at the base points
  have hone : ∀ i k, (((PsiC B c).map (branchSub 1 (ι (xs i)))).eval
      (ofPowerSeries ℤ K (Y i k))).order = 1 := by
    intro i k
    have := hE1 (Sum.inr i) (ofPowerSeries ℤ K (Y i k)) (List.mem_ofFn.mpr ⟨k, rfl⟩)
    simp only [hzI, Sum.elim_inr] at this
    rw [S.order_W_eq_fnWQ (PsiC B c) D (xs i) (hDx i) _ (hY' i k) (by rw [← hψW]; exact hψ0),
      ← hψW]
    exact this.symm
  refine ⟨fun i k hv ↦ ?_, fun i ↦ ?_, h3⟩
  · have hl2 := (lowerBd_iff_vanishAtG S.F (ι (xs i)) (ι (y i k)) (Y i k) (hY i k) (hYc i k)
      (hFY i k) (PsiC B c) 2).mpr hv
    have hne : ofPowerSeries ℤ K (((PsiC B c).map (psSub 1 (ι (xs i)))).eval (Y i k)) ≠ 0 := by
      intro h0
      have := hone i k
      rw [eval_branchSub_ofPS, h0, HahnSeries.order_zero] at this
      exact zero_ne_one this
    have := le_order_of_lowerBd _ hne 2 (by exact_mod_cast hl2)
    have h1 := hone i k
    rw [eval_branchSub_ofPS] at h1
    rw [h1] at this
    norm_num at this
  · have hW : S.evXY (PsiC B c) ≠ 0 := by
      have := S.fnWQ_mul (PsiC B c) D hB.hD
      intro h0
      rw [h0, ← hψW] at this
      exact hψ0 (Subtype.ext ((mul_eq_zero.mp this).resolve_right (fun h ↦ hB.hD
        (transcendental_iff.mp S.htr D h))))
    have hs := S.sum_order_fin (PsiC B c) m hm hW 1 one_pos (ι (xs i)) _ (hsx i)
    rw [List.map_ofFn, List.sum_ofFn] at hs
    simp only [Function.comp_apply] at hs
    have hsum1 : ∑ k : Fin S.F.natDegree, (((PsiC B c).map (branchSub 1 (ι (xs i)))).eval
        (ofPowerSeries ℤ K (Y i k))).order = S.F.natDegree := by
      rw [Finset.sum_congr rfl fun k _ ↦ hone i k]; simp
    rw [hsum1] at hs
    rw [Nat.cast_one, one_mul] at hs
    exact_mod_cast hs.symm

end CurveData

end Red

end Curves
