import RischTragerBronstein.Torsion.PrincipalG
import RischTragerBronstein.Torsion.KernelDVR

/-!
# The auxiliary function over the residue field (any characteristic)

* `one_le_order_iff_evalW`: along an unramified branch through `(x₀, y₀)` (with `D(x₀) ≠ 0`),
  `W(x, y)/D(x)` vanishes iff `W(x₀, y₀) = 0`;
* `reduced_vanishG`: if `ψ = ∑ cⱼ wⱼ` vanishes on `∑ c'_j F_{α_j} − Γ` and at the points
  `(xᵢ, y_{i,k})`, `k ≠ 0`, while `Γ − c ∞ₓ` is principal and the base points are non-special
  (`hNS`), then `ψ` also vanishes at the base points `(xᵢ, y_{i,0})`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Reduced

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

lemma list_sum_cast {α : Type*} (l : List α) (f : α → ℕ) :
    (l.map fun r ↦ (f r : ℤ)).sum = (((l.map f).sum : ℕ) : ℤ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

namespace CurveData

variable (S : CurveData C L)

lemma constantCoeff_eval_psSub (W : C[X][X]) (a : K) (Yp : PowerSeries K) :
    PowerSeries.constantCoeff ((W.map (psSub 1 a)).eval Yp) =
      Sup.evalW (W.map (mapRingHom (algebraMap C K))) a (PowerSeries.constantCoeff Yp) := by
  rw [eval_map, Polynomial.hom_eval₂, Sup.evalW, Polynomial.map_map, eval_map]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  rw [RingHom.comp_apply, coeff_zero_psSub, RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom]

lemma eval_branchSub_ofPS (W : C[X][X]) (a : K) (Yp : PowerSeries K) :
    (W.map (branchSub 1 a)).eval (ofPowerSeries ℤ K Yp) =
      ofPowerSeries ℤ K ((W.map (psSub 1 a)).eval Yp) := by
  have h : branchSub (C := C) 1 a = (ofPowerSeries ℤ K).comp (psSub 1 a) :=
    RingHom.ext fun P ↦ branchSub_eq_psSub 1 a P
  rw [h, ← Polynomial.map_map, eval_map, eval₂_at_apply]

/-- **Vanishing along an unramified branch is vanishing of the value.** -/
lemma one_le_order_iff_evalW (W : C[X][X]) (D : C[X]) (x y : C) (hDx : D.eval x ≠ 0)
    (Yp : PowerSeries K)
    (hY : (S.F.map (branchSub 1 (algebraMap C K x))).eval (ofPowerSeries ℤ K Yp) = 0)
    (hYc : PowerSeries.constantCoeff Yp = algebraMap C K y) (hne : S.fnWQ W D ≠ 0) :
    1 ≤ (S.embG (branchSub 1 (algebraMap C K x)) (branchSub_injective 1 one_pos _)
      (ofPowerSeries ℤ K Yp) hY (S.fnWQ W D)).order ↔ Sup.evalW W x y = 0 := by
  set ι := algebraMap C K
  have hD0 : D ≠ 0 := fun h ↦ hDx (by rw [h, eval_zero])
  have hgD : (branchSub (C := C) 1 (ι x) D).order = 0 := by
    rw [order_branchSub 1 one_pos _ D hD0, rootMultiplicity_eq_zero]
    · simp
    · rw [IsRoot.def, eval_map, eval₂_at_apply]
      exact (map_ne_zero_iff _ ι.injective).mpr hDx
  have hgD0 : branchSub (C := C) 1 (ι x) D ≠ 0 :=
    (map_ne_zero_iff _ (branchSub_injective 1 one_pos _)).mpr hD0
  have hemb := S.embG_fnWQ (branchSub 1 (ι x)) (branchSub_injective 1 one_pos _)
    (ofPowerSeries ℤ K Yp) hY W D
  have hne' : S.embG (branchSub 1 (ι x)) (branchSub_injective 1 one_pos _)
      (ofPowerSeries ℤ K Yp) hY (S.fnWQ W D) ≠ 0 :=
    (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hne
  set t := (W.map (psSub 1 (ι x))).eval Yp with ht
  have hs : (W.map (branchSub 1 (ι x))).eval (ofPowerSeries ℤ K Yp) = ofPowerSeries ℤ K t :=
    eval_branchSub_ofPS W (ι x) Yp
  rw [hs] at hemb
  have ht0 : ofPowerSeries ℤ K t ≠ 0 := by
    intro h; rw [h, zero_mul] at hemb; exact hne' hemb
  rw [hemb, HahnSeries.order_mul ht0 (inv_ne_zero hgD0), order_inv' _ hgD0, hgD, neg_zero,
    add_zero]
  have key : 1 ≤ (ofPowerSeries ℤ K t).order ↔ PowerSeries.constantCoeff t = 0 := by
    constructor
    · intro h
      have hl := lowerBd_of_le_order _ 1 h
      have := (lowerBd_ofPS_iff t 1).mp (by exact_mod_cast hl)
      rw [pow_one] at this
      exact PowerSeries.X_dvd_iff.mp this
    · intro h
      refine le_order_of_lowerBd _ ht0 1 ?_
      have := (lowerBd_ofPS_iff t 1).mpr (by rw [pow_one]; exact PowerSeries.X_dvd_iff.mpr h)
      exact_mod_cast this
  rw [key, ht, constantCoeff_eval_psSub, hYc, evalW_mapG]
  exact map_eq_zero_iff _ ι.injective

/-- The orders of a principal divisor's witness are exact: zero off its support. -/
theorem divGE_off [IsAlgClosed K] (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α) (N : J → ℕ)
    (hN : ∀ j, 0 < N j) (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (cΓ : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = cΓ * S.F.natDegree)
    (γ : C⟮S.x⟯⟮S.y⟯) (hγ0 : γ ≠ 0) (hγ : S.DivGE α N hN lf hlf Γ cΓ γ)
    (b : K) (hb : b ∉ Set.range (fun j ↦ algebraMap C K (α j))) (N' : ℕ) (hN' : N' ≠ 0)
    (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l) :
    (S.embG (branchSub N' b) (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r
      (S.root_of_mem hl hr) γ).order = 0 := by
  obtain ⟨Ni, hNi, li, hlen, hli⟩ := hBI
  have hlf' := fun j ↦ (S.length_of_split (hlf j))
  refine (S.exact_fn hBr γ hγ0 (fun j ↦ algebraMap C K (α j))
    (fun a b h ↦ hα ((algebraMap C K).injective h)) N hN lf hlf (fun j r ↦ (Γ j r : ℤ))
    (fun j r hr ↦ hγ.1 j r hr) (fun b hb N' hN' l hl r hr ↦ hγ.2.1 b hb N' hN' l hl r hr)
    Ni (Nat.pos_of_ne_zero hNi) li hli (fun _ ↦ -((Ni * cΓ : ℕ) : ℤ))
    (fun r hr ↦ hγ.2.2 Ni hNi li hli r hr) (fun j ↦ (dΓ j : ℤ)) (fun j ↦ ?_)
    (-((cΓ * S.F.natDegree : ℕ) : ℤ)) ?_ ?_).2.2 b hb N' hN' l hl r hr
  · rw [list_sum_cast, hdΓ j]; push_cast; ring
  · rw [List.map_const', List.sum_replicate, hlen]; push_cast; ring
  · rw [← Nat.cast_sum, hsumΓ]; ring

variable [IsAlgClosed K]

/-- **The reduced auxiliary function vanishes at the base points.** -/
theorem reduced_vanishG (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
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
    {g : ℕ} (xs : Fin g → C) (hxα : ∀ i j, xs i ≠ α j)
    (y : Fin g → Fin S.F.natDegree → C) (Y : Fin g → Fin S.F.natDegree → PowerSeries K)
    (hY : ∀ i k, (S.F.map (branchSub 1 (algebraMap C K (xs i)))).eval
      (ofPowerSeries ℤ K (Y i k)) = 0)
    (hYc : ∀ i k, PowerSeries.constantCoeff (Y i k) = algebraMap C K (y i k))
    (hsx : ∀ i, S.F.map (branchSub 1 (algebraMap C K (xs i))) =
      ((List.ofFn fun k ↦ ofPowerSeries ℤ K (Y i k)).map fun r ↦ X - Polynomial.C r).prod)
    (hDx : ∀ i, D.eval (xs i) ≠ 0) (hn : 0 < S.F.natDegree)
    (hM : M + cΓ = ∑ j, c' j + g)
    (hvT : ∀ j r (hr : r ∈ lf j), ((c' j * N j : ℕ) : ℤ) - Γ j r ≤
      (S.embG (branchSub (N j) (algebraMap C K (α j))) (branchSub_injective _ (hN j) _) r
        (S.root_of_mem (hlf j) hr) (S.elt B D c)).order)
    (hvx : ∀ i (k : Fin S.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW (PsiC B c) (xs i) (y i k) = 0)
    (γ : C⟮S.x⟯⟮S.y⟯) (hγ0 : γ ≠ 0) (hγ : S.DivGE α N hN lf hlf Γ cΓ γ)
    (hNS : ∀ q : Fin S.F.natDegree → C[X], (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g) →
      (∀ i (k : Fin S.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW (PsiC B q) (xs i) (y i k) = 0) →
      ∀ i, Sup.evalW (PsiC B q) (xs i) (y i ⟨0, hn⟩) = 0) :
    ∀ i, Sup.evalW (PsiC B c) (xs i) (y i ⟨0, hn⟩) = 0 := by
  classical
  set ι := algebraMap C K with hι
  set ψ := S.elt B D c with hψ
  have hψ0 : ψ ≠ 0 := fun h ↦ hc0 (elt_eq_zero hB.hD hB.deg hB.det c h)
  have hreg : S.RegularFinite K ψ := regular_elt hB.reg c
  set P : C[X] := ∏ j, (X - Polynomial.C (α j)) ^ c' j with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hPK : P.map ι = ∏ j, (X - Polynomial.C (ι (α j))) ^ c' j := by
    rw [hP, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun k _ ↦ by
      rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hαι : Function.Injective fun j ↦ ι (α j) := fun a b h ↦ hα (ι.injective h)
  have hdegP : P.natDegree = ∑ j, c' j := by rw [hP, natDegree_prodPow]
  set φ := γ * ψ * (S.polyF P)⁻¹ with hφ
  have hφ0 : φ ≠ 0 := mul_ne_zero (mul_ne_zero hγ0 hψ0) (inv_ne_zero (S.polyF_ne_zero hP0))
  -- orders of `φ`
  have hordφ : ∀ (g' : C[X] →+* LaurentSeries K) (hg : Function.Injective g') (r : LaurentSeries K)
      (hr : (S.F.map g').eval r = 0), (S.embG g' hg r hr φ).order =
        (S.embG g' hg r hr γ).order + (S.embG g' hg r hr ψ).order - (g' P).order := by
    intro g' hg r hr
    have h1 : S.embG g' hg r hr γ ≠ 0 := (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hγ0
    have h2 : S.embG g' hg r hr ψ ≠ 0 := (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0
    have h3 : g' P ≠ 0 := (map_ne_zero_iff _ hg).mpr hP0
    rw [hφ, map_mul, map_mul, map_inv₀, S.embG_polyF, HahnSeries.order_mul (mul_ne_zero h1 h2)
      (inv_ne_zero h3), HahnSeries.order_mul h1 h2, order_inv' _ h3]
    ring
  -- `φ` is regular at all finite branches
  have hφreg : S.RegularFinite K φ := by
    intro a N' hN' l hl r hr
    have hN0 : 0 < N' := Nat.pos_of_ne_zero hN'
    rw [hordφ, order_branchSub _ hN0 _ _ hP0, hPK]
    by_cases ha : ∃ j, ι (α j) = a
    · obtain ⟨j, rfl⟩ := ha
      rw [rootMultiplicity_prodPow_pt _ hαι c' j]
      obtain ⟨r0, hr0, htr⟩ := S.order_transfer (ι (α j)) (N j) N' (hN j) hN0 (lf j) l (hlf j) hl r hr
      have e1 := htr γ
      have e2 := htr ψ
      have b1 := hγ.1 j r0 hr0
      have b2 := hvT j r0 hr0
      have hNj : (0 : ℤ) < N j := by exact_mod_cast hN j
      have key : (N j : ℤ) * (N' * c' j) ≤ N j * ((S.embG (branchSub N' (ι (α j)))
          (branchSub_injective N' hN0 _) r (S.root_of_mem hl hr) γ).order +
          (S.embG (branchSub N' (ι (α j))) (branchSub_injective N' hN0 _) r
            (S.root_of_mem hl hr) ψ).order) := by
        rw [mul_add, e1, e2]
        push_cast at b2 ⊢
        nlinarith
      have := le_of_mul_le_mul_left key hNj
      push_cast
      linarith
    · push_neg at ha
      rw [rootMultiplicity_prodPow_off _ c' a (by rintro ⟨j, hj⟩; exact ha j hj)]
      have := hγ.2.1 a (by rintro ⟨j, hj⟩; exact ha j hj) N' hN' l hl r hr
      have := hreg a N' hN' l hl r hr
      simp only [CharP.cast_eq_zero, mul_zero, Nat.cast_zero, sub_zero]
      push_cast
      linarith
  -- pole order `≤ g` above infinity
  have hφinf : ∀ (N' : ℕ) (hN' : N' ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N') = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N') (infSub_injective N' (Nat.pos_of_ne_zero hN')) r
        (S.root_of_mem hl hr) φ) (-((N' * g : ℕ) : ℤ)) := by
    intro N' hN' l hl r hr
    have hN0 : 0 < N' := Nat.pos_of_ne_zero hN'
    refine lowerBd_of_le_order _ _ ?_
    rw [hordφ, order_infSub _ hN0 _ hP0, hdegP]
    have h1 := hγ.2.2 N' hN' l hl r hr
    have h2 := le_order_of_lowerBd _ ((map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0) _
      (inf_elt hB.inf c M hdeg N' hN' l hl r hr)
    have h3 : ((M + cΓ : ℕ) : ℤ) = ((∑ j, c' j + g : ℕ) : ℤ) := by rw [hM]
    push_cast at h1 h2 h3 ⊢
    nlinarith
  obtain ⟨q, hφq, hqdeg⟩ := lspace_complete hB φ hφreg g hφinf
  -- the branches through the base points
  have hsplit_mem : ∀ i k, (S.F.map (branchSub 1 (ι (xs i)))).eval (ofPowerSeries ℤ K (Y i k)) = 0 :=
    hY
  have hxoff : ∀ i, ι (xs i) ∉ Set.range (fun j ↦ ι (α j)) := by
    rintro i ⟨j, hj⟩; exact hxα i j (ι.injective hj).symm
  have hPx : ∀ i, (branchSub (C := C) 1 (ι (xs i)) P).order = 0 := by
    intro i
    rw [order_branchSub _ one_pos _ _ hP0, hPK, rootMultiplicity_prodPow_off _ c' _ (hxoff i)]
    simp
  -- the order of `γ` at base points is `0`
  have hγx : ∀ i k, (S.embG (branchSub 1 (ι (xs i))) (branchSub_injective 1 one_pos _)
      (ofPowerSeries ℤ K (Y i k)) (hY i k) γ).order = 0 := by
    intro i k
    exact S.divGE_off hBr hBI α hα N hN lf hlf Γ cΓ dΓ hdΓ hsumΓ γ hγ0 hγ (ι (xs i)) (hxoff i) 1
      one_ne_zero _ (hsx i) _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
  have hψW : ψ = S.fnWQ (PsiC B c) D := elt_eq_fnWQ B D c
  have hφW : φ = S.fnWQ (PsiC B q) D := by rw [hφq, elt_eq_fnWQ]
  -- orders of `φ` and `ψ` agree at the base fibres
  have hφψ : ∀ i k, (S.embG (branchSub 1 (ι (xs i))) (branchSub_injective 1 one_pos _)
      (ofPowerSeries ℤ K (Y i k)) (hY i k) φ).order = (S.embG (branchSub 1 (ι (xs i)))
      (branchSub_injective 1 one_pos _) (ofPowerSeries ℤ K (Y i k)) (hY i k) ψ).order := by
    intro i k
    rw [hordφ, hγx, hPx]; ring
  have hq : ∀ i (k : Fin S.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW (PsiC B q) (xs i) (y i k) = 0 := by
    intro i k hk
    have h1 := (S.one_le_order_iff_evalW (PsiC B c) D (xs i) (y i k) (hDx i) (Y i k) (hY i k)
      (hYc i k) (by rw [← hψW]; exact hψ0)).mpr (hvx i k hk)
    rw [← hψW, ← hφψ, hφW] at h1
    exact (S.one_le_order_iff_evalW (PsiC B q) D (xs i) (y i k) (hDx i) (Y i k) (hY i k)
      (hYc i k) (by rw [← hφW]; exact hφ0)).mp h1
  intro i
  have h1 := (S.one_le_order_iff_evalW (PsiC B q) D (xs i) (y i ⟨0, hn⟩) (hDx i) (Y i _) (hY i _)
    (hYc i _) (by rw [← hφW]; exact hφ0)).mpr (hNS q hqdeg hq i)
  rw [← hφW, hφψ, hψW] at h1
  exact (S.one_le_order_iff_evalW (PsiC B c) D (xs i) (y i ⟨0, hn⟩) (hDx i) (Y i _) (hY i _)
    (hYc i _) (by rw [← hψW]; exact hψ0)).mp h1

end CurveData

end Reduced

end Curves
