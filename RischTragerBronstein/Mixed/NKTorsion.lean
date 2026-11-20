import RischTragerBronstein.Mixed.NKTrace
import RischTragerBronstein.Mixed.KWClass

/-!
# Liouville forms with residues: the orders of the logarithms

For `f = v′ + ∑ dⱼ wⱼ′/wⱼ` (ℚ-independent constants `dⱼ ∈ C`) on a curve over a differential base
and a good place `a`, along a branch `x = a + Tᴺ` where `f` has at most a simple pole (relative to
`s`) with residue `ρ ∈ C` (`f₋ₙ = s₁₋ₙ ρ`): `∑ dⱼ ord wⱼ = ρ` (`sum_ord_eq_res`). Hence for a
`ℚ`-linear `Λ` and `eⱼ = M Λ(dⱼ) ∈ ℤ`, the function `γ = ∏ wⱼ^{eⱼ}` has order `M Λ(ρ)` there
(`order_logProd`): the residue divisor of `f` is torsion after projection by `Λ`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

section Ord

variable {K : Type*} [Field K]

lemma order_zpow_nk (z : LaurentSeries K) (hz : z ≠ 0) (e : ℤ) : (z ^ e).order = e * z.order := by
  rcases e with e | e
  · simp only [Int.ofNat_eq_natCast, zpow_natCast, HahnSeries.order_pow, nsmul_eq_mul]
  · rw [zpow_negSucc, order_inv_nk _ (pow_ne_zero _ hz), HahnSeries.order_pow, nsmul_eq_mul,
      Int.negSucc_eq]
    push_cast
    ring

lemma order_prod_zpow_nk {ι : Type*} (s : Finset ι) (z : ι → LaurentSeries K)
    (hz : ∀ i ∈ s, z i ≠ 0) (e : ι → ℤ) :
    (∏ i ∈ s, z i ^ e i) ≠ 0 ∧ (∏ i ∈ s, z i ^ e i).order = ∑ i ∈ s, e i * (z i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h0, h1⟩ := ih fun i hi ↦ hz i (Finset.mem_insert_of_mem hi)
    have hza := hz a (Finset.mem_insert_self a s)
    have hp : z a ^ e a ≠ 0 := zpow_ne_zero _ hza
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero hp h0, by rw [HahnSeries.order_mul hp h0, h1, order_zpow_nk _ hza]⟩

end Ord

namespace CurveData

open Differential

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **The residue determines the orders** along a branch at a good place. -/
theorem sum_ord_eq_res (k : ℕ) (d : ℕ → C) (w : ℕ → L)
    (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (a : K) (hgood : a′ ≠ (ω.map (algebraMap C K)).eval a) (N : ℕ) (hN : 0 < N)
    (Y : LaurentSeries K) (hY : (S.F.map (branchSub N a)).eval Y = 0) (ρ : C)
    (hbelow : ∀ i : ℤ, i < -(N : ℤ) →
      (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY ⟨f, hf⟩).coeff i = 0)
    (hres : (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY ⟨f, hf⟩).coeff (-(N : ℤ)) =
      (sBranch ω a N).coeff (1 - (N : ℤ)) * algebraMap C K ρ) :
    ∑ j : Fin k, ((S.embG (branchSub N a) (branchSub_injective N hN a) Y hY
      ⟨w j, (hw j j.2).1⟩).order : C) * d j = ρ := by
  classical
  set u : Fin k → L := fun i ↦ w i
  have hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯ := fun i ↦ (hw i i.2).1
  have hu0 : ∀ i, u i ≠ 0 := fun i ↦ (hw i i.2).2
  have heq' : f = v′ + ∑ i : Fin k, algebraMap C L (d i) * ((u i)′ / u i) := by
    rw [heq, Fin.sum_univ_eq_sum_range (fun j ↦ algebraMap C L (d j) * ((w j)′ / w j))]
  set s : LaurentSeries K := sBranch ω a N with hs
  obtain ⟨hs0, hsord⟩ := sBranch_order (C := C) ω a N hN (Ne.symm hgood)
  have hσ : s.order ≤ 0 := by rw [hsord]; omega
  have hXh := dS_branchW ω a N hN
  rw [SuperData.branchSub_eq_subst] at hXh
  have h := S.sumOrd_eq_resW' ω hx hK s _ hXh (branchSub N a) (branchSub_injective N hN a)
    (fun P ↦ by rw [SuperData.branchSub_eq_subst]) hs0 hσ Y hY Finset.univ (fun i : Fin k ↦ d i)
    u hu hu0 v f hv hf heq' (fun i hi ↦ hbelow i (by rw [hsord] at hi; omega))
  rw [hsord, show (1 - (N : ℤ)) - 1 = -(N : ℤ) by ring, hres, mul_comm _ (algebraMap C K ρ)] at h
  have hsc : s.coeff (1 - (N : ℤ)) ≠ 0 := by
    rw [← hsord]; exact (not_congr HahnSeries.coeff_order_eq_zero).mpr hs0
  have h2 := mul_right_cancel₀ hsc h
  apply (algebraMap C K).injective
  rw [← h2, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_intCast, mul_comm]

include hx hK in
/-- **The order of `∏ wⱼ^{eⱼ}`** (`eⱼ = M Λ(dⱼ)`) along a branch where `f` has residue `ρ`. -/
theorem order_logProd (k : ℕ) (d : ℕ → C) (w : ℕ → L)
    (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (a : K) (hgood : a′ ≠ (ω.map (algebraMap C K)).eval a) (N : ℕ) (hN : 0 < N)
    (Y : LaurentSeries K) (hY : (S.F.map (branchSub N a)).eval Y = 0) (ρ : C)
    (hbelow : ∀ i : ℤ, i < -(N : ℤ) →
      (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY ⟨f, hf⟩).coeff i = 0)
    (hres : (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY ⟨f, hf⟩).coeff (-(N : ℤ)) =
      (sBranch ω a N).coeff (1 - (N : ℤ)) * algebraMap C K ρ)
    (Λ : C →ₗ[ℚ] ℚ) (M : ℕ) (e : ℕ → ℤ) (he : ∀ j < k, (e j : ℚ) = M * Λ (d j))
    (hγ : (∏ j : Fin k, (w j) ^ (e j)) ∈ C⟮S.x⟯⟮S.y⟯) :
    ((S.embG (branchSub N a) (branchSub_injective N hN a) Y hY
      ⟨∏ j : Fin k, (w j) ^ (e j), hγ⟩).order : ℚ) = M * Λ ρ := by
  classical
  have hsum := S.sum_ord_eq_res ω hx hK k d w hw v f hv hf heq a hgood N hN Y hY ρ hbelow hres
  set φ := S.embG (branchSub N a) (branchSub_injective N hN a) Y hY
  have hprod : (⟨∏ j : Fin k, (w j) ^ (e j), hγ⟩ : C⟮S.x⟯⟮S.y⟯) =
      ∏ j : Fin k, (⟨w j, (hw j j.2).1⟩ : C⟮S.x⟯⟮S.y⟯) ^ (e j) :=
    Subtype.ext (by rw [IntermediateField.coe_prod]; rfl)
  have hφ0 : ∀ j : Fin k, φ ⟨w j, (hw j j.2).1⟩ ≠ 0 := fun j ↦
    (map_ne_zero_iff _ φ.injective).mpr fun h ↦ (hw j j.2).2 (congrArg Subtype.val h)
  rw [hprod, map_prod]
  simp only [map_zpow₀]
  rw [(order_prod_zpow_nk Finset.univ _ (fun j _ ↦ hφ0 j) _).2]
  push_cast
  rw [← hsum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [he j j.2, show ((φ ⟨w j, (hw j j.2).1⟩).order : C) * d j =
    (φ ⟨w j, (hw j j.2).1⟩).order • d j by rw [zsmul_eq_mul], map_zsmul, zsmul_eq_mul]
  ring

end CurveData

section Inf

open Differential

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K] [CharZero K]

open Classical in
/-- `deg R = ∑_{a ∈ U} mult_a R` over a finite set containing the roots. -/
lemma natDegree_eq_sum_mult (R : C[X]) (hR : R ≠ 0) (U : Finset K)
    (hU : (R.map (algebraMap C K)).roots.toFinset ⊆ U) :
    (R.natDegree : ℤ) = ∑ a ∈ U, ((R.map (algebraMap C K)).rootMultiplicity a : ℤ) := by
  classical
  have hR' : R.map (algebraMap C K) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hR
  rw [← Finset.sum_subset hU (fun a _ ha ↦ by
    rw [Multiset.mem_toFinset, mem_roots hR'] at ha
    have : rootMultiplicity a (R.map (algebraMap C K)) = 0 := rootMultiplicity_eq_zero ha
    rw [this]; rfl)]
  have h1 := Multiset.toFinset_sum_count_eq (R.map (algebraMap C K)).roots
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective
    (algebraMap C K).injective] at h1
  rw [← h1]
  push_cast
  exact Finset.sum_congr rfl fun a _ ↦ by rw [count_roots]

namespace CurveData

variable (S : CurveData C L)

/-- The sum of the orders of `W(x, y)` along a split fibre is the order of the norm. -/
lemma sum_order_eval (W : C[X][X]) (hW : S.evXY W ≠ 0) (hWn : W.natDegree < S.F.natDegree)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (l : List (LaurentSeries K))
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (l.map fun r ↦ ((W.map g).eval r).order).sum = (g (S.normW W S.F.natDegree)).order := by
  have hne := S.normW_ne_zero W S.F.natDegree hWn.le hW g hg l hl
  rw [S.branch_normW W S.F.natDegree hWn.le g l hl, order_list_prod _
    (S.branch_values_ne_zero W hW g hg l hl), List.map_map]
  rfl


/-- The sum over a list of a function constant on it. -/
lemma list_sum_const {β : Type*} (l : List β) (f : β → ℤ) (c : ℤ) (h : ∀ x ∈ l, f x = c) :
    (l.map f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx), List.length_cons]
    push_cast; ring

/-- **The order at infinity from the finite orders** (single place at infinity): if `z` has
order `o_{jk}` along the unramified branches above distinct points `α_j`, and order `0` at every
other finite branch, then `n · ord_∞ z = −N ∑ o_{jk}` along every branch `x = T^{−N}`. -/
theorem order_inf_of_finite (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) {J : Type*} [Fintype J]
    (α : J → K) (hα : Function.Injective α) (Y : J → Fin S.F.natDegree → LaurentSeries K)
    (hY : ∀ j, S.F.map (branchSub 1 (α j)) = ∏ k, (X - Polynomial.C (Y j k)))
    (o : J → Fin S.F.natDegree → ℤ)
    (ho : ∀ j k, (S.embG (branchSub 1 (α j)) (branchSub_injective 1 one_pos _) (Y j k)
      (S.root_of_split _ _ (hY j) k) z).order = o j k)
    (hother : ∀ b : K, b ∉ Set.range α → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) z).order = 0)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l) :
    (n : ℤ) * (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
      (S.root_of_mem hl hr) z).order = -((N : ℤ) * ∑ j, ∑ k, o j k) := by
  classical
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt z hF1
  have hxQ : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]; exact mul_ne_zero (fun h ↦ hz (Subtype.ext h)) hxQ
  set R := S.normW W S.F.natDegree with hR
  -- the order of `z` along a branch, from `W` and `Q`
  have hrel : ∀ (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (r : LaurentSeries K)
      (hr : (S.F.map g).eval r = 0),
      ((W.map g).eval r).order = (S.embG g hg r hr z).order + (g Q).order := fun g hg r hr ↦ by
    have he := S.eval_W_branch g hg r hr z W Q hWQ
    have h1 : S.embG g hg r hr z ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hz
    have h2 : g Q ≠ 0 := (map_ne_zero_iff _ hg).mpr hQ
    rw [he, HahnSeries.order_mul h1 h2]
  -- the fibre sums
  have hfib : ∀ (b : K) (M : ℕ) (hM : 0 < M) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub M b) = (l.map fun r ↦ X - Polynomial.C r).prod),
      (l.map fun r ↦ ((W.map (branchSub M b)).eval r).order).sum =
        M * ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) := fun b M hM l hl ↦ by
    rw [S.sum_order_eval W hW (by rw [hn] at hWn ⊢; exact hWn) _ (branchSub_injective M hM b) l hl]
    have hR0 := S.normW_ne_zero W S.F.natDegree hWn.le hW _ (branchSub_injective M hM b) l hl
    rw [order_branchSub M hM b R hR0]; push_cast; ring
  have hQo : ∀ (b : K) (M : ℕ) (hM : 0 < M),
      (branchSub M b Q).order = M * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ) :=
    fun b M hM ↦ by rw [order_branchSub M hM b Q hQ]; push_cast; ring
  -- outside the `α_j`: `mult R = n mult Q`
  have hout : ∀ b : K, b ∉ Set.range α → ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) =
      n * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ) := by
    intro b hb
    obtain ⟨M, hM, l0, hl0, hs0⟩ := S.branches_at b
    set l' := l0.map (HahnSeries.ofPowerSeries ℤ K) with hl'
    have hs' : S.F.map (branchSub M b) = (l'.map fun r ↦ X - Polynomial.C r).prod := by
      rw [hs0, hl', List.map_map]; rfl
    have h1 := hfib b M (Nat.pos_of_ne_zero hM) l' hs'
    have hlen : l'.length = n := by rw [hl', List.length_map, hl0, hn]
    rw [list_sum_const l' _ ((M : ℤ) * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ))
      (fun r hr' ↦ by
        rw [hrel _ (branchSub_injective M (Nat.pos_of_ne_zero hM) b) r (S.root_of_mem hs' hr'),
          hother b hb M hM l' hs' r hr', zero_add, hQo b M (Nat.pos_of_ne_zero hM)]), hlen] at h1
    have hMp : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
    have : (M : ℤ) * (n * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ)) =
        M * ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) := by rw [← h1]; ring
    exact (mul_left_cancel₀ hMp.ne' this).symm
  -- at the `α_j`
  have hat : ∀ j, ((R.map (algebraMap C K)).rootMultiplicity (α j) : ℤ) -
      n * ((Q.map (algebraMap C K)).rootMultiplicity (α j) : ℤ) = ∑ k, o j k := by
    intro j
    have hs' := S.list_of_fin (hY j)
    have h1 := hfib (α j) 1 one_pos _ hs'
    rw [List.map_ofFn, List.sum_ofFn] at h1
    have h2 : ∀ k, ((W.map (branchSub 1 (α j))).eval (Y j k)).order =
        o j k + ((Q.map (algebraMap C K)).rootMultiplicity (α j) : ℤ) := fun k ↦ by
      rw [hrel _ (branchSub_injective 1 one_pos _) (Y j k) (S.root_of_split _ _ (hY j) k), ho j k,
        hQo (α j) 1 one_pos]; ring
    simp only [Function.comp_apply, h2, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hnc : ((S.F.natDegree : ℕ) : ℤ) = n := by rw [hn]
    push_cast at h1
    linear_combination -h1 + ((Q.map (algebraMap C K)).rootMultiplicity (α j) : ℤ) * hnc
  -- the degrees
  have hR0 : R ≠ 0 := S.normW_ne_zero W S.F.natDegree hWn.le hW _
    (infSub_injective N (Nat.pos_of_ne_zero hN)) l hl
  set U : Finset K := (R.map (algebraMap C K)).roots.toFinset ∪
    (Q.map (algebraMap C K)).roots.toFinset ∪ Finset.univ.image α with hU
  have hdegR := natDegree_eq_sum_mult R hR0 U (by intro a ha; simp [hU, ha])
  have hdegQ := natDegree_eq_sum_mult Q hQ U (by intro a ha; simp [hU, ha])
  have hdeg : (R.natDegree : ℤ) - n * Q.natDegree = ∑ j, ∑ k, o j k := by
    rw [hdegR, hdegQ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := (R.map (algebraMap C K)).roots.toFinset ∪
      (Q.map (algebraMap C K)).roots.toFinset)) (fun a _ ha ↦ by
        rw [hout a (fun ⟨j, hj⟩ ↦ ha (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)), sub_self])]
    rw [Finset.sum_image (fun i _ j _ h ↦ hα h)]
    exact Finset.sum_congr rfl fun j _ ↦ hat j
  -- infinity: all branches have the same order
  have hNp := Nat.pos_of_ne_zero hN
  have hinf := hfib
  have hsumInf : (l.map fun r ↦ ((W.map (infSub N)).eval r).order).sum = -((N : ℤ) * R.natDegree) := by
    rw [S.sum_order_eval W hW (by rw [hn] at hWn ⊢; exact hWn) _ (infSub_injective N hNp) l hl,
      order_infSub N hNp R hR0]
  have hWn' : W.natDegree < n := by rw [← hn]; exact hWn
  have hW0 : W ≠ 0 := fun h ↦ hW (by rw [h]; simp [CurveData.evXY])
  have hconst : ∀ r' ∈ l, ((W.map (infSub N)).eval r').order = ((W.map (infSub N)).eval r).order := by
    intro r' hr'
    have h1 := (eval_order_inf S.F S.monic n d N hn hn0 hNp ha0 hd hw hcop r' (S.root_of_mem hl hr')
      W hW0 hWn').2
    have h2 := (eval_order_inf S.F S.monic n d N hn hn0 hNp ha0 hd hw hcop r (S.root_of_mem hl hr)
      W hW0 hWn').2
    have hnp : (0 : ℤ) < n := by exact_mod_cast hn0
    exact mul_left_cancel₀ hnp.ne' (h1.trans h2.symm)
  rw [list_sum_const l _ _ hconst, S.length_of_split hl, hn] at hsumInf
  have h3 := hrel (infSub N) (infSub_injective N hNp) r (S.root_of_mem hl hr)
  rw [order_infSub N hNp Q hQ] at h3
  rw [← hdeg]
  push_cast at h3 hsumInf ⊢
  linear_combination (n : ℤ) * h3.symm + hsumInf

end CurveData

end Inf

end Curves

namespace Curves

namespace CurveData

open Differential

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

open Classical in
/-- The order of `x − α` along a branch. -/
lemma order_xsub (α : C) (b : K) (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K)
    (hY : (S.F.map (branchSub N b)).eval Y = 0) :
    (S.embG (branchSub N b) (branchSub_injective N hN b) Y hY (S.polyF (X - Polynomial.C α))).order =
      if b = algebraMap C K α then (N : ℤ) else 0 := by
  have hP : (X - Polynomial.C α : C[X]) ≠ 0 := X_sub_C_ne_zero α
  have e : S.polyF (X - Polynomial.C α) = ⟨aeval S.x (X - Polynomial.C α), S.aeval_mem _⟩ :=
    Subtype.ext (S.coe_polyF _)
  rw [e, S.embG_polyX, order_branchSub N hN b _ hP, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, rootMultiplicity_X_sub_C]
  by_cases h : b = algebraMap C K α
  · simp [h]
  · simp [h]

/-- The order of `x − α` above infinity. -/
lemma order_xsub_inf (α : C) (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K)
    (hY : (S.F.map (infSub N)).eval Y = 0) :
    (S.embG (infSub N) (infSub_injective N hN) Y hY (S.polyF (X - Polynomial.C α))).order =
      -(N : ℤ) := by
  have hP : (X - Polynomial.C α : C[X]) ≠ 0 := X_sub_C_ne_zero α
  have e : S.polyF (X - Polynomial.C α) = ⟨aeval S.x (X - Polynomial.C α), S.aeval_mem _⟩ :=
    Subtype.ext (S.coe_polyF _)
  rw [e, S.embG_polyX, order_infSub N hN _ hP, natDegree_X_sub_C]
  simp


lemma rat_mul_den_int (q : ℚ) (m : ℕ) (h : q.den ∣ m) :
    ((q.num * ((m / q.den : ℕ) : ℤ) : ℤ) : ℚ) = q * m := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ q.den_pos]
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

include hx hK in
/-- **A Liouville form makes the residue divisor torsion**: from `f = v′ + ∑ dⱼ wⱼ′/wⱼ`
(ℚ-independent `dⱼ`) with residues `ρ_{jk}` at the unramified points `(α_j, y_{jk})`, residue-free
elsewhere at finite places, and `Γ_{jk} = s Λ(ρ_{jk}) + e_j` (`∑ Γ = c n`), some function `γ ≠ 0`
has `div γ ≥ M Γ − M c ∞ₓ` (single place at infinity). -/
theorem divGEU_of_liouville (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (n dd : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = dd)
    (hw' : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < dd * (n - i))
    (hcop : Nat.Coprime n dd) (k : ℕ) (d : ℕ → C) (w : ℕ → L)
    (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α)
    (ys : J → Fin S.F.natDegree → C) (hys : ∀ j, Function.Injective (ys j))
    (Y : J → Fin S.F.natDegree → PowerSeries K)
    (hY : ∀ j, S.F.map (branchSub 1 (algebraMap C K (α j))) =
      ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ K (Y j k))))
    (hYc : ∀ j k, PowerSeries.constantCoeff (Y j k) = algebraMap C K (ys j k))
    (ρ : J → Fin S.F.natDegree → C)
    (hbelow : ∀ j k (i : ℤ), i < -1 → (S.embG (branchSub 1 (algebraMap C K (α j)))
      (branchSub_injective 1 one_pos _) _ (S.root_of_split _ _ (hY j) k) ⟨f, hf⟩).coeff i = 0)
    (hres : ∀ j k, (S.embG (branchSub 1 (algebraMap C K (α j)))
      (branchSub_injective 1 one_pos _) _ (S.root_of_split _ _ (hY j) k) ⟨f, hf⟩).coeff (-1) =
        (sBranch ω (algebraMap C K (α j)) 1).coeff 0 * algebraMap C K (ρ j k))
    (hfree : ∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l) (i : ℤ), i < 1 - (N : ℤ) →
      (S.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S.root_of_mem hl hr) ⟨f, hf⟩).coeff i = 0)
    (Λ : C →ₗ[ℚ] ℚ) (sc : ℕ) (eS : J → ℤ) (Γ : J → Fin S.F.natDegree → ℕ) (cdeg : ℕ)
    (hΓ : ∀ j k, (Γ j k : ℚ) = sc * Λ (ρ j k) + eS j)
    (hsum : ∑ j, ∑ k, Γ j k = cdeg * n) :
    ∃ M : ℕ, 0 < M ∧ ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGEU (K := K) α ys (fun j k ↦ M * Γ j k) (M * cdeg) γ := by
  classical
  -- the integer exponents
  set M : ℕ := ∏ j ∈ Finset.range k, (Λ (d j)).den with hM
  have hMpos : 0 < M := Finset.prod_pos fun j _ ↦ (Λ (d j)).den_pos
  set e : ℕ → ℤ := fun j ↦ (Λ (d j)).num * ((M / (Λ (d j)).den : ℕ) : ℤ) with he
  have he' : ∀ j < k, (e j : ℚ) = M * Λ (d j) := fun j hj ↦ by
    have hdv : (Λ (d j)).den ∣ M := Finset.dvd_prod_of_mem (fun j ↦ (Λ (d j)).den)
      (Finset.mem_range.mpr hj)
    have := rat_mul_den_int (Λ (d j)) M hdv
    rw [he]; dsimp only
    rw [this, mul_comm]
  -- `γ₀ = ∏ wⱼ^{eⱼ}`
  have hγ0m : (∏ j : Fin k, (w j) ^ (e j)) ∈ C⟮S.x⟯⟮S.y⟯ :=
    prod_mem fun j _ ↦ zpow_mem (hw j j.2).1 _
  have hγ00 : (∏ j : Fin k, (w j) ^ (e j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hw j j.2).2
  set γ0 : C⟮S.x⟯⟮S.y⟯ := ⟨_, hγ0m⟩ with hγ0
  set γ : C⟮S.x⟯⟮S.y⟯ := γ0 ^ sc * ∏ j, (S.polyF (X - Polynomial.C (α j))) ^ ((M : ℤ) * eS j)
    with hγ
  have hxs0 : ∀ j, S.polyF (X - Polynomial.C (α j)) ≠ 0 := fun j h ↦ by
    have := congrArg Subtype.val h
    rw [S.coe_polyF] at this
    exact (X_sub_C_ne_zero (α j)) ((transcendental_iff.mp S.htr) _ this)
  have hγ0ne : γ0 ≠ 0 := fun h ↦ hγ00 (congrArg Subtype.val h)
  have hγne : γ ≠ 0 := mul_ne_zero (pow_ne_zero _ hγ0ne)
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hxs0 j))
  -- the order of `γ` along a finite branch
  have hordγ : ∀ (b : K) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
      (hr : (S.F.map (branchSub N b)).eval r = 0),
      (S.embG (branchSub N b) (branchSub_injective N hN b) r hr γ).order =
        sc * (S.embG (branchSub N b) (branchSub_injective N hN b) r hr γ0).order +
          ∑ j, (M : ℤ) * eS j * (if b = algebraMap C K (α j) then (N : ℤ) else 0) := by
    intro b N hN r hr
    set φ := S.embG (branchSub N b) (branchSub_injective N hN b) r hr
    have h0 : φ γ0 ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr hγ0ne
    have h1 : ∀ j, φ (S.polyF (X - Polynomial.C (α j))) ≠ 0 := fun j ↦
      (map_ne_zero_iff _ φ.injective).mpr (hxs0 j)
    rw [hγ, map_mul, map_pow, map_prod]
    simp only [map_zpow₀]
    rw [HahnSeries.order_mul (pow_ne_zero _ h0) (Finset.prod_ne_zero_iff.mpr fun j _ ↦
      zpow_ne_zero _ (h1 j)), HahnSeries.order_pow, nsmul_eq_mul,
      (order_prod_zpow_nk Finset.univ _ (fun j _ ↦ h1 j) _).2]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [S.order_xsub (α j) b N hN r hr]
  -- the orders of `γ₀`
  have hγ0α : ∀ jj kk, ((S.embG (branchSub 1 (algebraMap C K (α jj)))
      (branchSub_injective 1 one_pos _) _ (S.root_of_split _ _ (hY jj) kk) γ0).order : ℚ) =
        M * Λ (ρ jj kk) := fun jj kk ↦
    S.order_logProd ω hx hK k d w hw v f hv hf heq _ (hnd _) 1 one_pos _ _ (ρ jj kk)
      (fun i hi ↦ hbelow jj kk i (by simpa using hi)) (by have := hres jj kk; simpa using this) Λ M e
      he' hγ0m
  have hγ0o : ∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) γ0).order = 0 := by
    intro b hb N hN l hl r hr
    have h := S.order_logProd ω hx hK k d w hw v f hv hf heq b (hnd b) N (Nat.pos_of_ne_zero hN) r
      (S.root_of_mem hl hr) 0 (fun i hi ↦ hfree b hb N hN l hl r hr i (by omega))
      (by rw [map_zero, mul_zero]; exact hfree b hb N hN l hl r hr _ (by omega)) Λ M e he' hγ0m
    rw [map_zero, mul_zero] at h
    exact_mod_cast h
  -- the orders of `γ`
  have hαK : Function.Injective (fun j ↦ algebraMap C K (α j)) :=
    fun i j h ↦ hα ((algebraMap C K).injective h)
  have hγα : ∀ j k, (S.embG (branchSub 1 (algebraMap C K (α j))) (branchSub_injective 1 one_pos _)
      _ (S.root_of_split _ _ (hY j) k) γ).order = M * Γ j k := by
    intro j k
    rw [hordγ _ 1 one_pos, Finset.sum_eq_single j (fun j' _ hj' ↦ by
      rw [if_neg (fun h ↦ hj' (hαK h.symm)), mul_zero]) (by simp), if_pos rfl]
    have h1 := hγ0α j k
    have h2 := hΓ j k
    have : ((sc * (S.embG (branchSub 1 (algebraMap C K (α j))) (branchSub_injective 1 one_pos _)
        _ (S.root_of_split _ _ (hY j) k) γ0).order + (M : ℤ) * eS j * ((1 : ℕ) : ℤ) : ℤ) : ℚ) =
        ((M * Γ j k : ℕ) : ℚ) := by
      push_cast
      rw [h1, h2]; ring
    exact_mod_cast this
  have hγo : ∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) γ).order = 0 := by
    intro b hb N hN l hl r hr
    rw [hordγ b N (Nat.pos_of_ne_zero hN), hγ0o b hb N hN l hl r hr, mul_zero, zero_add]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [if_neg (fun h ↦ hb ⟨j, h.symm⟩), mul_zero]
  refine ⟨M, hMpos, γ, hγne, ⟨fun j k Yp hY' hc ↦ ?_, fun b hb N hN l hl r hr ↦ ?_,
    fun N hN l hl r hr ↦ ?_⟩⟩
  · have hinj : Function.Injective fun k ↦ PowerSeries.constantCoeff (Y j k) := fun k1 k2 h ↦ by
      simp only at h
      rw [hYc, hYc] at h
      exact hys j ((algebraMap C K).injective h)
    have hYe := S.unram_root_unique (algebraMap C K (α j)) (Y j) (hY j) hinj k Yp hY'
      (by rw [hc, hYc])
    subst hYe
    rw [hγα j k]
    push_cast; exact le_refl _
  · rw [hγo b hb N hN l hl r hr]
  · have h := S.order_inf_of_finite n dd hn hn0 ha0 hd hw' hcop γ hγne (fun j ↦ algebraMap C K (α j))
      hαK (fun j k ↦ HahnSeries.ofPowerSeries ℤ K (Y j k)) hY (fun j k ↦ (M * Γ j k : ℕ))
      (fun j k ↦ by rw [hγα j k]; push_cast; ring) hγo N hN l hl r hr
    have hs : (∑ j, ∑ k, ((M * Γ j k : ℕ) : ℤ)) = M * cdeg * n := by
      push_cast
      simp only [← Finset.mul_sum]
      rw [show (∑ j, ∑ k, (Γ j k : ℤ)) = ((∑ j, ∑ k, Γ j k : ℕ) : ℤ) by push_cast; rfl, hsum]
      push_cast; ring
    rw [hs] at h
    have hnp : (0 : ℤ) < n := by exact_mod_cast hn0
    have h2 : (n : ℤ) * (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr) γ).order = n * (-((N * (M * cdeg) : ℕ) : ℤ)) := by
      rw [h]; push_cast; ring
    rw [mul_left_cancel₀ hnp.ne' h2]

end CurveData

end Curves

namespace Curves

section SimplePole

variable {K : Type*} [Field K]

/-- **A simple pole**: `e/g` with `g(0) = 0 ≠ g′(0)` has no coefficient below `−1`, and
`(e/g)₋₁ = e(0)/g′(0)`. -/
lemma laurent_simple_pole (e g : PowerSeries K) (hg0 : PowerSeries.constantCoeff g = 0)
    (hg1 : PowerSeries.coeff 1 g ≠ 0) :
    (∀ i : ℤ, i < -1 → (HahnSeries.ofPowerSeries ℤ K e / HahnSeries.ofPowerSeries ℤ K g).coeff i = 0) ∧
    (HahnSeries.ofPowerSeries ℤ K e / HahnSeries.ofPowerSeries ℤ K g).coeff (-1) =
      PowerSeries.constantCoeff e / PowerSeries.coeff 1 g := by
  obtain ⟨g1, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg0
  have hc1 : PowerSeries.constantCoeff g1 ≠ 0 := by
    rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hg1
  have hinv : HahnSeries.ofPowerSeries ℤ K g1 * HahnSeries.ofPowerSeries ℤ K g1⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel _ hc1, map_one]
  have hg1ne : HahnSeries.ofPowerSeries ℤ K g1 ≠ 0 := fun h ↦ by
    rw [h, zero_mul] at hinv; exact zero_ne_one hinv
  have hq : HahnSeries.ofPowerSeries ℤ K e / HahnSeries.ofPowerSeries ℤ K (PowerSeries.X * g1) =
      HahnSeries.ofPowerSeries ℤ K (e * g1⁻¹) * HahnSeries.single (-1 : ℤ) (1 : K) := by
    rw [map_mul, map_mul, HahnSeries.ofPowerSeries_X, div_eq_mul_inv, mul_inv,
      eq_inv_of_mul_eq_one_right hinv]
    have hs : (HahnSeries.single (1 : ℤ) (1 : K))⁻¹ = HahnSeries.single (-1 : ℤ) 1 := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [HahnSeries.single_mul_single]; simp
    rw [hs]; ring
  rw [hq]
  have hcoef : ∀ i : ℤ, (HahnSeries.ofPowerSeries ℤ K (e * g1⁻¹) *
      HahnSeries.single (-1 : ℤ) (1 : K)).coeff i =
        (HahnSeries.ofPowerSeries ℤ K (e * g1⁻¹)).coeff (i + 1) := fun i ↦ by
    have := HahnSeries.coeff_mul_single_add (r := (1 : K))
      (x := HahnSeries.ofPowerSeries ℤ K (e * g1⁻¹)) (a := i + 1) (b := -1)
    rw [show i + 1 + -1 = i by ring, mul_one] at this
    exact this
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [hcoef, HahnSeries.ofPowerSeries_apply]
    refine HahnSeries.embDomain_notin_range ?_
    rintro ⟨n, hn⟩
    have : ((n : ℕ) : ℤ) = i + 1 := hn
    omega
  · rw [hcoef, show (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) by norm_num, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_inv,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, div_eq_mul_inv]

end SimplePole

section SimplePoleCurve

open Differential

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **The expansion of `B(x, y)/D(x)` at a simple root `α` of `D`** along an unramified branch
`y = Y(T)`: no term below `T⁻¹`, and `(B/D)₋₁ = B(α, Y(0))/D′(α)`. -/
lemma embG_simple_pole (B : C[X][X]) (D : C[X]) (α : C) (hD0 : D.eval α = 0)
    (hD1 : (derivative D).eval α ≠ 0) (Yp : PowerSeries K)
    (hY : (S.F.map (branchSub 1 (algebraMap C K α))).eval (HahnSeries.ofPowerSeries ℤ K Yp) = 0)
    (hf : S.evXY B / aeval S.x D ∈ C⟮S.x⟯⟮S.y⟯) :
    (∀ i : ℤ, i < -1 → (S.embG (branchSub 1 (algebraMap C K α)) (branchSub_injective 1 one_pos _)
      _ hY ⟨_, hf⟩).coeff i = 0) ∧
    (S.embG (branchSub 1 (algebraMap C K α)) (branchSub_injective 1 one_pos _) _ hY ⟨_, hf⟩).coeff
      (-1) = ((B.map (Polynomial.mapRingHom (algebraMap C K))).map
        (Polynomial.evalRingHom (algebraMap C K α))).eval (PowerSeries.constantCoeff Yp) /
          algebraMap C K ((derivative D).eval α) := by
  set a := algebraMap C K α with ha
  set g' : C[X] →+* PowerSeries K := (Polynomial.coeToPowerSeries.ringHom (R := K)).comp
    ((Polynomial.compRingHom (Polynomial.C a + X ^ 1)).comp
      (Polynomial.mapRingHom (algebraMap C K))) with hg'
  have hg : branchSub (C := C) (K := K) 1 a = (HahnSeries.ofPowerSeries ℤ K).comp g' := rfl
  have hfe : (⟨_, hf⟩ : C⟮S.x⟯⟮S.y⟯) = S.evT B / ⟨aeval S.x D, S.aeval_mem D⟩ :=
    Subtype.ext (by rw [IntermediateField.coe_div, S.coe_evT])
  rw [hfe, map_div₀, S.embG_evT, S.embG_polyX, hg, RingHom.comp_apply, eval_map]
  have hE : Polynomial.eval₂ ((HahnSeries.ofPowerSeries ℤ K).comp g')
      (HahnSeries.ofPowerSeries ℤ K Yp) B =
      HahnSeries.ofPowerSeries ℤ K (Polynomial.eval₂ g' Yp B) :=
    (Polynomial.hom_eval₂ B g' (HahnSeries.ofPowerSeries ℤ K) Yp).symm
  erw [hE]
  -- the denominator `D(a + T)`
  have hgD : ∀ P : C[X], g' P = ((Polynomial.taylor a (P.map (algebraMap C K)) : K[X]) :
      PowerSeries K) := fun P ↦ by
    rw [hg', RingHom.comp_apply, RingHom.comp_apply, Polynomial.taylor_apply, pow_one, add_comm]
    rfl
  have h0 : PowerSeries.constantCoeff (g' D) = 0 := by
    rw [hgD, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.taylor_coeff_zero, eval_map, ha, Polynomial.eval₂_at_apply, hD0, map_zero]
  have h1v : PowerSeries.coeff 1 (g' D) = algebraMap C K ((derivative D).eval α) := by
    rw [hgD, Polynomial.coeff_coe, Polynomial.taylor_coeff_one, Polynomial.derivative_map, eval_map,
      ha, Polynomial.eval₂_at_apply]
  have h1 : PowerSeries.coeff 1 (g' D) ≠ 0 := by
    rw [h1v]; exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr hD1
  obtain ⟨hb, hc⟩ := laurent_simple_pole (Polynomial.eval₂ g' Yp B) (g' D) h0 h1
  refine ⟨hb, ?_⟩
  rw [hc, h1v]
  congr 1
  -- the constant term of the numerator
  have hcc : (PowerSeries.constantCoeff (R := K)).comp g' =
      (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (algebraMap C K)) := by
    refine RingHom.ext fun P ↦ ?_
    rw [RingHom.comp_apply, hgD, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, Polynomial.taylor_coeff_zero]
    rfl
  rw [Polynomial.hom_eval₂, hcc, eval_map, Polynomial.eval₂_map]

end CurveData

end SimplePoleCurve

end Curves
