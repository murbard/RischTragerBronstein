import RischTragerBronstein.Torsion.IBExist3
import RischTragerBronstein.Torsion.Degree

/-!
# Integral bases exist (4): no integral function vanishes at infinity

**`evXY_eq_zero_of_vanish`**: if `W(x, y)/D(x)` (`deg_y W < n`, `D` split with roots at points
carrying branch systems `σ`) is regular along every `σ` and has positive order along every branch
of a system above infinity, then `W(x, y) = 0`. The product of the branch values of `W` is the norm
(`sum_order_fin`, `sum_order_inf`): regularity gives `mult_b N(W) ≥ n mult_b D` at every root `b`
of `D`, positivity at infinity gives `deg N(W) < n deg D`, a contradiction.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Vanish

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- A branch system above infinity, with coefficients in `C`. -/
structure InfSys where
  N : ℕ
  hN : 0 < N
  r : Fin S.F.natDegree → LaurentSeries C
  hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k))

variable {S}

/-- The expansion of `f` along the `k`-th branch above infinity. -/
noncomputable def InfSys.ev (τ : S.InfSys) (k : Fin S.F.natDegree) (f : C⟮S.x⟯⟮S.y⟯) :
    LaurentSeries C :=
  S.embG (infSub τ.N) (infSub_injective _ τ.hN) (τ.r k) (S.root_of_split _ τ.r τ.hs k) f

lemma order_mul_inv {K : Type*} [Field K] {x y : LaurentSeries K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y⁻¹).order = x.order - y.order := by
  have h1 : (x * y⁻¹).order + y.order = x.order := by
    rw [← HahnSeries.order_mul (mul_ne_zero hx (inv_ne_zero hy)) hy, mul_assoc,
      inv_mul_cancel₀ hy, mul_one]
  omega

lemma sum_mult_le (P : C[X]) (T : Finset C) : ∑ b ∈ T, P.rootMultiplicity b ≤ P.natDegree := by
  classical
  by_cases hP : P = 0
  · simp [hP]
  have h1 : ∑ b ∈ T, P.rootMultiplicity b = (P.roots.filter (· ∈ T)).card := by
    rw [← Multiset.sum_count_eq_card (s := T) (m := P.roots.filter (· ∈ T))
      (fun a ha ↦ (Multiset.mem_filter.mp ha).2)]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Multiset.count_filter_of_pos ha, count_roots]
  rw [h1]
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (card_roots' P)

/-- **No integral function vanishes at infinity.** -/
theorem evXY_eq_zero_of_vanish (A : List S.LocSys) (τ : S.InfSys) (W : C[X][X])
    (hW : W.natDegree < S.F.natDegree) (D : C[X]) (hD : D ≠ 0)
    (hsplit : Multiset.card D.roots = D.natDegree)
    (hroots : ∀ b, D.IsRoot b → ∃ σ ∈ A, σ.a = b)
    (hreg : ∀ σ ∈ A, ∀ k, LowerBd (σ.ev k (S.fnWQ W D)) 0)
    (hinf : ∀ k, LowerBd (τ.ev k (S.fnWQ W D)) 0) (k₀ : Fin S.F.natDegree)
    (hk₀ : LowerBd (τ.ev k₀ (S.fnWQ W D)) 1) : S.evXY W = 0 := by
  classical
  by_contra hW0
  let n := S.F.natDegree
  have hn : n = S.F.natDegree := rfl
  have hn0 : 0 < n := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  have hWm : W.natDegree ≤ n - 1 := by omega
  set P := (S.normW W (n - 1)).map (algebraMap C C) with hP
  have hPe : P = S.normW W (n - 1) := by rw [hP, Algebra.algebraMap_self, Polynomial.map_id]
  -- infinity
  have hlI : S.F.map (infSub τ.N) = ((List.ofFn τ.r).map fun r ↦ X - Polynomial.C r).prod := by
    rw [τ.hs, List.map_ofFn, List.prod_ofFn]; rfl
  have hsumI := S.sum_order_inf W (n - 1) hWm hW0 τ.N τ.hN _ hlI
  have hPne : S.normW W (n - 1) ≠ 0 :=
    S.normW_ne_zero W (n - 1) hWm hW0 _ (infSub_injective _ τ.hN) _ hlI
  have hDI : (infSub (K := C) τ.N D) ≠ 0 := (map_ne_zero_iff _ (infSub_injective _ τ.hN)).mpr hD
  have hordI : ∀ k (m : ℤ), LowerBd (τ.ev k (S.fnWQ W D)) m →
      m ≤ ((W.map (infSub τ.N)).eval (τ.r k)).order + τ.N * D.natDegree := by
    intro k m h1
    have hne := S.branch_values_ne_zero W hW0 _ (infSub_injective _ τ.hN) _ hlI _
      (List.mem_map.mpr ⟨τ.r k, List.mem_ofFn.mpr ⟨k, rfl⟩, rfl⟩)
    rw [InfSys.ev, S.embG_fnWQ] at h1
    have h2 := le_order_of_lowerBd _ (mul_ne_zero hne (inv_ne_zero hDI)) m h1
    rw [order_mul_inv hne hDI, order_infSub τ.N τ.hN D hD] at h2
    push_cast at h2 ⊢
    linarith
  have hI : (1 : ℤ) ≤ -(τ.N * (S.normW W (n - 1)).natDegree : ℤ) + n * (τ.N * D.natDegree) := by
    set f : Fin S.F.natDegree → ℤ := fun k ↦ ((W.map (infSub τ.N)).eval (τ.r k)).order +
      τ.N * (D.natDegree : ℤ) with hf
    have hsum : ((List.ofFn τ.r).map fun r ↦ ((W.map (infSub τ.N)).eval r).order +
        τ.N * (D.natDegree : ℤ)).sum = ∑ k, f k := by
      rw [List.map_ofFn, List.sum_ofFn]; rfl
    have h1 : (1 : ℤ) ≤ ∑ k, f k := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
      have h0 : 0 ≤ ∑ k ∈ Finset.univ.erase k₀, f k :=
        Finset.sum_nonneg fun k _ ↦ hordI k 0 (hinf k)
      have := hordI k₀ 1 hk₀
      linarith
    rw [← hsum, list_sum_map_add', hsumI, List.length_ofFn] at h1
    rw [← hn] at h1
    linarith
  -- the roots of `D`
  have hfin : ∀ b ∈ D.roots.toFinset, n * D.rootMultiplicity b ≤ P.rootMultiplicity b := by
    intro b hb
    obtain ⟨σ, hσ, rfl⟩ := hroots b (by
      have := Multiset.mem_toFinset.mp hb
      exact (mem_roots hD).mp this)
    have hl : S.F.map (branchSub σ.N (algebraMap C C σ.a)) =
        ((List.ofFn σ.r).map fun r ↦ X - Polynomial.C r).prod := by
      rw [σ.hs, List.map_ofFn, List.prod_ofFn]; rfl
    have hsum := S.sum_order_fin W (n - 1) hWm hW0 σ.N σ.hN _ _ hl
    have hDg : branchSub (C := C) σ.N (algebraMap C C σ.a) D ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective _ σ.hN _)).mpr hD
    have hoD := order_branchSub σ.N σ.hN (algebraMap C C σ.a) D hD
    rw [Algebra.algebraMap_self, Polynomial.map_id] at hoD
    have hk : ∀ k, (σ.N * D.rootMultiplicity σ.a : ℤ) ≤
        ((W.map (branchSub σ.N (algebraMap C C σ.a))).eval (σ.r k)).order := by
      intro k
      have hne := S.branch_values_ne_zero W hW0 _ (branchSub_injective _ σ.hN _) _ hl _
        (List.mem_map.mpr ⟨σ.r k, List.mem_ofFn.mpr ⟨k, rfl⟩, rfl⟩)
      have h1 := hreg σ hσ k
      rw [LocSys.ev, S.embG_fnWQ] at h1
      have h2 := le_order_of_lowerBd _ (mul_ne_zero hne (inv_ne_zero hDg)) 0 h1
      rw [order_mul_inv hne hDg] at h2
      simp only [RingHom.id_apply, Algebra.algebraMap_self] at hoD h2
      rw [hoD] at h2
      push_cast at h2
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      linarith
    have h1 : ((List.ofFn σ.r).map fun _ ↦ (σ.N * D.rootMultiplicity σ.a : ℤ)).sum ≤
        ((List.ofFn σ.r).map fun r ↦
          ((W.map (branchSub σ.N (algebraMap C C σ.a))).eval r).order).sum :=
      List.sum_le_sum fun r hr ↦ by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
        exact hk k
    rw [hsum, List.map_const', List.sum_replicate, List.length_ofFn] at h1
    simp only [nsmul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [Polynomial.map_id, ← hPe, ← hn] at h1
    have : ((n * D.rootMultiplicity σ.a : ℕ) : ℤ) * σ.N ≤ (P.rootMultiplicity σ.a : ℤ) * σ.N := by
      push_cast; nlinarith
    have hN' : (0 : ℤ) < σ.N := by exact_mod_cast σ.hN
    exact_mod_cast le_of_mul_le_mul_right this hN'
  -- degrees
  have hdegD : D.natDegree = ∑ b ∈ D.roots.toFinset, D.rootMultiplicity b := by
    rw [← hsplit, ← Multiset.toFinset_sum_count_eq]
    exact Finset.sum_congr rfl fun b _ ↦ count_roots D
  have h1 : n * D.natDegree ≤ P.natDegree := by
    rw [hdegD, Finset.mul_sum]
    exact (Finset.sum_le_sum hfin).trans (sum_mult_le P _)
  rw [hPe] at h1
  have hN : (0 : ℤ) < τ.N := by exact_mod_cast τ.hN
  have : (n : ℤ) * D.natDegree ≤ (S.normW W (n - 1)).natDegree := by exact_mod_cast h1
  nlinarith

end CurveData

end Vanish

end Curves
