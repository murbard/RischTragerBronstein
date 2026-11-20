import RischTragerBronstein.Torsion.NonSpec5

/-!
# Non-special base points exist (6): admissible fibres and descent

* `det_evalW`: `[Bⱼ(x, yₖ)] = Vandermonde(y) · [coeffᵢ Bⱼ (x)]` (for `deg_Y Bⱼ < n`);
* **`exists_admFib`**: over an algebraically closed field, for `G ≠ 0` such that `G(x) ≠ 0` forces
  the discriminant of `F(x, Y)` and `det [coeffᵢ Bⱼ](x)` to be nonzero, there are admissible fibres
  of roots of `F` above abscissae outside any finite set with `G(x) ≠ 0`;
* `AdmFib.map`, **`kerSp_descend`**: the property `kerSp ≤ span e0` descends along a field
  embedding `F → K`.
-/

open Polynomial Module

namespace Curves

open CPoly Sup GTors

section Adm

variable {K : Type*} [Field K] {n : ℕ}

lemma evalW_eq_sum_fin (V : K[X][X]) (hV : V.natDegree < n) (x y : K) :
    evalW V x y = ∑ i : Fin n, (V.coeff i).eval x * y ^ (i : ℕ) := by
  rw [evalW, eval_eq_sum_range' (n := n) ((natDegree_map_le).trans_lt hV), ← Fin.sum_univ_eq_sum_range]
  simp [coeff_map]

lemma det_evalW (B : Fin n → K[X][X]) (hB : ∀ j, (B j).natDegree < n) (x : K) (ys : Fin n → K) :
    (Matrix.of fun (k j : Fin n) ↦ evalW (B j) x (ys k)).det =
      (Matrix.vandermonde ys).det * (Matrix.of fun (i j : Fin n) ↦ ((B j).coeff i).eval x).det := by
  rw [← Matrix.det_mul]
  congr 1
  ext k j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vandermonde_apply, evalW_eq_sum_fin _ (hB j)]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

variable [IsAlgClosed K] [CharZero K]

/-- **Admissible fibres exist** outside any finite set. -/
theorem exists_admFib (F : K[X][X]) (hmon : F.Monic) (hdeg : F.natDegree = n)
    (B : Fin n → K[X][X]) (hB : ∀ j, (B j).natDegree < n) (G : K[X]) (hG0 : G ≠ 0)
    (hGd : ∀ x, G.eval x ≠ 0 → (resultant F (derivative F) n (n - 1)).eval x ≠ 0 ∧
      (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i).det.eval x ≠ 0) (s : Finset K) :
    ∃ fb : AdmFib B, fb.x ∉ s ∧ G.eval fb.x ≠ 0 ∧ ∀ k, evalW F fb.x (fb.ys k) = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (s ∪ G.roots.toFinset)
  simp only [Finset.mem_union, Multiset.mem_toFinset, mem_roots hG0, IsRoot.def, not_or] at hx
  obtain ⟨hr, hd⟩ := hGd x hx.2
  set p := F.map (evalRingHom x) with hp
  have hpm : p.Monic := hmon.map _
  have hpd : p.natDegree = n := by rw [hp, hmon.natDegree_map, hdeg]
  have hres : resultant p (derivative p) n (n - 1) ≠ 0 := by
    rw [hp, ← resultant_map_deriv]; exact hr
  have hsep : p.Separable := by
    have h' : resultant p (derivative p) ≠ 0 := by
      rw [natDegree_derivative, hpd]; exact hres
    by_contra hs
    exact h' (resultant_eq_zero_iff.mpr ⟨Or.inl hpm.ne_zero, hs⟩)
  set R := p.roots.toFinset
  have hcard : Fintype.card R = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hpd]
  set e := Fintype.equivFinOfCardEq hcard
  set ys : Fin n → K := fun k ↦ (e.symm k : K)
  have hinj : Function.Injective ys := fun a b h ↦ e.symm.injective (Subtype.ext h)
  have hroot : ∀ k, evalW F x (ys k) = 0 := fun k ↦ by
    have := (e.symm k).2
    simp only [R, Multiset.mem_toFinset, mem_roots hpm.ne_zero, IsRoot.def] at this
    exact this
  refine ⟨⟨x, ys, ?_⟩, hx.1, hx.2, hroot⟩
  rw [det_evalW B hB x ys]
  refine mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hinj) ?_
  have := RingHom.map_det (evalRingHom x) (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i)
  rw [coe_evalRingHom] at this
  rw [show (Matrix.of fun (i j : Fin n) ↦ ((B j).coeff i).eval x) =
    (evalRingHom x).mapMatrix (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i) by ext; simp, ← this]
  exact hd

end Adm

section Descend

variable {F K : Type*} [Field F] [Field K] (ρ : F →+* K) {n : ℕ} {B : Fin n → F[X][X]}

/-- An admissible fibre over `K` from one over `F`. -/
noncomputable def AdmFib.map (fb : AdmFib B) : AdmFib (fun j ↦ (B j).map (mapRingHom ρ)) where
  x := ρ fb.x
  ys := fun k ↦ ρ (fb.ys k)
  hdet := by
    have := RingHom.map_det ρ (Matrix.of fun (k j : Fin n) ↦ evalW (B j) fb.x (fb.ys k))
    rw [show (Matrix.of fun (k j : Fin n) ↦ evalW ((B j).map (mapRingHom ρ)) (ρ fb.x) (ρ (fb.ys k))) =
      ρ.mapMatrix (Matrix.of fun (k j : Fin n) ↦ evalW (B j) fb.x (fb.ys k)) by
        ext; simp [evalW_mapG], ← this]
    exact (map_ne_zero ρ).mpr fb.hdet

lemma exists_pre (fb : AdmFib (fun j ↦ (B j).map (mapRingHom ρ))) (x : F) (hx : ρ x = fb.x)
    (ys : Fin n → F) (hys : ∀ k, ρ (ys k) = fb.ys k) :
    ∃ fb' : AdmFib B, fb'.x = x ∧ fb'.ys = ys ∧ fb'.map ρ = fb := by
  have hdet : (Matrix.of fun (k j : Fin n) ↦ evalW (B j) x (ys k)).det ≠ 0 := by
    intro h0
    apply fb.hdet
    have := RingHom.map_det ρ (Matrix.of fun (k j : Fin n) ↦ evalW (B j) x (ys k))
    rw [h0, map_zero] at this
    rw [this]
    congr 1
    ext k j
    simp [← evalW_mapG, hx, hys]
  refine ⟨⟨x, ys, hdet⟩, rfl, rfl, ?_⟩
  cases fb
  simp only [AdmFib.map, AdmFib.mk.injEq]
  exact ⟨hx, funext hys⟩

variable (δ : Fin n → ℕ)

lemma mem_Vsp_map {m : ℕ} (c : Fin n → F[X]) (hc : c ∈ Vsp F δ m) :
    (fun j ↦ (c j).map ρ) ∈ Vsp K δ m := by
  rw [mem_Vsp] at hc ⊢
  intro j
  have := hc j
  rw [mem_degreeLT] at this ⊢
  rwa [degree_map]

lemma evPt_map (x y : F) (c : Fin n → F[X]) :
    evPt (fun j ↦ (B j).map (mapRingHom ρ)) (ρ x) (ρ y) (fun j ↦ (c j).map ρ) = ρ (evPt B x y c) := by
  simp only [evPt_apply, map_sum, map_mul, evalW_mapG, eval_map, Polynomial.eval₂_at_apply]

lemma prodX_map {r : ℕ} (f : Fin r → AdmFib B) : prodX (fun l ↦ (f l).map ρ) = (prodX f).map ρ := by
  simp [prodX, Polynomial.map_prod, AdmFib.map]

variable (hn : 0 < n)

/-- **Descent of `kerSp ≤ span e0`.** -/
theorem kerSp_descend (m r : ℕ) (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n)
    (h : kerSp δ m r (fun l ↦ (f l).map ρ) j₀ ≤ K ∙ e0 hn (fun l ↦ (f l).map ρ)) :
    kerSp δ m r f j₀ ≤ F ∙ e0 hn f := by
  classical
  intro c hc
  rw [mem_kerSp] at hc
  have hc' : (fun j ↦ (c j).map ρ) ∈ kerSp δ m r (fun l ↦ (f l).map ρ) j₀ := by
    rw [mem_kerSp]
    refine ⟨mem_Vsp_map ρ δ c hc.1, fun l k hk ↦ ?_⟩
    have := evPt_map ρ (B := B) (f l).x ((f l).ys k) c
    simp only [AdmFib.map] at this ⊢
    rw [this, hc.2 l k hk, map_zero]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h hc')
  have hmon : (prodX f).Monic := monic_prod_of_monic _ _ fun l _ ↦ monic_X_sub_C _
  set b := (c ⟨0, hn⟩).coeff r
  have h0 := congrFun ha ⟨0, hn⟩
  simp only [e0, Pi.smul_apply, Pi.single_eq_same, prodX_map] at h0
  have hab : a = ρ b := by
    have := congrArg (·.coeff r) h0
    simp only [Polynomial.smul_eq_C_mul, coeff_C_mul, coeff_map] at this
    have h1 : (prodX f).coeff r = 1 := by
      have := hmon.coeff_natDegree; rwa [natDegree_prodX] at this
    rw [h1, map_one, mul_one] at this
    exact this
  refine Submodule.mem_span_singleton.mpr ⟨b, funext fun j ↦ ?_⟩
  refine Polynomial.map_injective ρ ρ.injective ?_
  have hj := congrFun ha j
  rw [← hj]
  by_cases hj0 : j = ⟨0, hn⟩
  · subst hj0
    simp [e0, Polynomial.smul_eq_C_mul, prodX_map, hab, Polynomial.map_mul]
  · simp [e0, Pi.single_eq_of_ne hj0]

end Descend

end Curves
