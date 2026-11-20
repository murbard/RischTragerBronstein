import RischTragerBronstein.Torsion.GenusZero
import RischTragerBronstein.Torsion.BaseDescend

/-!
# Base points with algebraic coordinates

* `exists_admFibR`, **`exists_basepointsR`**: admissible (non-special) fibres with abscissas in
  any infinite set (e.g. the integers, so that the coordinates are algebraic over `ℚ`);
* **`exists_QB_pre`**: over an algebraically closed field of characteristic `0`, the roots of a
  rational polynomial are images of algebraic numbers (under the embedding of `ℚ̄`).
-/

open Polynomial

namespace Curves

open Sup

section Adm

variable {K : Type*} [Field K] {n : ℕ}
variable [IsAlgClosed K] [CharZero K]

/-- **Admissible fibres exist** outside any finite set, with abscissa in any infinite set. -/
theorem exists_admFibR (R : K → Prop) (hR : ∀ s : Finset K, ∃ x, x ∉ s ∧ R x)
    (F : K[X][X]) (hmon : F.Monic) (hdeg : F.natDegree = n)
    (B : Fin n → K[X][X]) (hB : ∀ j, (B j).natDegree < n) (G : K[X]) (hG0 : G ≠ 0)
    (hGd : ∀ x, G.eval x ≠ 0 → (resultant F (derivative F) n (n - 1)).eval x ≠ 0 ∧
      (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i).det.eval x ≠ 0) (s : Finset K) :
    ∃ fb : AdmFib B, fb.x ∉ s ∧ G.eval fb.x ≠ 0 ∧ (∀ k, evalW F fb.x (fb.ys k) = 0) ∧ R fb.x := by
  classical
  obtain ⟨x, hx, hRx⟩ := hR (s ∪ G.roots.toFinset)
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
  refine ⟨⟨x, ys, ?_⟩, hx.1, hx.2, hroot, hRx⟩
  rw [det_evalW B hB x ys]
  refine mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hinj) ?_
  have := RingHom.map_det (evalRingHom x) (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i)
  rw [coe_evalRingHom] at this
  rw [show (Matrix.of fun (i j : Fin n) ↦ ((B j).coeff i).eval x) =
    (evalRingHom x).mapMatrix (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i) by ext; simp, ← this]
  exact hd

end Adm

section Base

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

/-- **Non-special base points exist**, with abscissas in any infinite set. -/
theorem exists_basepointsR (R : K → Prop) (hR : ∀ s : Finset K, ∃ x, x ∉ s ∧ R x) (F : K[X][X]) (hmon : F.Monic) (hdeg : F.natDegree = n) (hn : 0 < n)
    (B : Fin n → K[X][X]) (hB : ∀ j, (B j).natDegree < n) (D : K[X]) (hD : D ≠ 0)
    (hres : resultant F (derivative F) n (n - 1) ≠ 0)
    (hdetC : (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i).det ≠ 0)
    (δ : Fin n → ℕ) (hδ0 : δ ⟨0, hn⟩ = 0) (hδ : ∀ j, j ≠ ⟨0, hn⟩ → 1 ≤ δ j) {g : ℕ}
    (hsum : ∑ j, δ j = g + n - 1) (bad : Finset K) :
    ∃ f : Fin g → AdmFib B, Function.Injective (fun l ↦ (f l).x) ∧ (∀ l, (f l).x ∉ bad) ∧
      (∀ l, D.eval (f l).x ≠ 0) ∧ (∀ l k, evalW F (f l).x ((f l).ys k) = 0) ∧
      (∀ l k, evalW (derivative F) (f l).x ((f l).ys k) ≠ 0) ∧
      kerSp δ g g f (fun _ ↦ ⟨0, hn⟩) ≤ K ∙ e0 hn f ∧ ∀ l, R (f l).x := by
  classical
  set G := D * resultant F (derivative F) n (n - 1) * (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i).det
    with hGdef
  have hG0 : G ≠ 0 := mul_ne_zero (mul_ne_zero hD hres) hdetC
  set Q : AdmFib B → Prop := fun fb ↦ fb.x ∉ bad ∧ D.eval fb.x ≠ 0 ∧
    (∀ k, evalW F fb.x (fb.ys k) = 0) ∧ (∀ k, evalW (derivative F) fb.x (fb.ys k) ≠ 0) ∧ R fb.x
    with hQ
  have hsup : ∀ s : Finset K, ∃ fb : AdmFib B, fb.x ∉ s ∧ Q fb := by
    intro s
    obtain ⟨fb, hx, hGx, hroots, hRx⟩ := exists_admFibR R hR F hmon hdeg B hB G hG0 (fun x hx ↦ by
      simp only [hGdef, eval_mul] at hx
      exact ⟨fun h ↦ hx (by rw [h, mul_zero, zero_mul]), fun h ↦ hx (by rw [h, mul_zero])⟩)
      (s ∪ bad)
    simp only [hGdef, eval_mul] at hGx
    have hres_x : (resultant F (derivative F) n (n - 1)).eval fb.x ≠ 0 := fun h ↦
      hGx (by rw [h, mul_zero, zero_mul])
    refine ⟨fb, fun h ↦ hx (Finset.mem_union_left _ h), fun h ↦ hx (Finset.mem_union_right _ h),
      fun h ↦ hGx (by rw [h, zero_mul, zero_mul]), hroots,
      fun k ↦ derivative_ne_zero_of_res hmon hdeg hres_x (hroots k), hRx⟩
  obtain ⟨f, hinj, hQf, j₀, hker⟩ := exists_nonspecial δ hn hδ0 hδ hsum Q hsup
  refine ⟨permF hn f j₀, hinj, fun l ↦ (hQf l).1, fun l ↦ (hQf l).2.1,
    fun l k ↦ (hQf l).2.2.1 _, fun l k ↦ (hQf l).2.2.2.1 _, ?_, fun l ↦ (hQf l).2.2.2.2⟩
  rw [kerSp_perm, e0_perm]
  exact hker

end Base

section Pre

variable {Kc : Type*} [Field Kc] [IsAlgClosed Kc] [CharZero Kc]

/-- **Roots of rational polynomials are images of algebraic numbers.** -/
lemma exists_QB_pre (p : ℚ[X]) (hp : p ≠ 0) (y : Kc) (hy : (p.map (algebraMap ℚ Kc)).eval y = 0) :
    ∃ z : NFC.QB, (IsAlgClosed.lift (R := ℚ) (S := NFC.QB) (M := Kc)).toRingHom z = y := by
  classical
  set ι := (IsAlgClosed.lift (R := ℚ) (S := NFC.QB) (M := Kc)).toRingHom with hιdef
  have hcomp : ι.comp (algebraMap ℚ NFC.QB) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have hmap : (p.map (algebraMap ℚ NFC.QB)).map ι = p.map (algebraMap ℚ Kc) := by
    rw [Polynomial.map_map, hcomp]
  have hne : p.map (algebraMap ℚ Kc) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr hp
  have hmem : y ∈ (p.map (algebraMap ℚ Kc)).roots := (mem_roots hne).mpr hy
  rw [← hmap, (IsAlgClosed.splits (p.map (algebraMap ℚ NFC.QB))).roots_map ι] at hmem
  obtain ⟨z, -, hz⟩ := Multiset.mem_map.mp hmem
  exact ⟨z, hz⟩

end Pre

end Curves
