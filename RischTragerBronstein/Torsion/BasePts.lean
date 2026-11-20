import RischTragerBronstein.Torsion.NonTorsExist3

/-!
# Non-special base points over an algebraically closed field

**`exists_basepoints`**: for a monic separable `F(x, Y)` of degree `n` over an algebraically closed
field of characteristic `0`, a basis `B` with non-vanishing coefficient determinant, weights `δ`
(`δ₀ = 0`, `δⱼ ≥ 1`, `∑ δ = g + n − 1`) and a non-zero `D`, there are `g` admissible fibres
(distinct abscissas outside any finite set, `D ≠ 0`, split into simple roots of `F`) which are
non-special (`kerSp ≤ span e0`, with the distinguished root first).
-/

open Polynomial

namespace Curves

open Sup

section Base

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

lemma derivative_ne_zero_of_res {F : K[X][X]} (hmon : F.Monic) (hdeg : F.natDegree = n)
    {x : K} (hres : (resultant F (derivative F) n (n - 1)).eval x ≠ 0) {y : K}
    (hy : evalW F x y = 0) : evalW (derivative F) x y ≠ 0 := by
  set p := F.map (evalRingHom x) with hp
  have hpm : p.Monic := hmon.map _
  have hpd : p.natDegree = n := by rw [hp, hmon.natDegree_map, hdeg]
  have hres' : resultant p (derivative p) n (n - 1) ≠ 0 := by
    rw [hp, ← resultant_map_deriv]; exact hres
  have hsep : p.Separable := by
    have h' : resultant p (derivative p) ≠ 0 := by
      rw [natDegree_derivative, hpd]; exact hres'
    by_contra hs
    exact h' (resultant_eq_zero_iff.mpr ⟨Or.inl hpm.ne_zero, hs⟩)
  have := hsep.eval₂_derivative_ne_zero (RingHom.id K) (x := y) (by
    rw [eval₂_id]; exact hy)
  rw [eval₂_id] at this
  rw [evalW, ← Polynomial.derivative_map]
  exact this

/-- **Non-special base points exist.** -/
theorem exists_basepoints (F : K[X][X]) (hmon : F.Monic) (hdeg : F.natDegree = n) (hn : 0 < n)
    (B : Fin n → K[X][X]) (hB : ∀ j, (B j).natDegree < n) (D : K[X]) (hD : D ≠ 0)
    (hres : resultant F (derivative F) n (n - 1) ≠ 0)
    (hdetC : (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i).det ≠ 0)
    (δ : Fin n → ℕ) (hδ0 : δ ⟨0, hn⟩ = 0) (hδ : ∀ j, j ≠ ⟨0, hn⟩ → 1 ≤ δ j) {g : ℕ}
    (hsum : ∑ j, δ j = g + n - 1) (bad : Finset K) :
    ∃ f : Fin g → AdmFib B, Function.Injective (fun l ↦ (f l).x) ∧ (∀ l, (f l).x ∉ bad) ∧
      (∀ l, D.eval (f l).x ≠ 0) ∧ (∀ l k, evalW F (f l).x ((f l).ys k) = 0) ∧
      (∀ l k, evalW (derivative F) (f l).x ((f l).ys k) ≠ 0) ∧
      kerSp δ g g f (fun _ ↦ ⟨0, hn⟩) ≤ K ∙ e0 hn f := by
  classical
  set G := D * resultant F (derivative F) n (n - 1) * (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i).det
    with hGdef
  have hG0 : G ≠ 0 := mul_ne_zero (mul_ne_zero hD hres) hdetC
  set Q : AdmFib B → Prop := fun fb ↦ fb.x ∉ bad ∧ D.eval fb.x ≠ 0 ∧
    (∀ k, evalW F fb.x (fb.ys k) = 0) ∧ (∀ k, evalW (derivative F) fb.x (fb.ys k) ≠ 0) with hQ
  have hsup : ∀ s : Finset K, ∃ fb : AdmFib B, fb.x ∉ s ∧ Q fb := by
    intro s
    obtain ⟨fb, hx, hGx, hroots⟩ := exists_admFib F hmon hdeg B hB G hG0 (fun x hx ↦ by
      simp only [hGdef, eval_mul] at hx
      exact ⟨fun h ↦ hx (by rw [h, mul_zero, zero_mul]), fun h ↦ hx (by rw [h, mul_zero])⟩)
      (s ∪ bad)
    simp only [hGdef, eval_mul] at hGx
    have hres_x : (resultant F (derivative F) n (n - 1)).eval fb.x ≠ 0 := fun h ↦
      hGx (by rw [h, mul_zero, zero_mul])
    refine ⟨fb, fun h ↦ hx (Finset.mem_union_left _ h), fun h ↦ hx (Finset.mem_union_right _ h),
      fun h ↦ hGx (by rw [h, zero_mul, zero_mul]), hroots,
      fun k ↦ derivative_ne_zero_of_res hmon hdeg hres_x (hroots k)⟩
  obtain ⟨f, hinj, hQf, j₀, hker⟩ := exists_nonspecial δ hn hδ0 hδ hsum Q hsup
  refine ⟨permF hn f j₀, hinj, fun l ↦ (hQf l).1, fun l ↦ (hQf l).2.1,
    fun l k ↦ (hQf l).2.2.1 _, fun l k ↦ (hQf l).2.2.2 _, ?_⟩
  rw [kerSp_perm, e0_perm]
  exact hker

end Base

end Curves
