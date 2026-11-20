import RischTragerBronstein.Algebraic.SupLogSpec

/-!
# Residues of the concrete integrand at the fibre points
-/

open Polynomial CPoly Differential IntermediateField

namespace Sup

section Pts

variable {F : Type*} [Field F]

lemma toB_coeff_ge (W : BPoly F) {n : ℕ} (hW : W.length ≤ n) : ∀ i, n ≤ i → (toB W).coeff i = 0 := by
  intro i hi
  rw [coeff_toB, List.getD_eq_default _ _ (by omega)]
  rfl

lemma exists_fibre {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (b β : K) (hb : b ≠ 0) (h : β ^ n = b ^ n) : ∃ k < n, β = ζ ^ k * b := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨k, hk, hkx⟩ := hζ.eq_pow_of_pow_eq_one (ξ := β / b) (by
    rw [div_pow, h, div_self (pow_ne_zero _ hb)])
  exact ⟨k, hk, by rw [hkx, div_mul_cancel₀ _ hb]⟩

lemma fibI_fibK {m n : ℕ} (q : Fin (m * n)) : finProdFinEquiv (fibI q, fibK q) = q := by
  simp only [fibI, fibK, Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] lemma fibI_equiv {m n : ℕ} (p : Fin m × Fin n) : fibI (finProdFinEquiv p) = p.1 := by
  simp [fibI]

@[simp] lemma fibK_equiv {m n : ℕ} (p : Fin m × Fin n) : fibK (finProdFinEquiv p) = p.2 := by
  simp [fibK]

/-- The fibre points are distinct. -/
lemma pt_injective {m n : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n) (a b : Fin m → F)
    (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0) :
    Function.Injective fun q : Fin (m * n) ↦ (ptA n a q, ptB n ζ b q) := by
  intro q q' h
  simp only [ptA, ptB, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hi := ha h1
  rw [hi] at h2
  have hk := mul_right_cancel₀ (hb _) h2
  have hk' : (fibK q : ℕ) = fibK q' := hζ.pow_inj (fibK q).2 (fibK q').2 hk
  rw [← fibI_fibK q, ← fibI_fibK q', hi, Fin.ext hk']

lemma pt_valid {m n : ℕ} (f : F[X]) {ζ : F} (hζ : IsPrimitiveRoot ζ n) (a b : Fin m → F)
    (hbf : ∀ i, b i ^ n = f.eval (a i)) (q : Fin (m * n)) :
    ptB n ζ b q ^ n = f.eval (ptA n a q) := by
  simp only [ptA, ptB]
  rw [mul_pow, ← pow_mul, mul_comm (fibK q : ℕ), pow_mul, hζ.pow_eq_one, one_pow, one_mul, hbf]

lemma pt_ne_zero {m n : ℕ} {ζ : F} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (b : Fin m → F)
    (hb : ∀ i, b i ≠ 0) (q : Fin (m * n)) : ptB n ζ b q ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) (hb _)

end Pts

section Res

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

open Differential.SuperData

/-- The mapped bivariate polynomial. -/
noncomputable abbrev mapB (ψ : F →+* C) (W : BPoly F) : C[X][X] := (toB W).map (mapRingHom ψ)

lemma map_mapB (ψ : F →+* C) (W : BPoly F) :
    (mapB ψ W).map (mapRingHom (algebraMap C K)) = (toB W).map (mapRingHom ((algebraMap C K).comp ψ)) := by
  rw [mapB, Polynomial.map_map, Polynomial.mapRingHom_comp]

open Classical in
/-- **The residues of the concrete integrand** at the ordinary points. -/
theorem res_integrand (S : SuperData C L) (ψ : F →+* C) (f : CPoly F) {n : ℕ} (hSn : S.n = n)
    (hSp : S.p = (toPoly f).map ψ) {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n) (a b : Fin m → F)
    (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0) (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i))
    (B B₁ : BPoly F) (G : Fin m → BPoly F) (hGn : ∀ i, (G i).length ≤ n) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    LaurentSeries.res (S.embXY α β hβ hβp
      (S.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i))) =
      ∑ q : Fin (m * n), if (α, β) = ((algebraMap C K).comp ψ (ptA n a q),
        (algebraMap C K).comp ψ (ptB n ζ b q)) then
          (algebraMap C K).comp ψ (resK ζ a b G (fibI q) (fibK q)) else 0 := by
  set ψ' := (algebraMap C K).comp ψ with hψ'
  have hψi : Function.Injective ψ' := ψ'.injective
  have hn : 0 < n := hSn ▸ S.hn
  have hζ' : IsPrimitiveRoot (ψ' ζ) n := hζ.map_of_injective hψi
  have hG : ∀ i j, S.n ≤ j → (mapB ψ (G i)).coeff j = 0 := fun i j hj ↦ by
    rw [mapB, coeff_map, toB_coeff_ge (G i) (hGn i) j (hSn ▸ hj), map_zero]
  rw [S.res_hInt_nb _ _ _ _ hG α β hβ hβp]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [fibI_equiv, fibK_equiv, ptA, ptB]
  by_cases hα : α = algebraMap C K (ψ (a i))
  · rw [if_pos hα]
    have hβn : β ^ n = ψ' (b i) ^ n := by
      rw [← hSn, hβp, hα, hSp, Polynomial.map_map, eval_map,
        show algebraMap C K (ψ (a i)) = ψ' (a i) from rfl, eval₂_hom, ← hbf, map_pow, hSn]
    obtain ⟨k0, hk0, hk0e⟩ := exists_fibre hn hζ' _ _ ((map_ne_zero_iff _ hψi).mpr (hb i)) hβn
    rw [Finset.sum_eq_single ⟨k0, hk0⟩]
    · rw [if_pos (by rw [hα, hk0e]; simp [ψ'])]
      rw [map_mapB, hα, hk0e, show algebraMap C K (ψ (a i)) = ψ' (a i) from rfl,
        show ψ' ζ ^ k0 * ψ' (b i) = ψ' (ζ ^ k0 * b i) by simp, evalW_map, ← evalB_eq]
      rfl
    · intro k _ hk
      rw [if_neg]
      intro h
      apply hk
      have h2 := (Prod.ext_iff.mp h).2
      rw [hk0e] at h2
      simp only [RingHom.coe_comp, Function.comp_apply, map_mul, map_pow] at h2
      have := mul_right_cancel₀ ((map_ne_zero_iff _ hψi).mpr (hb i)) h2
      exact Fin.ext (hζ'.pow_inj hk0 k.2 this).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hα]
    refine (Finset.sum_eq_zero fun k _ ↦ if_neg fun h ↦ hα ?_).symm
    exact (Prod.ext_iff.mp h).1

end Res

end Sup
