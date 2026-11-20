import RischTragerBronstein.Mixed.KLDecide
import RischTragerBronstein.Mixed.KWProj

/-!
# Components of integrands over a Kummer radical of any top level

`kl_componentsW`: the Galois projection of `kl_components` for a top level of either kind (the
derivation `tₘ′ = wₘ(tₘ)`, `KWProj`): if `∑ⱼ cⱼ θʲ` has an elementary integral, so does every
component `cⱼ θʲ`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 8000000 in
/-- **The components of an elementary integrand are elementary**, for a top level of any kind. -/
theorem kl_componentsW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true)
    (a : GPoly (LC m)) (nn : ℕ) (hnn : 0 < nn)
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) a = true) (hdegpos : 0 < degG (MO Fc ks m) a)
    (θ : L) (hθ : θ ^ nn = T.evP m a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (cs : ℕ → LC (m + 1))
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range nn, T.ev (m + 1) (cs j) * θ ^ j)) :
    ∀ j < nn, HasElementaryIntegral (T.ev (m + 1) (cs j) * θ ^ j) := by
  classical
  intro j hj
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  -- adjoin a primitive root of unity
  obtain ⟨E₂, _, _, _, _, hE₁₂, ζ, hζ⟩ := exists_root_ext E₁ nn hnn
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap E₁ E₂).injective
  letI : Algebra L E₂ := ((algebraMap E₁ E₂).comp (algebraMap L E₁)).toAlgebra
  haveI : IsScalarTower L E₁ E₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI hDA₂ : DifferentialAlgebra L E₂ :=
    ⟨fun z ↦ by
      change (algebraMap E₁ E₂ (algebraMap L E₁ z))′ = algebraMap E₁ E₂ (algebraMap L E₁ z′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hE₂ : IsElementaryExtension L E₂ := hE₁.trans hE₁₂
  have hg₂ : (algebraMap E₁ E₂ g)′ = algebraMap L E₂ (∑ j ∈ Finset.range nn,
      T.ev (m + 1) (cs j) * θ ^ j) := by
    rw [deriv_algebraMap, hg]; rfl
  obtain ⟨ι, s, c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₂ _ _ hg₂
  -- the tower in `E₂`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₂
  set ψ := algebraMap L E₂ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  set p₁ : (TE.F m)[X] := GPoly.toPoly (TE.MP m hTEm) a with hp₁
  have hsq₁ : Squarefree p₁ := GPoly.squarefreeCheck_sound (TE.MP m hTEm) hsqc
  have hdeg₁ : p₁.natDegree = degG (MO Fc ks m) a := (degG_eq (TE.MP m hTEm) a).symm
  have hy₁ : (ψ θ) ^ nn = aeval (TE.ts m) p₁ := by
    rw [hp₁, TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm), hPE, ← map_pow, hθ]
  let S₁ : SuperData (TE.F m) E₂ :=
    ⟨TE.ts m, ψ θ, nn, p₁, hTE m (by omega), hnn, hsq₁, by rw [hdeg₁]; exact hdegpos, hy₁,
      by exact_mod_cast hnn.ne'⟩
  have hx : S₁.x′ = aeval S₁.x (TE.wPoly m) := TE.deriv_ts_aeval m
  have hconstC : ∀ z : E₂, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₂) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₂, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the root of unity in the base
  obtain ⟨ζ₁, hζ₁⟩ := hconstC ζ (LaurentSeries.deriv_root_of_unity hnn hζ.pow_eq_one)
  have hζ₁p : IsPrimitiveRoot ζ₁ S₁.n := by
    rw [← hζ₁] at hζ
    exact (IsPrimitiveRoot.map_iff_of_injective (algebraMap (TE.F m) E₂).injective).mp hζ
  -- the Liouville form inside `C₁(x, y)`
  set U : ι → T₁ := fun i ↦ if h : i ∈ s then ⟨u i, hCT _ (hdata i h).2.1⟩ else 1 with hU
  set c₁ : ι → TE.F m := fun i ↦ if h : i ∈ s then Classical.choose (hconstC (c i) (hdata i h).1)
    else 0 with hc₁
  have hc₁v : ∀ i ∈ s, algebraMap (TE.F m) E₂ (c₁ i) = c i := fun i hi ↦ by
    simp only [hc₁, dif_pos hi]
    exact Classical.choose_spec (hconstC (c i) (hdata i hi).1)
  have hc₁d : ∀ i, (c₁ i)′ = 0 := fun i ↦ by
    by_cases hi : i ∈ s
    · apply (algebraMap (TE.F m) E₂).injective
      rw [← deriv_algebraMap, hc₁v i hi, (hdata i hi).1, map_zero]
    · simp only [hc₁, dif_neg hi, Derivation.map_zero]
  set F : T₁ := ⟨ψ (∑ j ∈ Finset.range nn, T.ev (m + 1) (cs j) * θ ^ j), hLT _⟩ with hF
  set V : T₁ := ⟨v, hCT v hv⟩ with hV
  have heqT : F = S₁.dTW (TE.wPoly m) hx V + ∑ i ∈ s, S₁.cst (c₁ i) * (S₁.dTW (TE.wPoly m) hx (U i) * (U i)⁻¹) := by
    apply Subtype.ext
    change ψ (∑ j ∈ Finset.range nn, T.ev (m + 1) (cs j) * θ ^ j) = _
    rw [heqL, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum, SuperData.coe_dTW,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [hU, dif_pos hi, IntermediateField.coe_mul, IntermediateField.coe_inv,
      SuperData.coe_dTW]
    rw [show ((S₁.cst (c₁ i) : T₁) : E₂) = algebraMap (TE.F m) E₂ (c₁ i) from rfl, hc₁v i hi,
      logDeriv, div_eq_mul_inv]
  -- the coordinates of the integrand
  have hmemx : ∀ q : LC (m + 1), ψ (T.ev (m + 1) q) ∈ (TE.F m)⟮S₁.x⟯ := fun q ↦ by
    have := hTEmem (m + 1) _ (T.ev_mem (m + 1) q)
    exact (TE.mem_F_succ).mp this
  set aa : Fin S₁.n → (TE.F m)⟮S₁.x⟯ := fun k ↦ ⟨ψ (T.ev (m + 1) (cs k)), hmemx _⟩ with haa
  have hFa : F = ∑ k : Fin S₁.n, algebraMap (TE.F m)⟮S₁.x⟯ T₁ (aa k) *
      AdjoinSimple.gen (TE.F m)⟮S₁.x⟯ S₁.y ^ (k : ℕ) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change ψ (∑ j ∈ Finset.range nn, T.ev (m + 1) (cs j) * θ ^ j) =
      ∑ k : Fin nn, (ψ (T.ev (m + 1) (cs k)) * (ψ θ) ^ (k : ℕ))
    rw [map_sum]
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ ψ (T.ev (m + 1) (cs k)) * (ψ θ) ^ k)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow]
  -- the projection onto the `yʲ`-component
  have hproj := S₁.proj_liouvilleW (TE.wPoly m) hx ζ₁ hζ₁p s c₁ hc₁d U V F heqT aa hFa ⟨j, hj⟩
  set W : T₁ := S₁.cst ((S₁.n : TE.F m)⁻¹) * ∑ k : Fin S₁.n, S₁.cst ((ζ₁ ^ (k : ℕ)) ^ (S₁.n - j)) *
    S₁.conj (ζ₁ ^ (k : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ₁p.pow_eq_one, one_pow]) V
    with hW
  set cc : Fin S₁.n × ι → TE.F m := fun ki ↦
    (S₁.n : TE.F m)⁻¹ * (ζ₁ ^ (ki.1 : ℕ)) ^ (S₁.n - j) * c₁ ki.2 with hcc
  set UU : Fin S₁.n × ι → E₂ := fun ki ↦ ((S₁.conj (ζ₁ ^ (ki.1 : ℕ))
      (by rw [← pow_mul, mul_comm, pow_mul, hζ₁p.pow_eq_one, one_pow]) (U ki.2) : T₁) : E₂)
    with hUU
  have hL : ψ (T.ev (m + 1) (cs j)) * (ψ θ) ^ j = (W : E₂)′ +
      ∑ ki ∈ (Finset.univ : Finset (Fin S₁.n)) ×ˢ s,
        algebraMap (TE.F m) E₂ (cc ki) * ((UU ki)′ * (UU ki)⁻¹) := by
    have h := congrArg (fun z : T₁ ↦ (z : E₂)) hproj
    simp only [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_pow,
      AdjoinSimple.coe_gen, AddSubmonoidClass.coe_finsetSum, SuperData.coe_dTW,
      IntermediateField.coe_inv] at h
    exact h
  -- a Liouville form in `E₂`, hence an elementary integral
  set l : List (E₂ × E₂) := ((Finset.univ : Finset (Fin S₁.n)) ×ˢ s).toList.map fun ki ↦
    (algebraMap (TE.F m) E₂ (cc ki), UU ki) with hl0
  have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
    intro p hp
    obtain ⟨ki, hki, rfl⟩ := List.mem_map.mp hp
    rw [Finset.mem_toList, Finset.mem_product] at hki
    refine ⟨?_, ?_⟩
    · have hw : (ζ₁ ^ (ki.1 : ℕ)) ^ (S₁.n - j) ∈ constants (TE.F m) :=
        LaurentSeries.deriv_root_of_unity (n := S₁.n) S₁.hn (by
          rw [← pow_mul, ← pow_mul, show (ki.1 : ℕ) * ((S₁.n - j) * S₁.n) =
            S₁.n * ((ki.1 : ℕ) * (S₁.n - j)) by ring, pow_mul, hζ₁p.pow_eq_one, one_pow])
      have hmem : cc ki ∈ constants (TE.F m) :=
        mul_mem (mul_mem (inv_mem (natCast_mem _ _)) hw) (hc₁d ki.2)
      change (algebraMap (TE.F m) E₂ (cc ki))′ = 0
      rw [deriv_algebraMap, show (cc ki)′ = 0 from hmem, map_zero]
    · have hU0 : U ki.2 ≠ 0 := by
        simp only [hU, dif_pos hki.2]
        exact fun h ↦ (hdata ki.2 hki.2).2.2 (congrArg Subtype.val h)
      have := (map_ne_zero_iff _ (RingHom.injective (S₁.conj (ζ₁ ^ (ki.1 : ℕ))
        (by rw [← pow_mul, mul_comm, pow_mul, hζ₁p.pow_eq_one, one_pow])))).mpr hU0
      exact fun h ↦ this (Subtype.ext h)
  have hform := hasElementaryIntegral_of_liouville_form (W : E₂) l hl
  have hsumeq : (W : E₂)′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum =
      algebraMap L E₂ (T.ev (m + 1) (cs j) * θ ^ j) := by
    rw [map_mul, map_pow, ← hψ, hL, hl0, List.map_map, Finset.sum_map_toList]
    congr 1
    refine Finset.sum_congr rfl fun ki _ ↦ ?_
    simp only [Function.comp_apply, logDeriv, div_eq_mul_inv]
  rw [hsumeq] at hform
  exact HasElementaryIntegral.of_extension hE₂ hform

end MTower

end Curves.MT
