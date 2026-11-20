import RischTragerBronstein.Algebraic.EllDecide
import RischTragerBronstein.Elliptic.DV.Chain
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Abel's direction with arbitrary residues: every `ℚ`-linear functional of the residues

`ell_torsion_functional`: for `y² = x³ + ax² + bx + c` and points `Pᵢ = (αᵢ, βᵢ)` over the constant
field `Kc` (not necessarily rational) with residues `rᵢ ∈ Kc` of the integrand
`(B(x) + ∑ rᵢ βᵢ / (x − αᵢ)) / y`: if the integral is elementary then, for every `ℚ`-linear
`Λ : Kc → ℚ` with `Λ(rᵢ) = zᵢ / D`, the point `∑ zᵢ Pᵢ` has finite order. This is the necessary
condition of Trager's decision for irrational residues (the residues are split along a `ℚ`-basis).
The proof reuses `ell_glue` (Liouville with `ℚ`-independent constants `κⱼ`, `2rᵢ = −∑ κⱼ nᵢⱼ`),
Abel's theorem for each logarithm (`2 ∑ᵢ nᵢⱼ Pᵢ = 0`) and an extension of `Λ` to the constants.
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

section EllFunctional

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 12800000 in
/-- **Abel's direction for arbitrary residues.** -/
theorem ell_torsion_functional (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (B : Kc[X]) {ι : Type*} (s : Finset ι) (α β r : ι → Kc)
    (hP : ∀ i, (EllDV.W Kc a b c).toAffine.Nonsingular (α i) (β i)) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hinj : Set.InjOn α s)
    (h : HasElementaryIntegral ((aeval x B + ∑ i ∈ s,
      algebraMap Kc E (r i * β i) / (x - algebraMap Kc E (α i))) / y))
    [DecidableEq Kc] (Λ : Kc →ₗ[ℚ] ℚ) (z : ι → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hΛ : ∀ i ∈ s, Λ (r i) = (z i : ℚ) / D) :
    IsOfFinAddOrder (∑ i ∈ s, z i • (Point.some _ _ (hP i) : (EllDV.W Kc a b c).toAffine.Point)) := by
  classical
  set p : ℚ[X] := X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) with hpdef
  have hpdeg : p.natDegree = 3 := by rw [hpdef]; compute_degree!
  have hodd : Odd p.natDegree := by rw [hpdeg]; decide
  obtain ⟨L, _, _, _, _, hE, g0, hg⟩ := h
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  obtain ⟨ιL, sL, cL, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g0 hg
  let Cc := constants L
  let _ : Differential Cc := ⟨0⟩
  have hDAc : DifferentialAlgebra Cc L := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun a b h ↦ by
    have := congrArg (fun z : Cc ↦ (z : L)) h
    simpa using this⟩
  set j := algebraMap E L with hjdef
  have hj : ∀ z : E, (j z)′ = j z′ := fun z ↦ deriv_algebraMap z
  have hCc : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hxL : (j x)′ = 1 := by rw [hj, hx, map_one]
  have htr : Transcendental Cc (j x) :=
    transcendental_of_deriv_ne_zero hCc (by rw [hxL]; exact one_ne_zero)
  have hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L) := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩
  set pC := p.map (algebraMap ℚ Cc) with hpC
  have haev : ∀ P : ℚ[X], aeval (j x) (P.map (algebraMap ℚ Cc)) = j (aeval x P) := by
    intro P
    rw [aeval_map_algebraMap, aeval_def, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_rat _ _
  have hyE : y ^ 2 = aeval x p := by rw [hy, hpdef]; simp
  have hyL : j y ^ 2 = aeval (j x) pC := by rw [hpC, haev, ← hyE, map_pow]
  have hpsq : Squarefree pC := by
    have hsep : p.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
    exact (hsep.map).squarefree
  have hdeg : pC.natDegree = p.natDegree :=
    natDegree_map_eq_of_injective (algebraMap ℚ Cc).injective _
  have hoddC : Odd pC.natDegree := hdeg ▸ hodd
  -- `C(x)` over the constants of `L` contains the image of `Kc(x)`
  have hKx : ∀ w : E, w ∈ Kc⟮x⟯ → j w ∈ Cc⟮j x⟯ := by
    let T : IntermediateField Kc E :=
      { carrier := {w | j w ∈ Cc⟮j x⟯}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
        one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
        zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
        algebraMap_mem' := fun c ↦ by
          simp only [Set.mem_setOf_eq]
          have hd : (j (algebraMap Kc E c))′ = 0 := by
            rw [hj, deriv_algebraMap, hC, map_zero, map_zero]
          obtain ⟨c', hc'⟩ := hconst _ hd
          rw [← hc']
          exact IntermediateField.algebraMap_mem _ _
        inv_mem' := fun a ha ↦ by
          simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
    have hle : Kc⟮x⟯ ≤ T := by
      rw [adjoin_simple_le_iff]
      exact mem_adjoin_simple_self Cc (j x)
    exact fun w hw ↦ hle hw
  set S := hypField (j x) (j y) htr pC hoddC hyL with hS
  have hEs : ∀ e : E, j e ∈ S := by
    intro e
    obtain ⟨α', β', hα', hβ', rfl⟩ := hgen e
    exact ⟨j α', j β', hKx α' hα', hKx β' hβ', by rw [map_add, map_mul]⟩
  have hcf : ∀ w ∈ constField E L, InHyp Cc (j x) (j y) w := by
    let N : IntermediateField E L :=
      { S with algebraMap_mem' := hEs }
    have : constField E L ≤ N := adjoin_le_iff.mpr fun w hw ↦ by
      obtain ⟨c', rfl⟩ := hconst w hw
      exact ⟨algebraMap Cc L c', 0, IntermediateField.algebraMap_mem _ _, zero_mem _, by ring⟩
    exact fun w hw ↦ this hw

  -- the constants `Kc → Cc`
  have hconstE : ∀ k : Kc, (j (algebraMap Kc E k))′ = 0 := fun k ↦ by
    rw [hj, deriv_algebraMap, hC, map_zero, map_zero]
  let φ : Kc →+* Cc :=
    { toFun := fun k ↦ ⟨j (algebraMap Kc E k), hconstE k⟩
      map_one' := by ext; simp
      map_mul' := fun u w ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun u w ↦ by ext; simp }
  have hφL : ∀ k : Kc, algebraMap Cc L (φ k) = j (algebraMap Kc E k) := fun _ ↦ rfl
  have hφinj : Function.Injective φ := φ.injective
  set αP : ι → Cc := fun i ↦ φ (α i) with hαP
  set βP : ι → Cc := fun i ↦ φ (β i) with hβPd
  set rP : ι → Cc := fun i ↦ φ (r i) with hrP
  have hinjP : Set.InjOn αP s := fun i hi i' hi' hh ↦ hinj hi hi' (hφinj hh)
  have hβP : ∀ i ∈ s, βP i ≠ 0 := fun i hi ↦ (map_ne_zero_iff φ hφinj).mpr (hβ i hi)
  have hcurve : ∀ i, βP i ^ 2 = αP i ^ 3 + a * αP i ^ 2 + b * αP i + c := by
    intro i
    have he := (EllDV.equation_W a b c).mp (hP i).1
    unfold EllDV.OnCurve at he
    have := congrArg φ he
    simpa [αP, βP] using this
  have hpαP' : ∀ i, pC.eval (αP i) = βP i ^ 2 := by
    intro i
    rw [hcurve i, hpC, hpdef, eval_map]
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eq_ratCast]
    push_cast; ring
  have hpαP : ∀ i ∈ s, pC.eval (αP i) = βP i ^ 2 := fun i _ ↦ hpαP' i
  have haevK : aeval (j x) (B.map φ) = j (aeval x B) := by
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]; rfl
  have heqL : (aeval (j x) (B.map φ) + ∑ i ∈ s, algebraMap Cc L (rP i * βP i) /
      (j x - algebraMap Cc L (αP i))) / j y = v′ + ∑ i ∈ sL, cL i * logDeriv (u i) := by
    rw [haevK, add_comm (v′), ← heq]
    simp only [map_div₀, map_add, map_sum, map_sub, rP, βP, αP, ← map_mul, hφL]
  obtain ⟨t, κ, a', b', hκind, hab, hN0, hshape, hres⟩ := ell_glue (j x) (j y) hCc hxL htr hconst
    pC hpsq hoddC hyL (B.map φ) s αP βP rP hinjP hβP hpαP sL cL u v
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩)
    (hcf v hv) heqL
  choose! m ε hdat hrel using hres
  have hpf : pC = EllAbel.f (a : Cc) (b : Cc) (c : Cc) := by
    rw [hpC, hpdef, EllAbel.f]; simp
  haveI : IsDedekindDomain (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.CoordinateRing :=
    isDedekindDomain_coordinateRing (a : Cc) (b : Cc) (c : Cc) (by
      have h' := hpsq; rw [hpf] at h'; exact h')
  have hns : ∀ i (w : Cc), w ^ 2 = βP i ^ 2 →
      (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Nonsingular (αP i) w := by
    intro i w hw
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff]
      simp only [EllAbel.W, zero_mul, add_zero, mul_zero]
      linear_combination hw + hcurve i, ?_⟩
    by_cases h0 : w = 0
    · left
      have h2 : βP i = 0 := by
        have : βP i ^ 2 = 0 := by rw [← hw, h0]; ring
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      have hroot : pC.eval (αP i) = 0 := by rw [hpαP' i, h2]; ring
      have hder : (derivative pC).eval (αP i) ≠ 0 := by
        intro hd
        have hsep : pC.Separable := (PerfectField.separable_iff_squarefree).mpr hpsq
        rw [Polynomial.separable_def] at hsep
        obtain ⟨u1, u2, huv⟩ := hsep
        have := congrArg (eval (αP i)) huv
        simp only [eval_add, eval_mul, eval_one, hroot, hd, mul_zero, add_zero] at this
        exact zero_ne_one this
      simp only [EllAbel.W, zero_mul, zero_sub, ne_eq, neg_eq_zero]
      intro hx0
      apply hder
      rw [hpf, EllAbel.f]
      simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X,
        zero_mul, zero_add, mul_one, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero,
        add_zero, mul_zero]
      push_cast at hx0 ⊢
      linear_combination hx0
    · right
      simp only [EllAbel.W, zero_mul, add_zero]
      exact mul_ne_zero two_ne_zero h0
  have hQns : ∀ i, (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Nonsingular (αP i) (βP i) :=
    fun i ↦ hns i _ rfl
  set Q : ι → (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point :=
    fun i ↦ Point.some _ _ (hQns i) with hQ
  have hTj : ∀ j0 ∈ t, (2 : ℤ) • ∑ i ∈ s, ((m i j0 : ℤ) * ε i j0) • Q i = 0 := by
    intro j0 hj0
    obtain ⟨lam, gq, hlam, hgq, hfac⟩ := norm_shape (hN pC (a' j0) (b' j0)) pC (hN0 j0 hj0) s αP
      hinjP (fun i ↦ m i j0) (fun i hi ↦ ⟨(hdat i hi j0 hj0).2.1, (hdat i hi j0 hj0).2.2.1⟩)
      (hshape j0 hj0)
    set β' : ι → Cc := fun i ↦ if i ∈ s then -(ε i j0 : Cc) * βP i else βP i with hβ'
    have hsign : ∀ i ∈ s, (ε i j0 : Cc) ^ 2 = 1 := by
      intro i hi
      rcases (hdat i hi j0 hj0).1 with h1 | h1 <;> rw [h1] <;> norm_num
    have hP' : ∀ i, (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Nonsingular (αP i) (β' i) := by
      intro i
      refine hns i _ ?_
      simp only [hβ']; split_ifs with hi
      · rw [mul_pow, neg_sq, hsign i hi, one_mul]
      · rfl
    have hβne : ∀ i ∈ s, β' i ≠ 0 := by
      intro i hi
      simp only [hβ', if_pos hi]
      refine mul_ne_zero ?_ (hβP i hi)
      rcases (hdat i hi j0 hj0).1 with h1 | h1 <;> rw [h1] <;> norm_num
    have hvan : ∀ i ∈ s, 0 < m i j0 →
        (a' j0).eval (αP i) + (b' j0).eval (αP i) * β' i = 0 := by
      intro i hi hm
      rw [(hdat i hi j0 hj0).2.2.2 hm]
      simp only [hβ', if_pos hi]
      ring
    have habel := EllAbel.abel_two_torsion (hsq := by rw [← hpf]; exact hpsq) (a' j0) (b' j0)
      (hab j0 hj0) s αP β' hP' hβne hinjP (fun i ↦ m i j0) gq (by rw [← hpf]; exact hgq) lam hlam
      (by rw [← hpf]; exact hfac) hvan
    have hpt : ∀ i ∈ s, (m i j0 • (Point.some _ _ (hP' i) :
        (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point)) =
        (-((m i j0 : ℤ) * ε i j0)) • Q i := by
      intro i hi
      rcases (hdat i hi j0 hj0).1 with h1 | h1
      · have e : (Point.some _ _ (hP' i) : (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point) =
            -Q i := by
          rw [hQ, Point.neg_some]
          simp only [Point.some.injEq, hβ', if_pos hi, h1, true_and]
          simp [negY, EllAbel.W]
        rw [e, h1]
        simp [← natCast_zsmul]
      · have e : (Point.some _ _ (hP' i) : (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point) =
            Q i := by
          rw [hQ]
          simp only [Point.some.injEq, hβ', if_pos hi, h1, true_and]
          push_cast; try ring
        rw [e, h1]
        simp [← natCast_zsmul]
    set T := ∑ i ∈ s, ((m i j0 : ℤ) * ε i j0) • Q i with hT
    have hT2 : (2 : ℤ) • T = 0 := by
      have : ∑ i ∈ s, (m i j0 • (Point.some _ _ (hP' i) :
          (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point)) = -T := by
        rw [Finset.sum_congr rfl hpt, hT, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [neg_zsmul]
      have h2 := habel
      rw [this, smul_neg, neg_eq_zero] at h2
      rw [← natCast_zsmul] at h2
      exact_mod_cast h2
    exact hT2

  -- extend `Λ` to the constants of `L`
  let φA : Kc →ₐ[ℚ] Cc := φ.toRatAlgHom
  set V : Submodule ℚ Cc := LinearMap.range φA.toLinearMap with hV
  let eV : Kc ≃ₗ[ℚ] V := LinearEquiv.ofInjective φA.toLinearMap (fun u w huw ↦ hφinj huw)
  obtain ⟨Λ', hΛ'⟩ := LinearMap.exists_extend (Λ ∘ₗ eV.symm.toLinearMap)
  have hΛφ : ∀ k : Kc, Λ' (φ k) = Λ k := by
    intro k
    have := congrArg (fun F : V →ₗ[ℚ] ℚ ↦ F (eV k)) hΛ'
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, eV,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
    exact this
  -- integral coefficients
  set g : ℕ → ℚ := fun jj ↦ Λ' (κ jj) with hg
  set M : ℕ := ∏ jj ∈ t, (g jj).den with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun jj _ ↦ (g jj).den_nz
  have hGint : ∀ jj ∈ t, (((g jj * M).num : ℤ) : ℚ) = g jj * M := fun jj hjj ↦ by
    have h1 := CPoly.Kron.den_mul_of_dvd (g jj) M (Finset.dvd_prod_of_mem _ hjj)
    have := Rat.num_div_den (g jj * M)
    rwa [h1, Nat.cast_one, div_one] at this
  set G : ℕ → ℤ := fun jj ↦ (g jj * M).num with hG
  have hrelQ : ∀ i ∈ s, (2 : ℚ) * M * z i =
      -((D : ℚ) * ∑ jj ∈ t, (g jj * M) * ((m i jj : ℚ) * ε i jj)) := by
    intro i hi
    have h1 := congrArg Λ' (hrel i hi)
    rw [map_neg, map_sum] at h1
    have h2 : Λ' (2 * rP i) = 2 * ((z i : ℚ) / D) := by
      rw [show (2 : Cc) * rP i = (2 : ℚ) • rP i by rw [Rat.smul_def]; norm_num, map_smul,
        hrP, hΛφ, hΛ i hi, smul_eq_mul]
    have h3 : ∀ jj ∈ t, Λ' (κ jj * ((m i jj : Cc) * ε i jj)) = g jj * ((m i jj : ℚ) * ε i jj) := by
      intro jj _
      rw [show κ jj * ((m i jj : Cc) * ε i jj) = (((m i jj : ℤ) * ε i jj : ℤ) : ℚ) • κ jj by
        rw [Rat.smul_def]; push_cast; ring, map_smul, smul_eq_mul]
      push_cast; ring
    rw [h2, Finset.sum_congr rfl h3] at h1
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    have e : ∑ jj ∈ t, (g jj * M) * ((m i jj : ℚ) * ε i jj) =
        M * ∑ jj ∈ t, g jj * ((m i jj : ℚ) * ε i jj) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [e, show ∑ jj ∈ t, g jj * ((m i jj : ℚ) * ε i jj) = -(2 * ((z i : ℚ) / D)) by
      linear_combination h1]
    field_simp
    try ring
  have hrelZ : ∀ i ∈ s, 2 * (M : ℤ) * z i =
      -((D : ℤ) * ∑ jj ∈ t, G jj * ((m i jj : ℤ) * ε i jj)) := by
    intro i hi
    have hq := hrelQ i hi
    rw [Finset.sum_congr rfl fun jj hjj ↦ by rw [← hGint jj hjj]] at hq
    exact_mod_cast hq
  -- `4M · ∑ zᵢ Qᵢ = 0`
  have hL : (2 * (M : ℤ)) • ∑ i ∈ s, z i • Q i =
      ∑ i ∈ s, ∑ jj ∈ t, (-((D : ℤ) * (G jj * ((m i jj : ℤ) * ε i jj)))) • Q i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [smul_smul, hrelZ i hi, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_smul]
  have hR : ∀ jj ∈ t, ∑ i ∈ s, (-((D : ℤ) * (G jj * ((m i jj : ℤ) * ε i jj)))) • Q i =
      (-((D : ℤ) * G jj)) • ∑ i ∈ s, ((m i jj : ℤ) * ε i jj) • Q i := by
    intro jj _
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul]; congr 1; ring
  have hS : (4 * (M : ℤ)) • ∑ i ∈ s, z i • Q i = 0 := by
    rw [show (4 * (M : ℤ)) = 2 * (2 * (M : ℤ)) by ring, mul_smul, hL, Finset.sum_comm,
      Finset.sum_congr rfl hR, Finset.smul_sum]
    exact Finset.sum_eq_zero fun jj hjj ↦ by rw [smul_comm, hTj jj hjj, smul_zero]
  -- back to `Kc`
  have hWC : (EllDV.W0 a b c).baseChange Cc = EllAbel.W (a : Cc) (b : Cc) (c : Cc) := by
    simp [EllDV.W0, EllAbel.W, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  let toC : (EllDV.W Kc a b c).toAffine.Point →+ (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point :=
    (EllNL.ptEquiv hWC).toAddMonoidHom.comp (Point.map (W' := EllDV.W0 a b c) φA)
  have htoC_inj : Function.Injective toC := by
    intro P P' hPP
    simp only [toC, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply] at hPP
    exact Point.map_injective _ ((EllNL.ptEquiv _).injective hPP)
  have htoC : ∀ i, toC (Point.some _ _ (hP i)) = Q i := by
    intro i
    change EllNL.ptEquiv hWC (Point.map (W' := EllDV.W0 a b c) φA (Point.some _ _ (hP i))) = Q i
    erw [Point.map_some]
    exact EllNL.ptEquiv_some _ _ _
  refine isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨4 * (M : ℤ), by
    have : (M : ℤ) ≠ 0 := by exact_mod_cast hM0
    positivity, htoC_inj ?_⟩
  rw [map_zsmul, map_sum, map_zero]
  simp only [map_zsmul, htoC]
  exact hS

set_option maxHeartbeats 1600000 in
/-- **Non-elementarity from a non-torsion point over a field `K` embedded in the constants.** -/
theorem not_elem_of_nontorsionK (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    {K : Type*} [Field K] [CharZero K] [DecidableEq K] [DecidableEq Kc] (ιK : K →+* Kc)
    (B : Kc[X]) {ι : Type*} (s : Finset ι) (α β r : ι → K)
    (hP : ∀ i, (EllDV.W K a b c).toAffine.Nonsingular (α i) (β i)) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hinj : Set.InjOn α s) (Λ : K →ₗ[ℚ] ℚ) (z : ι → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hΛ : ∀ i ∈ s, Λ (r i) = (z i : ℚ) / D)
    (hnt : ¬IsOfFinAddOrder (∑ i ∈ s, z i • (Point.some _ _ (hP i) :
      (EllDV.W K a b c).toAffine.Point))) :
    ¬HasElementaryIntegral ((aeval x B + ∑ i ∈ s,
      algebraMap Kc E (ιK (r i * β i)) / (x - algebraMap Kc E (ιK (α i)))) / y) := by
  classical
  intro h
  let φA : K →ₐ[ℚ] Kc := ιK.toRatAlgHom
  let mp : (EllDV.W K a b c).toAffine.Point →+ (EllDV.W Kc a b c).toAffine.Point :=
    Point.map (W' := EllDV.W0 a b c) φA
  have hmp_inj : Function.Injective mp := Point.map_injective φA
  have hPc : ∀ i, (EllDV.W Kc a b c).toAffine.Nonsingular (ιK (α i)) (ιK (β i)) := fun i ↦
    (WeierstrassCurve.Affine.baseChange_nonsingular (W := (EllDV.W0 a b c).toAffine) (f := φA)
      φA.injective (α i) (β i)).mpr (hP i)
  have hmp : ∀ i, mp (Point.some _ _ (hP i)) = Point.some _ _ (hPc i) := by
    intro i
    change Point.map (W' := EllDV.W0 a b c) φA (Point.some _ _ (hP i)) = _
    erw [Point.map_some]
    rfl
  -- extend `Λ` along `ιK`
  set V : Submodule ℚ Kc := LinearMap.range φA.toLinearMap
  let eV : K ≃ₗ[ℚ] V := LinearEquiv.ofInjective φA.toLinearMap (fun u w huw ↦ ιK.injective huw)
  obtain ⟨Λc, hΛc⟩ := LinearMap.exists_extend (Λ ∘ₗ eV.symm.toLinearMap)
  have hΛι : ∀ k : K, Λc (ιK k) = Λ k := by
    intro k
    have := congrArg (fun F : V →ₗ[ℚ] ℚ ↦ F (eV k)) hΛc
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, eV,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
    exact this
  have ht := ell_torsion_functional hC hCall x y hx a b c hsq hy hgen B s (fun i ↦ ιK (α i))
    (fun i ↦ ιK (β i)) (fun i ↦ ιK (r i)) hPc
    (fun i hi ↦ (map_ne_zero_iff ιK ιK.injective).mpr (hβ i hi))
    (fun i hi i' hi' hh ↦ hinj hi hi' (ιK.injective hh))
    (by simpa only [map_mul] using h) Λc z D hD (fun i hi ↦ by rw [hΛι, hΛ i hi])
  apply hnt
  obtain ⟨n, hn, hnP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hmp_inj ?_⟩
  rw [map_nsmul, map_sum, map_zero]
  simp only [map_zsmul, hmp]
  exact hnP

/-- `not_elem_of_nontorsionK` for a rational polynomial part. -/
theorem not_elem_of_nontorsion (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    {K : Type*} [Field K] [CharZero K] [DecidableEq K] [DecidableEq Kc] (ιK : K →+* Kc)
    (B : ℚ[X]) {ι : Type*} (s : Finset ι) (α β r : ι → K)
    (hP : ∀ i, (EllDV.W K a b c).toAffine.Nonsingular (α i) (β i)) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hinj : Set.InjOn α s) (Λ : K →ₗ[ℚ] ℚ) (z : ι → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hΛ : ∀ i ∈ s, Λ (r i) = (z i : ℚ) / D)
    (hnt : ¬IsOfFinAddOrder (∑ i ∈ s, z i • (Point.some _ _ (hP i) :
      (EllDV.W K a b c).toAffine.Point))) :
    ¬HasElementaryIntegral ((aeval x B + ∑ i ∈ s,
      algebraMap Kc E (ιK (r i * β i)) / (x - algebraMap Kc E (ιK (α i)))) / y) := by
  have := not_elem_of_nontorsionK hC hCall x y hx a b c hsq hy hgen ιK (B.map (algebraMap ℚ Kc))
    s α β r hP hβ hinj Λ z D hD hΛ hnt
  rwa [aeval_map_algebraMap] at this

end EllFunctional

end Differential
