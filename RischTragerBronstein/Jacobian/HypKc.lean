import RischTragerBronstein.Jacobian.AbelHyp
import RischTragerBronstein.Algebraic.EllQuadCert

/-!
# Hyperelliptic theory for curves with coefficients in the constants

Versions of the key results for `y² = p(x)` with `p` over the constants `Kc` (or over a field
`F ⊆ Kc`) instead of `ℚ`:

* `hyp_no_elemKc`: a non-zero residue-free remainder `B₀ dx / y` has no elementary integral;
* `hyp_decidesKc`: `∫ B / y` (`B ∈ F[x]`) is elementary iff the remainder of `hypRed` vanishes;
* `hyp_principal_of_elementaryKc`: Abel's direction (elementary ⇒ the residue divisor is torsion).
-/

open Polynomial IntermediateField

namespace Jac

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 12800000 in
/-- **Abel's direction in any genus, for a curve over a field `F ⊆ Kc`.** -/
theorem hyp_principal_of_elementaryKc (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {g : ℕ} {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ι0 : F →+* Kc) (p : F[X])
    (hsq : Squarefree p) (hpdeg : p.natDegree = 2 * g + 1)
    (hy : y ^ 2 = aeval x (p.map ι0)) (hgen : ∀ z : E, InHyp Kc x y z)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → F) (hb : ∀ i ∈ s, b i ≠ 0)
    (hab : ∀ i ∈ s, b i ^ 2 = p.eval (a i)) (hinj : Set.InjOn a s)
    (B : Kc[X]) (r : ι → Kc)
    (h : HasElementaryIntegral ((aeval x B + ∑ i ∈ s,
      algebraMap Kc E (r i * ι0 (b i)) / (x - algebraMap Kc E (ι0 (a i)))) / y))
    (Λ : Kc →ₗ[ℚ] ℚ) (z : ι → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hΛ : ∀ i ∈ s, Λ (r i) = (z i : ℚ) / D) :
    ∃ n, 1 ≤ n ∧ PrincipalMul p g (resDiv s a b z) n := by
  classical
  have hodd : Odd p.natDegree := ⟨g, hpdeg⟩
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
  set ψF : F →+* Cc := φ.comp ι0
  have haevK : ∀ P : Kc[X], aeval (j x) (P.map φ) = j (aeval x P) := by
    intro P
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]; rfl
  set pC := p.map ψF with hpC
  have hyL : j y ^ 2 = aeval (j x) pC := by
    rw [hpC, show ψF = φ.comp ι0 from rfl, ← Polynomial.map_map, haevK, ← hy, map_pow]
  have hpsq : Squarefree pC := by
    have hsep : p.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
    exact (hsep.map).squarefree
  have hdeg : pC.natDegree = p.natDegree := natDegree_map_eq_of_injective ψF.injective _
  have hoddC : Odd pC.natDegree := hdeg ▸ hodd
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
  set αP : ι → Cc := fun i ↦ ψF (a i) with hαP
  set βP : ι → Cc := fun i ↦ ψF (b i) with hβPd
  set rP : ι → Cc := fun i ↦ φ (r i) with hrP
  have hinjP : Set.InjOn αP s := fun i hi i' hi' hh ↦ hinj hi hi' (ψF.injective hh)
  have hβP : ∀ i ∈ s, βP i ≠ 0 := fun i hi ↦ (map_ne_zero_iff ψF ψF.injective).mpr (hb i hi)
  have hpαP : ∀ i ∈ s, pC.eval (αP i) = βP i ^ 2 := by
    intro i hi
    rw [hpC, hαP, hβPd, eval_map, eval₂_hom]
    show ψF (p.eval (a i)) = ψF (b i) ^ 2
    rw [← hab i hi, map_pow]
  have haevB : aeval (j x) (B.map φ) = j (aeval x B) := haevK B
  have heqL : (aeval (j x) (B.map φ) + ∑ i ∈ s, algebraMap Cc L (rP i * βP i) /
      (j x - algebraMap Cc L (αP i))) / j y = v′ + ∑ i ∈ sL, cL i * logDeriv (u i) := by
    rw [haevB, add_comm (v′), ← heq]
    simp only [map_div₀, map_add, map_sum, map_sub, rP, βP, αP, ψF, RingHom.comp_apply,
      ← map_mul, hφL]
  obtain ⟨t, κ, a', b', hκind, hab', hN0, hshape, hres⟩ := ell_glue (j x) (j y) hCc hxL htr hconst
    pC hpsq hoddC hyL (B.map φ) s αP βP rP hinjP hβP hpαP sL cL u v
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩)
    (hcf v hv) heqL
  choose! m ε hdat hrel using hres
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
  set gw : ℕ → ℚ := fun jj ↦ Λ' (κ jj) with hgw
  set M : ℕ := ∏ jj ∈ t, (gw jj).den with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun jj _ ↦ (gw jj).den_nz
  have hGint : ∀ jj ∈ t, (((gw jj * M).num : ℤ) : ℚ) = gw jj * M := fun jj hjj ↦ by
    have h1 := CPoly.Kron.den_mul_of_dvd (gw jj) M (Finset.dvd_prod_of_mem _ hjj)
    have := Rat.num_div_den (gw jj * M)
    rwa [h1, Nat.cast_one, div_one] at this
  set G : ℕ → ℤ := fun jj ↦ (gw jj * M).num with hG
  have hrelQ : ∀ i ∈ s, (2 : ℚ) * M * z i =
      -((D : ℚ) * ∑ jj ∈ t, (gw jj * M) * ((m i jj : ℚ) * ε i jj)) := by
    intro i hi
    have h1 := congrArg Λ' (hrel i hi)
    rw [map_neg, map_sum] at h1
    have h2 : Λ' (2 * rP i) = 2 * ((z i : ℚ) / D) := by
      rw [show (2 : Cc) * rP i = (2 : ℚ) • rP i by rw [Rat.smul_def]; norm_num, map_smul,
        hrP, hΛφ, hΛ i hi, smul_eq_mul]
    have h3 : ∀ jj ∈ t, Λ' (κ jj * ((m i jj : Cc) * ε i jj)) =
        gw jj * ((m i jj : ℚ) * ε i jj) := by
      intro jj _
      rw [show κ jj * ((m i jj : Cc) * ε i jj) = (((m i jj : ℤ) * ε i jj : ℤ) : ℚ) • κ jj by
        rw [Rat.smul_def]; push_cast; ring, map_smul, smul_eq_mul]
      push_cast; ring
    rw [h2, Finset.sum_congr rfl h3] at h1
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    have e : ∑ jj ∈ t, (gw jj * M) * ((m i jj : ℚ) * ε i jj) =
        M * ∑ jj ∈ t, gw jj * ((m i jj : ℚ) * ε i jj) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [e, show ∑ jj ∈ t, gw jj * ((m i jj : ℚ) * ε i jj) = -(2 * ((z i : ℚ) / D)) by
      linear_combination h1]
    field_simp
    try ring
  have hrelZ : ∀ i ∈ s, 2 * (M : ℤ) * z i =
      -((D : ℤ) * ∑ jj ∈ t, G jj * ((m i jj : ℤ) * ε i jj)) := by
    intro i hi
    have hq := hrelQ i hi
    rw [Finset.sum_congr rfl fun jj hjj ↦ by rw [← hGint jj hjj]] at hq
    exact_mod_cast hq
  -- the norm shapes of the logarithms
  have hns : ∀ jj ∈ t, ∃ (lam : Cc) (gq : Cc[X]), lam ≠ 0 ∧ gq ∣ pC ∧
      hnorm pC (a' jj, b' jj) = C lam * (∏ i ∈ s, (X - C (αP i)) ^ m i jj) * gq := by
    intro jj hjj
    exact norm_shape (hN pC (a' jj) (b' jj)) pC (hN0 jj hjj) s αP hinjP (fun i ↦ m i jj)
      (fun i hi ↦ ⟨(hdat i hi jj hjj).2.1, (hdat i hi jj hjj).2.2.1⟩) (hshape jj hjj)
  choose! lam gq hlam hgq hfac using hns
  -- the algebraic core over `Cc`
  have hpCdeg : pC.natDegree = 2 * g + 1 := by rw [hdeg, hpdeg]
  obtain ⟨ψ, hψ0, hψp, hψv⟩ := abel_core pC hpCdeg hpsq two_ne_zero s αP βP hβP
    (fun i hi ↦ (hpαP i hi).symm) hinjP t (fun jj ↦ (a' jj, b' jj)) hab' m ε
    (fun i hi jj hjj ↦ (hdat i hi jj hjj).1) lam gq hlam hgq hfac
    (fun i hi jj hjj hm ↦ (hdat i hi jj hjj).2.2.2 hm) (fun jj ↦ (D : ℤ) * G jj)
  -- `eᵢ = 2 M zᵢ`
  have he : ∀ i ∈ s, ∑ jj ∈ t, (D : ℤ) * G jj * (m i jj * -ε i jj) = 2 * M * z i := by
    intro i hi
    rw [hrelZ i hi, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun jj _ ↦ by ring
  have habs : ∀ i, (2 * (M : ℤ) * z i).natAbs = 2 * M * (z i).natAbs := fun i ↦ by
    rw [Int.natAbs_mul, Int.natAbs_mul]; simp
  have hsg : ∀ i, (2 * (M : ℤ) * z i).sign = (z i).sign := fun i ↦ by
    have hpos : 0 < 2 * (M : ℤ) := by positivity
    rw [Int.sign_mul, Int.sign_eq_one_of_pos hpos, one_mul]
  have hpmap : p.map ψF = pC := rfl
  have hPM : PrincipalMul pC g (emap ψF (resDiv s a b z)) (2 * M) := by
    refine ⟨ψ, hψ0, ?_, ?_⟩
    · rw [edeg_emap, edeg_resDiv, Finset.mul_sum]
      have hsum : ∑ i ∈ s, 2 * (∑ jj ∈ t, (D : ℤ) * G jj * (m i jj * -ε i jj)).natAbs =
          ∑ i ∈ s, 2 * M * (2 * (z i).natAbs) :=
        Finset.sum_congr rfl fun i hi ↦ by rw [he i hi, habs]; ring
      rw [← hsum]; exact hψp
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
      obtain ⟨i, hi, hz, rfl⟩ := mem_resDiv hq''
      have hvi := hψv i hi
      rw [he i hi, hsg, habs] at hvi
      show VanishAt pC ψ.1 ψ.2 (ψF (a i)) (ψF (((z i).sign : F) * b i))
        (2 * M * (2 * (z i).natAbs))
      rw [map_mul, map_intCast,
        show 2 * M * (2 * (z i).natAbs) = 2 * (2 * M * (z i).natAbs) by ring]
      exact hvi
  rw [← hpmap] at hPM
  refine ⟨2 * M, by omega, principalMul_descend ψF _ g _ ?_ _ hPM⟩
  intro q hq
  obtain ⟨i, hi, hz, rfl⟩ := mem_resDiv hq
  refine ⟨?_, ?_⟩
  · refine mul_ne_zero two_ne_zero (mul_ne_zero ?_ (hb i hi))
    rcases lt_trichotomy (z i) 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · exact absurd h hz
    · rw [Int.sign_eq_one_of_pos h]; norm_num
  · rw [mul_pow, ← hab i hi]
    rcases lt_trichotomy (z i) 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · exact absurd h hz
    · rw [Int.sign_eq_one_of_pos h]; norm_num


set_option maxHeartbeats 3200000 in
/-- `hyp_no_elemK` for a curve `y² = p(x)` with `p` over the constants. -/
theorem hyp_no_elemKc (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : Kc[X]) (hp : Squarefree p) (hodd : Odd p.natDegree)
    (hy : y ^ 2 = aeval x p) (hgen : ∀ z : E, InHyp Kc x y z) (g : E) (B0 : Kc[X])
    (hB0deg : B0 = 0 ∨ B0.natDegree + 2 ≤ p.natDegree)
    (h : HasElementaryIntegral (g′ + aeval x B0 / y)) : B0 = 0 := by
  obtain ⟨L, _, _, _, _, hE, g0, hg⟩ := h
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g0 hg
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
  let κ : Kc →+* Cc := (j.comp (algebraMap Kc E)).codRestrict (constants L) fun c ↦ by
    rw [mem_constants, RingHom.comp_apply, hj, deriv_algebraMap, hC, map_zero, map_zero]
  have haevK : ∀ P : Kc[X], aeval (j x) (P.map κ) = j (aeval x P) := by
    intro P
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
    rfl
  set pC := p.map κ with hpC
  have hyL : j y ^ 2 = aeval (j x) pC := by rw [hpC, haevK, ← hy, map_pow]
  have hpsq : Squarefree pC := by
    have hsep : p.Separable := (PerfectField.separable_iff_squarefree).mpr hp
    exact (hsep.map).squarefree
  have hdeg : pC.natDegree = p.natDegree := natDegree_map_eq_of_injective κ.injective _
  have hoddC : Odd pC.natDegree := hdeg ▸ hodd
  -- `C(x)` over the constants of `L` contains the image of `Kc(x)`
  have hKx : ∀ z : E, z ∈ Kc⟮x⟯ → j z ∈ Cc⟮j x⟯ := by
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
    exact fun z hz ↦ hle hz
  -- the field `C(x)(y)` in `L` contains `constField E L`
  set S := hypField (j x) (j y) htr pC hoddC hyL with hS
  have hEs : ∀ e : E, j e ∈ S := by
    intro e
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen e
    exact ⟨j α, j β, hKx α hα, hKx β hβ, by rw [map_add, map_mul]⟩
  have hcf : ∀ z ∈ constField E L, InHyp Cc (j x) (j y) z := by
    let N : IntermediateField E L :=
      { S with algebraMap_mem' := hEs }
    have : constField E L ≤ N := adjoin_le_iff.mpr fun z hz ↦ by
      obtain ⟨c', rfl⟩ := hconst z hz
      exact ⟨algebraMap Cc L c', 0, IntermediateField.algebraMap_mem _ _, zero_mem _, by ring⟩
    exact fun z hz ↦ this hz
  -- the identity for `B₀`
  have hB0 : aeval (j x) (B0.map κ) / j y =
      (v - j g)′ + ∑ i ∈ s, c i * logDeriv (u i) := by
    have hg' := heq
    rw [map_add, ← hj, map_div₀] at hg'
    rw [haevK, map_sub]
    linear_combination hg'
  have hmain := hyp_glue (j x) (j y) hCc hxL htr hconst pC hpsq hoddC hyL
    (B0.map κ) (by
      rcases hB0deg with h | h
      · left; rw [h, Polynomial.map_zero]
      · right; rw [natDegree_map_eq_of_injective κ.injective, hdeg]; exact h)
    s c u (v - j g)
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩)
    (by
      obtain ⟨α, β, hα, hβ, hvα⟩ := hcf v hv
      obtain ⟨α', β', hα', hβ', hg1⟩ := hEs g
      refine ⟨α - α', β - β', sub_mem hα hα', sub_mem hβ hβ', ?_⟩
      rw [hvα, hg1]; ring)
    hB0
  exact (Polynomial.map_eq_zero_iff κ.injective).mp hmain

open CPoly in
/-- **`∫ B / y` for a curve over `F ⊆ Kc`**: elementary iff the remainder of `hypRed` vanishes. -/
theorem hyp_decidesKc {F : Type*} [Field F] [DecidableEq F] [CharZero F] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (ι : F →+* Kc) (x y : E)
    (hx : x′ = 1) (p : CPoly F) (hp : Squarefree (toPoly p)) (hodd : Odd (toPoly p).natDegree)
    (hy : y ^ 2 = aeval x ((toPoly p).map ι)) (hgen : ∀ z : E, InHyp Kc x y z) (B : CPoly F) :
    HasElementaryIntegral (evF ι x B / y) ↔ isZero (hypRed p B).2 = true := by
  have hp0 : toPoly p ≠ 0 := hp.ne_zero
  have hp1 : 1 ≤ (toPoly p).natDegree := by obtain ⟨k, hk⟩ := hodd; omega
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hpK0 : (toPoly p).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hp0
  have hpx : aeval x ((toPoly p).map ι) ≠ 0 := aeval_ne_zero_of_tr x htrK hpK0
  have hy0 : y ≠ 0 := by rintro rfl; apply hpx; rw [← hy]; ring
  have hpdeg : ((toPoly p).map ι).natDegree = (toPoly p).natDegree :=
    natDegree_map_eq_of_injective ι.injective _
  have hpsqK : Squarefree ((toPoly p).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hp).map).squarefree
  obtain ⟨hsp, hB0deg⟩ := hypRed_spec p B hp1
  set C0 := (hypRed p B).1
  set B0 := (hypRed p B).2
  have hdec : evF ι x B / y = (aeval x ((toPoly C0).map ι) * y)′ + evF ι x B0 / y := by
    rw [deriv_mul_y_K hC x y hx _ _ hy hy0, evF, evF, hsp]
    simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map, map_C, map_add]
    rw [map_div₀, map_one, map_ofNat]
    ring
  rw [hdec, isZero_iff]
  constructor
  · intro h
    have := hyp_no_elemKc hC hCall x y hx _ hpsqK (by rw [hpdeg]; exact hodd) hy hgen _
      ((toPoly B0).map ι) (by
        rcases hB0deg with h0 | h0
        · left; rw [h0, Polynomial.map_zero]
        · right; rw [natDegree_map_eq_of_injective ι.injective, hpdeg]; exact h0) h
    exact (Polynomial.map_eq_zero_iff ι.injective).mp this
  · intro h0
    rw [evF, h0, Polynomial.map_zero, map_zero, zero_div, add_zero]
    exact hasElementaryIntegral_of_deriv _

end Jac
