import RischTragerBronstein.Jacobian.AbelCore
import RischTragerBronstein.Algebraic.EllFunctional

/-!
# Abel's direction in any genus

`hyp_principal_of_elementary`: on `y² = p(x)` (`p ∈ ℚ[x]` squarefree of degree `2g + 1`), let the
poles of `(B(x) + ∑ rᵢ βᵢ / (x − αᵢ)) / y` be points `Pᵢ = (αᵢ, βᵢ)` defined over a field `F`
embedded in the constants (`αᵢ = ι aᵢ`, `βᵢ = ι bᵢ`). If the integral is elementary, then for every
`ℚ`-linear `Λ` with `Λ(rᵢ) = zᵢ / D`, a positive multiple of the divisor
`∑ zᵢ ([Pᵢ] − [σPᵢ])` is principal over `F` (`PrincipalMul` for `resDiv`).

Proof: `ell_glue` (Liouville with `ℚ`-independent `κⱼ`, `2rᵢ = −∑ κⱼ mᵢⱼ εᵢⱼ`), the norm shapes
of the logarithms (`norm_shape`), `abel_core` with the integer weights `D Gⱼ` (`Gⱼ = M Λ(κⱼ)`), and
descent from the constants of the elementary extension to `F` through the linear-algebra test
(`principalC_complete`, `principalC_sound`).
-/

open Polynomial IntermediateField

namespace Jac

/-- The residue divisor `∑ zᵢ ([Pᵢ] − [σPᵢ])` in the form `D⁺ + σ D⁻`. -/
noncomputable def resDiv {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → F) (z : ι → ℤ) : EDiv F :=
  (s.toList.filter fun i ↦ z i ≠ 0).map fun i ↦ (a i, ((z i).sign : F) * b i, 2 * (z i).natAbs)

lemma mem_resDiv {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {a b : ι → F} {z : ι → ℤ} {q : F × F × ℕ} (hq : q ∈ resDiv s a b z) :
    ∃ i ∈ s, z i ≠ 0 ∧ q = (a i, ((z i).sign : F) * b i, 2 * (z i).natAbs) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_filter] at hi
  exact ⟨i, Finset.mem_toList.mp hi.1, by simpa using hi.2, rfl⟩

lemma edeg_resDiv {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → F) (z : ι → ℤ) : edeg (resDiv s a b z) = ∑ i ∈ s, 2 * (z i).natAbs := by
  unfold edeg resDiv
  rw [List.map_map]
  have key : ∀ L : List ι, ((L.filter fun i ↦ z i ≠ 0).map
      ((fun q : F × F × ℕ ↦ q.2.2) ∘ fun i ↦ (a i, ((z i).sign : F) * b i, 2 * (z i).natAbs))).sum =
      (L.map fun i ↦ 2 * (z i).natAbs).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons i L ih => by_cases hz : z i = 0 <;> simp_all [List.filter_cons]
  rw [key, Finset.sum_map_toList]

/-- **Descent of principality** along a field embedding (through the linear-algebra test). -/
theorem principalMul_descend {F S : Type*} [Field F] [DecidableEq F] [Field S] (φ : F →+* S)
    (f : F[X]) (g : ℕ) (Γ : EDiv F) (hΓ : ∀ q ∈ Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = f.eval q.1)
    (n : ℕ) (h : PrincipalMul (f.map φ) g (emap φ Γ) n) : PrincipalMul f g Γ n := by
  classical
  obtain ⟨ψ, hψ0, hψp, hψv⟩ := h
  rw [edeg_emap] at hψp
  set fC : CPoly F := (List.range (f.natDegree + 1)).map f.coeff
  have hfC : CPoly.toPoly fC = f := EllAlgo.toPoly_range_coeff f _ (Or.inr (Nat.lt_succ_self _))
  set N := n * edeg Γ
  set A := N / 2 + 1
  set B := if 2 * g + 1 ≤ N then (N - 2 * g - 1) / 2 + 1 else 0
  have hΓn : ∀ q ∈ escale n Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (CPoly.toPoly fC).eval q.1 := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    rw [hfC]; exact hΓ q' hq'
  have hA : ψ.1.degree < A := by
    by_cases h0 : ψ.1 = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    rw [degree_eq_natDegree h0]
    exact_mod_cast (show ψ.1.natDegree < A by have := hψp.1; omega)
  have hB : ψ.2.degree < B := by
    rcases hψp.2 with h0 | h0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    by_cases h00 : ψ.2 = 0
    · rw [h00, degree_zero]; exact WithBot.bot_lt_coe _
    rw [degree_eq_natDegree h00]
    have hB' : B = (N - 2 * g - 1) / 2 + 1 := by simp only [B]; rw [if_pos (by omega)]
    rw [hB']
    exact_mod_cast (show ψ.2.natDegree < (N - 2 * g - 1) / 2 + 1 by omega)
  have hne := principalC_complete φ fC (escale n Γ) A B hΓn ψ hψ0 hA hB (by
    rw [hfC, emap_escale]; exact hψv)
  obtain ⟨⟨j, cs⟩, hjc⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨ψF, hψF0, hψFA, hψFB, hψFv⟩ := principalC_sound fC (escale n Γ) A B hΓn hjc
  rw [hfC] at hψFv
  refine ⟨ψF, hψF0, ⟨?_, ?_⟩, hψFv⟩
  · by_cases h0 : ψF.1 = 0
    · simp [h0]
    rw [degree_eq_natDegree h0] at hψFA
    have : ψF.1.natDegree < A := by exact_mod_cast hψFA
    omega
  · by_cases h0 : ψF.2 = 0
    · left; exact h0
    right
    rw [degree_eq_natDegree h0] at hψFB
    have : ψF.2.natDegree < B := by exact_mod_cast hψFB
    simp only [B] at this
    split_ifs at this with hN
    · omega
    · omega

section Main

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 12800000 in
/-- **Abel's direction in any genus.** -/
theorem hyp_principal_of_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {g : ℕ} (p : ℚ[X]) (hsq : Squarefree p) (hpdeg : p.natDegree = 2 * g + 1)
    (hy : y ^ 2 = aeval x p) (hgen : ∀ z : E, InHyp Kc x y z)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ι0 : F →+* Kc)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → F) (hb : ∀ i ∈ s, b i ≠ 0)
    (hab : ∀ i ∈ s, b i ^ 2 = (p.map (algebraMap ℚ F)).eval (a i)) (hinj : Set.InjOn a s)
    (B : Kc[X]) (r : ι → Kc)
    (h : HasElementaryIntegral ((aeval x B + ∑ i ∈ s,
      algebraMap Kc E (r i * ι0 (b i)) / (x - algebraMap Kc E (ι0 (a i)))) / y))
    (Λ : Kc →ₗ[ℚ] ℚ) (z : ι → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hΛ : ∀ i ∈ s, Λ (r i) = (z i : ℚ) / D) :
    ∃ n, 1 ≤ n ∧ PrincipalMul (p.map (algebraMap ℚ F)) g (resDiv s a b z) n := by
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
  set pC := p.map (algebraMap ℚ Cc) with hpC
  have haev : ∀ P : ℚ[X], aeval (j x) (P.map (algebraMap ℚ Cc)) = j (aeval x P) := by
    intro P
    rw [aeval_map_algebraMap, aeval_def, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_rat _ _
  have hyL : j y ^ 2 = aeval (j x) pC := by rw [hpC, haev, ← hy, map_pow]
  have hpsq : Squarefree pC := by
    have hsep : p.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
    exact (hsep.map).squarefree
  have hdeg : pC.natDegree = p.natDegree :=
    natDegree_map_eq_of_injective (algebraMap ℚ Cc).injective _
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
  set αP : ι → Cc := fun i ↦ ψF (a i) with hαP
  set βP : ι → Cc := fun i ↦ ψF (b i) with hβPd
  set rP : ι → Cc := fun i ↦ φ (r i) with hrP
  have hinjP : Set.InjOn αP s := fun i hi i' hi' hh ↦ hinj hi hi' (ψF.injective hh)
  have hβP : ∀ i ∈ s, βP i ≠ 0 := fun i hi ↦ (map_ne_zero_iff ψF ψF.injective).mpr (hb i hi)
  have hpαP : ∀ i ∈ s, pC.eval (αP i) = βP i ^ 2 := by
    intro i hi
    have := congrArg ψF (hab i hi)
    rw [map_pow] at this
    rw [this, hpC, hαP, eval_map, eval_map, hom_eval₂]
    congr 1
    exact RingHom.ext_rat _ _
  have haevK : aeval (j x) (B.map φ) = j (aeval x B) := by
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]; rfl
  have heqL : (aeval (j x) (B.map φ) + ∑ i ∈ s, algebraMap Cc L (rP i * βP i) /
      (j x - algebraMap Cc L (αP i))) / j y = v′ + ∑ i ∈ sL, cL i * logDeriv (u i) := by
    rw [haevK, add_comm (v′), ← heq]
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
  have hpmap : (p.map (algebraMap ℚ F)).map ψF = pC := by
    rw [Polynomial.map_map, hpC]; congr 1; exact RingHom.ext_rat _ _
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

end Main

end Jac
