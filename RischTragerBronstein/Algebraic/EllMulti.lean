import RischTragerBronstein.Algebraic.EllMixed
import RischTragerBronstein.Elementary.SqrtIndep

/-!
# Residues in any number of quadratic classes

`ell_torsion_multi`: if `∫ (B + ∑ᵢ (zᵢ/D) γᵢ d_{cl(i)} /(x − αᵢ) + ∑_{class k₀} …) dx / y` is
elementary, with the classes `d_k` pairwise in distinct square classes, then the class-`k₀`
divisor is torsion on the twist by `d_{k₀}`. As `ell_torsion_mixed`, with all the square roots
adjoined at once (`exists_sqrts_ext`) and the separating functional coming from the
`ℚ`-independence of square roots of distinct classes (`SqrtIndep.sqrt_indep`).
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

/-- A `ℚ`-linear functional picking the coefficient of one square root. -/
lemma exists_sep_functional_multi {Cc : Type*} [Field Cc] [CharZero Cc] {κ : Type*}
    [DecidableEq κ] (Kl : Finset κ) (sC : κ → Cc) (dk : κ → ℤ)
    (hs : ∀ k ∈ Kl, sC k ^ 2 = (dk k : Cc)) (hd : ∀ k ∈ Kl, dk k ≠ 0)
    (hcls : ∀ k ∈ Kl, ∀ k' ∈ Kl, k ≠ k' → ∀ q : ℚ, ((dk k * dk k' : ℤ) : ℚ) ≠ q ^ 2)
    (k₀ : κ) (hk₀ : k₀ ∈ Kl) :
    ∃ l : Cc →ₗ[ℚ] ℚ, l (sC k₀) = 1 ∧ ∀ k ∈ Kl, k ≠ k₀ → l (sC k) = 0 := by
  classical
  let f : (Kl → ℚ) →ₗ[ℚ] Cc :=
    { toFun := fun v ↦ ∑ k : Kl, v k • sC k
      map_add' := fun v w ↦ by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r v ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change ∑ k : Kl, v k • sC k = 0 at hv
    have hz := SqrtIndep.sqrt_indep Kl sC (fun k ↦ (dk k : ℚ)) (fun k hk ↦ by
        rw [hs k hk]; push_cast; rfl) (fun k hk ↦ by exact_mod_cast hd k hk)
      (fun k hk k' hk' hkk' q ↦ by have := hcls k hk k' hk' hkk' q; push_cast at this ⊢; exact this)
      (fun k ↦ if hk : k ∈ Kl then v ⟨k, hk⟩ else 0) (by
        rw [← Finset.sum_coe_sort Kl]
        rw [← hv]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [dif_pos k.2, Rat.smul_def])
    ext k
    have := hz k k.2
    simp only [dif_pos k.2] at this
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  have hf : ∀ k (hk : k ∈ Kl), f (Pi.single ⟨k, hk⟩ 1) = sC k := fun k hk ↦ by
    change ∑ k' : Kl, (Pi.single (⟨k, hk⟩ : Kl) (1 : ℚ) : Kl → ℚ) k' • sC k' = sC k
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
    · simp
  have hgf : ∀ k (hk : k ∈ Kl), g (sC k) = Pi.single ⟨k, hk⟩ 1 := fun k hk ↦ by
    rw [← hf k hk]
    exact congrArg (fun φ ↦ φ (Pi.single ⟨k, hk⟩ 1)) hg
  refine ⟨(LinearMap.proj ⟨k₀, hk₀⟩).comp g, ?_, fun k hk hkk ↦ ?_⟩
  · simp [hgf k₀ hk₀]
  · simp only [LinearMap.comp_apply, LinearMap.proj_apply, hgf k hk]
    exact Pi.single_eq_of_ne (fun h ↦ hkk (congrArg Subtype.val h).symm) _

section Multi

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 12800000 in
/-- **Residues in several quadratic classes**: if the integral is elementary, the divisor of the
class-`k₀` residues is torsion on the twist by `d_{k₀}`. -/
theorem ell_torsion_multi (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (B : ℚ[X]) {κ : Type*} [DecidableEq κ] (Kl : Finset κ) (dk : κ → ℤ)
    (hdk : ∀ k ∈ Kl, dk k ≠ 0)
    (hcls : ∀ k ∈ Kl, ∀ k' ∈ Kl, k ≠ k' → ∀ q : ℚ, ((dk k * dk k' : ℤ) : ℚ) ≠ q ^ 2)
    (k₀ : κ) (hk₀ : k₀ ∈ Kl)
    {ι₁ ι₂ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (cl : ι₁ → κ)
    (hcl : ∀ i, cl i ∈ Kl ∧ cl i ≠ k₀) (α₁ γ₁ : ι₁ → ℚ) (α₂ γ₂ : ι₂ → ℚ)
    (hQ₁ : ∀ i, (dk (cl i) : ℚ) * γ₁ i ^ 2 = α₁ i ^ 3 + a * α₁ i ^ 2 + b * α₁ i + c)
    (hP : ∀ i, (EllNL.W (a * dk k₀) (b * dk k₀ ^ 2) (c * dk k₀ ^ 3)).toAffine.Nonsingular
      (dk k₀ * α₂ i) (dk k₀ ^ 2 * γ₂ i))
    (hγ₁ : ∀ i ∈ s₁, γ₁ i ≠ 0) (hγ₂ : ∀ i ∈ s₂, γ₂ i ≠ 0)
    (hinj₁ : Set.InjOn α₁ s₁) (hinj₂ : Set.InjOn α₂ s₂) (z₁ : ι₁ → ℤ) (z₂ : ι₂ → ℤ)
    (D : ℕ) (hD : D ≠ 0)
    (h : HasElementaryIntegral ((aeval x B + ∑ i ∈ s₁,
      (((z₁ i : ℚ) / D * γ₁ i * dk (cl i) : ℚ) : E) / (x - ((α₁ i : ℚ) : E)) + ∑ i ∈ s₂,
      (((z₂ i : ℚ) / D * γ₂ i * dk k₀ : ℚ) : E) / (x - ((α₂ i : ℚ) : E))) / y)) :
    IsOfFinAddOrder (∑ i ∈ s₂, z₂ i • (Point.some _ _ (hP i) :
      (EllNL.W (a * dk k₀) (b * dk k₀ ^ 2) (c * dk k₀ ^ 3)).toAffine.Point)) := by
  classical
  set d₂ := dk k₀ with hd₂def
  have hd₂ : d₂ ≠ 0 := hdk k₀ hk₀
  set p : ℚ[X] := X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) with hpdef
  have hpdeg : p.natDegree = 3 := by rw [hpdef]; compute_degree!
  have hodd : Odd p.natDegree := by rw [hpdeg]; decide
  obtain ⟨L0, _, _, _, _, hE0, g00, hg0⟩ := h
  have : CharZero L0 := charZero_of_injective_algebraMap (algebraMap E L0).injective
  -- adjoin all the square roots
  obtain ⟨L, _, _, _, hDAL, hEL, _, hroots⟩ := exists_sqrts_ext (L := L0)
    (Kl.toList.map fun k ↦ ((dk k : ℤ) : ℚ)) (by
      intro d hd
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
      exact_mod_cast hdk k (Finset.mem_toList.mp hk))
  have hroot : ∀ k ∈ Kl, ∃ s : L, s ^ 2 = (((dk k : ℤ) : ℚ) : L) ∧ s′ = 0 := fun k hk ↦
    hroots _ (List.mem_map.mpr ⟨k, Finset.mem_toList.mpr hk, rfl⟩)
  choose! sq hsq2 hsq' using hroot
  letI : Algebra E L := ((algebraMap L0 L).comp (algebraMap E L0)).toAlgebra
  haveI : IsScalarTower E L0 L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra E L :=
    ⟨fun a ↦ by
      change (algebraMap L0 L (algebraMap E L0 a))′ = algebraMap L0 L (algebraMap E L0 a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hE : IsElementaryExtension E L := hE0.trans hEL
  set g0 := algebraMap L0 L g00
  have hg : g0′ = algebraMap E L ((aeval x B + ∑ i ∈ s₁,
      (((z₁ i : ℚ) / D * γ₁ i * dk (cl i) : ℚ) : E) / (x - ((α₁ i : ℚ) : E)) + ∑ i ∈ s₂,
      (((z₂ i : ℚ) / D * γ₂ i * d₂ : ℚ) : E) / (x - ((α₂ i : ℚ) : E))) / y) := by
    rw [deriv_algebraMap, hg0]; rfl
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
  -- the square roots among the constants of `L`
  set sC : κ → Cc := fun k ↦ if hk : k ∈ Kl then ⟨sq k, hsq' k hk⟩ else 0 with hsCdef
  have hsC : ∀ k ∈ Kl, sC k ^ 2 = (dk k : Cc) := by
    intro k hk
    apply Subtype.ext
    simp only [sC, dif_pos hk]
    push_cast
    rw [hsq2 k hk]; push_cast; rfl
  have hsC0 : ∀ k ∈ Kl, sC k ≠ 0 := fun k hk h0 ↦ by
    apply hdk k hk; exact_mod_cast (by rw [← hsC k hk, h0]; ring : (dk k : Cc) = 0)
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂
  -- the class-`k₀` points satisfy `d₂ γ² = p(α)`
  have hQ₂ : ∀ i, (d₂ : ℚ) * γ₂ i ^ 2 = α₂ i ^ 3 + a * α₂ i ^ 2 + b * α₂ i + c := by
    intro i
    have he := (EllNL.equation_W _ _ _).mp (hP i).1
    unfold EllNL.OnCurve at he
    push_cast at he
    have : (d₂ : ℚ) ^ 3 * ((d₂ : ℚ) * γ₂ i ^ 2 - (α₂ i ^ 3 + a * α₂ i ^ 2 + b * α₂ i + c)) = 0 := by
      linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hd₂q))
  -- the data of `ell_glue`, indexed by `ι₁ ⊕ ι₂`
  set sP : Finset (ι₁ ⊕ ι₂) := s₁.disjSum s₂ with hsP
  set αP : ι₁ ⊕ ι₂ → Cc := fun i ↦ Sum.elim (fun k ↦ ((α₁ k : ℚ) : Cc)) (fun k ↦ ((α₂ k : ℚ) : Cc)) i
  set βP : ι₁ ⊕ ι₂ → Cc := fun i ↦ Sum.elim (fun k ↦ ((γ₁ k : ℚ) : Cc) * sC (cl k))
    (fun k ↦ ((γ₂ k : ℚ) : Cc) * sC k₀) i
  set rP : ι₁ ⊕ ι₂ → Cc := fun i ↦ Sum.elim (fun k ↦ (((z₁ k : ℚ) / D : ℚ) : Cc) * sC (cl k))
    (fun k ↦ (((z₂ k : ℚ) / D : ℚ) : Cc) * sC k₀) i
  have hcurve : ∀ i, βP i ^ 2 = αP i ^ 3 + a * αP i ^ 2 + b * αP i + c := by
    rintro (k | k)
    · simp only [αP, βP, Sum.elim_inl]
      have := congrArg (fun q : ℚ ↦ (q : Cc)) (hQ₁ k)
      push_cast at this
      rw [mul_pow, hsC (cl k) (hcl k).1, ← this]; ring
    · simp only [αP, βP, Sum.elim_inr]
      have := congrArg (fun q : ℚ ↦ (q : Cc)) (hQ₂ k)
      push_cast at this
      rw [mul_pow, hsC k₀ hk₀, ← this]; ring
  have hβP : ∀ i ∈ sP, βP i ≠ 0 := by
    rintro (k | k) hk
    · simp only [sP, Finset.inl_mem_disjSum] at hk
      simp only [βP, Sum.elim_inl]
      exact mul_ne_zero (by exact_mod_cast hγ₁ k hk) (hsC0 _ (hcl k).1)
    · simp only [sP, Finset.inr_mem_disjSum] at hk
      simp only [βP, Sum.elim_inr]; exact mul_ne_zero (by exact_mod_cast hγ₂ k hk) (hsC0 k₀ hk₀)
  have hinjP : Set.InjOn αP sP := by
    rintro (k | k) hk (k' | k') hk' he
    · simp only [αP, Sum.elim_inl] at he
      have : α₁ k = α₁ k' := by exact_mod_cast he
      rw [hinj₁ (by simpa [sP] using hk) (by simpa [sP] using hk') this]
    · exfalso
      simp only [αP, Sum.elim_inl, Sum.elim_inr] at he
      have hα : α₁ k = α₂ k' := by exact_mod_cast he
      have hk1 : k ∈ s₁ := by simpa [sP] using hk
      have e := (hQ₁ k).trans (hα ▸ (hQ₂ k')).symm
      apply hcls (cl k) (hcl k).1 k₀ hk₀ (hcl k).2 (γ₂ k' * d₂ / γ₁ k)
      have h0 := hγ₁ k hk1
      rw [div_pow, eq_div_iff (pow_ne_zero 2 h0)]
      push_cast
      linear_combination (d₂ : ℚ) * e
    · exfalso
      simp only [αP, Sum.elim_inl, Sum.elim_inr] at he
      have hα : α₂ k = α₁ k' := by exact_mod_cast he
      have hk1 : k' ∈ s₁ := by simpa [sP] using hk'
      have e := (hQ₁ k').trans (hα ▸ (hQ₂ k)).symm
      apply hcls (cl k') (hcl k').1 k₀ hk₀ (hcl k').2 (γ₂ k * d₂ / γ₁ k')
      have h0 := hγ₁ k' hk1
      rw [div_pow, eq_div_iff (pow_ne_zero 2 h0)]
      push_cast
      linear_combination (d₂ : ℚ) * e
    · simp only [αP, Sum.elim_inr] at he
      have : α₂ k = α₂ k' := by exact_mod_cast he
      rw [hinj₂ (by simpa [sP] using hk) (by simpa [sP] using hk') this]
  have hpαP : ∀ i ∈ sP, pC.eval (αP i) = βP i ^ 2 := by
    intro i _
    rw [hcurve i, hpC, hpdef, eval_map]
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eq_ratCast]
    push_cast; ring
  have heqL : (aeval (j x) (B.map (algebraMap ℚ Cc)) + ∑ i ∈ sP, algebraMap Cc L (rP i * βP i) /
      (j x - algebraMap Cc L (αP i))) / j y = v′ + ∑ i ∈ sL, cL i * logDeriv (u i) := by
    have hrb₁ : ∀ k, (((z₁ k : ℚ) / D : ℚ) : Cc) * sC (cl k) * (((γ₁ k : ℚ) : Cc) * sC (cl k)) =
        (((z₁ k : ℚ) / D * γ₁ k * dk (cl k) : ℚ) : Cc) := by
      intro k
      rw [show (((z₁ k : ℚ) / D : ℚ) : Cc) * sC (cl k) * (((γ₁ k : ℚ) : Cc) * sC (cl k)) =
        (((z₁ k : ℚ) / D : ℚ) : Cc) * ((γ₁ k : ℚ) : Cc) * sC (cl k) ^ 2 by ring,
        hsC (cl k) (hcl k).1]
      push_cast; ring
    have hrb₂ : ∀ k, (((z₂ k : ℚ) / D : ℚ) : Cc) * sC k₀ * (((γ₂ k : ℚ) : Cc) * sC k₀) =
        (((z₂ k : ℚ) / D * γ₂ k * d₂ : ℚ) : Cc) := by
      intro k
      rw [show (((z₂ k : ℚ) / D : ℚ) : Cc) * sC k₀ * (((γ₂ k : ℚ) : Cc) * sC k₀) =
        (((z₂ k : ℚ) / D : ℚ) : Cc) * ((γ₂ k : ℚ) : Cc) * sC k₀ ^ 2 by ring, hsC k₀ hk₀]
      push_cast; ring
    rw [haev, add_comm (v′), ← heq, hsP, Finset.sum_disjSum]
    simp only [rP, βP, αP, Sum.elim_inl, Sum.elim_inr, hrb₁, hrb₂, map_div₀, map_add, map_sum,
      map_sub, map_ratCast, add_assoc]
  obtain ⟨t, κ, a', b', -, hab, hN0, hshape, hres⟩ := ell_glue (j x) (j y) hCc hxL htr hconst
    pC hpsq hoddC hyL (B.map (algebraMap ℚ Cc)) sP αP βP rP hinjP hβP hpαP sL cL u v
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩)
    (hcf v hv) heqL
  choose! m ε hdat hrel using hres
  have hpf : pC = EllAbel.f (a : Cc) (b : Cc) (c : Cc) := by
    rw [hpC, hpdef, EllAbel.f]; simp
  have hQns : ∀ i, (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Nonsingular (αP i) (βP i) :=
    fun i ↦ ell_ns a b c pC hpf hpsq _ _ (hcurve i)
  set Q : ι₁ ⊕ ι₂ → (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point :=
    fun i ↦ Point.some _ _ (hQns i) with hQ
  -- Abel for every logarithm
  have habel : ∀ jj ∈ t, (2 : ℤ) • ∑ i ∈ sP, ((m i jj : ℤ) * ε i jj) • Q i = 0 := fun jj hjj ↦
    ell_abel_log a b c pC hpf hpsq sP αP βP hinjP hβP hcurve (a' jj) (b' jj) (hab jj hjj)
      (hN0 jj hjj) (hshape jj hjj) (fun i ↦ m i jj) (fun i ↦ ε i jj)
      (fun i hi ↦ hdat i hi jj hjj) hQns
  -- the separating functional and the integer weights
  obtain ⟨l, hl₂, hl₁⟩ := exists_sep_functional_multi Kl sC dk hsC hdk hcls k₀ hk₀
  set qv : ℕ → ℚ := fun jj ↦ l (κ jj)
  set K : ℕ := ∏ jj ∈ t, (qv jj).den with hK
  have hK0 : K ≠ 0 := Finset.prod_ne_zero_iff.mpr fun jj _ ↦ (qv jj).den_ne_zero
  set e : ℕ → ℤ := fun jj ↦ (qv jj * K).num
  have he : ∀ jj ∈ t, (e jj : ℚ) = qv jj * K := fun jj hjj ↦
    num_mul_of_den_dvd' _ _ (Finset.dvd_prod_of_mem _ hjj)
  -- the residue relations, through `l`
  have hlin : ∀ i ∈ sP, ∑ jj ∈ t, (e jj : ℚ) * ((m i jj : ℚ) * ε i jj) = -2 * K * l (rP i) := by
    intro i hi
    have h1 := congrArg l (hrel i hi)
    rw [map_neg, map_sum] at h1
    have h2 : ∀ jj ∈ t, l (κ jj * ((m i jj : Cc) * ε i jj)) = qv jj * ((m i jj : ℚ) * ε i jj) := by
      intro jj _
      rw [show κ jj * ((m i jj : Cc) * ε i jj) = ((m i jj : ℤ) * ε i jj) • κ jj by
        rw [zsmul_eq_mul]; push_cast; ring, map_zsmul, zsmul_eq_mul]
      push_cast; ring
    rw [Finset.sum_congr rfl h2] at h1
    rw [show (2 : Cc) * rP i = (2 : ℚ) • rP i by rw [Rat.smul_def]; push_cast; rfl, map_smul,
      smul_eq_mul] at h1
    rw [Finset.sum_congr rfl fun jj hjj ↦ by rw [he jj hjj]]
    have : ∑ jj ∈ t, qv jj * K * ((m i jj : ℚ) * ε i jj) =
        K * ∑ jj ∈ t, qv jj * ((m i jj : ℚ) * ε i jj) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [this, ← neg_eq_iff_eq_neg.mpr h1]
    ring
  have hlr₁ : ∀ k, l (rP (Sum.inl k)) = 0 := fun k ↦ by
    simp only [rP, Sum.elim_inl]
    rw [show (((z₁ k : ℚ) / D : ℚ) : Cc) * sC (cl k) = ((z₁ k : ℚ) / D) • sC (cl k) by
      rw [Rat.smul_def], map_smul, hl₁ (cl k) (hcl k).1 (hcl k).2, smul_zero]
  have hlr₂ : ∀ k, l (rP (Sum.inr k)) = (z₂ k : ℚ) / D := fun k ↦ by
    simp only [rP, Sum.elim_inr]
    rw [show (((z₂ k : ℚ) / D : ℚ) : Cc) * sC k₀ = ((z₂ k : ℚ) / D) • sC k₀ by rw [Rat.smul_def],
      map_smul, hl₂, smul_eq_mul, mul_one]
  -- combine the Abel relations with the weights
  set w : ι₁ ⊕ ι₂ → ℤ := fun i ↦ ∑ jj ∈ t, e jj * ((m i jj : ℤ) * ε i jj)
  have hcomb : (2 : ℤ) • ∑ i ∈ sP, w i • Q i = 0 := by
    have : ∑ jj ∈ t, e jj • ((2 : ℤ) • ∑ i ∈ sP, ((m i jj : ℤ) * ε i jj) • Q i) = 0 :=
      Finset.sum_eq_zero fun jj hjj ↦ by rw [habel jj hjj, smul_zero]
    rw [← this]
    simp only [Finset.smul_sum, w, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun jj _ ↦ ?_
    ring_nf
  have hw : ∀ i ∈ sP, (D : ℤ) * w i = -2 * K * (Sum.elim (fun _ ↦ 0) z₂ i) := by
    intro i hi
    have h1 := hlin i hi
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    have : ((D * w i : ℤ) : ℚ) = ((-2 * K * (Sum.elim (fun _ ↦ 0) z₂ i) : ℤ) : ℚ) := by
      push_cast [w]
      rw [h1]
      rcases i with k | k
      · rw [hlr₁]; simp
      · rw [hlr₂]; simp only [Sum.elim_inr]; field_simp
    exact_mod_cast this
  have hfin2 : ((-4 : ℤ) * K) • ∑ k ∈ s₂, z₂ k • Q (Sum.inr k) = 0 := by
    have h1 : (D : ℤ) • ((2 : ℤ) • ∑ i ∈ sP, w i • Q i) = 0 := by rw [hcomb, smul_zero]
    rw [smul_smul, Finset.smul_sum] at h1
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [smul_smul, show (D : ℤ) * 2 * w i = 2 * ((D : ℤ) * w i) by ring, hw i hi]] at h1
    rw [hsP, Finset.sum_disjSum] at h1
    simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, zero_smul, Finset.sum_const_zero,
      zero_add] at h1
    rw [Finset.smul_sum]
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_smul]; ring_nf
  -- the twist `E^{d₂}(ℚ) → E(C)`
  obtain ⟨Td, hTd_inj, hTd⟩ := EllNL.twist_transport a b c d₂ hd₂ (sC k₀) (hsC k₀ hk₀)
  have hQtoK : ∀ k, Td (Point.some _ _ (hP k)) = Q (Sum.inr k) := fun k ↦
    hTd (α₂ k) (γ₂ k) (hP k) (hQns (Sum.inr k))
  have hfin : IsOfFinAddOrder (Td (∑ k ∈ s₂, z₂ k •
      (Point.some _ _ (hP k) : (EllNL.W (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3)).toAffine.Point))) := by
    rw [map_sum]
    simp only [map_zsmul, hQtoK]
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨(-4 : ℤ) * K,
      mul_ne_zero (by norm_num) (by exact_mod_cast hK0), hfin2⟩
  obtain ⟨n, hn, hnP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hfin
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hTd_inj ?_⟩
  rw [map_nsmul, hnP, map_zero]

end Multi

end Differential
