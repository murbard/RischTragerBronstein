import RischTragerBronstein.Algebraic.EllTwist

/-!
# Residues in two quadratic classes

`ell_abel_log`: Abel's theorem for one normalized logarithm `a + b y` of the Liouville form
(`2 ∑ nᵢ Qᵢ = 0`, `nᵢ = ± mᵢ` its signed multiplicity at `(αᵢ, βᵢ)`).

`ell_torsion_mixed`: if `∫ (B + ∑ᵢ (zᵢ/D) γᵢ dᵢ /(x − αᵢ)) dx / y` is elementary, with every
`dᵢ ∈ {d₁, d₂}` and `d₁ d₂` not a square, then the class-`d₂` part `∑_{dᵢ = d₂} zᵢ (d₂αᵢ, d₂²γᵢ)`
is torsion on the twist by `d₂`. Proof: a `ℚ`-linear functional `λ` on the constants with
`λ(√d₂) = 1`, `λ(√d₁) = 0` (the two roots are `ℚ`-independent) turns the residue relations
`2 rᵢ = −∑ⱼ κⱼ nᵢⱼ` into integer relations `∑ⱼ eⱼ nᵢⱼ ∝ zᵢ [dᵢ = d₂]`, and the per-logarithm
Abel relations combine with the weights `eⱼ`.
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

/-- **Abel for one logarithm**: `2 ∑ ±mᵢ Qᵢ = 0`. -/
lemma ell_abel_log {Cc : Type*} [Field Cc] [CharZero Cc] [DecidableEq Cc] (a b c : ℤ) (pC : Cc[X])
    (hpf : pC = EllAbel.f (a : Cc) (b : Cc) (c : Cc)) (hpsq : Squarefree pC)
    {ι : Type*} (s : Finset ι) (αP βP : ι → Cc) (hinjP : Set.InjOn αP s)
    (hβP : ∀ i ∈ s, βP i ≠ 0)
    (hcurve : ∀ i, βP i ^ 2 = αP i ^ 3 + a * αP i ^ 2 + b * αP i + c)
    (a' b' : Cc[X]) (hab : IsCoprime a' b') (hN0 : hN pC a' b' ≠ 0)
    (hshape : ∀ q : Cc[X], Irreducible q → q ∣ hN pC a' b' →
      (∃ i ∈ s, q ∣ X - Polynomial.C (αP i)) ∨ (q ∣ pC ∧ ¬q ^ 2 ∣ hN pC a' b'))
    (m : ι → ℕ) (ε : ι → ℤ)
    (hdat : ∀ i ∈ s, (ε i = 1 ∨ ε i = -1) ∧
      (X - Polynomial.C (αP i)) ^ m i ∣ hN pC a' b' ∧
      ¬(X - Polynomial.C (αP i)) ^ (m i + 1) ∣ hN pC a' b' ∧
      (0 < m i → a'.eval (αP i) = ε i * βP i * b'.eval (αP i)))
    (hQns : ∀ i, (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Nonsingular (αP i) (βP i)) :
    (2 : ℤ) • ∑ i ∈ s, ((m i : ℤ) * ε i) •
      (Point.some _ _ (hQns i) : (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point) = 0 := by
  classical
  obtain ⟨lam, gq, hlam, hgq, hfac⟩ := norm_shape (hN pC a' b') pC hN0 s αP
    hinjP m (fun i hi ↦ ⟨(hdat i hi).2.1, (hdat i hi).2.2.1⟩) hshape
  haveI : IsDedekindDomain (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.CoordinateRing :=
    isDedekindDomain_coordinateRing (a : Cc) (b : Cc) (c : Cc) (by
      have h' := hpsq; rw [hpf] at h'; exact h')
  have hpαP' : ∀ i, pC.eval (αP i) = βP i ^ 2 := by
    intro i
    rw [hcurve i, hpf, EllAbel.f]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
  set β' : ι → Cc := fun i ↦ if i ∈ s then -(ε i : Cc) * βP i else βP i with hβ'
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
  have hsign : ∀ i ∈ s, (ε i : Cc) ^ 2 = 1 := by
    intro i hi
    rcases (hdat i hi).1 with h1 | h1 <;> rw [h1] <;> norm_num
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
    rcases (hdat i hi).1 with h1 | h1 <;> rw [h1] <;> norm_num
  have hvan : ∀ i ∈ s, 0 < m i → a'.eval (αP i) + b'.eval (αP i) * β' i = 0 := by
    intro i hi hm
    rw [(hdat i hi).2.2.2 hm]
    simp only [hβ', if_pos hi]
    ring
  have habel := EllAbel.abel_two_torsion (hsq := by rw [← hpf]; exact hpsq) a' b'
    hab s αP β' hP' hβne hinjP m gq (by rw [← hpf]; exact hgq) lam hlam
    (by rw [← hpf]; exact hfac) hvan
  set Q : ι → (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point :=
    fun i ↦ Point.some _ _ (hQns i) with hQ
  have hpt : ∀ i ∈ s, (m i • (Point.some _ _ (hP' i) :
      (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point)) = (-((m i : ℤ) * ε i)) • Q i := by
    intro i hi
    rcases (hdat i hi).1 with h1 | h1
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
  set T := ∑ i ∈ s, ((m i : ℤ) * ε i) • Q i with hT
  have : ∑ i ∈ s, (m i • (Point.some _ _ (hP' i) :
      (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point)) = -T := by
    rw [Finset.sum_congr rfl hpt, hT, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [neg_zsmul]
  have h2 := habel
  rw [this, smul_neg, neg_eq_zero] at h2
  rw [← natCast_zsmul] at h2
  exact_mod_cast h2

/-- Points on the curve are nonsingular (the curve is smooth). -/
lemma ell_ns {Cc : Type*} [Field Cc] [CharZero Cc] (a b c : ℤ) (pC : Cc[X])
    (hpf : pC = EllAbel.f (a : Cc) (b : Cc) (c : Cc)) (hpsq : Squarefree pC) (α w : Cc)
    (hcurve : w ^ 2 = α ^ 3 + a * α ^ 2 + b * α + c) :
    (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Nonsingular α w := by
  rw [nonsingular_iff']
  refine ⟨by
    rw [equation_iff]
    simp only [EllAbel.W, zero_mul, add_zero]
    linear_combination hcurve, ?_⟩
  by_cases h0 : w = 0
  · left
    have hroot : pC.eval α = 0 := by
      rw [hpf, EllAbel.f]
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
      rw [h0] at hcurve; linear_combination -hcurve
    have hder : (derivative pC).eval α ≠ 0 := by
      intro hd
      have hsep : pC.Separable := (PerfectField.separable_iff_squarefree).mpr hpsq
      rw [Polynomial.separable_def] at hsep
      obtain ⟨u1, u2, huv⟩ := hsep
      have := congrArg (eval α) huv
      simp only [eval_add, eval_mul, eval_one, hroot, hd, mul_zero, add_zero] at this
      exact zero_ne_one this
    simp only [EllAbel.W, zero_mul, zero_sub, ne_eq, neg_eq_zero]
    intro hx0
    apply hder
    rw [hpf, EllAbel.f]
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X,
      zero_mul, zero_add, mul_one, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      add_zero]
    push_cast at hx0 ⊢
    linear_combination hx0
  · right
    simp only [EllAbel.W, zero_mul, add_zero]
    exact mul_ne_zero two_ne_zero h0

/-- A `ℚ`-linear functional separating `√d₂` from `√d₁` (`d₁d₂` not a square). -/
lemma exists_sep_functional {Cc : Type*} [Field Cc] [CharZero Cc] (s₁ s₂ : Cc) (d₁ d₂ : ℤ)
    (h₁ : s₁ ^ 2 = d₁) (h₂ : s₂ ^ 2 = d₂) (hd₂ : d₂ ≠ 0)
    (hns : ∀ q : ℚ, ((d₁ * d₂ : ℤ) : ℚ) ≠ q ^ 2) :
    ∃ l : Cc →ₗ[ℚ] ℚ, l s₁ = 0 ∧ l s₂ = 1 := by
  have hs₂ : s₂ ≠ 0 := by
    rintro rfl; apply hd₂; exact_mod_cast (by rw [← h₂]; ring : (d₂ : Cc) = 0)
  let f : (Fin 2 → ℚ) →ₗ[ℚ] Cc :=
    { toFun := fun v ↦ v 0 • s₁ + v 1 • s₂
      map_add' := fun v w ↦ by simp only [Pi.add_apply, add_smul]; abel
      map_smul' := fun r v ↦ by simp only [Pi.smul_apply, smul_eq_mul, mul_smul,
        RingHom.id_apply, smul_add] }
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change v 0 • s₁ + v 1 • s₂ = 0 at hv
    simp only [Rat.smul_def] at hv
    have hsq : ((v 0 : Cc) * s₁) ^ 2 = ((v 1 : Cc) * s₂) ^ 2 := by
      rw [show (v 0 : Cc) * s₁ = -((v 1 : Cc) * s₂) by linear_combination hv]; ring
    rw [mul_pow, mul_pow, h₁, h₂] at hsq
    have hq : (v 0) ^ 2 * d₁ = (v 1) ^ 2 * d₂ := by exact_mod_cast hsq
    have h0 : v 0 = 0 := by
      by_contra h0
      apply hns (v 1 * d₂ / v 0)
      push_cast
      field_simp
      linear_combination hq
    have h1 : v 1 = 0 := by
      rw [h0, Rat.cast_zero, zero_mul, zero_add] at hv
      exact_mod_cast (mul_eq_zero.mp hv).resolve_right hs₂
    ext i; fin_cases i <;> simp [h0, h1]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  refine ⟨(LinearMap.proj 1).comp g, ?_, ?_⟩
  · have := congrArg (fun φ ↦ φ (Pi.single 0 1)) hg
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    have e : f (Pi.single 0 1) = s₁ := by simp [f]
    rw [e] at this
    simp [this]
  · have := congrArg (fun φ ↦ φ (Pi.single 1 1)) hg
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    have e : f (Pi.single 1 1) = s₂ := by simp [f]
    rw [e] at this
    simp [this]

lemma num_mul_of_den_dvd' (q : ℚ) (n : ℕ) (h : q.den ∣ n) : (((q * n).num : ℤ) : ℚ) = q * n := by
  obtain ⟨m, hm⟩ := h
  have : q * n = ((q.num * m : ℤ) : ℚ) := by
    rw [hm]
    nth_rewrite 1 [← Rat.num_div_den q]
    push_cast
    have : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    field_simp
  rw [this, Rat.num_intCast]

section Mixed

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 12800000 in
/-- **Residues in two quadratic classes**: if the integral is elementary, the divisor of the
class-`d₂` residues is torsion on the twist by `d₂`. -/
theorem ell_torsion_mixed (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (B : ℚ[X]) (d₁ d₂ : ℤ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hns : ∀ q : ℚ, ((d₁ * d₂ : ℤ) : ℚ) ≠ q ^ 2)
    {ι₁ ι₂ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (α₁ γ₁ : ι₁ → ℚ) (α₂ γ₂ : ι₂ → ℚ)
    (hQ₁ : ∀ i, (d₁ : ℚ) * γ₁ i ^ 2 = α₁ i ^ 3 + a * α₁ i ^ 2 + b * α₁ i + c)
    (hP : ∀ i, (EllNL.W (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3)).toAffine.Nonsingular (d₂ * α₂ i)
      (d₂ ^ 2 * γ₂ i))
    (hγ₁ : ∀ i ∈ s₁, γ₁ i ≠ 0) (hγ₂ : ∀ i ∈ s₂, γ₂ i ≠ 0)
    (hinj₁ : Set.InjOn α₁ s₁) (hinj₂ : Set.InjOn α₂ s₂) (z₁ : ι₁ → ℤ) (z₂ : ι₂ → ℤ)
    (D : ℕ) (hD : D ≠ 0)
    (h : HasElementaryIntegral ((aeval x B + ∑ i ∈ s₁,
      (((z₁ i : ℚ) / D * γ₁ i * d₁ : ℚ) : E) / (x - ((α₁ i : ℚ) : E)) + ∑ i ∈ s₂,
      (((z₂ i : ℚ) / D * γ₂ i * d₂ : ℚ) : E) / (x - ((α₂ i : ℚ) : E))) / y)) :
    IsOfFinAddOrder (∑ i ∈ s₂, z₂ i •
      (Point.some _ _ (hP i) : (EllNL.W (a * d₂) (b * d₂ ^ 2) (c * d₂ ^ 3)).toAffine.Point)) := by
  classical
  set p : ℚ[X] := X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) with hpdef
  have hpdeg : p.natDegree = 3 := by rw [hpdef]; compute_degree!
  have hodd : Odd p.natDegree := by rw [hpdeg]; decide
  obtain ⟨L0, _, _, _, _, hE0, g00, hg0⟩ := h
  have : CharZero L0 := charZero_of_injective_algebraMap (algebraMap E L0).injective
  -- adjoin `√d₁`, then `√d₂`
  obtain ⟨L1, _, _, _, hDAL1, hEL1, sq₁, hsq₁2, hsq₁', -⟩ := exists_sqrt_ext (((d₁ : ℚ) : L0))
    (deriv_ratCast_L _) (by exact_mod_cast hd₁)
  letI : Algebra E L1 := ((algebraMap L0 L1).comp (algebraMap E L0)).toAlgebra
  haveI : IsScalarTower E L0 L1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA1 : DifferentialAlgebra E L1 :=
    ⟨fun a ↦ by
      change (algebraMap L0 L1 (algebraMap E L0 a))′ = algebraMap L0 L1 (algebraMap E L0 a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hE1 : IsElementaryExtension E L1 := hE0.trans hEL1
  have : CharZero L1 := charZero_of_injective_algebraMap (algebraMap E L1).injective
  obtain ⟨L, _, _, _, hDAL, hEL, sq₂, hsq₂2, hsq₂', -⟩ := exists_sqrt_ext (((d₂ : ℚ) : L1))
    (deriv_ratCast_L _) (by exact_mod_cast hd₂)
  letI : Algebra E L := ((algebraMap L1 L).comp (algebraMap E L1)).toAlgebra
  haveI : IsScalarTower E L1 L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra E L :=
    ⟨fun a ↦ by
      change (algebraMap L1 L (algebraMap E L1 a))′ = algebraMap L1 L (algebraMap E L1 a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hE : IsElementaryExtension E L := hE1.trans hEL
  set g0 := algebraMap L1 L (algebraMap L0 L1 g00)
  have hg : g0′ = algebraMap E L ((aeval x B + ∑ i ∈ s₁,
      (((z₁ i : ℚ) / D * γ₁ i * d₁ : ℚ) : E) / (x - ((α₁ i : ℚ) : E)) + ∑ i ∈ s₂,
      (((z₂ i : ℚ) / D * γ₂ i * d₂ : ℚ) : E) / (x - ((α₂ i : ℚ) : E))) / y) := by
    rw [deriv_algebraMap, deriv_algebraMap, hg0]; rfl
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
  have hsq₁L : (algebraMap L1 L sq₁)′ = 0 := by rw [deriv_algebraMap, hsq₁', map_zero]
  set sC₁ : Cc := ⟨algebraMap L1 L sq₁, hsq₁L⟩ with hsC₁def
  set sC₂ : Cc := ⟨sq₂, hsq₂'⟩ with hsC₂def
  have hsC₁ : sC₁ ^ 2 = (d₁ : Cc) := by
    apply Subtype.ext
    push_cast [sC₁]
    rw [← map_pow, hsq₁2, map_ratCast, map_ratCast]; push_cast; rfl
  have hsC₂ : sC₂ ^ 2 = (d₂ : Cc) := by
    apply Subtype.ext
    push_cast [sC₂]
    rw [hsq₂2, map_ratCast]; push_cast; rfl
  have hsC0 : ∀ (sC : Cc) (d : ℤ), sC ^ 2 = d → d ≠ 0 → sC ≠ 0 := by
    intro sC d h hd0 h0
    apply hd0; exact_mod_cast (by rw [← h, h0]; ring : (d : Cc) = 0)
  have hsC₁0 := hsC0 sC₁ d₁ hsC₁ hd₁
  have hsC₂0 := hsC0 sC₂ d₂ hsC₂ hd₂
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂
  -- the class-`d₂` points satisfy `d₂ γ² = p(α)`
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
  set βP : ι₁ ⊕ ι₂ → Cc := fun i ↦ Sum.elim (fun k ↦ ((γ₁ k : ℚ) : Cc) * sC₁)
    (fun k ↦ ((γ₂ k : ℚ) : Cc) * sC₂) i
  set rP : ι₁ ⊕ ι₂ → Cc := fun i ↦ Sum.elim (fun k ↦ (((z₁ k : ℚ) / D : ℚ) : Cc) * sC₁)
    (fun k ↦ (((z₂ k : ℚ) / D : ℚ) : Cc) * sC₂) i
  have hcurve : ∀ i, βP i ^ 2 = αP i ^ 3 + a * αP i ^ 2 + b * αP i + c := by
    rintro (k | k)
    · simp only [αP, βP, Sum.elim_inl]
      have := congrArg (fun q : ℚ ↦ (q : Cc)) (hQ₁ k)
      push_cast at this
      rw [mul_pow, hsC₁, ← this]; ring
    · simp only [αP, βP, Sum.elim_inr]
      have := congrArg (fun q : ℚ ↦ (q : Cc)) (hQ₂ k)
      push_cast at this
      rw [mul_pow, hsC₂, ← this]; ring
  have hβP : ∀ i ∈ sP, βP i ≠ 0 := by
    rintro (k | k) hk
    · simp only [sP, Finset.inl_mem_disjSum] at hk
      simp only [βP, Sum.elim_inl]; exact mul_ne_zero (by exact_mod_cast hγ₁ k hk) hsC₁0
    · simp only [sP, Finset.inr_mem_disjSum] at hk
      simp only [βP, Sum.elim_inr]; exact mul_ne_zero (by exact_mod_cast hγ₂ k hk) hsC₂0
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
      apply hns (γ₂ k' * d₂ / γ₁ k)
      have h0 := hγ₁ k hk1
      rw [div_pow, eq_div_iff (pow_ne_zero 2 h0)]
      push_cast
      linear_combination (d₂ : ℚ) * e
    · exfalso
      simp only [αP, Sum.elim_inl, Sum.elim_inr] at he
      have hα : α₂ k = α₁ k' := by exact_mod_cast he
      have hk1 : k' ∈ s₁ := by simpa [sP] using hk'
      have e := (hQ₁ k').trans (hα ▸ (hQ₂ k)).symm
      apply hns (γ₂ k * d₂ / γ₁ k')
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
    have hrb₁ : ∀ k, (((z₁ k : ℚ) / D : ℚ) : Cc) * sC₁ * (((γ₁ k : ℚ) : Cc) * sC₁) =
        (((z₁ k : ℚ) / D * γ₁ k * d₁ : ℚ) : Cc) := by
      intro k
      rw [show (((z₁ k : ℚ) / D : ℚ) : Cc) * sC₁ * (((γ₁ k : ℚ) : Cc) * sC₁) =
        (((z₁ k : ℚ) / D : ℚ) : Cc) * ((γ₁ k : ℚ) : Cc) * sC₁ ^ 2 by ring, hsC₁]
      push_cast; ring
    have hrb₂ : ∀ k, (((z₂ k : ℚ) / D : ℚ) : Cc) * sC₂ * (((γ₂ k : ℚ) : Cc) * sC₂) =
        (((z₂ k : ℚ) / D * γ₂ k * d₂ : ℚ) : Cc) := by
      intro k
      rw [show (((z₂ k : ℚ) / D : ℚ) : Cc) * sC₂ * (((γ₂ k : ℚ) : Cc) * sC₂) =
        (((z₂ k : ℚ) / D : ℚ) : Cc) * ((γ₂ k : ℚ) : Cc) * sC₂ ^ 2 by ring, hsC₂]
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
  obtain ⟨l, hl₁, hl₂⟩ := exists_sep_functional sC₁ sC₂ d₁ d₂ hsC₁ hsC₂ hd₂ hns
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
    rw [show (((z₁ k : ℚ) / D : ℚ) : Cc) * sC₁ = ((z₁ k : ℚ) / D) • sC₁ by rw [Rat.smul_def],
      map_smul, hl₁, smul_zero]
  have hlr₂ : ∀ k, l (rP (Sum.inr k)) = (z₂ k : ℚ) / D := fun k ↦ by
    simp only [rP, Sum.elim_inr]
    rw [show (((z₂ k : ℚ) / D : ℚ) : Cc) * sC₂ = ((z₂ k : ℚ) / D) • sC₂ by rw [Rat.smul_def],
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
  obtain ⟨Td, hTd_inj, hTd⟩ := EllNL.twist_transport a b c d₂ hd₂ sC₂ hsC₂
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

end Mixed

end Differential
