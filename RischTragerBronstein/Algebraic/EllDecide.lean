import RischTragerBronstein.Algebraic.EllShape
import RischTragerBronstein.Algebraic.HypDecide
import RischTragerBronstein.Elliptic.Transport
import RischTragerBronstein.Elliptic.Dedekind

/-!
# Elliptic integrals with logarithmic part: non-elementarity from infinite order

`y² = p(x) = x³ + ax² + bx + c` (`a, b, c ∈ ℤ`, `p` squarefree). For rational points
`Pᵢ = (αᵢ, βᵢ)` (`βᵢ ≠ 0`), integers `zᵢ` and `D ≥ 1`, the integrand

  `f = (B(x) + ∑ᵢ (zᵢ / D) βᵢ / (x − αᵢ)) / y`

has residues `±zᵢ/D` at `(αᵢ, ±βᵢ)`. `ell_torsion_of_elementary`: if `∫ f dx` is elementary, then
`∑ zᵢ Pᵢ` has finite order in `E(ℚ)`. Proof: Liouville's theorem, reduction to `ℚ`-independent
constants and the residue data (`ell_glue`); one logarithm `u = a + by` with a non-zero residue
contribution has, by Abel's theorem (`EllAbel.abel_two_torsion`, the coordinate ring being
Dedekind), `2 ∑ nᵢ Pᵢ = 0`, and independence forces `nᵢ ∝ zᵢ`. With the Nagell–Lutz torsion test
(`EllNL.torsionTest`) this proves integrals non-elementary.
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

section EllDecide

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 6400000 in
/-- **An elementary elliptic integral forces the residue divisor to be torsion.** -/
theorem ell_torsion_of_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (B : ℚ[X]) {ι : Type*} (s : Finset ι) (α β : ι → ℚ)
    (hP : ∀ i, (EllNL.W a b c).toAffine.Nonsingular (α i) (β i)) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hinj : Set.InjOn α s) (z : ι → ℤ) (D : ℕ) (hD : D ≠ 0)
    (h : HasElementaryIntegral ((aeval x B + ∑ i ∈ s,
      (((z i : ℚ) / D * β i : ℚ) : E) / (x - ((α i : ℚ) : E))) / y)) :
    IsOfFinAddOrder (∑ i ∈ s, z i • (Point.some _ _ (hP i) : (EllNL.W a b c).toAffine.Point)) := by
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
  -- the data of `ell_glue`
  set αP : ι → Cc := fun i ↦ ((α i : ℚ) : Cc) with hαP
  set βP : ι → Cc := fun i ↦ ((β i : ℚ) : Cc) with hβPd
  set rP : ι → Cc := fun i ↦ (((z i : ℚ) / D : ℚ) : Cc) with hrP
  have hinjP : Set.InjOn αP s := fun i hi i' hi' h ↦
    hinj hi hi' (Rat.cast_injective (by simpa only [αP] using h))
  have hβP : ∀ i ∈ s, βP i ≠ 0 := fun i hi ↦ by
    simp only [βP]; exact_mod_cast hβ i hi
  have hcurve : ∀ i, βP i ^ 2 = αP i ^ 3 + a * αP i ^ 2 + b * αP i + c := by
    intro i
    have he := (EllNL.equation_W a b c).mp (hP i).1
    unfold EllNL.OnCurve at he
    simp only [αP, βP]
    have := congrArg (fun q : ℚ ↦ (q : Cc)) he
    push_cast at this
    exact this
  have hpαP' : ∀ i, pC.eval (αP i) = βP i ^ 2 := by
    intro i
    rw [hcurve i, hpC, hpdef, eval_map]
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eq_ratCast, αP]
    push_cast; ring
  have hpαP : ∀ i ∈ s, pC.eval (αP i) = βP i ^ 2 := fun i _ ↦ hpαP' i
  have heqL : (aeval (j x) (B.map (algebraMap ℚ Cc)) + ∑ i ∈ s, algebraMap Cc L (rP i * βP i) /
      (j x - algebraMap Cc L (αP i))) / j y = v′ + ∑ i ∈ sL, cL i * logDeriv (u i) := by
    rw [haev, add_comm (v′), ← heq]
    simp only [map_div₀, map_add, map_sum, map_sub, map_ratCast, map_mul, rP, βP, αP, Rat.cast_mul]
  obtain ⟨t, κ, a', b', hκind, hab, hN0, hshape, hres⟩ := ell_glue (j x) (j y) hCc hxL htr hconst
    pC hpsq hoddC hyL (B.map (algebraMap ℚ Cc)) s αP βP rP hinjP hβP hpαP sL cL u v
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩)
    (hcf v hv) heqL
  -- the trivial case
  by_cases hz : ∀ i ∈ s, z i = 0
  · rw [Finset.sum_eq_zero fun i hi ↦ by rw [hz i hi]; exact zero_zsmul _]
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨1, one_pos, by simp⟩
  push_neg at hz
  obtain ⟨i0, hi0, hzi0⟩ := hz
  choose! m ε hdat hrel using hres
  have hrP0 : rP i0 ≠ 0 := by
    simp only [rP]
    have : ((z i0 : ℚ) / D) ≠ 0 := div_ne_zero (by exact_mod_cast hzi0) (by exact_mod_cast hD)
    exact_mod_cast this
  -- a logarithm with a non-zero contribution at `αᵢ₀`
  obtain ⟨j0, hj0, hmj0⟩ : ∃ j0 ∈ t, m i0 j0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have := hrel i0 hi0
    rw [Finset.sum_eq_zero fun j hj ↦ by rw [hall j hj]; simp] at this
    exact hrP0 (by linear_combination this / 2)
  -- independence: `(z i₀) nᵢ = (zᵢ) nᵢ₀` for the logarithm `j0`
  have hprop : ∀ i ∈ s, (z i0 : ℤ) * ((m i j0 : ℤ) * ε i j0) = z i * ((m i0 j0 : ℤ) * ε i0 j0) := by
    intro i hi
    have hg := hκind (fun j ↦ ((z i0 : ℚ) / D) * ((m i j : ℚ) * ε i j) -
      ((z i : ℚ) / D) * ((m i0 j : ℚ) * ε i0 j)) (by
        have h1 := hrel i hi
        have h2 := hrel i0 hi0
        have e : ∑ j ∈ t, (((((z i0 : ℚ) / D) * ((m i j : ℚ) * ε i j) -
            ((z i : ℚ) / D) * ((m i0 j : ℚ) * ε i0 j)) : ℚ) : Cc) * κ j =
            rP i0 * ∑ j ∈ t, κ j * ((m i j : Cc) * ε i j) -
              rP i * ∑ j ∈ t, κ j * ((m i0 j : Cc) * ε i0 j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [rP]; push_cast; ring
        rw [e, ← neg_neg (∑ j ∈ t, κ j * ((m i j : Cc) * ε i j)), ← h1,
          ← neg_neg (∑ j ∈ t, κ j * ((m i0 j : Cc) * ε i0 j)), ← h2]
        ring) j0 hj0
    simp only [sub_eq_zero] at hg
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    field_simp at hg
    have h2 : ((z i0 * ((m i j0 : ℤ) * ε i j0) : ℤ) : ℚ) =
        ((z i * ((m i0 j0 : ℤ) * ε i0 j0) : ℤ) : ℚ) := by
      push_cast; linear_combination hg
    exact_mod_cast h2
  have hn0 : (m i0 j0 : ℤ) * ε i0 j0 ≠ 0 := by
    rcases (hdat i0 hi0 j0 hj0).1 with h1 | h1 <;> rw [h1] <;> simp [hmj0]
  -- Abel for the logarithm `j0`
  obtain ⟨lam, gq, hlam, hgq, hfac⟩ := norm_shape (hN pC (a' j0) (b' j0)) pC (hN0 j0 hj0) s αP
    hinjP (fun i ↦ m i j0) (fun i hi ↦ ⟨(hdat i hi j0 hj0).2.1, (hdat i hi j0 hj0).2.2.1⟩)
    (hshape j0 hj0)
  have hpf : pC = EllAbel.f (a : Cc) (b : Cc) (c : Cc) := by
    rw [hpC, hpdef, EllAbel.f]; simp
  haveI : IsDedekindDomain (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.CoordinateRing :=
    isDedekindDomain_coordinateRing (a : Cc) (b : Cc) (c : Cc) (by
      have h' := hpsq; rw [hpf] at h'; exact h')
  set β' : ι → Cc := fun i ↦ if i ∈ s then -(ε i j0 : Cc) * βP i else βP i with hβ'
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
  -- translate to the points `Qᵢ = (αᵢ, βᵢ)`
  have hQns : ∀ i, (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Nonsingular (αP i) (βP i) :=
    fun i ↦ hns i _ rfl
  set Q : ι → (EllAbel.W (a : Cc) (b : Cc) (c : Cc)).toAffine.Point :=
    fun i ↦ Point.some _ _ (hQns i) with hQ
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
  -- `S = ∑ zᵢ Qᵢ` has finite order
  have hQtoK : ∀ i, EllNL.toK a b c Cc (Point.some _ _ (hP i)) = Q i := fun i ↦
    EllNL.toK_some a b c Cc (hP i) (hQns i)
  refine EllNL.isOfFinAddOrder_of_toK a b c Cc ?_
  rw [map_sum]
  simp only [map_zsmul, hQtoK]
  refine isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨2 * ((m i0 j0 : ℤ) * ε i0 j0),
    mul_ne_zero two_ne_zero hn0, ?_⟩
  have e : ((m i0 j0 : ℤ) * ε i0 j0) • ∑ i ∈ s, z i • Q i = z i0 • T := by
    rw [hT, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [smul_smul, smul_smul, mul_comm _ (z i), ← hprop i hi]
  rw [mul_smul, e, smul_comm, hT2, smul_zero]

end EllDecide

end Differential
