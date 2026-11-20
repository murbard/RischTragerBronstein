import RischTragerBronstein.Algebraic.SuperExact
import RischTragerBronstein.Liouville.Transcendence

/-!
# Deciding `∫ B(x) yʲ / p(x) dx` on a superelliptic curve `yⁿ = p(x)`

For `p` squarefree with `gcd(n, deg p) = 1` and `0 < j < n`, the integrand `B(x) yʲ / p(x)`
(i.e. `B(x) p(x)^{(j − n)/n}`) has no residues at the finite points. `super_decides`:

  `∫ B yʲ / p dx` is elementary  ⟺  the remainder of `supRed (j/n) p B` vanishes,

and then the integral is algebraic, `C(x) yʲ`. The proof: Liouville's theorem, the
residue-free case (`super_second_kind`) and `super_exact_zero`.
-/

open Polynomial IntermediateField CPoly

namespace Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma res_eq_zero_of_order {K : Type*} [Field K] (F : LaurentSeries K) (h : 0 ≤ F.order) :
    LaurentSeries.res F = 0 := by
  by_cases hF : F = 0
  · rw [hF]; rfl
  exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

lemma supRed_hr {F : Type*} [Field F] [CharZero F] (n d j : ℕ) (hn : 0 < n) (hd : 0 < d)
    (hj : 0 < j) (m : ℕ) : (m : F) + d * ((j : F) / n) ≠ 0 := by
  have hn0 : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (m : F) + d * ((j : F) / n) = ((m * n + d * j : ℕ) : F) / n by push_cast; field_simp]
  refine div_ne_zero ?_ hn0
  have : 0 < d * j := Nat.mul_pos hd hj
  exact_mod_cast (show m * n + d * j ≠ 0 by omega)

/-- The algebraic decomposition `B yʲ / p = (C yʲ)′ + R yʲ / p` on a superelliptic curve. -/
lemma super_decomp {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    [Differential C] [Differential L] [DifferentialAlgebra C L] (S : SuperData C L)
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (j : ℕ) (B Cr R : C[X])
    (hB : B = S.p * derivative Cr + Polynomial.C ((j : C) / S.n) * (Cr * derivative S.p) + R) :
    aeval S.x B * S.y ^ j / aeval S.x S.p =
      (aeval S.x Cr * S.y ^ j)′ + aeval S.x R * S.y ^ j / aeval S.x S.p := by
  have h1 := S.deriv_poly_y_mul hC hx Cr j
  have hp0 := S.p_ne_zero
  rw [eq_div_of_mul_eq hp0 h1, hB, map_add]
  ring

open Classical in
/-- **Deciding `∫ B(x) yʲ / p(x) dx`** on `yⁿ = p(x)` (`p` squarefree, `gcd(n, deg p) = 1`,
`0 < j < n`). -/
theorem super_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ι : F →+* Kc) (n : ℕ) (p : CPoly F)
    (hp : Squarefree (toPoly p)) (hpd : 0 < (toPoly p).natDegree)
    (hcop : Nat.Coprime n (toPoly p).natDegree)
    (hy : y ^ n = aeval x ((toPoly p).map ι)) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯)
    (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (B : CPoly F) :
    HasElementaryIntegral (aeval x ((toPoly B).map ι) * y ^ j / aeval x ((toPoly p).map ι)) ↔
      isZero (supRed ((j : F) / n) p B).2 = true := by
  have hn : 0 < n := by omega
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  set pK := (toPoly p).map ι with hpKdef
  have hsqK : Squarefree pK := ((PerfectField.separable_iff_squarefree.mpr hp).map).squarefree
  have hpK : 0 < pK.natDegree := by rw [natDegree_map_eq_of_injective ι.injective]; exact hpd
  let SE : SuperData Kc E := ⟨x, y, n, pK, htrK, hn, hsqK, hpK, hy, Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨hsp, hRdeg⟩ := supRed_spec ((j : F) / n) p B hpd (supRed_hr n _ j hn hpd hj0)
  set Cr := toPoly (supRed ((j : F) / n) p B).1
  set R := toPoly (supRed ((j : F) / n) p B).2
  have hιr : ι ((j : F) / n) = (j : Kc) / n := by simp
  have hBK : (toPoly B).map ι = pK * derivative (Cr.map ι) +
      Polynomial.C ((j : Kc) / n) * (Cr.map ι * derivative pK) + R.map ι := by
    rw [hsp]
    simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map, Polynomial.map_C, hιr, pK]
    ring
  have hdec := super_decomp SE hC hx j _ (Cr.map ι) (R.map ι) hBK
  rw [isZero_iff]
  constructor
  · intro h
    rw [show aeval x ((toPoly B).map ι) * y ^ j / aeval x pK = _ from hdec] at h
    obtain ⟨L, _, _, _, _, hE, G, hG⟩ := h
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
    obtain ⟨ιL, sL, cL, u, v, hdata, hv, heq⟩ := liouville_strong hE _ G hG
    let Cc := constants L
    let _ : Differential Cc := ⟨0⟩
    have hDAc : DifferentialAlgebra Cc L := ⟨fun c ↦ c.2⟩
    have hcharC : CharZero Cc := ⟨fun a b h ↦ by
      have := congrArg (fun z : Cc ↦ (z : L)) h
      simpa using this⟩
    set jE := algebraMap E L with hjdef
    have hj : ∀ z : E, (jE z)′ = jE z′ := fun z ↦ deriv_algebraMap z
    have hCc : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
    have hxL : (jE x)′ = 1 := by rw [hj, hx, map_one]
    have htr : Transcendental Cc (jE x) :=
      transcendental_of_deriv_ne_zero hCc (by rw [hxL]; exact one_ne_zero)
    have hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L) := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩
    have hconstE : ∀ k : Kc, (jE (algebraMap Kc E k))′ = 0 := fun k ↦ by
      rw [hj, deriv_algebraMap, hC, map_zero, map_zero]
    let φ : Kc →+* Cc :=
      { toFun := fun k ↦ ⟨jE (algebraMap Kc E k), hconstE k⟩
        map_one' := by ext; simp
        map_mul' := fun u w ↦ by ext; simp
        map_zero' := by ext; simp
        map_add' := fun u w ↦ by ext; simp }
    have hφL : ∀ k : Kc, algebraMap Cc L (φ k) = jE (algebraMap Kc E k) := fun _ ↦ rfl
    have haevK : ∀ P : Kc[X], aeval (jE x) (P.map φ) = jE (aeval x P) := by
      intro P
      rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]; rfl
    set pC := pK.map φ with hpC
    have hyL : jE y ^ n = aeval (jE x) pC := by rw [hpC, haevK, ← hy, map_pow]
    have hsqC : Squarefree pC := ((PerfectField.separable_iff_squarefree.mpr hsqK).map).squarefree
    have hpC0 : 0 < pC.natDegree := by rw [natDegree_map_eq_of_injective φ.injective]; exact hpK
    let SL : SuperData Cc L := ⟨jE x, jE y, n, pC, htr, hn, hsqC, hpC0, hyL, Nat.cast_ne_zero.mpr hn.ne'⟩
    have hcopL : Nat.Coprime SL.n SL.p.natDegree := by
      show Nat.Coprime n pC.natDegree
      rw [natDegree_map_eq_of_injective φ.injective, natDegree_map_eq_of_injective ι.injective]
      exact hcop
    -- `E` lands in `Cc⟮x⟯⟮y⟯`
    have hKx : ∀ w : E, w ∈ Kc⟮x⟯ → jE w ∈ Cc⟮jE x⟯ := by
      let T : IntermediateField Kc E :=
        { carrier := {w | jE w ∈ Cc⟮jE x⟯}
          mul_mem' := fun {a b} ha hb ↦ by
            simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
          one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
          add_mem' := fun {a b} ha hb ↦ by
            simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
          zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
          algebraMap_mem' := fun c ↦ by
            simp only [Set.mem_setOf_eq]
            rw [← hφL]
            exact IntermediateField.algebraMap_mem _ _
          inv_mem' := fun a ha ↦ by
            simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
      have hle : Kc⟮x⟯ ≤ T := by
        rw [adjoin_simple_le_iff]
        exact mem_adjoin_simple_self Cc (jE x)
      exact fun w hw ↦ hle hw
    have hEs : ∀ e : E, jE e ∈ Cc⟮jE x⟯⟮jE y⟯ := by
      let T : IntermediateField Kc⟮x⟯ E :=
        { carrier := {w | jE w ∈ Cc⟮jE x⟯⟮jE y⟯}
          mul_mem' := fun {a b} ha hb ↦ by
            simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
          one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
          add_mem' := fun {a b} ha hb ↦ by
            simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
          zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
          algebraMap_mem' := fun c ↦ by
            simp only [Set.mem_setOf_eq]
            exact IntermediateField.algebraMap_mem (Cc⟮jE x⟯⟮jE y⟯)
              (⟨jE c, hKx c c.2⟩ : Cc⟮jE x⟯)
          inv_mem' := fun a ha ↦ by
            simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
      have hle : Kc⟮x⟯⟮y⟯ ≤ T := by
        rw [adjoin_simple_le_iff]
        exact mem_adjoin_simple_self _ (jE y)
      exact fun e ↦ hle (hgen e)
    have hcf : ∀ w ∈ Differential.constField E L, w ∈ Cc⟮jE x⟯⟮jE y⟯ := by
      let N : IntermediateField E L :=
        { (Cc⟮jE x⟯⟮jE y⟯).toSubfield with algebraMap_mem' := hEs }
      have : Differential.constField E L ≤ N := adjoin_le_iff.mpr fun w hw ↦ by
        obtain ⟨c', rfl⟩ := hconst w hw
        exact SL.const_mem c'
      exact fun w hw ↦ this hw
    -- the equation in `L`
    set RC : Cc[X] := (R.map ι).map φ with hRCdef
    set f0 : L := aeval (jE x) RC * jE y ^ j / aeval (jE x) pC
    set gL : L := jE (aeval x (Cr.map ι) * y ^ j)
    have hf0E : f0 = jE (aeval x (R.map ι) * y ^ j / aeval x pK) := by
      simp only [f0, map_div₀, map_mul, map_pow, hRCdef, haevK, hpC]
    have heq' : f0 = (v - gL)′ + ∑ i ∈ sL, cL i * logDeriv (u i) := by
      have h2 : jE ((aeval x (Cr.map ι) * y ^ j)′ + aeval x (R.map ι) * y ^ j / aeval x pK) =
          gL′ + f0 := by
        rw [map_add, hj, hf0E]
      rw [h2] at heq
      rw [map_sub]
      linear_combination heq
    have hf0 : f0 ∈ Cc⟮jE x⟯⟮jE y⟯ := by rw [hf0E]; exact hEs _
    have hv' : v - gL ∈ Cc⟮jE x⟯⟮jE y⟯ := sub_mem (hcf v hv) (hEs _)
    have hu : ∀ i ∈ sL, u i ≠ 0 ∧ u i ∈ Cc⟮jE x⟯⟮jE y⟯ := fun i hi ↦
      ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩
    have hc : ∀ i ∈ sL, (cL i)′ = 0 := fun i hi ↦ (hdata i hi).1
    -- residues of `f0` vanish
    have hFeq : RC ≠ 0 → (⟨f0, hf0⟩ : Cc⟮jE x⟯⟮jE y⟯) =
        SL.polyX RC * AdjoinSimple.gen Cc⟮jE x⟯ (jE y) ^ j * (SL.polyX pC)⁻¹ := fun _ ↦
      Subtype.ext (by
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, IntermediateField.coe_inv,
          AdjoinSimple.coe_gen, f0, div_eq_mul_inv]
        rw [SL.polyX_coe, SL.polyX_coe])
    have hf00 : RC = 0 → (⟨f0, hf0⟩ : Cc⟮jE x⟯⟮jE y⟯) = 0 := fun h0 ↦
      Subtype.ext (by simp [f0, h0])
    have hnb : ∀ (α β : AlgebraicClosure Cc) (hβ : β ≠ 0)
        (hβp : β ^ SL.n = (SL.p.map (algebraMap Cc (AlgebraicClosure Cc))).eval α),
        LaurentSeries.res (SL.embXY α β hβ hβp ⟨f0, hf0⟩) = 0 := by
      intro α β hβ hβp
      by_cases hR0 : RC = 0
      · rw [hf00 hR0, map_zero]; rfl
      refine res_eq_zero_of_order _ ?_
      have h1 := SL.ordAt_Ryp (K := AlgebraicClosure Cc) j RC hR0 α β hβp
      rw [if_neg hβ, ← hFeq hR0, SL.ordAt_nb _ α β hβ hβp] at h1
      exact h1
    have hbr : ∀ (e γ : AlgebraicClosure Cc)
        (he : (SL.p.map (algebraMap Cc (AlgebraicClosure Cc))).eval e = 0) (hγ : γ ≠ 0)
        (hγp : γ ^ SL.n = (Polynomial.derivative (SL.p.map
          (algebraMap Cc (AlgebraicClosure Cc)))).eval e),
        LaurentSeries.res (SL.embB e γ he hγ hγp ⟨f0, hf0⟩ *
          HahnSeries.single ((SL.n : ℤ) - 1) (SL.n : AlgebraicClosure Cc)) = 0 := by
      intro e γ he hγ hγp
      by_cases hR0 : RC = 0
      · rw [hf00 hR0, map_zero, zero_mul]; rfl
      by_cases hz : SL.embB e γ he hγ hγp ⟨f0, hf0⟩ = 0
      · rw [hz, zero_mul]; rfl
      refine res_eq_zero_of_order _ ?_
      have h1 := SL.ordAt_Ryp (K := AlgebraicClosure Cc) j RC hR0 e 0
        (by rw [he, zero_pow SL.hn.ne'])
      rw [if_pos rfl, ← hFeq hR0, SL.ordAt_br _ e γ he hγ hγp] at h1
      have hs : HahnSeries.single ((SL.n : ℤ) - 1) (SL.n : AlgebraicClosure Cc) ≠ 0 :=
        HahnSeries.single_ne_zero (by exact_mod_cast SL.hn.ne')
      rw [HahnSeries.order_mul hz hs, HahnSeries.order_single (by exact_mod_cast SL.hn.ne')]
      have : (SL.n : ℤ) = n := rfl
      omega
    have hexact := SL.super_second_kind (AlgebraicClosure Cc) hCc hxL hconst hcopL f0 (v - gL) hf0
      hv' sL cL u hc hu heq' hnb hbr
    have hRCd : RC = 0 ∨ RC.natDegree + 2 ≤ SL.p.natDegree := by
      rcases hRdeg with h0 | h0
      · left; simp [hRCdef, show R = 0 from h0]
      · right
        show RC.natDegree + 2 ≤ pC.natDegree
        rw [hRCdef, hpC, natDegree_map_eq_of_injective φ.injective,
          natDegree_map_eq_of_injective φ.injective, natDegree_map_eq_of_injective ι.injective,
          natDegree_map_eq_of_injective ι.injective]
        exact h0
    have hz := SL.super_exact_zero (AlgebraicClosure Cc) hCc hxL j hj0 hjn RC hRCd (v - gL) hv'
      hexact
    rw [hRCdef] at hz
    exact (Polynomial.map_eq_zero_iff ι.injective).mp
      ((Polynomial.map_eq_zero_iff φ.injective).mp hz)
  · intro h0
    have h0' : R = 0 := h0
    rw [show aeval x ((toPoly B).map ι) * y ^ j / aeval x pK = _ from hdec, h0',
      Polynomial.map_zero, map_zero, zero_mul, zero_div, add_zero]
    exact hasElementaryIntegral_of_deriv _

end Differential
