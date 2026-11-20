import RischTragerBronstein.Algebraic.SupLogConcrete
import RischTragerBronstein.Liouville.Transcendence

/-!
# Lifting an elementary integral to a superelliptic Liouville form

`super_lift`: if `g ∈ E = Kc(x, y)` (`yⁿ = p(x)`) has an elementary integral, then in some
differential field `L ⊇ E` with constants `Cc ⊇ Kc`, `g = v′ + ∑ dᵢ uᵢ′/uᵢ` with `v, uᵢ` in the
superelliptic function field `Cc(x, y)` (Liouville's theorem, strong form). Stated in
continuation-passing style.
-/

open Polynomial IntermediateField

namespace Differential

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The Liouville lift** on a superelliptic curve. -/
theorem super_lift {P : Prop} (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (n : ℕ)
    (hn : 0 < n) (pK : Kc[X]) (hsqK : Squarefree pK) (hpK : 0 < pK.natDegree)
    (hy : y ^ n = aeval x pK) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (g : E)
    (hel : HasElementaryIntegral g)
    (k : ∀ (Cc L : Type u) [Field Cc] [CharZero Cc] [Field L] [CharZero L] [Algebra Cc L]
      [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] (φ : Kc →+* Cc)
      (jE : E →+* L) (SL : SuperData Cc L),
      (∀ c : Cc, c′ = 0) → SL.x′ = 1 → (∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L)) →
      SL.x = jE x → SL.y = jE y → SL.n = n → SL.p = pK.map φ →
      (∀ z : E, (jE z)′ = jE z′) → (∀ c : Kc, jE (algebraMap Kc E c) = algebraMap Cc L (φ c)) →
      (∀ z : E, jE z ∈ Cc⟮SL.x⟯⟮SL.y⟯) →
      (∀ (v : L), v ∈ Cc⟮SL.x⟯⟮SL.y⟯ → ∀ (ιI : Type) (sI : Finset ιI) (d w : ιI → L),
        (∀ i ∈ sI, (d i)′ = 0) → (∀ i ∈ sI, w i ≠ 0 ∧ w i ∈ Cc⟮SL.x⟯⟮SL.y⟯) →
        jE g = v′ + ∑ i ∈ sI, d i * logDeriv (w i) → P)) : P := by
  obtain ⟨L, _, _, _, _, hE, G, hG⟩ := hel
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
  refine k Cc L φ jE SL hCc hxL hconst rfl rfl rfl rfl hj (fun c ↦ rfl) hEs v (hcf v hv) ιL sL cL u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩) ?_
  rw [heq, add_comm]

end Differential
