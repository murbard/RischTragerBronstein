import RischTragerBronstein.Mixed.KPLocal

/-!
# Liouville forms on `yⁿ = p(x)` over a differential base: the logarithms lie in the base

`S : SuperData C L`, the base `C` a differential field, `x′ = η ∈ C` with `η` not a derivative in
the algebraic closure `K` of `C` (`x` is a primitive, e.g. `x = log u`), `gcd(n, deg p) = 1`.

**`logs_in_base`**: if `f = v′ + ∑ dⱼ wⱼ′/wⱼ` in `C(x, y)` with constant, `ℚ`-linearly
independent `dⱼ`, and `f` has no pole at any finite place, then every `wⱼ` lies in `C`.

At every finite place the expansion is differential for `dS s` (`embG_dS`), with `s = η − α′` at an
ordinary point and `s = (η − e′)/n · X^{1−n}` at a branch point, both non-zero because `η` has no
antiderivative; the residue of the Liouville form vanishes (`residue_eq_zero`), so
`∑ dⱼ ord wⱼ = 0`, hence every order is `0` by independence; an element without zeros and poles
at the finite points is a constant (`const_of_ordAt_zero`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace Differential

lemma shiftHom_eq_subst {C K : Type*} [Field C] [Field K] [Algebra C K] (α : K) :
    shiftHom (C := C) α = substHom (shiftX α) := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [shiftHom_C, substHom_apply, Polynomial.map_C, aeval_C, HahnSeries.algebraMap_apply']
    exact (ofPowerSeries_C _).symm
  · rw [shiftHom_X, substHom_apply, Polynomial.map_X, aeval_X]

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]
variable (S : SuperData C L) (η : C) (hx : S.x′ = algebraMap C L η)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

section Generic

variable (s Xh : LaurentSeries K) (hXh : dS s Xh = HahnSeries.C (algebraMap C K η))
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hx hK hXh hgX

/-- **The residue of a Liouville form at a place** where the integrand has no coefficient below
`ord s`. -/
theorem sumOrd_eq_zero (hs : s ≠ 0) (hσ : s.order ≤ 0) (Y : LaurentSeries K)
    (hY : Y ^ S.n = g S.p) {ι : Type*} (I : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hF : ∀ k < s.order, (S.embG g hg Y hY ⟨f, hf⟩).coeff k = 0) :
    ∑ i ∈ I, algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K) = 0 := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embG g hg Y hY
  have hdc := S.derivClosedXY' η hx
  have hT : (⟨f, hf⟩ : T) = ⟨v′, hdc v hv⟩ + ∑ i ∈ I,
      (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) *
        ((⟨(u i)′, hdc _ (hu i)⟩ : T) / ⟨u i, hu i⟩) :=
    Subtype.ext (by simp [heq])
  have hφ0 : ∀ i, φ ⟨u i, hu i⟩ ≠ 0 := fun i ↦
    (map_ne_zero_iff φ φ.injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
  have hcst : ∀ i, φ ⟨algebraMap C L (c i), S.const_mem (c i)⟩ =
      HahnSeries.C (algebraMap C K (c i)) := fun i ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    have e : (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) =
        algebraMap C⟮S.x⟯ T (algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i))) :=
      Subtype.ext (by
        show algebraMap C L (c i) = ((algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i)) : C⟮S.x⟯) : L)
        rw [algebraMap_adjoinSimple, aeval_C])
    rw [e, S.embG_algebraMap, S.embXG_algebraMap, hgX, substHom_C]
  refine residue_eq_zero I s (φ ⟨f, hf⟩) (φ ⟨v, hv⟩) (fun i ↦ φ ⟨u i, hu i⟩)
    (fun i ↦ algebraMap C K (c i)) hs hσ (fun i _ ↦ hφ0 i) ?_ hF
  rw [hT, map_add, map_sum, S.embG_dS η hx hK s Xh hXh g hg hgX Y hY v hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_dS η hx hK s Xh hXh g hg hgX Y hY (u i) (hu i), hcst,
    div_eq_mul_inv]

end Generic

/-- The coefficients below `0` of a series of non-negative order vanish. -/
lemma coeff_neg_of_order_nonneg {F : LaurentSeries K} (hF : F = 0 ∨ 0 ≤ F.order) {k : ℤ}
    (hk : k < 0) : F.coeff k = 0 := by
  rcases hF with rfl | hF
  · rfl
  · exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

variable [IsAlgClosed K]

include hx hK in
/-- **The orders of the logarithms vanish at every finite place.** -/
theorem ordAt_logs_zero (hnd : ∀ α : K, α′ ≠ algebraMap C K η) (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (hind : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (hreg : S.IsIntegralS K ⟨f, hf⟩) (α β : K) (hv' : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (j : ℕ) (hj : j < k) : S.ordAt K ⟨w j, (hw j hj).1⟩ α β = 0 := by
  classical
  -- the logarithms indexed by `Fin k`
  set u : Fin k → L := fun i ↦ w i
  have hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯ := fun i ↦ (hw i i.2).1
  have hu0 : ∀ i, u i ≠ 0 := fun i ↦ (hw i i.2).2
  have heq' : f = v′ + ∑ i : Fin k, algebraMap C L (d i) * ((u i)′ / u i) := by
    rw [heq, Fin.sum_univ_eq_sum_range (fun j ↦ algebraMap C L (d j) * ((w j)′ / w j))]
  -- the independence turns `∑ dⱼ ordⱼ = 0` into `ordⱼ = 0`
  have hconcl : ∀ ord : Fin k → ℤ,
      ∑ i : Fin k, algebraMap C K (d i) * ((ord i : ℤ) : K) = 0 → ∀ i, ord i = 0 := by
    intro ord hsum i
    have hC : ∑ jj ∈ Finset.range k, ((if h : jj < k then (ord ⟨jj, h⟩ : ℚ) else 0 : ℚ) : C) *
        d jj = 0 := by
      apply (algebraMap C K).injective
      rw [map_zero, ← hsum, map_sum, ← Fin.sum_univ_eq_sum_range
        (fun jj ↦ algebraMap C K (((if h : jj < k then (ord ⟨jj, h⟩ : ℚ) else 0 : ℚ) : C) * d jj))]
      refine Finset.sum_congr rfl fun ii _ ↦ ?_
      rw [dif_pos ii.2, map_mul, map_ratCast, mul_comm]
      push_cast
      rfl
    have := hind _ hC i i.2
    rw [dif_pos i.2] at this
    exact_mod_cast this
  have hηK : ∀ α : K, algebraMap C K η - α′ ≠ 0 := fun α h ↦ hnd α (sub_eq_zero.mp h).symm
  by_cases hβ : β = 0
  · -- a branch point
    subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv', zero_pow S.hn.ne']
    obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
    set s : LaurentSeries K := HahnSeries.C ((algebraMap C K η - α′) / S.n) *
      single (1 - (S.n : ℤ)) 1 with hs
    have hc0 : (algebraMap C K η - α′) / (S.n : K) ≠ 0 :=
      div_ne_zero (hηK α) (by exact_mod_cast S.hn.ne')
    have hsord : s.order = 1 - S.n := order_branch_s _ hc0 S.n
    have hs' : s = single (1 - (S.n : ℤ)) ((algebraMap C K η - α′) / S.n) := by
      rw [hs, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
    have hs0 : s ≠ 0 := by rw [hs']; exact HahnSeries.single_ne_zero hc0
    have hσ : s.order ≤ 0 := by rw [hsord]; have := S.hn; omega
    have hXh := dS_branch α (algebraMap C K η) S.n S.hn
    have h1 : S.embB α γ he hγ hγp ⟨f, hf⟩ = 0 ∨ 0 ≤ (S.embB α γ he hγ hγp ⟨f, hf⟩).order := by
      by_cases h0 : S.embB α γ he hγ hγp ⟨f, hf⟩ = 0
      · exact Or.inl h0
      · right
        have := hreg α 0 (by rw [he, zero_pow S.hn.ne'])
        rwa [S.ordAt_br ⟨f, hf⟩ α γ he hγ hγp] at this
    have hsum := S.sumOrd_eq_zero η hx hK s _ hXh (branchSub S.n α)
      (branchSub_injective S.n S.hn α) (fun P ↦ by rw [branchSub_eq_subst]) hs0 hσ
      (S.branchYe α γ hγ hγp) (S.branchYe_pow α γ he hγ hγp) Finset.univ (fun i : Fin k ↦ d i) u
      hu hu0 v f hv hf heq' (fun kk hkk ↦ coeff_neg_of_order_nonneg h1 (by omega))
    have := hconcl (fun i ↦ (S.embB α γ he hγ hγp ⟨u i, hu i⟩).order) hsum ⟨j, hj⟩
    rw [S.ordAt_br _ α γ he hγ hγp]
    exact this
  · -- an ordinary point
    set s : LaurentSeries K := HahnSeries.C (algebraMap C K η - α′) with hs
    have hs0 : s ≠ 0 := by rw [hs]; exact HahnSeries.C_ne_zero (hηK α)
    have hσ : s.order ≤ 0 := by rw [hs, HahnSeries.order_C]
    have hXh : dS s (shiftX α) = HahnSeries.C (algebraMap C K η) := dS_shift α _
    have h1 : S.embXY α β hβ hv' ⟨f, hf⟩ = 0 ∨ 0 ≤ (S.embXY α β hβ hv' ⟨f, hf⟩).order := by
      by_cases h0 : S.embXY α β hβ hv' ⟨f, hf⟩ = 0
      · exact Or.inl h0
      · right
        have := hreg α β hv'
        rwa [S.ordAt_nb ⟨f, hf⟩ α β hβ hv'] at this
    have hs00 : s.order = 0 := by rw [hs, HahnSeries.order_C]
    have hsum := S.sumOrd_eq_zero η hx hK s _ hXh (shiftHom α) (shiftHom_injective α)
      (fun P ↦ by rw [shiftHom_eq_subst]) hs0 hσ
      (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hv'))
      (by rw [← map_pow, branchY_pow]; rfl) Finset.univ (fun i : Fin k ↦ d i) u hu hu0 v f hv hf
      heq' (fun kk hkk ↦ coeff_neg_of_order_nonneg h1 (by omega))
    have := hconcl (fun i ↦ (S.embXY α β hβ hv' ⟨u i, hu i⟩).order) hsum ⟨j, hj⟩
    rw [S.ordAt_nb _ α β hβ hv']
    exact this

include hx hK in
/-- **The logarithms lie in the base.** -/
theorem logs_in_base (hnd : ∀ α : K, α′ ≠ algebraMap C K η)
    (hcop : Nat.Coprime S.n S.p.natDegree) (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (hind : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (hreg : S.IsIntegralS K ⟨f, hf⟩) :
    ∀ j < k, ∃ c : C, w j = algebraMap C L c := by
  intro j hj
  have hw0 : (⟨w j, (hw j hj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦ (hw j hj).2 (congrArg Subtype.val h)
  exact S.const_of_ordAt_zero K hcop _ hw0 fun α β hv' ↦
    S.ordAt_logs_zero η hx hK hnd k d w hw hind v f hv hf heq hreg α β hv' j hj

end SuperData

end Differential
