import RischTragerBronstein.Mixed.NKEmbed
import RischTragerBronstein.Mixed.KWMain
import RischTragerBronstein.Mixed.KQLocal

/-!
# Liouville forms on general curves over a differential base: the logarithms at good places

For a general plane curve `S : CurveData C L` over a differential field `C` with `x′ = ω(x)`, and a
good place `x = a` (`a′ ≠ ω(a)`, `a` in the algebraic closure `K` of `C`): along every branch
`x = a + Tᴺ`, `y = Y(T)` where the integrand `f = v′ + ∑ dⱼ wⱼ′/wⱼ` has no pole, the logarithms have
order `0` when the constants `dⱼ` are `ℚ`-linearly independent (`logs_zero_branchW`). This is
`KWMain` (`yⁿ = p(x)`) for arbitrary curves.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

namespace LaurentSeries

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- **`V` has no pole** where the integrand has at most a simple pole (relative to `s`). -/
theorem V_regular {ι : Type*} (I : Finset ι) (s F V : K⸨X⸩) (U : ι → K⸨X⸩) (κ : ι → K)
    (hs : s ≠ 0) (hσ : s.order ≤ 0) (hU : ∀ i ∈ I, U i ≠ 0)
    (heq : F = dS s V + ∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹))
    (hF : ∀ k < s.order - 1, F.coeff k = 0) : V = 0 ∨ 0 ≤ V.order := by
  have hlog : ∀ k, (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k =
      ∑ i ∈ I, κ i * (dS s (U i) * (U i)⁻¹).coeff k := fun k ↦ by
    rw [HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ ↦ coeff_C_mul _ _ _
  have hlogBelow : ∀ k < s.order - 1,
      (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k = 0 := fun k hk ↦ by
    rw [hlog]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).1 k hk, mul_zero]
  by_contra hcon
  push Not at hcon
  obtain ⟨hV0, hm⟩ := hcon
  obtain ⟨-, hlead⟩ := coeff_dS_pole s V hV0 hm.ne hσ
  have hc : F.coeff (V.order - 1 + s.order) = (dS s V + ∑ i ∈ I, HahnSeries.C (κ i) *
      (dS s (U i) * (U i)⁻¹)).coeff (V.order - 1 + s.order) :=
    congrArg (fun G ↦ G.coeff (V.order - 1 + s.order)) heq
  rw [HahnSeries.coeff_add, hlead, hlogBelow _ (by omega), add_zero,
    hF _ (by omega)] at hc
  have h1 : (V.order : K) ≠ 0 := by exact_mod_cast hm.ne
  have h2 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs
  have h3 : V.coeff V.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hV0
  exact mul_ne_zero (mul_ne_zero h1 h2) h3 hc.symm

/-- **The pole bound for `V`**: if `V` has a pole, `F` has a coefficient at `ord V − 1 + ord s`. -/
theorem V_pole_bound {ι : Type*} (I : Finset ι) (s F V : K⸨X⸩) (U : ι → K⸨X⸩) (κ : ι → K)
    (hs : s ≠ 0) (hσ : s.order ≤ 0) (hU : ∀ i ∈ I, U i ≠ 0)
    (heq : F = dS s V + ∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹))
    (hV0 : V ≠ 0) (hm : V.order < 0) : F.coeff (V.order - 1 + s.order) ≠ 0 := by
  have hlog : ∀ k, (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k =
      ∑ i ∈ I, κ i * (dS s (U i) * (U i)⁻¹).coeff k := fun k ↦ by
    rw [HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ ↦ coeff_C_mul _ _ _
  have hlogBelow : ∀ k < s.order - 1,
      (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k = 0 := fun k hk ↦ by
    rw [hlog]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).1 k hk, mul_zero]
  obtain ⟨-, hlead⟩ := coeff_dS_pole s V hV0 hm.ne hσ
  rw [heq, HahnSeries.coeff_add, hlead, hlogBelow _ (by omega), add_zero]
  have h1 : (V.order : K) ≠ 0 := by exact_mod_cast hm.ne
  have h2 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs
  have h3 : V.coeff V.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hV0
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

end LaurentSeries

namespace Curves

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

section Generic

variable (s Xh : LaurentSeries K) (hXh : dS s Xh = substHom Xh ω)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hx hK hXh hgX

/-- **The residue of a Liouville form along a branch** where the integrand has no coefficient
below `ord s`. -/
theorem sumOrd_eq_zeroW' (hs : s ≠ 0) (hσ : s.order ≤ 0) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) {ι : Type*} (I : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hF : ∀ k < s.order, (S.embG g hg Y hY ⟨f, hf⟩).coeff k = 0) :
    ∑ i ∈ I, algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K) = 0 := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embG g hg Y hY
  have hdc := S.derivClosedXYW' ω hx
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
    rw [e, S.embG_algebraMap, S.embXG_algebraMap, hgX, SuperData.substHom_C]
  refine residue_eq_zero I s (φ ⟨f, hf⟩) (φ ⟨v, hv⟩) (fun i ↦ φ ⟨u i, hu i⟩)
    (fun i ↦ algebraMap C K (c i)) hs hσ (fun i _ ↦ hφ0 i) ?_ hF
  rw [hT, map_add, map_sum, S.embG_dSW' ω hx hK s Xh hXh g hg hgX Y hY v hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_dSW' ω hx hK s Xh hXh g hg hgX Y hY (u i) (hu i), hcst,
    div_eq_mul_inv]

/-- **The embedding of a Liouville form** along a branch, as a series identity. -/
lemma embG_liouvilleW (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) {ι : Type*}
    (I : Finset ι) (c : ι → C) (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (v f : L)
    (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i)) :
    S.embG g hg Y hY ⟨f, hf⟩ = dS s (S.embG g hg Y hY ⟨v, hv⟩) + ∑ i ∈ I,
      HahnSeries.C (algebraMap C K (c i)) * (dS s (S.embG g hg Y hY ⟨u i, hu i⟩) *
        (S.embG g hg Y hY ⟨u i, hu i⟩)⁻¹) := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embG g hg Y hY
  have hdc := S.derivClosedXYW' ω hx
  have hT : (⟨f, hf⟩ : T) = ⟨v′, hdc v hv⟩ + ∑ i ∈ I,
      (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) *
        ((⟨(u i)′, hdc _ (hu i)⟩ : T) / ⟨u i, hu i⟩) :=
    Subtype.ext (by simp [heq])
  have hcst : ∀ i, φ ⟨algebraMap C L (c i), S.const_mem (c i)⟩ =
      HahnSeries.C (algebraMap C K (c i)) := fun i ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    have e : (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) =
        algebraMap C⟮S.x⟯ T (algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i))) :=
      Subtype.ext (by
        show algebraMap C L (c i) = ((algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i)) : C⟮S.x⟯) : L)
        rw [algebraMap_adjoinSimple, aeval_C])
    rw [e, S.embG_algebraMap, S.embXG_algebraMap, hgX, SuperData.substHom_C]
  rw [hT, map_add, map_sum, S.embG_dSW' ω hx hK s Xh hXh g hg hgX Y hY v hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_dSW' ω hx hK s Xh hXh g hg hgX Y hY (u i) (hu i), hcst,
    div_eq_mul_inv]

/-- **The residue at a simple pole** along a branch: `(∑ cᵢ ord uᵢ) · s₀ = f₋₁`. -/
theorem sumOrd_eq_resW' (hs : s ≠ 0) (hσ : s.order ≤ 0) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) {ι : Type*} (I : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hF : ∀ k < s.order - 1, (S.embG g hg Y hY ⟨f, hf⟩).coeff k = 0) :
    (∑ i ∈ I, algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K)) *
      s.coeff s.order = (S.embG g hg Y hY ⟨f, hf⟩).coeff (s.order - 1) := by
  have hφ0 : ∀ i, S.embG g hg Y hY ⟨u i, hu i⟩ ≠ 0 := fun i ↦
    (map_ne_zero_iff _ (S.embG g hg Y hY).injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
  exact LaurentSeries.residue_eq I s _ _ _ _ hs hσ (fun i _ ↦ hφ0 i)
    (S.embG_liouvilleW ω hx hK s Xh hXh g hg hgX Y hY I c u hu v f hv hf heq) hF

/-- **`v` has no pole** along a branch where `f` has at most a simple pole. -/
theorem v_regularW' (hs : s ≠ 0) (hσ : s.order ≤ 0) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) {ι : Type*} (I : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hF : ∀ k < s.order - 1, (S.embG g hg Y hY ⟨f, hf⟩).coeff k = 0) :
    S.embG g hg Y hY ⟨v, hv⟩ = 0 ∨ 0 ≤ (S.embG g hg Y hY ⟨v, hv⟩).order := by
  have hφ0 : ∀ i, S.embG g hg Y hY ⟨u i, hu i⟩ ≠ 0 := fun i ↦
    (map_ne_zero_iff _ (S.embG g hg Y hY).injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
  exact LaurentSeries.V_regular I s _ _ _ _ hs hσ (fun i _ ↦ hφ0 i)
    (S.embG_liouvilleW ω hx hK s Xh hXh g hg hgX Y hY I c u hu v f hv hf heq) hF

/-- **The pole bound for `v` along a branch**: if `v` has a pole of order `m`, then `f` has a
non-zero coefficient at `−m − 1 + ord s`. -/
theorem v_pole_boundW' (hs : s ≠ 0) (hσ : s.order ≤ 0) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) {ι : Type*} (I : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hV0 : S.embG g hg Y hY ⟨v, hv⟩ ≠ 0) (hm : (S.embG g hg Y hY ⟨v, hv⟩).order < 0) :
    (S.embG g hg Y hY ⟨f, hf⟩).coeff ((S.embG g hg Y hY ⟨v, hv⟩).order - 1 + s.order) ≠ 0 := by
  have hφ0 : ∀ i, S.embG g hg Y hY ⟨u i, hu i⟩ ≠ 0 := fun i ↦
    (map_ne_zero_iff _ (S.embG g hg Y hY).injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
  exact LaurentSeries.V_pole_bound I s _ _ _ _ hs hσ (fun i _ ↦ hφ0 i)
    (S.embG_liouvilleW ω hx hK s Xh hXh g hg hgX Y hY I c u hu v f hv hf heq) hV0 hm

end Generic

include hx hK in
/-- **The logarithms have order `0` along every branch at a good place where `f` has no pole.** -/
theorem logs_zero_branchW (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (hind : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (a : K) (hgood : a′ ≠ (ω.map (algebraMap C K)).eval a) (N : ℕ) (hN : 0 < N)
    (Y : LaurentSeries K) (hY : (S.F.map (branchSub N a)).eval Y = 0)
    (hreg : S.embG (branchSub N a) (branchSub_injective N hN a) Y hY ⟨f, hf⟩ = 0 ∨
      0 ≤ (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY ⟨f, hf⟩).order)
    (j : ℕ) (hj : j < k) :
    (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY ⟨w j, (hw j hj).1⟩).order = 0 := by
  classical
  set u : Fin k → L := fun i ↦ w i
  have hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯ := fun i ↦ (hw i i.2).1
  have hu0 : ∀ i, u i ≠ 0 := fun i ↦ (hw i i.2).2
  have heq' : f = v′ + ∑ i : Fin k, algebraMap C L (d i) * ((u i)′ / u i) := by
    rw [heq, Fin.sum_univ_eq_sum_range (fun j ↦ algebraMap C L (d j) * ((w j)′ / w j))]
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
  have hωK : (ω.map (algebraMap C K)).eval a - a′ ≠ 0 := fun h ↦ hgood (sub_eq_zero.mp h).symm
  set s : LaurentSeries K := sBranch ω a N with hs
  have hc : s.coeff (1 - (N : ℤ)) ≠ 0 := by
    rw [hs, sBranch_coeff _ _ _ hN]
    exact mul_ne_zero (one_div_ne_zero (by exact_mod_cast hN.ne')) hωK
  have hs0 : s ≠ 0 := fun h ↦ hc (by rw [h]; rfl)
  have hσ : s.order ≤ 0 := (HahnSeries.order_le_of_coeff_ne_zero hc).trans (by omega)
  have hXh := dS_branchW ω a N hN
  rw [SuperData.branchSub_eq_subst] at hXh
  have hsum := S.sumOrd_eq_zeroW' ω hx hK s _ hXh (branchSub N a) (branchSub_injective N hN a)
    (fun P ↦ by rw [SuperData.branchSub_eq_subst]) hs0 hσ Y hY Finset.univ (fun i : Fin k ↦ d i) u hu hu0 v f
    hv hf heq' (fun kk hkk ↦ SuperData.coeff_neg_of_order_nonneg hreg (by omega))
  exact hconcl _ hsum ⟨j, hj⟩

end CurveData

end Curves
