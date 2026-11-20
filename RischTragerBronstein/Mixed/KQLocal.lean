import RischTragerBronstein.Mixed.KWMain

/-!
# Residues of a Liouville form at a simple pole

`residue_eq`: in Laurent series over a differential field, with the derivation `dS s` (`s` of
order `σ ≤ 0`), if `F = dS s V + ∑ κᵢ dS s Uᵢ / Uᵢ` and `F` has no coefficient below `σ − 1`, then
`(∑ κᵢ ord Uᵢ) s_σ = F_{σ−1}` (a pole of `V` would propagate below `σ − 1`).

`ordAt_logs_resW`: on `yⁿ = p(x)`, `x′ = ω(x)`, at a good ordinary place `(α, β)` where
`f = v′ + ∑ dⱼ wⱼ′/wⱼ` has at most a simple pole, `(∑ dⱼ ord wⱼ) (ω(α) − α′)` is the coefficient
of `X⁻¹` in the expansion of `f`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

namespace LaurentSeries

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- **The residue of a Liouville form at a simple pole.** -/
theorem residue_eq {ι : Type*} (I : Finset ι) (s F V : K⸨X⸩) (U : ι → K⸨X⸩) (κ : ι → K)
    (hs : s ≠ 0) (hσ : s.order ≤ 0) (hU : ∀ i ∈ I, U i ≠ 0)
    (heq : F = dS s V + ∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹))
    (hF : ∀ k < s.order - 1, F.coeff k = 0) :
    (∑ i ∈ I, κ i * ((U i).order : K)) * s.coeff s.order = F.coeff (s.order - 1) := by
  have hlog : ∀ k, (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k =
      ∑ i ∈ I, κ i * (dS s (U i) * (U i)⁻¹).coeff k := fun k ↦ by
    rw [HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ ↦ coeff_C_mul _ _ _
  have hlogBelow : ∀ k < s.order - 1,
      (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k = 0 := fun k hk ↦ by
    rw [hlog]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).1 k hk, mul_zero]
  have hV : V = 0 ∨ 0 ≤ V.order := by
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
  have hc : F.coeff (s.order - 1) = (dS s V + ∑ i ∈ I, HahnSeries.C (κ i) *
      (dS s (U i) * (U i)⁻¹)).coeff (s.order - 1) := congrArg (fun G ↦ G.coeff (s.order - 1)) heq
  rw [HahnSeries.coeff_add, coeff_dS_regular s V hV (by omega) hσ, zero_add, hlog] at hc
  rw [hc, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).2]
  ring

end LaurentSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]
variable (S : SuperData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

section Generic

variable (s Xh : LaurentSeries K) (hXh : dS s Xh = substHom Xh ω)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hx hK hXh hgX

/-- **The residue of a Liouville form at a place** where the integrand has at most a simple
pole (relative to `ord s`). -/
theorem sumOrd_eq_resW (hs : s ≠ 0) (hσ : s.order ≤ 0) (Y : LaurentSeries K)
    (hY : Y ^ S.n = g S.p) {ι : Type*} (I : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hF : ∀ k < s.order - 1, (S.embG g hg Y hY ⟨f, hf⟩).coeff k = 0) :
    (∑ i ∈ I, algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K)) *
      s.coeff s.order = (S.embG g hg Y hY ⟨f, hf⟩).coeff (s.order - 1) := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embG g hg Y hY
  have hdc := S.derivClosedXYW ω hx
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
  refine residue_eq I s (φ ⟨f, hf⟩) (φ ⟨v, hv⟩) (fun i ↦ φ ⟨u i, hu i⟩)
    (fun i ↦ algebraMap C K (c i)) hs hσ (fun i _ ↦ hφ0 i) ?_ hF
  rw [hT, map_add, map_sum, S.embG_dSW ω hx hK s Xh hXh g hg hgX Y hY v hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_dSW ω hx hK s Xh hXh g hg hgX Y hY (u i) (hu i), hcst,
    div_eq_mul_inv]

end Generic

variable [IsAlgClosed K]

include hx hK in
/-- **The residue at a good ordinary place**: if `f` has at most a simple pole at `(α, β)`,
`β ≠ 0`, then `(∑ dⱼ ord wⱼ) (ω(α) − α′)` is the coefficient of `X⁻¹` of `f` there. -/
theorem ordAt_logs_resW (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (α β : K) (hβ : β ≠ 0) (hv' : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (hgood : α′ ≠ (ω.map (algebraMap C K)).eval α)
    (hpole : ∀ kk < -1, (S.embXY α β hβ hv' ⟨f, hf⟩).coeff kk = 0) :
    (∑ j ∈ Finset.range k, algebraMap C K (d j) *
      (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ α β : K) else 0)) *
        ((ω.map (algebraMap C K)).eval α - α′) =
      (S.embXY α β hβ hv' ⟨f, hf⟩).coeff (-1) := by
  classical
  set u : Fin k → L := fun i ↦ w i
  have hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯ := fun i ↦ (hw i i.2).1
  have hu0 : ∀ i, u i ≠ 0 := fun i ↦ (hw i i.2).2
  have heq' : f = v′ + ∑ i : Fin k, algebraMap C L (d i) * ((u i)′ / u i) := by
    rw [heq, Fin.sum_univ_eq_sum_range (fun j ↦ algebraMap C L (d j) * ((w j)′ / w j))]
  set s : LaurentSeries K := substHom (shiftX α) ω - HahnSeries.C α′ with hs
  have hc : s.coeff 0 = (ω.map (algebraMap C K)).eval α - α′ := by
    rw [hs, HahnSeries.coeff_sub, ← shiftHom_eq_subst, coeff_zero_shiftHom, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
  have hc0 : s.coeff 0 ≠ 0 := by
    rw [hc]; exact fun h ↦ hgood (sub_eq_zero.mp h).symm
  have hs0 : s ≠ 0 := fun h ↦ hc0 (by rw [h]; rfl)
  have h1 : substHom (shiftX α) ω = ofPowerSeries ℤ K
      (((ω.map (algebraMap C K)).comp (X + Polynomial.C α) : K[X]) : PowerSeries K) := by
    rw [← shiftHom_eq_subst, shiftHom_apply]
  have hneg : ∀ kk < 0, s.coeff kk = 0 := fun kk hkk ↦ by
    rw [hs, HahnSeries.coeff_sub, h1, PowerSeries.coeff_coe, ite_eq_left hkk, HahnSeries.C_apply,
      HahnSeries.coeff_single_of_ne hkk.ne, sub_zero]
  have hord : s.order = 0 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc0) ?_
    by_contra hlt
    push Not at hlt
    exact (not_congr HahnSeries.coeff_order_eq_zero).mpr hs0 (hneg _ hlt)
  have hXh : dS s (shiftX α) = substHom (shiftX α) ω := dS_shiftW α ω
  have hsum := S.sumOrd_eq_resW ω hx hK s _ hXh (shiftHom α) (shiftHom_injective α)
    (fun P ↦ by rw [shiftHom_eq_subst]) hs0 hord.le
    (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hv'))
    (by rw [← map_pow, branchY_pow]; rfl) Finset.univ (fun i : Fin k ↦ d i) u hu hu0 v f hv hf
    heq' (fun kk hkk ↦ by rw [hord] at hkk; exact hpole kk (by omega))
  rw [hord, hc] at hsum
  have e : ∑ j ∈ Finset.range k, algebraMap C K (d j) *
      (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ α β : K) else 0) =
      ∑ i : Fin k, algebraMap C K (d i) * ((S.embXY α β hβ hv' ⟨u i, hu i⟩).order : K) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ algebraMap C K (d j) *
      (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ α β : K) else 0))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [dif_pos i.2, S.ordAt_nb _ α β hβ hv']
  rw [e]
  exact hsum

end SuperData

end Differential
