import RischTragerBronstein.Mixed.KWEmbed
import RischTragerBronstein.Mixed.KPMain

/-!
# Liouville forms on `yⁿ = p(x)` with `x′ = ω(x)`: the logarithms at the good places

The generalization of `KPMain` from `x′ = η ∈ C` to `x′ = ω(x)`, `ω ∈ C[x]`. A finite place over
`x = α` (`α` in the algebraic closure `K` of `C`) is *good* when `α′ ≠ ω(α)` (for a logarithm,
every place; for an exponential `x′ = ηx`, every place with `α ≠ 0`). At a good place the local
derivation is `dS s` with `s = ω(α + X) − α′` (ordinary point, order `0`) or
`s = (ω(e + Xⁿ) − e′)/(n X^{n−1})` (branch point, order `1 − n`), and the residue argument of
`KPMain` applies:

**`ordAt_logs_zeroW`**: if `f = v′ + ∑ dⱼ wⱼ′/wⱼ` in `C(x, y)` with constant, `ℚ`-linearly
independent `dⱼ`, then every `wⱼ` has order `0` at every good place where `f` has no pole.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace Differential

section Local

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K] [CharZero K]

lemma coeff_zero_shiftHom (α : K) (P : C[X]) :
    (shiftHom (C := C) α P).coeff 0 = (P.map (algebraMap C K)).eval α := by
  rw [shiftHom_apply, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, coeff_coe_powerSeries,
    Polynomial.coeff_coe, coeff_zero_eq_eval_zero, eval_comp]
  simp

lemma coeff_zero_branchSub (m : ℕ) (hm : 0 < m) (e : K) (P : C[X]) :
    (branchSub (C := C) m e P).coeff 0 = (P.map (algebraMap C K)).eval e := by
  rw [branchSub_apply, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, coeff_coe_powerSeries,
    Polynomial.coeff_coe, coeff_zero_eq_eval_zero, eval_comp]
  simp [zero_pow hm.ne']

/-- **The derivation at an ordinary point** `x = α + X`. -/
lemma dS_shiftW (α : K) (ω : C[X]) :
    dS (substHom (shiftX α) ω - HahnSeries.C α′) (shiftX α) = substHom (shiftX α) ω := by
  rw [shiftX, map_add, dS_C, dS_apply, coefDeriv_single_one, derivative_single_one, zero_add]
  simp only [sub_self, Int.cast_one]
  rw [← HahnSeries.C_apply, HahnSeries.C_one, mul_one]
  ring

/-- The local `s` at a branch point. -/
noncomputable def sBranch (ω : C[X]) (e : K) (n : ℕ) : K⸨X⸩ :=
  HahnSeries.C (1 / (n : K)) * (branchSub (C := C) n e ω - HahnSeries.C e′) *
    single (1 - (n : ℤ)) 1

/-- **The derivation at a branch point** `x = e + Xⁿ`. -/
lemma dS_branchW (ω : C[X]) (e : K) (n : ℕ) (hn : 0 < n) :
    dS (sBranch ω e n) (HahnSeries.C e + single (n : ℤ) 1) = branchSub (C := C) n e ω := by
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  rw [map_add, dS_C, dS_apply, coefDeriv_single_one, derivative_single_one, zero_add, sBranch,
    mul_assoc, HahnSeries.single_mul_single, show (1 - (n : ℤ)) + ((n : ℤ) - 1) = 0 by ring,
    one_mul, ← HahnSeries.C_apply, mul_comm (HahnSeries.C (1 / (n : K))), mul_assoc,
    ← map_mul, Int.cast_natCast, one_div, inv_mul_cancel₀ hn0, map_one, mul_one]
  ring

lemma sBranch_coeff (ω : C[X]) (e : K) (n : ℕ) (hn : 0 < n) :
    (sBranch ω e n).coeff (1 - (n : ℤ)) =
      1 / (n : K) * ((ω.map (algebraMap C K)).eval e - e′) := by
  rw [sBranch]
  have h := HahnSeries.coeff_mul_single_add (a := (0 : ℤ)) (b := 1 - (n : ℤ)) (r := (1 : K))
    (x := HahnSeries.C (1 / (n : K)) * (branchSub (C := C) n e ω - HahnSeries.C e′))
  rw [zero_add] at h
  rw [h, mul_one, LaurentSeries.coeff_C_mul, HahnSeries.coeff_sub, coeff_zero_branchSub _ hn,
    HahnSeries.C_apply, HahnSeries.coeff_single_same]

end Local

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

/-- **The residue of a Liouville form at a place** where the integrand has no coefficient below
`ord s`. -/
theorem sumOrd_eq_zeroW (hs : s ≠ 0) (hσ : s.order ≤ 0) (Y : LaurentSeries K)
    (hY : Y ^ S.n = g S.p) {ι : Type*} (I : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hF : ∀ k < s.order, (S.embG g hg Y hY ⟨f, hf⟩).coeff k = 0) :
    ∑ i ∈ I, algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K) = 0 := by
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
  refine residue_eq_zero I s (φ ⟨f, hf⟩) (φ ⟨v, hv⟩) (fun i ↦ φ ⟨u i, hu i⟩)
    (fun i ↦ algebraMap C K (c i)) hs hσ (fun i _ ↦ hφ0 i) ?_ hF
  rw [hT, map_add, map_sum, S.embG_dSW ω hx hK s Xh hXh g hg hgX Y hY v hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_dSW ω hx hK s Xh hXh g hg hgX Y hY (u i) (hu i), hcst,
    div_eq_mul_inv]

end Generic

variable [IsAlgClosed K]

include hx hK in
/-- **The orders of the logarithms vanish at every good place where `f` has no pole.** -/
theorem ordAt_logs_zeroW (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (hind : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (α β : K) (hv' : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (hgood : α′ ≠ (ω.map (algebraMap C K)).eval α)
    (hreg : 0 ≤ S.ordAt K ⟨f, hf⟩ α β)
    (j : ℕ) (hj : j < k) : S.ordAt K ⟨w j, (hw j hj).1⟩ α β = 0 := by
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
  have hωK : (ω.map (algebraMap C K)).eval α - α′ ≠ 0 := fun h ↦ hgood (sub_eq_zero.mp h).symm
  by_cases hβ : β = 0
  · -- a branch point
    subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv', zero_pow S.hn.ne']
    obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
    set s : LaurentSeries K := sBranch ω α S.n with hs
    have hc : s.coeff (1 - (S.n : ℤ)) ≠ 0 := by
      rw [hs, sBranch_coeff _ _ _ S.hn]
      exact mul_ne_zero (one_div_ne_zero (by exact_mod_cast S.hn.ne')) hωK
    have hs0 : s ≠ 0 := fun h ↦ hc (by rw [h]; rfl)
    have hσ : s.order ≤ 0 :=
      (HahnSeries.order_le_of_coeff_ne_zero hc).trans (by have := S.hn; omega)
    have hXh := dS_branchW ω α S.n S.hn
    rw [branchSub_eq_subst] at hXh
    have h1 : S.embB α γ he hγ hγp ⟨f, hf⟩ = 0 ∨ 0 ≤ (S.embB α γ he hγ hγp ⟨f, hf⟩).order := by
      by_cases h0 : S.embB α γ he hγ hγp ⟨f, hf⟩ = 0
      · exact Or.inl h0
      · right
        rwa [S.ordAt_br ⟨f, hf⟩ α γ he hγ hγp] at hreg
    have hsum := S.sumOrd_eq_zeroW ω hx hK s _ hXh (branchSub S.n α)
      (branchSub_injective S.n S.hn α) (fun P ↦ by rw [branchSub_eq_subst]) hs0 hσ
      (S.branchYe α γ hγ hγp) (S.branchYe_pow α γ he hγ hγp) Finset.univ (fun i : Fin k ↦ d i) u
      hu hu0 v f hv hf heq' (fun kk hkk ↦ coeff_neg_of_order_nonneg h1 (by omega))
    have := hconcl (fun i ↦ (S.embB α γ he hγ hγp ⟨u i, hu i⟩).order) hsum ⟨j, hj⟩
    rw [S.ordAt_br _ α γ he hγ hγp]
    exact this
  · -- an ordinary point
    set s : LaurentSeries K := substHom (shiftX α) ω - HahnSeries.C α′ with hs
    have hc : s.coeff 0 ≠ 0 := by
      rw [hs, HahnSeries.coeff_sub, ← shiftHom_eq_subst, coeff_zero_shiftHom, HahnSeries.C_apply,
        HahnSeries.coeff_single_same]
      exact hωK
    have hs0 : s ≠ 0 := fun h ↦ hc (by rw [h]; rfl)
    have hσ : s.order ≤ 0 := HahnSeries.order_le_of_coeff_ne_zero hc
    have hXh : dS s (shiftX α) = substHom (shiftX α) ω := dS_shiftW α ω
    have h1 : S.embXY α β hβ hv' ⟨f, hf⟩ = 0 ∨ 0 ≤ (S.embXY α β hβ hv' ⟨f, hf⟩).order := by
      by_cases h0 : S.embXY α β hβ hv' ⟨f, hf⟩ = 0
      · exact Or.inl h0
      · right
        rwa [S.ordAt_nb ⟨f, hf⟩ α β hβ hv'] at hreg
    have hsum := S.sumOrd_eq_zeroW ω hx hK s _ hXh (shiftHom α) (shiftHom_injective α)
      (fun P ↦ by rw [shiftHom_eq_subst]) hs0 hσ
      (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hv'))
      (by rw [← map_pow, branchY_pow]; rfl) Finset.univ (fun i : Fin k ↦ d i) u hu hu0 v f hv hf
      heq' (fun kk hkk ↦ coeff_neg_of_order_nonneg h1 (by omega))
    have := hconcl (fun i ↦ (S.embXY α β hβ hv' ⟨u i, hu i⟩).order) hsum ⟨j, hj⟩
    rw [S.ordAt_nb _ α β hβ hv']
    exact this

end SuperData

end Differential
