import RischTragerBronstein.Mixed.KWMain
import RischTragerBronstein.Mixed.KPMain2

/-!
# The class argument at the branch points for `x′ = ω(x)`

At a branch point `x = e + Xⁿ` the local derivation is `dS s` with
`s = (ω(e + Xⁿ) − e′)/(n Xⁿ⁻¹)` (`sBranch`), of order `1 − n` (at a good place) and covariant under
`X ↦ ζX`: `s(ζX) = ζ s(X)` for `ζⁿ = 1` (`sBranch_scale`). This is all the class argument of
`KPClass`/`KPMain2` uses, so it carries over (`residue_eq_zero_classW`, `ordAt_logs_zero_classW`):
the logarithms of a Liouville form for `b(x) yʲ` (`0 < j < n`, `b` with poles only at the branch
points and at bad places) have order `0` at every good branch point.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

namespace LaurentSeries

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- `X ↦ ζX` commutes with `dS s` when `s(ζX) = ζ s(X)`. -/
lemma dS_scaleLW (ζ : K) (n : ℕ) (hn : 0 < n) (hζ : ζ ^ n = 1) (hζ0 : ζ ≠ 0) (s : K⸨X⸩)
    (hs : scaleL ζ hζ0 s = HahnSeries.C ζ * s) (F : K⸨X⸩) :
    dS s (scaleL ζ hζ0 F) = scaleL ζ hζ0 (dS s F) := by
  have hζ' : ζ′ = 0 := deriv_root_of_unity hn hζ
  rw [dS_apply, dS_apply, map_add, map_mul, coefDeriv_scaleL ζ hζ0 hζ', derivative_scaleL, hs]
  ring

lemma dS_projLW (ζ : K) (n : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (hζ0 : ζ ≠ 0)
    (s : K⸨X⸩) (hs : ∀ k : ℕ, scaleL (ζ ^ k) (pow_ne_zero k hζ0) s = HahnSeries.C (ζ ^ k) * s)
    (F : K⸨X⸩) : dS s (projL ζ hζ0 n F) = projL ζ hζ0 n (dS s F) := by
  have hC : dS s (HahnSeries.C ((n : K)⁻¹)) = 0 := by
    rw [dS_C, Derivation.leibniz_inv, Derivation.map_natCast, smul_zero, map_zero]
  rw [projL, projL, Derivation.leibniz, hC, smul_zero, add_zero, smul_eq_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact dS_scaleLW (ζ ^ k) n hn (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    (pow_ne_zero k hζ0) s (hs k) F

/-- **The class residue argument for a covariant `s` of order `1 − n`.** -/
theorem residue_eq_zero_classW {ι : Type*} (I : Finset ι) (ζ : K) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (hζ0 : ζ ≠ 0) (s : K⸨X⸩) (hs0 : s ≠ 0) (hsord : s.order = 1 - n)
    (hsc : ∀ k : ℕ, scaleL (ζ ^ k) (pow_ne_zero k hζ0) s = HahnSeries.C (ζ ^ k) * s)
    (F V : K⸨X⸩) (U : ι → K⸨X⸩) (κ : ι → K) (hU : ∀ i ∈ I, U i ≠ 0)
    (heq : F = dS s V + ∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹))
    (hF : projL ζ hζ0 n F = 0) :
    ∑ i ∈ I, κ i * ((U i).order : K) = 0 := by
  have hσ : s.order ≤ 0 := by rw [hsord]; omega
  set Λ := ∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹) with hΛ
  have hlog : ∀ k, Λ.coeff k = ∑ i ∈ I, κ i * (dS s (U i) * (U i)⁻¹).coeff k := fun k ↦ by
    rw [hΛ, HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ ↦ coeff_C_mul _ _ _
  have hΛbelow : ∀ k < -(n : ℤ), Λ.coeff k = 0 := fun k hk ↦ by
    rw [hlog]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).1 k (by rw [hsord]; omega), mul_zero]
  have hΛn : Λ.coeff (-(n : ℤ)) = (∑ i ∈ I, κ i * ((U i).order : K)) * s.coeff s.order := by
    rw [hlog, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [show (-(n : ℤ)) = s.order - 1 by rw [hsord]; ring,
      (coeff_dS_logDeriv s (U i) (hU i hi) hσ).2]
    ring
  have hP := congrArg (projL ζ hζ0 n) heq
  rw [hF, projL_add, ← dS_projLW ζ n hn hζ hζ0 s hsc] at hP
  set V₀ := projL ζ hζ0 n V with hV₀
  have hPΛ : ∀ k, (projL ζ hζ0 n Λ).coeff k = if (n : ℤ) ∣ k then Λ.coeff k else 0 :=
    coeff_projL ζ n hn hζ hζ0 Λ
  have hV₀c : ∀ k, V₀.coeff k ≠ 0 → (n : ℤ) ∣ k := fun k hk ↦ by
    by_contra hd
    rw [hV₀, coeff_projL ζ n hn hζ hζ0, if_neg hd] at hk
    exact hk rfl
  have hV : V₀ = 0 ∨ 0 ≤ V₀.order := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hV0, hm⟩ := hcon
    have hdiv : (n : ℤ) ∣ V₀.order :=
      hV₀c _ ((not_congr HahnSeries.coeff_order_eq_zero).mpr hV0)
    have hle : V₀.order ≤ -(n : ℤ) := by
      obtain ⟨q, hq⟩ := hdiv
      rw [hq] at hm ⊢
      have : q < 0 := by
        by_contra h
        push Not at h
        have : (0 : ℤ) ≤ (n : ℤ) * q := mul_nonneg (by omega) h
        omega
      nlinarith
    obtain ⟨-, hlead⟩ := coeff_dS_pole s V₀ hV0 hm.ne hσ
    have hc0 := congrArg (fun G ↦ G.coeff (V₀.order - 1 + s.order)) hP
    simp only [HahnSeries.coeff_zero, HahnSeries.coeff_add] at hc0
    rw [hlead, hPΛ] at hc0
    have hsm : V₀.order - 1 + s.order < -(n : ℤ) := by rw [hsord]; omega
    rw [hΛbelow _ hsm] at hc0
    simp only [ite_self, add_zero] at hc0
    have h1 : (V₀.order : K) ≠ 0 := by exact_mod_cast hm.ne
    have h2 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs0
    have h3 : V₀.coeff V₀.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hV0
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 hc0.symm
  have hc0 := congrArg (fun G ↦ G.coeff (-(n : ℤ))) hP
  simp only [HahnSeries.coeff_zero, HahnSeries.coeff_add] at hc0
  rw [coeff_dS_regular s V₀ hV (by rw [hsord]; omega) hσ, zero_add, hPΛ,
    if_pos (dvd_neg.mpr dvd_rfl), hΛn] at hc0
  have h2 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs0
  exact (mul_eq_zero.mp hc0.symm).resolve_right h2

end LaurentSeries

namespace Differential

section Branch

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K] [CharZero K]

lemma order_eq_zero_of {F : K⸨X⸩} (h0 : F.coeff 0 ≠ 0) (hge : 0 ≤ F.order) : F.order = 0 :=
  le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h0) hge

lemma branchSub_order_nonneg (m : ℕ) (hm : 0 < m) (e : K) (P : C[X]) :
    0 ≤ (branchSub (C := C) m e P).order := by
  by_cases hP : P = 0
  · rw [hP, map_zero, HahnSeries.order_zero]
  · rw [order_branchSub m hm e P hP]; positivity

/-- **The branch `s` has order `1 − n`** at a good place. -/
lemma sBranch_order (ω : C[X]) (e : K) (n : ℕ) (hn : 0 < n)
    (hgood : (ω.map (algebraMap C K)).eval e ≠ e′) :
    sBranch ω e n ≠ 0 ∧ (sBranch ω e n).order = 1 - n := by
  set A' := branchSub (C := C) n e ω - HahnSeries.C e′ with hA'
  have hA0c : A'.coeff 0 ≠ 0 := by
    rw [hA', HahnSeries.coeff_sub, coeff_zero_branchSub _ hn, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    exact sub_ne_zero.mpr hgood
  have hA'0 : A' ≠ 0 := fun h ↦ hA0c (by rw [h]; rfl)
  have hAge : 0 ≤ A'.order := by
    have := HahnSeries.min_order_le_order_add (x := branchSub (C := C) n e ω)
      (y := -HahnSeries.C e′) (by rw [← sub_eq_add_neg]; exact hA'0)
    rw [← sub_eq_add_neg] at this
    refine le_trans (le_min (branchSub_order_nonneg n hn e ω) ?_) this
    rw [HahnSeries.order_neg]
    by_cases he : e′ = 0
    · rw [he, map_zero, HahnSeries.order_zero]
    · rw [HahnSeries.order_C]
  have hAord := order_eq_zero_of hA0c hAge
  have hn0 : (1 / (n : K)) ≠ 0 := one_div_ne_zero (by exact_mod_cast hn.ne')
  have hC0 : HahnSeries.C (1 / (n : K)) ≠ (0 : K⸨X⸩) := HahnSeries.C_ne_zero hn0
  have hs1 : (single (1 - (n : ℤ)) (1 : K) : K⸨X⸩) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  refine ⟨mul_ne_zero (mul_ne_zero hC0 hA'0) hs1, ?_⟩
  rw [sBranch, HahnSeries.order_mul (mul_ne_zero hC0 hA'0) hs1,
    HahnSeries.order_mul hC0 hA'0, HahnSeries.order_C, hAord, HahnSeries.order_single one_ne_zero]
  ring

end Branch

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]
variable (S : SuperData C L)

/-- **The branch `s` is covariant**: `s(ζX) = ζ s(X)`. -/
lemma sBranch_scale (ω : C[X]) (e : K) (z : K) (hz : z ≠ 0) (hzn : z ^ S.n = 1) :
    scaleL z hz (sBranch ω e S.n) = HahnSeries.C z * sBranch ω e S.n := by
  have hb : scaleL z hz (branchSub (C := C) S.n e ω) = branchSub S.n e ω := by
    have := congrArg (fun φ : C[X] →+* K⸨X⸩ ↦ φ ω) (S.scaleL_branchSub z hz hzn e)
    exact this
  rw [sBranch, map_mul, map_mul, map_sub, hb, scaleL_C, scaleL_C, scaleL_single]
  have hzz : z ^ (1 - (S.n : ℤ)) = z := by
    rw [zpow_sub₀ hz, zpow_one, zpow_natCast, hzn, div_one]
  rw [hzz, show (single (1 - (S.n : ℤ)) (z * 1) : K⸨X⸩) = HahnSeries.C z * single (1 - (S.n : ℤ)) 1 by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add]]
  ring

section ClassW

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

section Generic

variable (s Xh : LaurentSeries K) (hXh : dS s Xh = substHom Xh ω)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hx hK hXh hgX

/-- **The residue of a Liouville form at a branch point**, for an integrand without class-`0` part,
for a covariant `s` of order `1 − n`. -/
theorem sumOrd_eq_zero_classW (ζ : K) (hζ : IsPrimitiveRoot ζ S.n) (hζ0 : ζ ≠ 0) (hs0 : s ≠ 0)
    (hsord : s.order = 1 - S.n)
    (hsc : ∀ k : ℕ, scaleL (ζ ^ k) (pow_ne_zero k hζ0) s = HahnSeries.C (ζ ^ k) * s)
    (Y : LaurentSeries K) (hY : Y ^ S.n = g S.p) {ι : Type*} (I : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L)
    (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ I, algebraMap C L (c i) * ((u i)′ / u i))
    (hF : projL ζ hζ0 S.n (S.embG g hg Y hY ⟨f, hf⟩) = 0) :
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
  refine residue_eq_zero_classW I ζ S.n S.hn hζ hζ0 s hs0 hsord hsc (φ ⟨f, hf⟩) (φ ⟨v, hv⟩)
    (fun i ↦ φ ⟨u i, hu i⟩) (fun i ↦ algebraMap C K (c i)) (fun i _ ↦ hφ0 i) ?_ hF
  rw [hT, map_add, map_sum, S.embG_dSW ω hx hK s Xh hXh g hg hgX Y hY v hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_dSW ω hx hK s Xh hXh g hg hgX Y hY (u i) (hu i), hcst,
    div_eq_mul_inv]

end Generic

variable [IsAlgClosed K]

include hx hK in
/-- **At a good branch point the logarithms have order `0`**, for `f = b yʲ` (`0 < j < n`,
`b ∈ C(x)` arbitrary). -/
theorem ordAt_logs_zero_classW (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (hind : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (b : L) (hb : b ∈ C⟮S.x⟯) (jj : ℕ) (hj0 : 0 < jj) (hjn : jj < S.n) (hfb : f = b * S.y ^ jj)
    (α : K) (he : (S.p.map (algebraMap C K)).eval α = 0)
    (hgood : α′ ≠ (ω.map (algebraMap C K)).eval α)
    (j : ℕ) (hj : j < k) : S.ordAt K ⟨w j, (hw j hj).1⟩ α 0 = 0 := by
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
  obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
  set s : LaurentSeries K := sBranch ω α S.n with hs
  obtain ⟨hs0, hsord⟩ := sBranch_order ω α S.n S.hn (fun h ↦ hgood h.symm)
  have hXh := dS_branchW ω α S.n S.hn
  rw [branchSub_eq_subst] at hXh
  obtain ⟨ζ, hζ⟩ := exists_primitive (K := K) S.n S.hn (S.hnK K)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero S.hn.ne'
  have hsc : ∀ kk : ℕ, scaleL (ζ ^ kk) (pow_ne_zero kk hζ0) s = HahnSeries.C (ζ ^ kk) * s :=
    fun kk ↦ S.sBranch_scale ω α (ζ ^ kk) (pow_ne_zero kk hζ0)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  have hfm : (⟨f, hf⟩ : C⟮S.x⟯⟮S.y⟯) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨b, hb⟩ *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ jj := Subtype.ext (by simp [hfb])
  have hsum := S.sumOrd_eq_zero_classW ω hx hK s _ hXh (branchSub S.n α)
    (branchSub_injective S.n S.hn α) (fun P ↦ by rw [branchSub_eq_subst]) ζ hζ hζ0 hs0 hsord hsc
    (S.branchYe α γ hγ hγp) (S.branchYe_pow α γ he hγ hγp) Finset.univ (fun i : Fin k ↦ d i) u
    hu hu0 v f hv hf heq' (by
      rw [hfm]
      exact S.projL_embB_zero ζ hζ hζ0 α γ he hγ hγp ⟨b, hb⟩ jj hj0 hjn)
  have := hconcl (fun i ↦ (S.embB α γ he hγ hγp ⟨u i, hu i⟩).order) hsum ⟨j, hj⟩
  rw [S.ordAt_br _ α γ he hγ hγp]
  exact this

end ClassW

end SuperData

end Differential
