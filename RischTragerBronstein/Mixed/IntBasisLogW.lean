import RischTragerBronstein.Mixed.NKEmbed
import RischTragerBronstein.Curves.IntBasisLog

/-!
# Logarithmic stability along finite branches with a coefficient derivation

For a curve `F(x, y) = 0` over a differential field `C` (not necessarily constants) with
`x′ = ω(x)`: if `f` has no finite pole and `f′ = W(x, y)/Q(x)`, then `rad(Q) f′` has no finite pole
(`regularFinite_rad_derivW`). Along a branch `x = a + Tᴺ` the derivation is `δ + s d/dT` with
`s = (ω(x̂) − a′)/(N Tᴺ⁻¹)` (`embG_dSW'`), so it lowers the order by at most `N − 1`, which the
factor `x − a` of `rad Q` makes up. This is `regularFinite_rad_deriv` (constant `C`, `x′ = 1`) for
curves whose coefficients are not constant.
-/

open Polynomial HahnSeries IntermediateField LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]

namespace CurveData

variable (S : CurveData C L)

/-- The coefficient derivation keeps the order bound `0`. -/
lemma lowerBd_coefDeriv {z : LaurentSeries K} {m : ℤ} (hz : LowerBd z m) :
    LowerBd (coefDeriv z) m := fun k hk ↦ by
  rw [coeff_coefDeriv, hz k hk]
  exact Differential.deriv.map_zero

/-- The speed `s` of the branch `x = a + Tᴺ`: `dS s x̂ = ω(x̂)`. -/
noncomputable def branchSpeed (ω : C[X]) (N : ℕ) (a : K) : LaurentSeries K :=
  (substHom (HahnSeries.C a + single (N : ℤ) 1) ω - HahnSeries.C a′) *
    single (1 - (N : ℤ)) ((N : K)⁻¹)

lemma dS_branchSpeed (ω : C[X]) (N : ℕ) (hN : 0 < N) (a : K) :
    dS (branchSpeed ω N a) (HahnSeries.C a + single (N : ℤ) 1) =
      substHom (HahnSeries.C a + single (N : ℤ) 1) ω := by
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [dS_apply, map_add, coefDeriv_C, coefDeriv_single, Differential.deriv.map_one_eq_zero,
    HahnSeries.single_eq_zero, add_zero, map_add, derivative_laurent_C, zero_add]
  have hd : derivative K (single (N : ℤ) (1 : K)) = single ((N : ℤ) - 1) (N : K) := by
    have := Differential.derivation_single (K := K) (N : ℤ)
    rw [LaurentSeries.derivation_apply] at this
    rw [this, Int.cast_natCast]
  rw [hd, branchSpeed, mul_assoc, HahnSeries.single_mul_single, inv_mul_cancel₀ hN']
  have e : 1 - (N : ℤ) + ((N : ℤ) - 1) = 0 := by ring
  rw [e, ← HahnSeries.C_apply, HahnSeries.C_one, mul_one]
  ring

lemma lowerBd_branchSpeed (ω : C[X]) (N : ℕ) (a : K) :
    LowerBd (branchSpeed ω N a) (1 - (N : ℤ)) := by
  have h1 : LowerBd (substHom (C := C) (HahnSeries.C a + single (N : ℤ) 1) ω -
      HahnSeries.C a′) 0 := by
    refine LowerBd.sub ?_ (lowerBd_C _)
    rw [← SuperData.branchSub_eq_subst]
    exact lowerBd_branchSub_nonneg N a ω
  have := h1.mul (lowerBd_single (1 - (N : ℤ)) ((N : K)⁻¹))
  rwa [zero_add] at this

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **Logarithmic stability with a coefficient derivation**: if `f` has no finite pole and
`f′ = W/Q`, then `rad(Q) f′` has no finite pole. -/
theorem regularFinite_rad_derivW (f : C⟮S.x⟯⟮S.y⟯)
    (hf : S.RegularFinite K f) (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0)
    (hWQ : ((f : L))′ * aeval S.x Q = S.evXY W) :
    S.RegularFinite K ((⟨aeval S.x (UniqueFactorizationMonoid.radical Q), S.aeval_mem _⟩ :
      C⟮S.x⟯⟮S.y⟯) * ⟨(f : L)′, S.derivClosedXYW' ω hx f f.2⟩) := by
  classical
  intro a N hN l hl r hr
  have hN0 := Nat.pos_of_ne_zero hN
  have hY := S.root_of_mem hl hr
  set R := UniqueFactorizationMonoid.radical Q with hR
  have hR0 : R ≠ 0 := radical_ne_zero' Q
  rw [map_mul, S.embG_polyX]
  refine order_nonneg_of_lowerBd _ ?_
  by_cases hQa : (Q.map (algebraMap C K)).eval a = 0
  · -- a branch above a root of `Q`: the derivation lowers the order by at most `N − 1`
    have hRa := eval_radical_eq_zero Q hQ a hQa
    have hRord : LowerBd (branchSub (C := C) N a R) (N : ℤ) := by
      have ho := order_branchSub (K := K) N hN0 a R hR0
      have hm : 1 ≤ (R.map (algebraMap C K)).rootMultiplicity a :=
        (rootMultiplicity_pos ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hR0)).mpr
          hRa
      intro k hk
      refine HahnSeries.coeff_eq_zero_of_lt_order ?_
      rw [ho]
      have : (N : ℤ) ≤ ((N * (R.map (algebraMap C K)).rootMultiplicity a : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_mul_of_pos_right N hm
      omega
    have hd := S.embG_dSW' ω hx hK (branchSpeed ω N a) (HahnSeries.C a + single (N : ℤ) 1)
      (dS_branchSpeed ω N hN0 a) (branchSub N a) (branchSub_injective N hN0 a)
      (fun P ↦ by rw [SuperData.branchSub_eq_subst]) r hY (f : L) f.2
    simp only [Subtype.coe_eta] at hd
    rw [hd]
    have hfr : LowerBd (S.embG (branchSub N a) (branchSub_injective N hN0 a) r hY f) 0 :=
      lowerBd_of_order_nonneg (hf a N hN l hl r hr)
    rw [dS_apply]
    have h1 : LowerBd (coefDeriv (S.embG (branchSub N a) (branchSub_injective N hN0 a) r hY f) +
        branchSpeed ω N a * derivative K
          (S.embG (branchSub N a) (branchSub_injective N hN0 a) r hY f)) (1 - (N : ℤ)) := by
      refine LowerBd.add ((lowerBd_coefDeriv hfr).mono (by omega)) ?_
      have := (lowerBd_branchSpeed ω N a).mul (lowerBd_derivative_zero hfr)
      rwa [add_zero] at this
    have := hRord.mul h1
    refine this.mono ?_
    omega
  · -- elsewhere `W/Q` has no pole
    have h1 := S.lowerBd_fin N hN0 a r hY ⟨(f : L)′, S.derivClosedXYW' ω hx f f.2⟩ W Q hQ hWQ
    rw [rootMultiplicity_eq_zero hQa, mul_zero, Nat.cast_zero, neg_zero] at h1
    have := (lowerBd_branchSub_nonneg N a R).mul h1
    rwa [zero_add] at this

end CurveData

end Curves
