import RischTragerBronstein.Mixed.KQLocal
import RischTragerBronstein.Algebraic.SuperPrincipalSem

/-!
# The expansion of `b y` at a pole of `b`

`pole_of_mul`: if `F Xᵉ G = H` in Laurent series with `G, H` power series and `G(0) ≠ 0`, then `F`
has nothing below `−e` and `F_{−e} G(0) = H(0)`.

`expand_pole`: on `yⁿ = p(x)`, for `f` with `f · Q(x) = P(x) y` and `Q(α + X) = Xᵉ R(X)`, `R(0) ≠ 0`,
the expansion of `f` at `(α, β)` (`β ≠ 0`) has nothing below `−e` and its coefficient at `−e` is
`P(α) β / R(0)`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

namespace LaurentSeries

variable {K : Type*} [Field K] [Differential K] [CharZero K]

lemma pole_of_mul {F G H : K⸨X⸩} (e : ℕ) (h : F * single (e : ℤ) 1 * G = H)
    (hG : ∀ k < 0, G.coeff k = 0) (hG0 : G.coeff 0 ≠ 0) (hH : ∀ k < 0, H.coeff k = 0) :
    (∀ k < -(e : ℤ), F.coeff k = 0) ∧ F.coeff (-(e : ℤ)) * G.coeff 0 = H.coeff 0 := by
  set F' := F * single (e : ℤ) (1 : K) with hF'def
  have hF' : ∀ k, F'.coeff k = F.coeff (k - e) := fun k ↦ by
    have := HahnSeries.coeff_mul_single_add (r := (1 : K)) (x := F) (a := k - e) (b := (e : ℤ))
    rw [sub_add_cancel, mul_one] at this
    exact this
  have hneg : ∀ k < 0, F'.coeff k = 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨k, hk, hk0⟩ := hc
    have hF'0 : F' ≠ 0 := fun h0 ↦ hk0 (by rw [h0]; rfl)
    have ho : F'.order ≤ k := HahnSeries.order_le_of_coeff_ne_zero hk0
    have := coeff_mul_add (x := F') (y := G) (a := F'.order) (b := 0) (coeff_lt_order_eq_zero F') hG
    rw [add_zero, h, hH _ (by omega)] at this
    exact mul_ne_zero ((not_congr HahnSeries.coeff_order_eq_zero).mpr hF'0) hG0 this.symm
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · have := hneg (k + e) (by omega)
    rwa [hF', add_sub_cancel_right] at this
  · have := coeff_mul_add (x := F') (y := G) (a := 0) (b := 0) hneg hG
    rw [add_zero, h, hF', zero_sub] at this
    exact this.symm

end LaurentSeries

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

lemma embXY_ofPS (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (P : C[X]) : S.embXY α β hβ hβp (S.polyX P) =
      ofPowerSeries ℤ K (((P.map (algebraMap C K)).comp (X + Polynomial.C α) : K[X]) :
        PowerSeries K) := S.embXY_polyX α β hβ hβp P

/-- **The expansion of `f` with `f Q(x) = P(x) y`** at a point where `Q(α + X) = Xᵉ R(X)`. -/
theorem expand_pole (f : C⟮S.x⟯⟮S.y⟯) (P Q : C[X])
    (hfQ : f * S.polyX Q = S.polyX P * AdjoinSimple.gen C⟮S.x⟯ S.y)
    (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (e : ℕ) (R : K[X]) (hR : (Q.map (algebraMap C K)).comp (X + Polynomial.C α) = X ^ e * R)
    (hR0 : R.eval 0 ≠ 0) :
    (∀ k < -(e : ℤ), (S.embXY α β hβ hβp f).coeff k = 0) ∧
      (S.embXY α β hβ hβp f).coeff (-(e : ℤ)) * R.eval 0 = (P.map (algebraMap C K)).eval α * β := by
  set Y := branchY S.n S.hn (S.hnK K) S.p α β hβ hβp
  have h := congrArg (S.embXY α β hβ hβp) hfQ
  rw [map_mul, map_mul, S.embXY_polyX, S.embXY_polyX, S.embXY_gen, hR] at h
  have hsplit : ofPowerSeries ℤ K (((X ^ e * R : K[X])) : PowerSeries K) =
      single (e : ℤ) 1 * ofPowerSeries ℤ K ((R : K[X]) : PowerSeries K) := by
    rw [Polynomial.coe_mul, map_mul, Polynomial.coe_pow, Polynomial.coe_X, ofPowerSeries_X_pow]
  rw [hsplit, ← mul_assoc, ← map_mul] at h
  have hG : ∀ k < 0, (ofPowerSeries ℤ K ((R : K[X]) : PowerSeries K)).coeff k = 0 := fun k hk ↦ by
    rw [PowerSeries.coeff_coe, ite_eq_left hk]
  have hH : ∀ k < 0, (ofPowerSeries ℤ K
      ((((P.map (algebraMap C K)).comp (X + Polynomial.C α) : K[X]) : PowerSeries K) * Y)).coeff k
        = 0 := fun k hk ↦ by
    rw [PowerSeries.coeff_coe, ite_eq_left hk]
  have hG0 : (ofPowerSeries ℤ K ((R : K[X]) : PowerSeries K)).coeff 0 = R.eval 0 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, coeff_coe_powerSeries, Polynomial.coeff_coe,
      coeff_zero_eq_eval_zero]
  obtain ⟨h1, h2⟩ := pole_of_mul e h hG (by rw [hG0]; exact hR0) hH
  refine ⟨h1, ?_⟩
  rw [← hG0, h2]
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, coeff_coe_powerSeries,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, branchY_const,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    coeff_zero_eq_eval_zero, eval_comp]
  simp

end SuperData

end Differential
