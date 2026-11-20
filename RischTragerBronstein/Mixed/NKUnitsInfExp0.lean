import RischTragerBronstein.Mixed.NKUnitsInfExp
import RischTragerBronstein.Mixed.NKUnitsInf0

/-!
# Liouville forms over an exponential level with S-units

`nk_liouvilleEU_span0`: over `t = eᵃ` the logarithmic derivatives are regular at the places above
`t = 0`, so the logarithms of a Liouville form are S-units (`S` = the places at infinity and above
`0`). When `x` and given units `u₀ᵢ` span the S-units (`UnitsSpan0`, e.g. `unitsSpan0_inf`), the
logarithmic part is `∑ κᵢ u₀ᵢ′/u₀ᵢ + ℓ` with constants `κᵢ` and `ℓ ∈ C` — no condition on the
places above `0` is needed (compare `nk_liouvilleEU_span`, a single place above `0`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

set_option linter.unusedSectionVars false

namespace Curves

namespace CurveData

open GTors CPoly Sup

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L)

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

set_option maxHeartbeats 4000000 in
include hx hK in
/-- **A Liouville form over an exponential level has its logarithmic part in `∑ C u₀ᵢ′/u₀ᵢ + C`**
when `x` and the `u₀ᵢ` span the S-units (`S` = the places at infinity and above `0`). -/
theorem nk_liouvilleEU_span0 (η : C) (hω : ω = Polynomial.C η * X)
    (hnd : ∀ a : K, a ≠ 0 → a′ ≠ (ω.map (algebraMap C K)).eval a)
    {mu : ℕ} (u0 : Fin mu → C⟮S.x⟯⟮S.y⟯) (hspan : S.UnitsSpan0 K u0) (hu0 : ∀ i, u0 i ≠ 0)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (hres : ∀ (a : K), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l) (k : ℤ), k < 1 - (N : ℤ) →
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) ⟨f, hf⟩).coeff k = 0)
    {ι' : Type*} (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (κ : Fin mu → C) (ℓ : C), (∀ i, (κ i)′ = 0) ∧
      f = v′ + ∑ i, algebraMap C L (κ i) * logDeriv (u0 i : L) + algebraMap C L ℓ := by
  classical
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dite_cond_eq_true (eq_true hjj)]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
  have hd'c : ∀ jj < k, (d' jj)′ = 0 := fun jj hjj ↦ by
    apply (algebraMap C L).injective
    rw [← deriv_algebraMap, hdd jj hjj, hd' jj hjj, map_zero]
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hww : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  have hx0 : S.x ≠ 0 := fun h ↦ S.htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  have hpow : ∀ jj < k, ∃ (a κ : ℤ) (b : Fin mu → ℤ), a ≠ 0 ∧ ∃ cj : C, cj ≠ 0 ∧
      (w jj) ^ a = algebraMap C L cj * S.x ^ κ * ∏ i, (u0 i : L) ^ b i := by
    intro jj hjj
    have hwne : (⟨w jj, (hww jj hjj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦
      (hww jj hjj).2 (congrArg Subtype.val h)
    obtain ⟨a, κ, b, ha, cj, hcj⟩ := hspan _ hwne
      fun a ha N hN l hl r hr ↦ S.logs_zero_branchR ω hx hK k d' w hww hind' v f hv hf heq' a
        (hnd a ha) N (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (hres a ha N hN l hl r hr)
        jj hjj
    refine ⟨a, κ, b, ha, cj, fun h0 ↦ ?_, hcj⟩
    rw [h0, map_zero, zero_mul, zero_mul] at hcj
    exact zpow_ne_zero a (hww jj hjj).2 hcj
  choose! a κ b ha cj hcj0 hcj using hpow
  have hu0L : ∀ i, (u0 i : L) ≠ 0 := fun i h ↦ hu0 i (Subtype.ext h)
  have hlx : logDeriv S.x = algebraMap C L η := by
    rw [logDeriv, hx, hω, map_mul, aeval_C, aeval_X, mul_div_assoc, div_self hx0, mul_one]
  have hlprod : ∀ bb : Fin mu → ℤ, logDeriv (∏ i, (u0 i : L) ^ bb i) =
      ∑ i, (bb i : L) * logDeriv (u0 i : L) := by
    intro bb
    rw [logDeriv, logDeriv_finset_prod _ _ (fun i _ ↦ zpow_ne_zero _ (hu0L i))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := logDeriv_zpow' (u0 i : L) (hu0L i) (bb i)
    simp only [logDeriv] at this ⊢
    exact this
  have hlw : ∀ jj < k, (w jj)′ / w jj =
      (algebraMap C L ((cj jj)′ / cj jj) + κ jj * algebraMap C L η +
        ∑ i, (b jj i : L) * logDeriv (u0 i : L)) / (a jj : L) := by
    intro jj hjj
    have hwj := (hww jj hjj).2
    have ha0' : (a jj : L) ≠ 0 := by exact_mod_cast ha jj hjj
    have h1 : logDeriv ((w jj) ^ a jj) = a jj * logDeriv (w jj) := logDeriv_zpow' _ hwj _
    have hc0 : algebraMap C L (cj jj) ≠ 0 := (map_ne_zero_iff _ (algebraMap C L).injective).mpr
      (hcj0 jj hjj)
    have hpne : ∏ i, (u0 i : L) ^ b jj i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu0L i)
    have h2 : logDeriv (algebraMap C L (cj jj) * S.x ^ κ jj * ∏ i, (u0 i : L) ^ b jj i) =
        algebraMap C L ((cj jj)′ / cj jj) + κ jj * algebraMap C L η +
          ∑ i, (b jj i : L) * logDeriv (u0 i : L) := by
      rw [Differential.logDeriv_mul _ _ (mul_ne_zero hc0 (zpow_ne_zero _ hx0)) hpne,
        Differential.logDeriv_mul _ _ hc0 (zpow_ne_zero _ hx0), hlprod, logDeriv_zpow' _ hx0, hlx,
        logDeriv, deriv_algebraMap, ← map_div₀]
    rw [hcj jj hjj, h2] at h1
    rw [← logDeriv]
    field_simp
    linear_combination -h1
  refine ⟨fun i ↦ ∑ jj ∈ Finset.range k, d' jj * ((b jj i : C) / (a jj : C)),
    ∑ jj ∈ Finset.range k, d' jj * (((cj jj)′ / cj jj + κ jj * η) / (a jj : C)), ?_, ?_⟩
  · intro i
    rw [map_sum]
    refine Finset.sum_eq_zero fun jj hjj ↦ ?_
    rw [Derivation.leibniz, hd'c jj (Finset.mem_range.mp hjj), smul_zero, add_zero, smul_eq_mul]
    have : ((b jj i : C) / (a jj : C))′ = 0 := by
      rw [show ((b jj i : C) / (a jj : C)) = (((b jj i : ℚ) / (a jj : ℚ) : ℚ) : C) by
        push_cast; rfl]
      exact Differential.deriv_ratCast_K _
    rw [this, mul_zero]
  · rw [heq', add_assoc]
    congr 1
    have e : ∀ i, algebraMap C L (∑ jj ∈ Finset.range k, d' jj * ((b jj i : C) / (a jj : C))) *
        logDeriv (u0 i : L) = ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) / (a jj : L) *
          ((b jj i : L) * logDeriv (u0 i : L)) := by
      intro i
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun jj _ ↦ ?_
      simp only [map_mul, map_div₀, map_intCast]
      ring
    simp only [e]
    rw [Finset.sum_comm, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    have hj := Finset.mem_range.mp hjj
    have ha0 : (a jj : L) ≠ 0 := by exact_mod_cast ha jj hj
    rw [hlw jj hj, ← Finset.mul_sum]
    simp only [map_mul, map_div₀, map_intCast, map_add]
    field_simp
    ring

end CurveData

end Curves
