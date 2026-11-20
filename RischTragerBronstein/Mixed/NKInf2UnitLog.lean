import RischTragerBronstein.Mixed.NKInf2Unit
import RischTragerBronstein.Mixed.NKLogDecide

/-!
# The logarithmic part with a non-constant unit

On a curve with two places at infinity and a non-constant unit `u₀` (at the finite places), every
unit is `c u₀^{b/a}` (`mem_pow_unit`), so the logarithmic part of a Liouville form is
`κ u₀′/u₀ + ℓ` with `κ` a constant and `ℓ ∈ C` (`nk_liouville_unit`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

namespace CurveData

open Differential GTors CPoly Sup

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

set_option maxHeartbeats 4000000 in
include hx hK in
/-- **A Liouville form has its logarithmic part in `C u₀′/u₀ + C`** (two places at infinity, a
non-constant unit `u₀`). -/
theorem nk_liouville_unit (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (k0 M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k0 * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k0 M).Monic)
    (hGn : (invP (shiftP S.F 0) k0 M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (ιF : F →+* C) (Fc : BPoly F) (hmon : (toB Fc).Monic)
    (hSF : (mobCurve S 0 k0 M hM hGm hGn).F = (toB Fc).map (mapRingHom ιF))
    (Pc : PlaceCert F) (hPcd : Pc.Facts Fc (toB Fc).natDegree) (hn0 : 0 < (toB Fc).natDegree)
    (hfib1 : Pc.fib.length = 1) (hpl2 : Pc.pl.length = 2) (hα0 : Pc.fα 0 = 0)
    (u0 : C⟮S.x⟯⟮S.y⟯) (hu0 : u0 ≠ 0) (hnc : ¬ ∃ c : C, (u0 : L) = algebraMap C L c)
    (hfin0 : ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u0).order = 0)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K ⟨f, hf⟩)
    {ι' : Type*} (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ κ ℓ : C, κ′ = 0 ∧ f = v′ + algebraMap C L κ * logDeriv (u0 : L) + algebraMap C L ℓ := by
  classical
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
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
  -- each `wⱼ` is a power of `u₀` up to a constant
  have hpow : ∀ jj < k, ∃ a b : ℤ, a ≠ 0 ∧ ∃ cj : C, cj ≠ 0 ∧
      (w jj) ^ a = algebraMap C L cj * (u0 : L) ^ b := by
    intro jj hjj
    have hw0 : (⟨w jj, (hww jj hjj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦
      (hww jj hjj).2 (congrArg Subtype.val h)
    obtain ⟨a, b, ha, cj, hcj⟩ := S.mem_pow_unit (Kb := K) k0 M hM hGm hGn hgeo ιF Fc hmon hSF Pc
      hPcd hn0 hfib1 hpl2 hα0 u0 hu0 hnc hfin0 _ hw0 fun a N hN l hl r hr ↦
        S.logs_zero_branchW ω hx hK k d' w hww hind' v f hv hf heq' a (hnd a) N
          (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (Or.inr (hreg a N hN l hl r hr)) jj hjj
    refine ⟨a, b, ha, cj, fun h0 ↦ ?_, hcj⟩
    rw [h0, map_zero, zero_mul] at hcj
    exact zpow_ne_zero a (hww jj hjj).2 hcj
  choose! a b ha cj hcj0 hcj using hpow
  have hu0L : (u0 : L) ≠ 0 := fun h ↦ hu0 (Subtype.ext h)
  have hlw : ∀ jj < k, (w jj)′ / w jj =
      (algebraMap C L ((cj jj)′ / cj jj) + (b jj : L) * logDeriv (u0 : L)) / (a jj : L) := by
    intro jj hjj
    have hw0 := (hww jj hjj).2
    have ha0 : (a jj : L) ≠ 0 := by exact_mod_cast ha jj hjj
    have h1 : logDeriv ((w jj) ^ a jj) = a jj * logDeriv (w jj) := logDeriv_zpow' (w jj) hw0 _
    have hc0 : algebraMap C L (cj jj) ≠ 0 := (map_ne_zero_iff _ (algebraMap C L).injective).mpr
      (hcj0 jj hjj)
    have h2 : logDeriv (algebraMap C L (cj jj) * (u0 : L) ^ b jj) =
        algebraMap C L ((cj jj)′ / cj jj) + b jj * logDeriv (u0 : L) := by
      rw [Differential.logDeriv_mul _ _ hc0 (zpow_ne_zero _ hu0L), logDeriv_zpow' _ hu0L, logDeriv,
        deriv_algebraMap, ← map_div₀]
    rw [hcj jj hjj, h2] at h1
    rw [← logDeriv, h1]
    field_simp
  refine ⟨∑ jj ∈ Finset.range k, d' jj * ((b jj : C) / (a jj : C)),
    ∑ jj ∈ Finset.range k, d' jj * (((cj jj)′ / cj jj) / (a jj : C)), ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun jj hjj ↦ ?_
    rw [Derivation.leibniz, hd'c jj (Finset.mem_range.mp hjj), smul_zero, add_zero, smul_eq_mul]
    have : ((b jj : C) / (a jj : C))′ = 0 := by
      rw [show ((b jj : C) / (a jj : C)) = (((b jj : ℚ) / (a jj : ℚ) : ℚ) : C) by push_cast; rfl]
      exact Differential.deriv_ratCast_K _
    rw [this, mul_zero]
  · rw [heq', add_assoc]
    congr 1
    rw [map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    have hj := Finset.mem_range.mp hjj
    have ha0 : (a jj : L) ≠ 0 := by exact_mod_cast ha jj hj
    rw [hlw jj hj]
    simp only [map_mul, map_div₀, map_intCast]
    field_simp
    ring

set_option maxHeartbeats 4000000 in
include hx hK in
/-- **A Liouville form has its logarithmic part in `∑ C uᵢ′/uᵢ + C`** (`m + 1` places at
infinity, `m` units multiplicatively independent modulo constants). -/
theorem nk_liouville_units (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (k0 M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k0 * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k0 M).Monic)
    (hGn : (invP (shiftP S.F 0) k0 M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (ιF : F →+* C) (Fc : BPoly F) (hmon : (toB Fc).Monic)
    (hSF : (mobCurve S 0 k0 M hM hGm hGn).F = (toB Fc).map (mapRingHom ιF))
    (Pc : PlaceCert F) (hPcd : Pc.Facts Fc (toB Fc).natDegree) (hn0 : 0 < (toB Fc).natDegree)
    (hfib1 : Pc.fib.length = 1) (hα0 : Pc.fα 0 = 0) {m : ℕ} (hpl : Pc.pl.length = m + 1)
    (u0 : Fin m → C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u0 i ≠ 0)
    (hfin0 : ∀ i (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u0 i)).order = 0)
    (hindU : ∀ a : Fin m → ℤ, (∃ c : C, ∏ i, (u0 i : L) ^ a i = algebraMap C L c) → a = 0)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K ⟨f, hf⟩)
    {ι' : Type*} (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (κ : Fin m → C) (ℓ : C), (∀ i, (κ i)′ = 0) ∧
      f = v′ + ∑ i, algebraMap C L (κ i) * logDeriv (u0 i : L) + algebraMap C L ℓ := by
  classical
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
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
  have hpow : ∀ jj < k, ∃ (N : ℤ) (a : Fin m → ℤ), N ≠ 0 ∧ ∃ cj : C, cj ≠ 0 ∧
      (w jj) ^ N = algebraMap C L cj * ∏ i, (u0 i : L) ^ a i := by
    intro jj hjj
    have hwne : (⟨w jj, (hww jj hjj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦
      (hww jj hjj).2 (congrArg Subtype.val h)
    obtain ⟨N, a, hN, cj, hcj⟩ := S.mem_pow_units (Kb := K) k0 M hM hGm hGn hgeo ιF Fc hmon hSF Pc
      hPcd hn0 hfib1 hα0 hpl u0 hu0 hfin0 hindU _ hwne fun a N hN l hl r hr ↦
        S.logs_zero_branchW ω hx hK k d' w hww hind' v f hv hf heq' a (hnd a) N
          (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (Or.inr (hreg a N hN l hl r hr)) jj hjj
    refine ⟨N, a, hN, cj, fun h0 ↦ ?_, hcj⟩
    rw [h0, map_zero, zero_mul] at hcj
    exact zpow_ne_zero N (hww jj hjj).2 hcj
  choose! N a hN cj hcj0 hcj using hpow
  have hu0L : ∀ i, (u0 i : L) ≠ 0 := fun i h ↦ hu0 i (Subtype.ext h)
  have hlw : ∀ jj < k, (w jj)′ / w jj =
      (algebraMap C L ((cj jj)′ / cj jj) + ∑ i, (a jj i : L) * logDeriv (u0 i : L)) / (N jj : L) := by
    intro jj hjj
    have hwj := (hww jj hjj).2
    have hN0 : (N jj : L) ≠ 0 := by exact_mod_cast hN jj hjj
    have h1 : logDeriv ((w jj) ^ N jj) = N jj * logDeriv (w jj) := logDeriv_zpow' (w jj) hwj _
    have hc0 : algebraMap C L (cj jj) ≠ 0 := (map_ne_zero_iff _ (algebraMap C L).injective).mpr
      (hcj0 jj hjj)
    have hpne : ∏ i, (u0 i : L) ^ a jj i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu0L i)
    have h2 : logDeriv (algebraMap C L (cj jj) * ∏ i, (u0 i : L) ^ a jj i) =
        algebraMap C L ((cj jj)′ / cj jj) + ∑ i, (a jj i : L) * logDeriv (u0 i : L) := by
      rw [Differential.logDeriv_mul _ _ hc0 hpne, Differential.logDeriv_prod _ _ _
        (fun i _ ↦ zpow_ne_zero _ (hu0L i)), logDeriv, deriv_algebraMap, ← map_div₀]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ logDeriv_zpow' _ (hu0L i) _
    rw [hcj jj hjj, h2] at h1
    rw [← logDeriv, h1]
    field_simp
  refine ⟨fun i ↦ ∑ jj ∈ Finset.range k, d' jj * ((a jj i : C) / (N jj : C)),
    ∑ jj ∈ Finset.range k, d' jj * (((cj jj)′ / cj jj) / (N jj : C)), fun i ↦ ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun jj hjj ↦ ?_
    rw [Derivation.leibniz, hd'c jj (Finset.mem_range.mp hjj), smul_zero, add_zero, smul_eq_mul]
    have : ((a jj i : C) / (N jj : C))′ = 0 := by
      rw [show ((a jj i : C) / (N jj : C)) = (((a jj i : ℚ) / (N jj : ℚ) : ℚ) : C) by push_cast; rfl]
      exact Differential.deriv_ratCast_K _
    rw [this, mul_zero]
  · rw [heq', add_assoc]
    congr 1
    simp only [map_sum, map_mul, map_div₀, map_intCast]
    rw [Finset.sum_congr rfl fun jj hjj ↦ by rw [hlw jj (Finset.mem_range.mp hjj)]]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    have hN0 : (N jj : L) ≠ 0 := by exact_mod_cast hN jj (Finset.mem_range.mp hjj)
    field_simp
    have e : ∀ i, (N jj : L) * (algebraMap C L (d' jj) * (a jj i : L) * logDeriv (u0 i : L) /
        (N jj : L)) = algebraMap C L (d' jj) * ((a jj i : L) * logDeriv (u0 i : L)) := fun i ↦ by
      field_simp
    rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ ↦ e i, ← Finset.mul_sum, map_div₀]
    ring

end CurveData

end Curves
