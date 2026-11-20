import RischTragerBronstein.Mixed.NKExp0
import RischTragerBronstein.Mixed.NKTorsion

/-!
# Liouville forms over an exponential level

For `x′ = η x` (an exponential level) on a curve with a single place at infinity **and** a single
place above `x = 0`, every function `u` without zeros and poles above `x ≠ 0` satisfies
`uⁿ = c xᵏ` with `c ∈ C` (`unit_pow_exp`): its order along every branch above `0` is the same
(`eval_order_zero`), so `uⁿ x⁻ᵏ` is a unit at every finite place, hence a constant. Hence the
logarithmic part of a Liouville form for an integrand without finite poles lies in `C`
(`nk_liouvilleE`): `u′/u = (c′/c + κ η)/n`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

set_option linter.unusedSectionVars false

namespace Curves

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L)

/-- **Units outside `x = 0` are `c xᵏ` up to an `n`-th power.** -/
theorem unit_pow_exp (n dd d0 : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = dd)
    (hw' : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < dd * (n - i))
    (hcop : Nat.Coprime n dd) (hd0 : (S.F.coeff 0).natTrailingDegree = d0)
    (hw0 : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨
      d0 * (n - i) < n * (S.F.coeff i).natTrailingDegree)
    (hcop0 : Nat.Coprime n d0) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hfin : ∀ (a : K), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u).order = 0) :
    ∃ (κ : ℤ) (c : C), (u : L) ^ n = algebraMap C L c * S.x ^ κ := by
  classical
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt u hF1
  have hxQ : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
  have hW0 : W ≠ 0 := fun h ↦ by
    have : (u : L) * aeval S.x Q = 0 := by rw [hWQ, h]; simp [CurveData.evXY]
    exact mul_ne_zero (fun h' ↦ hu (Subtype.ext h')) hxQ this
  set κ : ℤ := (wt0W n d0 W : ℤ) - n * Q.natTrailingDegree with hκ
  set X0 : C⟮S.x⟯⟮S.y⟯ := S.polyF (X - Polynomial.C 0) with hX0
  have hX00 : X0 ≠ 0 := fun h ↦ by
    have := congrArg Subtype.val h
    rw [hX0, S.coe_polyF] at this
    exact (X_sub_C_ne_zero (0 : C)) ((transcendental_iff.mp S.htr) _ this)
  have hX0v : (X0 : L) = S.x := by rw [hX0, S.coe_polyF]; simp
  set z : C⟮S.x⟯⟮S.y⟯ := u ^ n * X0 ^ (-κ) with hz
  have hz0 : z ≠ 0 := mul_ne_zero (pow_ne_zero _ hu) (zpow_ne_zero _ hX00)
  have hzo : ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) z).order = 0 := by
    intro a N hN l hl r hr
    have hNp := Nat.pos_of_ne_zero hN
    set φ := S.embG (branchSub N a) (branchSub_injective N hNp a) r (S.root_of_mem hl hr)
    have hu' : φ u ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr hu
    have hX' : φ X0 ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr hX00
    have hXo := S.order_xsub (0 : C) a N hNp r (S.root_of_mem hl hr)
    rw [hz, map_mul, map_pow, map_zpow₀, HahnSeries.order_mul (pow_ne_zero _ hu')
      (zpow_ne_zero _ hX'), HahnSeries.order_pow, order_zpow_nk _ hX', nsmul_eq_mul]
    change (n : ℤ) * (φ u).order + -κ * (φ X0).order = 0
    rw [show φ X0 = S.embG (branchSub N a) (branchSub_injective N hNp a) r (S.root_of_mem hl hr)
      (S.polyF (X - Polynomial.C 0)) from rfl, hXo]
    by_cases ha : a = 0
    · subst ha
      rw [if_pos (by rw [map_zero])]
      -- `n ord u = N κ` above `0`
      have hrel := S.eval_W_branch (branchSub N 0) (branchSub_injective N hNp 0) r
        (S.root_of_mem hl hr) u W Q hWQ
      have hev := eval_order_zero (K := K) S.F S.monic n d0 N hn hn0 hNp ha0 hd0 hw0 hcop0 r
        (S.root_of_mem hl hr) W hW0 (by rw [← hn]; exact hWn)
      have hQo := order_branchSub_zero (K := K) N hNp Q hQ
      rw [hrel, HahnSeries.order_mul hu' (branchSub_zero_ne_zero N hNp Q hQ), hQo] at hev
      have hev2 := hev.2
      rw [hκ]
      push_cast at hev2 ⊢
      have hNp' : (0 : ℤ) < N := by exact_mod_cast hNp
      nlinarith
    · rw [if_neg (by rw [map_zero]; exact ha), hfin a ha N hN l hl r hr]
      ring
  obtain ⟨c, hc⟩ := S.mem_const_of_unit_inf (K := K) n dd hn hn0 ha0 hd hw' hcop z hz0 hzo
  refine ⟨κ, c, ?_⟩
  have hx0 : S.x ≠ 0 := by rw [← hX0v]; exact fun h ↦ hX00 (Subtype.ext h)
  have e : (z : L) = (u : L) ^ n * S.x ^ (-κ) := by
    rw [hz, IntermediateField.coe_mul, IntermediateField.coe_pow,
      show ((X0 ^ (-κ) : C⟮S.x⟯⟮S.y⟯) : L) = (X0 : L) ^ (-κ) from
        map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val X0 (-κ), hX0v]
  rw [← hc, e, mul_assoc, ← zpow_add₀ hx0, neg_add_cancel, zpow_zero, mul_one]

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **A Liouville form over an exponential level has its logarithmic part in the base**
(single places above `0` and `∞`, no finite poles above `x ≠ 0`). -/
theorem nk_liouvilleE (η : C) (hω : ω = Polynomial.C η * X)
    (hnd : ∀ a : K, a ≠ 0 → a′ ≠ (ω.map (algebraMap C K)).eval a)
    (n dd d0 : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = dd)
    (hw' : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < dd * (n - i))
    (hcop : Nat.Coprime n dd) (hd0 : (S.F.coeff 0).natTrailingDegree = d0)
    (hw0 : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨
      d0 * (n - i) < n * (S.F.coeff i).natTrailingDegree)
    (hcop0 : Nat.Coprime n d0)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (hres : ∀ (a : K), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l) (k : ℤ), k < 1 - (N : ℤ) →
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) ⟨f, hf⟩).coeff k = 0)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ ℓ : C, f = v′ + algebraMap C L ℓ := by
  classical
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dite_cond_eq_true (eq_true hjj)]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
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
  -- each `wⱼ` is `c xᵏ` up to an `n`-th power
  have hpow : ∀ jj < k, ∃ (κ : ℤ) (cj : C), cj ≠ 0 ∧
      (w jj) ^ n = algebraMap C L cj * S.x ^ κ := by
    intro jj hjj
    have hu0 : (⟨w jj, (hww jj hjj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦
      (hww jj hjj).2 (congrArg Subtype.val h)
    obtain ⟨κ, cj, hcj⟩ := S.unit_pow_exp (K := K) n dd d0 hn hn0 ha0 hd hw' hcop hd0 hw0 hcop0 _
      hu0 fun a ha N hN l hl r hr ↦ S.logs_zero_branchR ω hx hK k d' w hww hind' v f hv hf heq' a
        (hnd a ha) N (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (hres a ha N hN l hl r hr)
        jj hjj
    refine ⟨κ, cj, fun h0 ↦ ?_, hcj⟩
    rw [h0, map_zero, zero_mul] at hcj
    exact (hww jj hjj).2 (pow_eq_zero_iff (by omega) |>.mp hcj)
  choose! κ cj hcj0 hcj using hpow
  have hx0 : S.x ≠ 0 := fun h ↦ S.htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  have hlx : logDeriv S.x = algebraMap C L η := by
    rw [logDeriv, hx, hω, map_mul, aeval_C, aeval_X, mul_div_assoc, div_self hx0, mul_one]
  have hlw : ∀ jj < k, (w jj)′ / w jj =
      algebraMap C L (((cj jj)′ / cj jj + κ jj * η) / n) := by
    intro jj hjj
    have hw0 := (hww jj hjj).2
    have hn0' : (n : L) ≠ 0 := by exact_mod_cast hn0.ne'
    have h1 : logDeriv ((w jj) ^ n) = n * logDeriv (w jj) := by
      have := logDeriv_zpow' (w jj) hw0 (n : ℤ); simpa using this
    have h2 : logDeriv (algebraMap C L (cj jj) * S.x ^ κ jj) =
        algebraMap C L ((cj jj)′ / cj jj) + κ jj * algebraMap C L η := by
      have hc0 : algebraMap C L (cj jj) ≠ 0 := (map_ne_zero_iff _ (algebraMap C L).injective).mpr
        (hcj0 jj hjj)
      rw [Differential.logDeriv_mul _ _ hc0 (zpow_ne_zero _ hx0), logDeriv_zpow' _ hx0, hlx, logDeriv,
        deriv_algebraMap, ← map_div₀]
    rw [hcj jj hjj, h2] at h1
    rw [← logDeriv, map_div₀, map_add, map_mul, map_intCast, map_natCast]
    field_simp
    linear_combination -h1
  refine ⟨∑ jj ∈ Finset.range k, d' jj * (((cj jj)′ / cj jj + κ jj * η) / n), ?_⟩
  rw [heq', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun jj hjj ↦ ?_
  rw [hlw jj (Finset.mem_range.mp hjj), map_mul]

end CurveData

end Curves
