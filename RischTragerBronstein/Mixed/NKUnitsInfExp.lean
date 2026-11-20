import RischTragerBronstein.Mixed.NKInfRUnitExp
import RischTragerBronstein.Mixed.NKUnitsInf

/-!
# Several places at infinity over an exponential level, any curve split at infinity

`unit_pow_expU_inf`, `nk_liouvilleEU_inf`: as `unit_pow_expU`, `nk_liouvilleEU`, with the place
certificate on the inverted curve replaced by a branch system above infinity with `mu + 1` roots
(`mem_pow_units_inf`), so that they apply to curves with non-constant coefficients.
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

/-- **Units outside `x = 0` are `c xᵏ ∏ u₀ᵢ^{bᵢ/a}` up to an `n`-th power** (several places at
infinity, independent units `u₀ᵢ`). -/
theorem unit_pow_expU_span (n d0 : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0)
    {mu : ℕ} (u0 : Fin mu → C⟮S.x⟯⟮S.y⟯) (hspan : S.UnitsSpan K u0) (hu0 : ∀ i, u0 i ≠ 0)
    (hfin0 : ∀ i (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u0 i)).order = 0)
    (hindU : ∀ a : Fin mu → ℤ, (∃ c : C, ∏ i, (u0 i : L) ^ a i = algebraMap C L c) → a = 0)
    (hd0 : (S.F.coeff 0).natTrailingDegree = d0)
    (hw0 : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨
      d0 * (n - i) < n * (S.F.coeff i).natTrailingDegree)
    (hcop0 : Nat.Coprime n d0) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hfin : ∀ (a : K), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u).order = 0) :
    ∃ (κ a : ℤ) (b : Fin mu → ℤ), a ≠ 0 ∧ ∃ c : C,
      ((u : L) ^ n * S.x ^ (-κ)) ^ a = algebraMap C L c * ∏ i, (u0 i : L) ^ b i := by
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
  obtain ⟨a, b, ha, c, hc⟩ := hspan z hz0 hzo
  refine ⟨κ, a, b, ha, c, ?_⟩
  have e : (z : L) = (u : L) ^ n * S.x ^ (-κ) := by
    rw [hz, IntermediateField.coe_mul, IntermediateField.coe_pow,
      show ((X0 ^ (-κ) : C⟮S.x⟯⟮S.y⟯) : L) = (X0 : L) ^ (-κ) from
        map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val X0 (-κ), hX0v]
  rw [← e, hc]

/-- **Units outside `x = 0` are `c xᵏ ∏ u₀ᵢ^{bᵢ/a}` up to an `n`-th power** (several places at
infinity, independent units `u₀ᵢ`). -/
theorem unit_pow_expU_inf (n d0 : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
    (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod)
    {mu : ℕ} (hlen : S.F.natDegree = mu + 1)
    (u0 : Fin mu → C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u0 i ≠ 0)
    (hfin0 : ∀ i (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u0 i)).order = 0)
    (hindU : ∀ a : Fin mu → ℤ, (∃ c : C, ∏ i, (u0 i : L) ^ a i = algebraMap C L c) → a = 0)
    (hd0 : (S.F.coeff 0).natTrailingDegree = d0)
    (hw0 : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨
      d0 * (n - i) < n * (S.F.coeff i).natTrailingDegree)
    (hcop0 : Nat.Coprime n d0) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hfin : ∀ (a : K), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u).order = 0) :
    ∃ (κ a : ℤ) (b : Fin mu → ℤ), a ≠ 0 ∧ ∃ c : C,
      ((u : L) ^ n * S.x ^ (-κ)) ^ a = algebraMap C L c * ∏ i, (u0 i : L) ^ b i :=
  S.unit_pow_expU_span n d0 hn hn0 ha0 u0
    (S.unitsSpan_inf hgeo Ni hNi li hli hlen u0 hu0 hfin0 hindU) hu0 hfin0 hindU hd0 hw0 hcop0 u hu hfin

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

set_option maxHeartbeats 4000000 in
include hx hK in
/-- **A Liouville form over an exponential level has its logarithmic part in `∑ C u₀ᵢ′/u₀ᵢ + C`**
(several places at infinity with independent units `u₀ᵢ`, a single place above `0`). -/
theorem nk_liouvilleEU_span (η : C) (hω : ω = Polynomial.C η * X)
    (hnd : ∀ a : K, a ≠ 0 → a′ ≠ (ω.map (algebraMap C K)).eval a)
    (n d0 : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0)
    {mu : ℕ} (u0 : Fin mu → C⟮S.x⟯⟮S.y⟯) (hspan : S.UnitsSpan K u0) (hu0 : ∀ i, u0 i ≠ 0)
    (hfin0 : ∀ i (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u0 i)).order = 0)
    (hindU : ∀ a : Fin mu → ℤ, (∃ c : C, ∏ i, (u0 i : L) ^ a i = algebraMap C L c) → a = 0)
    (hd0 : (S.F.coeff 0).natTrailingDegree = d0)
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
  have hpow : ∀ jj < k, ∃ (κ a : ℤ) (b : Fin mu → ℤ), a ≠ 0 ∧ ∃ cj : C, cj ≠ 0 ∧
      ((w jj) ^ n * S.x ^ (-κ)) ^ a = algebraMap C L cj * ∏ i, (u0 i : L) ^ b i := by
    intro jj hjj
    have hwne : (⟨w jj, (hww jj hjj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦
      (hww jj hjj).2 (congrArg Subtype.val h)
    obtain ⟨κ, a, b, ha, cj, hcj⟩ := S.unit_pow_expU_span (K := K) n d0 hn hn0 ha0
      u0 hspan hu0 hfin0 hindU hd0 hw0 hcop0 _ hwne
      fun a ha N hN l hl r hr ↦ S.logs_zero_branchR ω hx hK k d' w hww hind' v f hv hf heq' a
        (hnd a ha) N (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (hres a ha N hN l hl r hr)
        jj hjj
    have hx0 : S.x ≠ 0 := fun h ↦ S.htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
    refine ⟨κ, a, b, ha, cj, fun h0 ↦ ?_, hcj⟩
    rw [h0, map_zero, zero_mul] at hcj
    exact zpow_ne_zero a (mul_ne_zero (pow_ne_zero _ (hww jj hjj).2) (zpow_ne_zero _ hx0)) hcj
  choose! κ a b ha cj hcj0 hcj using hpow
  have hx0 : S.x ≠ 0 := fun h ↦ S.htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  have hu0L : ∀ i, (u0 i : L) ≠ 0 := fun i h ↦ hu0 i (Subtype.ext h)
  have hlx : logDeriv S.x = algebraMap C L η := by
    rw [logDeriv, hx, hω, map_mul, aeval_C, aeval_X, mul_div_assoc, div_self hx0, mul_one]
  have hn0L : (n : L) ≠ 0 := by exact_mod_cast hn0.ne'
  have hlprod : ∀ bb : Fin mu → ℤ, logDeriv (∏ i, (u0 i : L) ^ bb i) =
      ∑ i, (bb i : L) * logDeriv (u0 i : L) := by
    intro bb
    rw [logDeriv, logDeriv_finset_prod _ _ (fun i _ ↦ zpow_ne_zero _ (hu0L i))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := logDeriv_zpow' (u0 i : L) (hu0L i) (bb i)
    simp only [logDeriv] at this ⊢
    exact this
  have hlw : ∀ jj < k, (w jj)′ / w jj =
      ((algebraMap C L ((cj jj)′ / cj jj) + ∑ i, (b jj i : L) * logDeriv (u0 i : L)) / (a jj : L) +
        κ jj * algebraMap C L η) / n := by
    intro jj hjj
    have hwj := (hww jj hjj).2
    have ha0' : (a jj : L) ≠ 0 := by exact_mod_cast ha jj hjj
    have hz0 : (w jj) ^ n * S.x ^ (-κ jj) ≠ 0 := mul_ne_zero (pow_ne_zero _ hwj) (zpow_ne_zero _ hx0)
    have h1 : logDeriv (((w jj) ^ n * S.x ^ (-κ jj)) ^ a jj) =
        a jj * (n * logDeriv (w jj) - κ jj * algebraMap C L η) := by
      rw [logDeriv_zpow' _ hz0, Differential.logDeriv_mul _ _ (pow_ne_zero _ hwj)
        (zpow_ne_zero _ hx0), logDeriv_zpow' _ hx0, hlx]
      have := logDeriv_zpow' (w jj) hwj (n : ℤ)
      simp only [zpow_natCast] at this
      rw [this]; push_cast; ring
    have hc0 : algebraMap C L (cj jj) ≠ 0 := (map_ne_zero_iff _ (algebraMap C L).injective).mpr
      (hcj0 jj hjj)
    have hpne : ∏ i, (u0 i : L) ^ b jj i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu0L i)
    have h2 : logDeriv (algebraMap C L (cj jj) * ∏ i, (u0 i : L) ^ b jj i) =
        algebraMap C L ((cj jj)′ / cj jj) + ∑ i, (b jj i : L) * logDeriv (u0 i : L) := by
      rw [Differential.logDeriv_mul _ _ hc0 hpne, hlprod, logDeriv, deriv_algebraMap, ← map_div₀]
    rw [hcj jj hjj, h2] at h1
    rw [← logDeriv]
    field_simp
    linear_combination -h1
  refine ⟨fun i ↦ ∑ jj ∈ Finset.range k, d' jj * ((b jj i : C) / ((a jj : C) * n)),
    ∑ jj ∈ Finset.range k, d' jj * ((((cj jj)′ / cj jj) / (a jj : C) + κ jj * η) / n), ?_, ?_⟩
  · intro i
    rw [map_sum]
    refine Finset.sum_eq_zero fun jj hjj ↦ ?_
    rw [Derivation.leibniz, hd'c jj (Finset.mem_range.mp hjj), smul_zero, add_zero, smul_eq_mul]
    have : ((b jj i : C) / ((a jj : C) * n))′ = 0 := by
      rw [show ((b jj i : C) / ((a jj : C) * n)) = (((b jj i : ℚ) / ((a jj : ℚ) * n) : ℚ) : C) by
        push_cast; rfl]
      exact Differential.deriv_ratCast_K _
    rw [this, mul_zero]
  · rw [heq', add_assoc]
    congr 1
    have e : ∀ i, algebraMap C L (∑ jj ∈ Finset.range k, d' jj * ((b jj i : C) / ((a jj : C) * n))) *
        logDeriv (u0 i : L) = ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) / ((a jj : L) * n) *
          ((b jj i : L) * logDeriv (u0 i : L)) := by
      intro i
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun jj _ ↦ ?_
      simp only [map_mul, map_div₀, map_intCast, map_natCast]
      ring
    simp only [e]
    rw [Finset.sum_comm, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    have hj := Finset.mem_range.mp hjj
    have ha0 : (a jj : L) ≠ 0 := by exact_mod_cast ha jj hj
    rw [hlw jj hj, ← Finset.mul_sum]
    simp only [map_mul, map_div₀, map_intCast, map_add, map_natCast]
    field_simp
    ring

set_option maxHeartbeats 4000000 in
include hx hK in
/-- **A Liouville form over an exponential level has its logarithmic part in `∑ C u₀ᵢ′/u₀ᵢ + C`**
(several places at infinity with independent units `u₀ᵢ`, a single place above `0`). -/
theorem nk_liouvilleEU_inf (η : C) (hω : ω = Polynomial.C η * X)
    (hnd : ∀ a : K, a ≠ 0 → a′ ≠ (ω.map (algebraMap C K)).eval a)
    (n d0 : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
    (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod)
    {mu : ℕ} (hlen : S.F.natDegree = mu + 1)
    (u0 : Fin mu → C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u0 i ≠ 0)
    (hfin0 : ∀ i (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u0 i)).order = 0)
    (hindU : ∀ a : Fin mu → ℤ, (∃ c : C, ∏ i, (u0 i : L) ^ a i = algebraMap C L c) → a = 0)
    (hd0 : (S.F.coeff 0).natTrailingDegree = d0)
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
    {ι' : Type*} (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (κ : Fin mu → C) (ℓ : C), (∀ i, (κ i)′ = 0) ∧
      f = v′ + ∑ i, algebraMap C L (κ i) * logDeriv (u0 i : L) + algebraMap C L ℓ :=
  S.nk_liouvilleEU_span ω hx hK η hω hnd n d0 hn hn0 ha0 u0
    (S.unitsSpan_inf hgeo Ni hNi li hli hlen u0 hu0 hfin0 hindU) hu0 hfin0 hindU hd0 hw0 hcop0
    hconstC f hf hres s c u hc hu v hv heq

end CurveData

end Curves
