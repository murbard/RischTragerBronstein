import RischTragerBronstein.Mixed.KPTower

/-!
# `B(x) yʲ` over a differential base: a Liouville form forces exactness

**`kp_liouville`**: `S : SuperData C L` with `x′ = η ∈ C`, `η` without antiderivative in the
algebraic closure `K` of `C`, `gcd(n, deg p) = 1`, `C` containing all the constants of `L`. If
`b yʲ = v′ + ∑ cᵢ uᵢ′/uᵢ` (`b ∈ C(x)`, `0 < j < n`, `b yʲ` without poles at the finite places,
constant `cᵢ`, all in `C(x, y)`), then `b yʲ = (a yʲ)′` for some `a ∈ C(x)`.

The constants are made `ℚ`-independent (`logSum_qindep`), the logarithms lie in `C`
(`logs_in_base`), and the `yʲ`-coordinate of `v` is the antiderivative (`exact_of_log_in_base`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L) (η : C) (hx : S.x′ = algebraMap C L η)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **A Liouville form for `b yʲ` forces `b yʲ = (a yʲ)′`.** -/
theorem kp_liouville (hnd : ∀ α : K, α′ ≠ algebraMap C K η)
    (hcop : Nat.Coprime S.n S.p.natDegree)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (j : ℕ) (hj0 : 0 < j) (hjn : j < S.n) (b : L) (hb : b ∈ C⟮S.x⟯)
    (hbm : b * S.y ^ j ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.IsIntegralS K ⟨b * S.y ^ j, hbm⟩)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ j = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, b * S.y ^ j = (a * S.y ^ j)′ := by
  classical
  -- `ℚ`-independent constants
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd jj hjj))
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hw' : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : b * S.y ^ j = v′ + ∑ jj ∈ Finset.range k,
      algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  -- the logarithms lie in `C`
  have hbase := S.logs_in_base η hx hK hnd hcop k d' w hw' hind' v _ hv hbm heq' hreg
  choose! e he using hbase
  -- the logarithmic part is a constant of `C`
  set ℓ : C := ∑ jj ∈ Finset.range k, d' jj * logDeriv (e jj) with hℓ
  have hlog : ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) =
      algebraMap C L ℓ := by
    rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [he jj (Finset.mem_range.mp hjj), map_mul, ← logDeriv, logDeriv_algebraMap]
  rw [hlog] at heq'
  exact S.exact_of_log_in_base η hx j hj0 hjn b hb v hv ℓ heq'

end SuperData

end Differential
