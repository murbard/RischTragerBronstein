import RischTragerBronstein.Mixed.NKNormUnit

/-!
# The residue divisor of an elementary integrand is principal

`exists_unit_of_residues`: for a Liouville form `f = v′ + ∑ cᵢ uᵢ′/uᵢ` (`f` regular at the finite
places) whose residues at the places at infinity are the rationals `ρ_r`, there are `M > 0` and
a unit `w` (no zeros or poles at the finite places) with `ord_r w = M N ρ_r` along every branch
`r` above infinity: the residue divisor is `ℚ`-principal. (Write `f` with `ℚ`-independent
coefficients `dⱼ` and logarithms `wⱼ`; the residue identity `∑ dⱼ ord wⱼ = N ρ` holds by
uniqueness of residues, and a `ℚ`-linear form `λ` with `λ(1) = 1` gives
`∑ λ(dⱼ) ord wⱼ = N ρ`.) This is the input of the non-torsion arguments.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L) (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **The residue divisor of an elementary integrand is `ℚ`-principal.** -/
theorem exists_unit_of_residues (hnd : ∀ a : K, a′ ≠ algebraMap C K η)
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
    (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K ⟨f, hf⟩)
    (ρ : LaurentSeries K → ℚ)
    (hρ : ∀ r (hr : r ∈ li), ∃ γ : K, (S.embG (infSub Ni) (infSub_injective Ni hNi) r
      (S.root_of_mem hli hr) ⟨f, hf⟩).coeff (Ni : ℤ) + (ρ r : K) * algebraMap C K η = γ′)
    {ι' : Type*} [DecidableEq ι'] (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (Mden : ℕ) (_ : 0 < Mden) (w : C⟮S.x⟯⟮S.y⟯), w ≠ 0 ∧ S.UnitFin K w ∧
      ∀ r (hr : r ∈ li), ((S.embG (infSub Ni) (infSub_injective Ni hNi) r (S.root_of_mem hli hr)
        w).order : ℚ) = Mden * Ni * ρ r := by
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
  have hgoodη : ∀ a : K, a′ ≠ ((Polynomial.C η).map (algebraMap C K)).eval a := fun a ↦ by
    rw [Polynomial.map_C, eval_C]; exact hnd a
  have hfinw : ∀ jj (hjj : jj < k), S.UnitFin K ⟨w jj, (hww jj hjj).1⟩ :=
    fun jj hjj a N hN l hl r hr ↦
      S.logs_zero_branchW (Polynomial.C η) hx hK k d' w hww hind' v f hv hf heq' a (hgoodη a) N
        (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (Or.inr (hreg a N hN l hl r hr)) jj hjj
  -- a `ℚ`-linear form with `λ(1) = 1`
  have hinjQ : Function.Injective (algebraMap ℚ C) := (algebraMap ℚ C).injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ C)
    (LinearMap.ker_eq_bot.mpr hinjQ)
  have hg1 : ∀ q : ℚ, g (q : C) = q := fun q ↦ by
    have := congrArg (fun φ : ℚ →ₗ[ℚ] ℚ ↦ φ q) hg
    simpa using this
  set κ : ℕ → ℚ := fun jj ↦ g (d' jj) with hκ
  -- the common denominator
  set Mden : ℕ := ∏ jj ∈ Finset.range k, (κ jj).den with hMden
  have hM0 : 0 < Mden := Finset.prod_pos fun jj _ ↦ (κ jj).den_pos
  have hint : ∀ jj ∈ Finset.range k, ∃ n : ℤ, (n : ℚ) = κ jj * Mden := by
    intro jj hjj
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun jj ↦ (κ jj).den) hjj
    refine ⟨(κ jj).num * m, ?_⟩
    rw [hMden, hm]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  choose! nn hnn using hint
  set W : C⟮S.x⟯⟮S.y⟯ := ∏ jj ∈ Finset.range k, (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1) ^
    nn jj with hW
  have hne : ∀ jj ∈ Finset.range k, (if h : jj < k then (⟨w jj, (hww jj h).1⟩ : C⟮S.x⟯⟮S.y⟯)
      else 1) ≠ 0 := fun jj hjj ↦ by
    rw [dif_pos (Finset.mem_range.mp hjj)]
    exact fun h0 ↦ (hww jj (Finset.mem_range.mp hjj)).2 (congrArg Subtype.val h0)
  have hW0 : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun jj hjj ↦ zpow_ne_zero _ (hne jj hjj)
  refine ⟨Mden, hM0, W, hW0, ?_, fun r hr ↦ ?_⟩
  · -- `W` is a unit at the finite places
    intro a N hN l hl r hr
    rw [hW, S.order_prod_zpow _ _ _ hne]
    refine Finset.sum_eq_zero fun jj hjj ↦ ?_
    rw [dif_pos (Finset.mem_range.mp hjj), hfinw jj (Finset.mem_range.mp hjj) a N hN l hl r hr,
      mul_zero]
  · -- the orders at infinity
    obtain ⟨γ, hγ⟩ := hρ r hr
    set φ := S.embG (infSub Ni) (infSub_injective Ni hNi) r (S.root_of_mem hli hr) with hφ
    obtain ⟨β, hβ⟩ := S.coeff_liouville_top η hx hK Ni hNi r (S.root_of_mem hli hr)
      (Finset.range k) d' (fun jj hjj ↦ hd'c jj (Finset.mem_range.mp hjj))
      (fun jj ↦ if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1) (fun jj hjj ↦ hne jj hjj)
      ⟨v, hv⟩ ⟨f, hf⟩ (by
        show f = _
        rw [heq']
        congr 1
        refine Finset.sum_congr rfl fun jj hjj ↦ ?_
        rw [dif_pos (Finset.mem_range.mp hjj)])
    set o : ℕ → ℤ := fun jj ↦ (φ (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)).order with ho
    -- residue uniqueness: `∑ d'ⱼ oⱼ / N = ρ`
    set ρK : K := (∑ jj ∈ Finset.range k, algebraMap C K (d' jj) * (o jj : K)) / Ni with hρK
    have hρK' : ρK′ = 0 := by
      have hn : ((Ni : K))′ = 0 := Derivation.map_natCast _ _
      rw [hρK, Derivation.leibniz_div, map_sum, hn]
      have h1 : ∀ jj ∈ Finset.range k, (algebraMap C K (d' jj) * (o jj : K))′ = 0 := fun jj hjj ↦ by
        rw [Derivation.leibniz, hK, hd'c jj (Finset.mem_range.mp hjj), map_zero,
          Derivation.map_intCast]
        simp
      rw [Finset.sum_eq_zero h1]
      simp
    have hρq : ((ρ r : ℚ) : K)′ = 0 := deriv_ratCast_K _
    have huniq := residue_unique η hnd γ β ρK (ρ r : K) hρK' hρq (by rw [← hγ, ← hβ, hρK]; ring)
    -- in `C`: `∑ d'ⱼ oⱼ = N ρ`
    have hC : ∑ jj ∈ Finset.range k, d' jj * (o jj : C) = ((Ni * ρ r : ℚ) : C) := by
      apply (algebraMap C K).injective
      rw [map_sum, map_ratCast]
      have hN0 : (Ni : K) ≠ 0 := by exact_mod_cast hNi.ne'
      have := huniq
      rw [hρK, div_eq_iff hN0] at this
      push_cast
      rw [mul_comm (Ni : K), ← this]
      refine Finset.sum_congr rfl fun jj _ ↦ ?_
      simp [map_intCast]
    -- apply `λ`
    have hgsum := congrArg g hC
    rw [map_sum, hg1] at hgsum
    have hterm : ∀ jj ∈ Finset.range k, g (d' jj * (o jj : C)) = κ jj * o jj := fun jj _ ↦ by
      rw [show d' jj * (o jj : C) = ((o jj : ℚ)) • d' jj by
        rw [Rat.smul_def]; push_cast; ring, map_smul, smul_eq_mul, hκ]
      ring
    rw [Finset.sum_congr rfl hterm] at hgsum
    -- the order of `W`
    have hord : (φ W).order = ∑ jj ∈ Finset.range k, nn jj * o jj := by
      rw [hW, S.order_prod_zpow _ _ _ hne]
    rw [hord]
    push_cast
    rw [Finset.sum_congr rfl fun jj hjj ↦ by rw [hnn jj hjj]]
    rw [show ∑ jj ∈ Finset.range k, κ jj * (Mden : ℚ) * (o jj : ℚ) =
      (Mden : ℚ) * ∑ jj ∈ Finset.range k, κ jj * (o jj : ℚ) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, hgsum]
    ring

end CurveData

end Curves
