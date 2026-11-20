import RischTragerBronstein.Mixed.NKInf2

/-!
# Two places at infinity: the unit group

When `P₁ − P₂` is torsion there are non-constant units. Given one, `u₀`, every unit `w` at the
finite places satisfies `wᵃ = c u₀ᵇ` with `a ≠ 0` (`mem_pow_unit`): on the inverted curve the
orders of units along the roots above `x′ = 0` are constant on the two places and sum to `0`, so
one order determines all (`fibre_orders_zero_of_one`); `wᵃ u₀⁻ᵇ` with `a, b` the orders of
`u₀, w` along one root then has no zero or pole, hence is a constant.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential GTors CPoly Sup

section Unit

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

set_option maxHeartbeats 8000000 in
/-- **One vanishing order on the fibre forces all**: a function with order `0` outside the fibre
above `α` (with two places, `PlaceCert` facts) and order `0` along one certified root has order
`0` along every branch above `α`. -/
theorem fibre_orders_zero_of_one (S2 : CurveData C L) (ι : F →+* C) (Fc : BPoly F)
    (hmon : (toB Fc).Monic) (hSF : S2.F = (toB Fc).map (mapRingHom ι))
    (Pc : PlaceCert F) (hPcd : Pc.Facts Fc (toB Fc).natDegree) (hn0 : 0 < (toB Fc).natDegree)
    (hfib1 : Pc.fib.length = 1) (hpl2 : Pc.pl.length = 2)
    (z : C⟮S2.x⟯⟮S2.y⟯) (hz : z ≠ 0)
    (hother : ∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S2.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S2.root_of_mem hl hr) z).order = 0)
    (hinf : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S2.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (infSub N)
        (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S2.root_of_mem hl hr) z).order = 0)
    (k₀ : ℕ) (hk₀ : k₀ < S2.F.natDegree) (hN0 : 0 < Pc.fN 0)
    (hz₀ : ∀ hr : (S2.F.map (branchSub (Pc.fN 0) (algebraMap C Kb (ι (Pc.fα 0))))).eval
      (lmap (algebraMap C Kb) (rCC ι Fc Pc 0 k₀)) = 0,
      (S2.embG (branchSub (Pc.fN 0) (algebraMap C Kb (ι (Pc.fα 0))))
        (branchSub_injective _ hN0 _) _ hr z).order = 0) :
    ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S2.F.map (branchSub N (algebraMap C Kb (ι (Pc.fα 0)))) =
        (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (branchSub N (algebraMap C Kb (ι (Pc.fα 0))))
        (branchSub_injective N (Nat.pos_of_ne_zero hN) _) r (S2.root_of_mem hl hr) z).order = 0 := by
  classical
  have hnS : S2.F.natDegree = (toB Fc).natDegree := by rw [hSF, hmon.natDegree_map]
  have hn' : (toB Fc).natDegree = S2.F.natDegree := hnS.symm
  have hPcF := hPcd
  have hNpos : ∀ j : Fin Pc.fib.length, 0 < Pc.fN j := fun j ↦ PlaceCert.fN_pos hPcd hn0 j j.2
  have hspC := fun j : Fin Pc.fib.length ↦ split_places_map S2 ι Fc hmon hSF Pc hPcd j j.2
  have hlf : ∀ j : Fin Pc.fib.length,
      S2.F.map (branchSub (Pc.fN j) (algebraMap C Kb (ι (Pc.fα j)))) =
      ((List.ofFn fun k : Fin S2.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ι Fc Pc j k)).map
        fun r ↦ X - Polynomial.C r).prod := fun j ↦
    S2.split_lmap (K := Kb) (Pc.fN j) (ι (Pc.fα j)) (fun k ↦ rCC ι Fc Pc j k) (hspC j).1
  have hinjK : ∀ j : Fin Pc.fib.length, Function.Injective fun k : Fin S2.F.natDegree ↦
      lmap (algebraMap C Kb) (rCC ι Fc Pc j k) := fun j ↦ (lmap_injective _).comp (hspC j).2
  have hj0lt : 0 < Pc.fib.length := by rw [hfib1]; exact Nat.zero_lt_one
  set j0 : Fin Pc.fib.length := ⟨0, hj0lt⟩ with hj0
  have hjj : ∀ j : Fin Pc.fib.length, j = j0 := fun j ↦
    Fin.ext (by have h1 := j.2; have h2 : (j : ℕ) < 1 := hfib1 ▸ h1; simp only [hj0]; omega)
  set α0 := algebraMap C Kb (ι (Pc.fα 0)) with hα0
  set N := Pc.fN 0 with hNdef
  have hN : 0 < N := hNpos j0
  set R : Fin S2.F.natDegree → LaurentSeries Kb :=
    fun k ↦ lmap (algebraMap C Kb) (rCC ι Fc Pc 0 k) with hR
  have hl0 : S2.F.map (branchSub N α0) = ((List.ofFn R).map fun r ↦ X - Polynomial.C r).prod :=
    hlf j0
  have hRmem : ∀ k, R k ∈ List.ofFn R := fun k ↦ List.mem_ofFn.mpr ⟨k, rfl⟩
  set O : Fin S2.F.natDegree → ℤ := fun k ↦ (S2.embG (branchSub N α0)
    (branchSub_injective N hN α0) (R k) (S2.root_of_mem hl0 (hRmem k)) z).order with hO
  -- the orders sum to zero
  set o : LaurentSeries Kb → ℤ := fun r ↦ if hr : r ∈ List.ofFn R then
      (S2.embG (branchSub N α0) (branchSub_injective N hN α0) r (S2.root_of_mem hl0 hr) z).order
    else 0 with ho
  have hsum0 := S2.fibre_sum_zero z hz α0 N hN (List.ofFn R) hl0 o
    (fun r hr ↦ by simp only [ho]; rw [dif_pos hr]) hother hinf
  have hsum : ∑ k, O k = 0 := by
    rw [List.map_ofFn, List.sum_ofFn] at hsum0
    rw [← hsum0]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Function.comp_apply, ho, dif_pos (hRmem k), hO]
  -- the orders are constant on places
  have hk' : ∀ k : Fin S2.F.natDegree, (k : ℕ) < (toB Fc).natDegree := fun k ↦ by
    rw [hn']; exact k.2
  have hplace : ∀ k k' : Fin S2.F.natDegree, Pc.rπ 0 k = Pc.rπ 0 k' → O k = O k' :=
    fun k k' h ↦ order_rCC_place S2 ι Fc Pc hPcd 0 hj0lt k k' (hk' k) (hk' k') h hN _ _ z
  have hrt := fun k : Fin S2.F.natDegree ↦ (hPcd.rt 0 hj0lt).2 k (hk' k)
  have hπlt : ∀ k : Fin S2.F.natDegree, Pc.rπ 0 k < 2 := fun k ↦ by
    have := (hrt k).1; rwa [hpl2] at this
  have hrep : ∀ π < 2, ∃ k : Fin S2.F.natDegree, Pc.rπ 0 k = π := fun π hπ ↦ by
    obtain ⟨j, hj, k, hk, hk2⟩ := hPcd.surj π (by rw [hpl2]; exact hπ)
    have : j = 0 := by rw [hfib1] at hj; omega
    subst this
    exact ⟨⟨k, by rw [← hn']; exact hk⟩, hk2⟩
  haveI : Nonempty (Fin S2.F.natDegree) := ⟨⟨0, by rw [hnS]; exact hn0⟩⟩
  choose! kr hkr using hrep
  set Ô : ℕ → ℤ := fun π ↦ O (kr π) with hÔ
  have hOk : ∀ k, O k = Ô (Pc.rπ 0 k) := fun k ↦ hplace k _ (hkr _ (hπlt k)).symm
  -- ramification indices along a place
  set σ : ℕ → ℕ := fun π ↦ Pc.rs 0 (kr π) with hσ
  have hsk : ∀ k : Fin S2.F.natDegree, Pc.rs 0 k = σ (Pc.rπ 0 k) := fun k ↦ by
    obtain ⟨hπk, -, -, hNk, -⟩ := hrt k
    obtain ⟨-, -, -, hNk', -⟩ := hrt (kr (Pc.rπ 0 k))
    rw [hkr _ (hπlt k)] at hNk'
    exact Nat.eq_of_mul_eq_mul_right (hPcd.pl _ hπk).2.1 (hNk.symm.trans hNk')
  -- the counts of the places
  set c : ℕ → ℕ := fun π ↦ (Finset.univ.filter fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = π).card
    with hc
  have hcpos : ∀ π < 2, 0 < c π := fun π hπ ↦
    Finset.card_pos.mpr ⟨kr π, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkr π hπ⟩⟩
  have hsplit : ∀ f : ℕ → ℤ, ∑ k : Fin S2.F.natDegree, f (Pc.rπ 0 k) =
      (c 0 : ℤ) * f 0 + (c 1 : ℤ) * f 1 := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = 0)]
    congr 1
    · rw [Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
        nsmul_eq_mul]
    · have e : Finset.univ.filter (fun k : Fin S2.F.natDegree ↦ ¬ Pc.rπ 0 k = 0) =
          Finset.univ.filter (fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := hπlt k
        omega
      rw [e, Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
        nsmul_eq_mul]
  have eqO : (c 0 : ℤ) * Ô 0 + (c 1 : ℤ) * Ô 1 = 0 := by
    rw [← hsplit Ô, ← hsum]
    exact Finset.sum_congr rfl fun k _ ↦ (hOk k).symm
  -- all orders vanish
  have hall : ∀ k, O k = 0 := by
    have hk0 : O ⟨k₀, hk₀⟩ = 0 := hz₀ _
    have hc0 : (0 : ℤ) < c 0 := by exact_mod_cast hcpos 0 (by norm_num)
    have hc1 : (0 : ℤ) < c 1 := by exact_mod_cast hcpos 1 (by norm_num)
    rw [hOk] at hk0
    have hπ0 := hπlt ⟨k₀, hk₀⟩
    have hb : Ô 0 = 0 ∧ Ô 1 = 0 := by
      interval_cases h : Pc.rπ 0 (⟨k₀, hk₀⟩ : Fin S2.F.natDegree)
      · refine ⟨hk0, ?_⟩
        rw [hk0, mul_zero, zero_add] at eqO
        exact (mul_eq_zero.mp eqO).resolve_left hc1.ne'
      · refine ⟨?_, hk0⟩
        rw [hk0, mul_zero, add_zero] at eqO
        exact (mul_eq_zero.mp eqO).resolve_left hc0.ne'
    intro k
    rw [hOk k]
    have := hπlt k
    interval_cases (Pc.rπ 0 k)
    · exact hb.1
    · exact hb.2
  -- any branch system above `α`
  intro N' hN' l hl r hr
  obtain ⟨r0, hr0, hrel⟩ := S2.order_transfer α0 N N' hN (Nat.pos_of_ne_zero hN') (List.ofFn R) l
    hl0 hl r hr
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr0
  have h := hrel z
  have hk : (S2.embG (branchSub N α0) (branchSub_injective N hN α0) (R k)
      (S2.root_of_mem hl0 hr0) z).order = O k := rfl
  rw [hk, hall k, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hN.ne')



set_option maxHeartbeats 8000000 in
/-- **Vanishing orders outside one place force all** (any number of places): a function with order `0` outside the fibre
above `α` (with two places, `PlaceCert` facts) and order `0` along one certified root has order
`0` along every branch above `α`. -/
theorem fibre_orders_zero_of_rest (S2 : CurveData C L) (ι : F →+* C) (Fc : BPoly F)
    (hmon : (toB Fc).Monic) (hSF : S2.F = (toB Fc).map (mapRingHom ι))
    (Pc : PlaceCert F) (hPcd : Pc.Facts Fc (toB Fc).natDegree) (hn0 : 0 < (toB Fc).natDegree)
    (hfib1 : Pc.fib.length = 1)
    (z : C⟮S2.x⟯⟮S2.y⟯) (hz : z ≠ 0)
    (hother : ∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S2.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S2.root_of_mem hl hr) z).order = 0)
    (hinf : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S2.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (infSub N)
        (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S2.root_of_mem hl hr) z).order = 0)
    (π₀ : ℕ) (hN0 : 0 < Pc.fN 0)
    (hz₀ : ∀ k : Fin S2.F.natDegree, Pc.rπ 0 k ≠ π₀ →
      ∀ hr : (S2.F.map (branchSub (Pc.fN 0) (algebraMap C Kb (ι (Pc.fα 0))))).eval
        (lmap (algebraMap C Kb) (rCC ι Fc Pc 0 k)) = 0,
      (S2.embG (branchSub (Pc.fN 0) (algebraMap C Kb (ι (Pc.fα 0))))
        (branchSub_injective _ hN0 _) _ hr z).order = 0) :
    ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S2.F.map (branchSub N (algebraMap C Kb (ι (Pc.fα 0)))) =
        (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (branchSub N (algebraMap C Kb (ι (Pc.fα 0))))
        (branchSub_injective N (Nat.pos_of_ne_zero hN) _) r (S2.root_of_mem hl hr) z).order = 0 := by
  classical
  have hnS : S2.F.natDegree = (toB Fc).natDegree := by rw [hSF, hmon.natDegree_map]
  have hn' : (toB Fc).natDegree = S2.F.natDegree := hnS.symm
  have hPcF := hPcd
  have hNpos : ∀ j : Fin Pc.fib.length, 0 < Pc.fN j := fun j ↦ PlaceCert.fN_pos hPcd hn0 j j.2
  have hspC := fun j : Fin Pc.fib.length ↦ split_places_map S2 ι Fc hmon hSF Pc hPcd j j.2
  have hlf : ∀ j : Fin Pc.fib.length,
      S2.F.map (branchSub (Pc.fN j) (algebraMap C Kb (ι (Pc.fα j)))) =
      ((List.ofFn fun k : Fin S2.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ι Fc Pc j k)).map
        fun r ↦ X - Polynomial.C r).prod := fun j ↦
    S2.split_lmap (K := Kb) (Pc.fN j) (ι (Pc.fα j)) (fun k ↦ rCC ι Fc Pc j k) (hspC j).1
  have hinjK : ∀ j : Fin Pc.fib.length, Function.Injective fun k : Fin S2.F.natDegree ↦
      lmap (algebraMap C Kb) (rCC ι Fc Pc j k) := fun j ↦ (lmap_injective _).comp (hspC j).2
  have hj0lt : 0 < Pc.fib.length := by rw [hfib1]; exact Nat.zero_lt_one
  set j0 : Fin Pc.fib.length := ⟨0, hj0lt⟩ with hj0
  have hjj : ∀ j : Fin Pc.fib.length, j = j0 := fun j ↦
    Fin.ext (by have h1 := j.2; have h2 : (j : ℕ) < 1 := hfib1 ▸ h1; simp only [hj0]; omega)
  set α0 := algebraMap C Kb (ι (Pc.fα 0)) with hα0
  set N := Pc.fN 0 with hNdef
  have hN : 0 < N := hNpos j0
  set R : Fin S2.F.natDegree → LaurentSeries Kb :=
    fun k ↦ lmap (algebraMap C Kb) (rCC ι Fc Pc 0 k) with hR
  have hl0 : S2.F.map (branchSub N α0) = ((List.ofFn R).map fun r ↦ X - Polynomial.C r).prod :=
    hlf j0
  have hRmem : ∀ k, R k ∈ List.ofFn R := fun k ↦ List.mem_ofFn.mpr ⟨k, rfl⟩
  set O : Fin S2.F.natDegree → ℤ := fun k ↦ (S2.embG (branchSub N α0)
    (branchSub_injective N hN α0) (R k) (S2.root_of_mem hl0 (hRmem k)) z).order with hO
  -- the orders sum to zero
  set o : LaurentSeries Kb → ℤ := fun r ↦ if hr : r ∈ List.ofFn R then
      (S2.embG (branchSub N α0) (branchSub_injective N hN α0) r (S2.root_of_mem hl0 hr) z).order
    else 0 with ho
  have hsum0 := S2.fibre_sum_zero z hz α0 N hN (List.ofFn R) hl0 o
    (fun r hr ↦ by simp only [ho]; rw [dif_pos hr]) hother hinf
  have hsum : ∑ k, O k = 0 := by
    rw [List.map_ofFn, List.sum_ofFn] at hsum0
    rw [← hsum0]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Function.comp_apply, ho, dif_pos (hRmem k), hO]
  -- the orders are constant on places
  have hk' : ∀ k : Fin S2.F.natDegree, (k : ℕ) < (toB Fc).natDegree := fun k ↦ by
    rw [hn']; exact k.2
  have hplace : ∀ k k' : Fin S2.F.natDegree, Pc.rπ 0 k = Pc.rπ 0 k' → O k = O k' :=
    fun k k' h ↦ order_rCC_place S2 ι Fc Pc hPcd 0 hj0lt k k' (hk' k) (hk' k') h hN _ _ z
  have hrt := fun k : Fin S2.F.natDegree ↦ (hPcd.rt 0 hj0lt).2 k (hk' k)
  -- all orders vanish
  have hall : ∀ k, O k = 0 := by
    have hrest : ∀ k : Fin S2.F.natDegree, Pc.rπ 0 k ≠ π₀ → O k = 0 := fun k hk ↦ hz₀ k hk _
    by_cases hex : ∃ k₁ : Fin S2.F.natDegree, Pc.rπ 0 k₁ = π₀
    · obtain ⟨k₁, hk₁⟩ := hex
      have hsum' : ∑ k, O k = (Finset.univ.filter fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = π₀).card *
          O k₁ := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = π₀)]
        rw [Finset.sum_eq_zero (s := Finset.univ.filter fun k : Fin S2.F.natDegree ↦ ¬ Pc.rπ 0 k = π₀)
          fun k hk ↦ hrest k (Finset.mem_filter.mp hk).2, add_zero]
        rw [Finset.sum_congr rfl fun k hk ↦ hplace k k₁ (by rw [(Finset.mem_filter.mp hk).2, hk₁]),
          Finset.sum_const, nsmul_eq_mul]
      have hpos : (0 : ℤ) < (Finset.univ.filter fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = π₀).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨k₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁⟩⟩
      have h1 : O k₁ = 0 := by
        rw [hsum] at hsum'
        exact (mul_eq_zero.mp hsum'.symm).resolve_left hpos.ne'
      intro k
      by_cases hk : Pc.rπ 0 k = π₀
      · rw [hplace k k₁ (by rw [hk, hk₁]), h1]
      · exact hrest k hk
    · push Not at hex
      exact fun k ↦ hrest k (hex k)
  -- any branch system above `α`
  intro N' hN' l hl r hr
  obtain ⟨r0, hr0, hrel⟩ := S2.order_transfer α0 N N' hN (Nat.pos_of_ne_zero hN') (List.ofFn R) l
    hl0 hl r hr
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr0
  have h := hrel z
  have hk : (S2.embG (branchSub N α0) (branchSub_injective N hN α0) (R k)
      (S2.root_of_mem hl0 hr0) z).order = O k := rfl
  rw [hk, hall k, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hN.ne')



set_option maxHeartbeats 8000000 in
/-- **Units are powers of a given non-constant unit** (two places at infinity, place data of the
inverted curve checked). -/
theorem mem_pow_unit (S : CurveData C L) (k M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k M).Monic)
    (hGn : (invP (shiftP S.F 0) k M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (ι : F →+* C) (Fc : BPoly F) (hmon : (toB Fc).Monic)
    (hSF : (mobCurve S 0 k M hM hGm hGn).F = (toB Fc).map (mapRingHom ι))
    (Pc : PlaceCert F) (hPcd : Pc.Facts Fc (toB Fc).natDegree) (hn0 : 0 < (toB Fc).natDegree)
    (hfib1 : Pc.fib.length = 1) (hpl2 : Pc.pl.length = 2) (hα0 : Pc.fα 0 = 0)
    (u0 : C⟮S.x⟯⟮S.y⟯) (hu0 : u0 ≠ 0) (hnc : ¬ ∃ c : C, (u0 : L) = algebraMap C L c)
    (hfin0 : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u0).order = 0)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hfin : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ ∃ c : C, (w : L) ^ a = algebraMap C L c * (u0 : L) ^ b := by
  classical
  set S' := mobCurve S 0 k M hM hGm hGn with hS'
  have hxinv : 1 / S'.x = S.x := by rw [S.mob_x k M hM hGm hGn, one_div_one_div]
  have hα : algebraMap C Kb (ι (Pc.fα 0)) = 0 := by rw [hα0, map_zero, map_zero]
  -- a unit of `S` seen on `S'`: order `0` off the fibre above `x′ = 0`
  have hoff : ∀ v : C⟮S.x⟯⟮S.y⟯, v ≠ 0 → (∀ (a : Kb) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) v).order = 0) →
      ∃ z : C⟮S'.x⟯⟮S'.y⟯, (z : L) = v ∧ z ≠ 0 ∧
      (∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
        (l : List (LaurentSeries Kb))
        (hl : S'.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (branchSub N b)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S'.root_of_mem hl hr) z).order = 0) ∧
      (∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S'.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (infSub N)
          (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S'.root_of_mem hl hr) z).order = 0) := by
    intro v hv hvf
    have hreg : S.RegularFinite Kb v := fun a N hN l hl r hr ↦ (hvf a N hN l hl r hr).ge
    have hregI : S.RegularFinite Kb v⁻¹ := fun a N hN l hl r hr ↦ by
      rw [map_inv₀, order_inv_nk _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr hv),
        hvf a N hN l hl r hr, neg_zero]
    obtain ⟨M1, hM1, hev1⟩ := S.integral_of_regular v hreg
    obtain ⟨M2, hM2, hev2⟩ := S.integral_of_regular v⁻¹ hregI
    obtain ⟨z, hzv⟩ : ∃ z : C⟮S'.x⟯⟮S'.y⟯, (z : L) = v :=
      ⟨⟨v, (S.mob_mem_iff k M hM hGm hGn v).2 v.2⟩, rfl⟩
    have hz0 : z ≠ 0 := by
      intro h; apply hv; apply Subtype.ext
      rw [ZeroMemClass.coe_zero, ← hzv, h, ZeroMemClass.coe_zero]
    have h1 : (M1.map (aeval (1 / S'.x)).toRingHom).eval (z : L) = 0 := by
      rw [hxinv, hzv]; exact hev1
    have h2 : (M2.map (aeval (1 / S'.x)).toRingHom).eval ((z : L)⁻¹) = 0 := by
      rw [hxinv, hzv]; rw [IntermediateField.coe_inv] at hev2; exact hev2
    refine ⟨z, hzv, hz0, fun b hb N hN l hl r hr ↦ ?_, fun N hN l hl r hr ↦ ?_⟩
    · exact S'.order_zero_of_inv_integral _ _ (fun c ↦ branchSub_C N b c)
        (orderTop_inv_branchSub N (Nat.pos_of_ne_zero hN) b (by rwa [hα] at hb)) r _ z hz0 M1 M2
        hM1 hM2 h1 h2
    · exact S'.order_zero_of_inv_integral _ _ (fun c ↦ infSub_C N c)
        (orderTop_inv_infSub N) r _ z hz0 M1 M2 hM1 hM2 h1 h2
  -- a function regular everywhere on `S'` and lying in `C(x, y)` is a constant
  have hconst : ∀ y : C⟮S'.x⟯⟮S'.y⟯, y ≠ 0 →
      (∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
        (l : List (LaurentSeries Kb))
        (hl : S'.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (branchSub N b)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S'.root_of_mem hl hr) y).order = 0) →
      (∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S'.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (infSub N)
          (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S'.root_of_mem hl hr) y).order = 0) →
      (∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S'.F.map (branchSub N (algebraMap C Kb (ι (Pc.fα 0)))) =
          (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l),
        (S'.embG (branchSub N (algebraMap C Kb (ι (Pc.fα 0))))
          (branchSub_injective N (Nat.pos_of_ne_zero hN) _) r (S'.root_of_mem hl hr) y).order = 0) →
      ∃ c : C, (y : L) = algebraMap C L c := by
    intro y hy hy1 hy2 hy3
    have hregS' : S'.RegularFinite Kb y := by
      intro a N hN l hl r hr
      by_cases ha : a = algebraMap C Kb (ι (Pc.fα 0))
      · subst ha; exact (hy3 N hN l hl r hr).ge
      · exact (hy1 a ha N hN l hl r hr).ge
    have hinfS' : S'.RegularInf Kb y := fun N hN l hl r hr ↦ (hy2 N hN l hl r hr).ge
    obtain ⟨M0, hM0, hyM⟩ := S'.algebraic_of_regularG (K := Kb) S'.hasBranches S'.hasBranchesInf y
      hregS' hinfS'
    have hyS : (y : L) ∈ C⟮S.x⟯⟮S.y⟯ := (S.mob_mem_iff k M hM hGm hGn y).1 y.2
    exact S.mem_const_of_alg_geo hgeo ⟨y, hyS⟩ M0 hM0 hyM
  obtain ⟨z0, hz0v, hz00, hz0o, hz0i⟩ := hoff u0 hu0 hfin0
  obtain ⟨z, hzv, hz0, hzo, hzi⟩ := hoff w hw hfin
  -- the certified roots
  have hnS : S'.F.natDegree = (toB Fc).natDegree := by rw [hSF, hmon.natDegree_map]
  have hN0 : 0 < Pc.fN 0 := PlaceCert.fN_pos hPcd hn0 0 (by rw [hfib1]; exact Nat.zero_lt_one)
  have hspC := split_places_map S' ι Fc hmon hSF Pc hPcd 0 (by rw [hfib1]; exact Nat.zero_lt_one)
  have hl0 := S'.split_lmap (K := Kb) (Pc.fN 0) (ι (Pc.fα 0)) (fun k ↦ rCC ι Fc Pc 0 k) hspC.1
  have hroot : ∀ k : Fin S'.F.natDegree, (S'.F.map (branchSub (Pc.fN 0)
      (algebraMap C Kb (ι (Pc.fα 0))))).eval (lmap (algebraMap C Kb) (rCC ι Fc Pc 0 k)) = 0 :=
    fun k ↦ S'.root_of_mem hl0 (List.mem_ofFn.mpr ⟨k, rfl⟩)
  set ord : C⟮S'.x⟯⟮S'.y⟯ → Fin S'.F.natDegree → ℤ := fun v k ↦
    (S'.embG (branchSub (Pc.fN 0) (algebraMap C Kb (ι (Pc.fα 0)))) (branchSub_injective _ hN0 _)
      _ (hroot k) v).order with hord
  -- `u₀` has a non-zero order along some certified root
  have hex : ∃ k, ord z0 k ≠ 0 := by
    by_contra hall
    push Not at hall
    have hk0 : 0 < S'.F.natDegree := by rw [hnS]; exact hn0
    have hfz := S'.fibre_orders_zero_of_one ι Fc hmon hSF Pc hPcd hn0 hfib1 hpl2 z0 hz00 hz0o hz0i
      0 hk0 hN0 (fun _ ↦ hall ⟨0, hk0⟩)
    obtain ⟨c, hc⟩ := hconst z0 hz00 hz0o hz0i hfz
    exact hnc ⟨c, by rw [← hz0v, hc]⟩
  obtain ⟨k₁, hk₁⟩ := hex
  set a := ord z0 k₁ with ha
  set b := ord z k₁ with hb
  set y : C⟮S'.x⟯⟮S'.y⟯ := z ^ a * z0 ^ (-b) with hy
  have hy0 : y ≠ 0 := mul_ne_zero (zpow_ne_zero _ hz0) (zpow_ne_zero _ hz00)
  have hordy : ∀ (g : C[X] →+* LaurentSeries Kb) (hg : Function.Injective g) (Y : LaurentSeries Kb)
      (hY : (S'.F.map g).eval Y = 0),
      (S'.embG g hg Y hY y).order = a * (S'.embG g hg Y hY z).order +
        (-b) * (S'.embG g hg Y hY z0).order := by
    intro g hg Y hY
    have e1 : S'.embG g hg Y hY z ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hz0
    have e2 : S'.embG g hg Y hY z0 ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hz00
    rw [hy, map_mul, map_zpow₀, map_zpow₀, HahnSeries.order_mul (zpow_ne_zero _ e1)
      (zpow_ne_zero _ e2), order_zpow_ls _ e1, order_zpow_ls _ e2]
  have hy1 : ∀ b' : Kb, b' ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S'.F.map (branchSub N b') = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (branchSub N b')
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b') r (S'.root_of_mem hl hr) y).order = 0 :=
    fun b' hb' N hN l hl r hr ↦ by
      rw [hordy, hzo b' hb' N hN l hl r hr, hz0o b' hb' N hN l hl r hr]; ring
  have hy2 : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S'.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (infSub N)
        (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S'.root_of_mem hl hr) y).order = 0 :=
    fun N hN l hl r hr ↦ by rw [hordy, hzi N hN l hl r hr, hz0i N hN l hl r hr]; ring
  have hy3 := S'.fibre_orders_zero_of_one ι Fc hmon hSF Pc hPcd hn0 hfib1 hpl2 y hy0 hy1 hy2
    k₁ k₁.2 hN0 (fun hr ↦ by
      rw [hordy]
      change a * ord z k₁ + -b * ord z0 k₁ = 0
      rw [← hb, ← ha]; ring)
  obtain ⟨c, hc⟩ := hconst y hy0 hy1 hy2 hy3
  refine ⟨a, b, hk₁, c, ?_⟩
  have hu0L : (u0 : L) ≠ 0 := fun h ↦ hu0 (Subtype.ext h)
  have e : (y : L) = (w : L) ^ a * ((u0 : L) ^ b)⁻¹ := by
    rw [hy, IntermediateField.coe_mul, show ((z ^ a : C⟮S'.x⟯⟮S'.y⟯) : L) = (z : L) ^ a from
      map_zpow₀ (C⟮S'.x⟯⟮S'.y⟯).val z a, show ((z0 ^ (-b) : C⟮S'.x⟯⟮S'.y⟯) : L) = (z0 : L) ^ (-b) from
      map_zpow₀ (C⟮S'.x⟯⟮S'.y⟯).val z0 (-b), hzv, hz0v, zpow_neg]
  rw [hc] at e
  rw [e, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hu0L), mul_one]

set_option maxHeartbeats 16000000 in
/-- **Units are power products of given independent units** (`m + 1` places at infinity of `S`,
all above `x′ = 0` on the inverted curve, and `m` units multiplicatively independent modulo
constants): every unit `w` satisfies `w^N = c ∏ uᵢ^{aᵢ}` with `N ≠ 0`. -/
theorem mem_pow_units (S : CurveData C L) (k M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k M).Monic)
    (hGn : (invP (shiftP S.F 0) k M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (ι : F →+* C) (Fc : BPoly F) (hmon : (toB Fc).Monic)
    (hSF : (mobCurve S 0 k M hM hGm hGn).F = (toB Fc).map (mapRingHom ι))
    (Pc : PlaceCert F) (hPcd : Pc.Facts Fc (toB Fc).natDegree) (hn0 : 0 < (toB Fc).natDegree)
    (hfib1 : Pc.fib.length = 1) (hα0 : Pc.fα 0 = 0) {m : ℕ} (hpl : Pc.pl.length = m + 1)
    (u : Fin m → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ a : Fin m → ℤ, (∃ c : C, ∏ i, (u i : L) ^ a i = algebraMap C L c) → a = 0)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hfin : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) :
    ∃ (N : ℤ) (a : Fin m → ℤ), N ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N = algebraMap C L c * ∏ i, (u i : L) ^ a i := by
  classical
  set S' := mobCurve S 0 k M hM hGm hGn with hS'
  have hxinv : 1 / S'.x = S.x := by rw [S.mob_x k M hM hGm hGn, one_div_one_div]
  have hα : algebraMap C Kb (ι (Pc.fα 0)) = 0 := by rw [hα0, map_zero, map_zero]
  -- a unit of `S` seen on `S'`: order `0` off the fibre above `x′ = 0`
  have hoff : ∀ v : C⟮S.x⟯⟮S.y⟯, v ≠ 0 → (∀ (a : Kb) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) v).order = 0) →
      ∃ z : C⟮S'.x⟯⟮S'.y⟯, (z : L) = v ∧ z ≠ 0 ∧
      (∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
        (l : List (LaurentSeries Kb))
        (hl : S'.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (branchSub N b)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S'.root_of_mem hl hr) z).order = 0) ∧
      (∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S'.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (infSub N)
          (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S'.root_of_mem hl hr) z).order = 0) := by
    intro v hv hvf
    have hreg : S.RegularFinite Kb v := fun a N hN l hl r hr ↦ (hvf a N hN l hl r hr).ge
    have hregI : S.RegularFinite Kb v⁻¹ := fun a N hN l hl r hr ↦ by
      rw [map_inv₀, order_inv_nk _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr hv),
        hvf a N hN l hl r hr, neg_zero]
    obtain ⟨M1, hM1, hev1⟩ := S.integral_of_regular v hreg
    obtain ⟨M2, hM2, hev2⟩ := S.integral_of_regular v⁻¹ hregI
    obtain ⟨z, hzv⟩ : ∃ z : C⟮S'.x⟯⟮S'.y⟯, (z : L) = v :=
      ⟨⟨v, (S.mob_mem_iff k M hM hGm hGn v).2 v.2⟩, rfl⟩
    have hz0 : z ≠ 0 := by
      intro h; apply hv; apply Subtype.ext
      rw [ZeroMemClass.coe_zero, ← hzv, h, ZeroMemClass.coe_zero]
    have h1 : (M1.map (aeval (1 / S'.x)).toRingHom).eval (z : L) = 0 := by
      rw [hxinv, hzv]; exact hev1
    have h2 : (M2.map (aeval (1 / S'.x)).toRingHom).eval ((z : L)⁻¹) = 0 := by
      rw [hxinv, hzv]; rw [IntermediateField.coe_inv] at hev2; exact hev2
    refine ⟨z, hzv, hz0, fun b hb N hN l hl r hr ↦ ?_, fun N hN l hl r hr ↦ ?_⟩
    · exact S'.order_zero_of_inv_integral _ _ (fun c ↦ branchSub_C N b c)
        (orderTop_inv_branchSub N (Nat.pos_of_ne_zero hN) b (by rwa [hα] at hb)) r _ z hz0 M1 M2
        hM1 hM2 h1 h2
    · exact S'.order_zero_of_inv_integral _ _ (fun c ↦ infSub_C N c)
        (orderTop_inv_infSub N) r _ z hz0 M1 M2 hM1 hM2 h1 h2
  -- a function regular everywhere on `S'` and lying in `C(x, y)` is a constant
  have hconst : ∀ y : C⟮S'.x⟯⟮S'.y⟯, y ≠ 0 →
      (∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
        (l : List (LaurentSeries Kb))
        (hl : S'.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (branchSub N b)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S'.root_of_mem hl hr) y).order = 0) →
      (∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S'.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (infSub N)
          (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S'.root_of_mem hl hr) y).order = 0) →
      (∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S'.F.map (branchSub N (algebraMap C Kb (ι (Pc.fα 0)))) =
          (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l),
        (S'.embG (branchSub N (algebraMap C Kb (ι (Pc.fα 0))))
          (branchSub_injective N (Nat.pos_of_ne_zero hN) _) r (S'.root_of_mem hl hr) y).order = 0) →
      ∃ c : C, (y : L) = algebraMap C L c := by
    intro y hy hy1 hy2 hy3
    have hregS' : S'.RegularFinite Kb y := by
      intro a N hN l hl r hr
      by_cases ha : a = algebraMap C Kb (ι (Pc.fα 0))
      · subst ha; exact (hy3 N hN l hl r hr).ge
      · exact (hy1 a ha N hN l hl r hr).ge
    have hinfS' : S'.RegularInf Kb y := fun N hN l hl r hr ↦ (hy2 N hN l hl r hr).ge
    obtain ⟨M0, hM0, hyM⟩ := S'.algebraic_of_regularG (K := Kb) S'.hasBranches S'.hasBranchesInf y
      hregS' hinfS'
    have hyS : (y : L) ∈ C⟮S.x⟯⟮S.y⟯ := (S.mob_mem_iff k M hM hGm hGn y).1 y.2
    exact S.mem_const_of_alg_geo hgeo ⟨y, hyS⟩ M0 hM0 hyM
  choose zu hzuv hzu0 hzuo hzui using fun i ↦ hoff (u i) (hu i) (hfinu i)
  obtain ⟨zw, hzwv, hzw0, hzwo, hzwi⟩ := hoff w hw hfin
  -- the certified roots and their places
  have hnS : S'.F.natDegree = (toB Fc).natDegree := by rw [hSF, hmon.natDegree_map]
  have hN0 : 0 < Pc.fN 0 := PlaceCert.fN_pos hPcd hn0 0 (by rw [hfib1]; exact Nat.zero_lt_one)
  have hspC := split_places_map S' ι Fc hmon hSF Pc hPcd 0 (by rw [hfib1]; exact Nat.zero_lt_one)
  have hl0 := S'.split_lmap (K := Kb) (Pc.fN 0) (ι (Pc.fα 0)) (fun k ↦ rCC ι Fc Pc 0 k) hspC.1
  have hroot : ∀ k : Fin S'.F.natDegree, (S'.F.map (branchSub (Pc.fN 0)
      (algebraMap C Kb (ι (Pc.fα 0))))).eval (lmap (algebraMap C Kb) (rCC ι Fc Pc 0 k)) = 0 :=
    fun k ↦ S'.root_of_mem hl0 (List.mem_ofFn.mpr ⟨k, rfl⟩)
  set φk : Fin S'.F.natDegree → (C⟮S'.x⟯⟮S'.y⟯ →+* LaurentSeries Kb) := fun k ↦
    S'.embG (branchSub (Pc.fN 0) (algebraMap C Kb (ι (Pc.fα 0)))) (branchSub_injective _ hN0 _)
      _ (hroot k) with hφk
  have hk' : ∀ k : Fin S'.F.natDegree, (k : ℕ) < (toB Fc).natDegree := fun k ↦ by
    rw [← hnS]; exact k.2
  have hplace : ∀ v (k k' : Fin S'.F.natDegree), Pc.rπ 0 k = Pc.rπ 0 k' →
      (φk k v).order = (φk k' v).order := fun v k k' h ↦
    order_rCC_place S' ι Fc Pc hPcd 0 (by rw [hfib1]; exact Nat.zero_lt_one) k k' (hk' k) (hk' k')
      h hN0 _ _ v
  have hπlt : ∀ k : Fin S'.F.natDegree, Pc.rπ 0 k < m + 1 := fun k ↦ by
    have := ((hPcd.rt 0 (by rw [hfib1]; exact Nat.zero_lt_one)).2 k (hk' k)).1; rwa [hpl] at this
  have hrep : ∀ p < m + 1, ∃ k : Fin S'.F.natDegree, Pc.rπ 0 k = p := fun p hp ↦ by
    obtain ⟨j, hj, k, hk, hk2⟩ := hPcd.surj p (by rw [hpl]; exact hp)
    have : j = 0 := by rw [hfib1] at hj; omega
    subst this
    exact ⟨⟨k, by rw [hnS]; exact hk⟩, hk2⟩
  haveI : Nonempty (Fin S'.F.natDegree) := ⟨⟨0, by rw [hnS]; exact hn0⟩⟩
  choose! kr hkr using hrep
  -- orders of power products
  have hordp : ∀ (g : C[X] →+* LaurentSeries Kb) (hg : Function.Injective g) (Y : LaurentSeries Kb)
      (hY : (S'.F.map g).eval Y = 0) (e0 : ℤ) (e : Fin m → ℤ),
      (S'.embG g hg Y hY (zw ^ e0 * ∏ i, zu i ^ e i)).order =
        e0 * (S'.embG g hg Y hY zw).order + ∑ i, e i * (S'.embG g hg Y hY (zu i)).order := by
    intro g hg Y hY e0 e
    have hw' : S'.embG g hg Y hY zw ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hzw0
    obtain ⟨hp0, hpo⟩ := order_prod_zpow_nk Finset.univ (fun i ↦ S'.embG g hg Y hY (zu i))
      (fun i _ ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr (hzu0 i)) e
    rw [map_mul, map_zpow₀, map_prod]
    simp only [map_zpow₀]
    rw [HahnSeries.order_mul (zpow_ne_zero _ hw') hp0, order_zpow_ls _ hw', hpo]
  have hprod_ne : ∀ (e0 : ℤ) (e : Fin m → ℤ), zw ^ e0 * ∏ i, zu i ^ e i ≠ 0 := fun e0 e ↦
    mul_ne_zero (zpow_ne_zero _ hzw0) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hzu0 i))
  -- a power product with vanishing orders at the places `0, …, m − 1` is a constant
  have hkey : ∀ (e0 : ℤ) (e : Fin m → ℤ),
      (∀ p : Fin m, e0 * (φk (kr p) zw).order + ∑ i, e i * (φk (kr p) (zu i)).order = 0) →
      ∃ c : C, ((zw ^ e0 * ∏ i, zu i ^ e i : C⟮S'.x⟯⟮S'.y⟯) : L) = algebraMap C L c := by
    intro e0 e hzero
    set y := zw ^ e0 * ∏ i, zu i ^ e i with hy
    have hy1 : ∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
        (l : List (LaurentSeries Kb))
        (hl : S'.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (branchSub N b)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S'.root_of_mem hl hr) y).order = 0 :=
      fun b hb N hN l hl r hr ↦ by
        rw [hy, hordp, hzwo b hb N hN l hl r hr, Finset.sum_eq_zero fun i _ ↦ by
          rw [hzuo i b hb N hN l hl r hr, mul_zero]]; ring
    have hy2 : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S'.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (infSub N)
          (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S'.root_of_mem hl hr) y).order = 0 :=
      fun N hN l hl r hr ↦ by
        rw [hy, hordp, hzwi N hN l hl r hr, Finset.sum_eq_zero fun i _ ↦ by
          rw [hzui i N hN l hl r hr, mul_zero]]; ring
    have hy3 := S'.fibre_orders_zero_of_rest ι Fc hmon hSF Pc hPcd hn0 hfib1 y (hprod_ne e0 e)
      hy1 hy2 m hN0 (fun k hk hr ↦ by
        have hp : Pc.rπ 0 k < m := by have := hπlt k; omega
        have h1 := hplace y k (kr (Pc.rπ 0 k)) (hkr _ (hπlt k)).symm
        change (φk k y).order = 0
        rw [h1, hy, hφk]
        simp only
        rw [hordp]
        exact hzero ⟨Pc.rπ 0 k, hp⟩)
    exact hconst y (hprod_ne e0 e) hy1 hy2 hy3
  -- the order matrix of the units at the places `0, …, m − 1`
  set A : Matrix (Fin m) (Fin m) ℤ := fun i p ↦ (φk (kr p) (zu i)).order with hA
  set b : Fin m → ℤ := fun p ↦ (φk (kr p) zw).order with hb
  have hcoe : ∀ (e0 : ℤ) (e : Fin m → ℤ), ((zw ^ e0 * ∏ i, zu i ^ e i : C⟮S'.x⟯⟮S'.y⟯) : L) =
      (w : L) ^ e0 * ∏ i, (u i : L) ^ e i := fun e0 e ↦ by
    rw [IntermediateField.coe_mul, show ((zw ^ e0 : C⟮S'.x⟯⟮S'.y⟯) : L) = (zw : L) ^ e0 from
      map_zpow₀ (C⟮S'.x⟯⟮S'.y⟯).val zw e0, hzwv, IntermediateField.coe_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [show ((zu i ^ e i : C⟮S'.x⟯⟮S'.y⟯) : L) = (zu i : L) ^ e i from
      map_zpow₀ (C⟮S'.x⟯⟮S'.y⟯).val (zu i) (e i), hzuv i]
  have hw0L : (w : L) ≠ 0 := fun h ↦ hw (Subtype.ext h)
  by_cases hdet : A.det = 0
  · -- the units would be dependent
    exfalso
    obtain ⟨a, ha0, hAa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (show A.transpose.det = 0 by rw [Matrix.det_transpose]; exact hdet)
    obtain ⟨c, hc⟩ := hkey 0 a fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Pi.zero_apply] at this
      rw [zero_mul, zero_add]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    apply ha0
    apply hind a
    refine ⟨c, ?_⟩
    rw [← hc, hcoe, zpow_zero, one_mul]
  · -- Cramer: `A.transpose (adj A.transpose b) = det A • b`
    set a : Fin m → ℤ := Matrix.mulVec (A.transpose).adjugate b with ha
    have hAa : Matrix.mulVec A.transpose a = A.det • b := by
      rw [ha, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.det_transpose, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    obtain ⟨c, hc⟩ := hkey A.det (fun i ↦ -a i) fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Pi.smul_apply,
        smul_eq_mul] at this
      have e : ∑ i, -a i * (φk (kr p) (zu i)).order = -(A.det * b p) := by
        rw [← this, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [neg_mul, mul_comm (a i)]; rfl
      rw [e, hb]; ring
    refine ⟨A.det, a, hdet, c, ?_⟩
    rw [hcoe] at hc
    have hprodne : ∏ i, (u i : L) ^ a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
      zpow_ne_zero _ (fun h ↦ hu i (Subtype.ext h))
    have e2 : ∏ i, (u i : L) ^ (-a i) = (∏ i, (u i : L) ^ a i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ zpow_neg _ _
    rw [e2] at hc
    rw [← hc, mul_assoc, inv_mul_cancel₀ hprodne, mul_one]

end CurveData

end Unit

end Curves
