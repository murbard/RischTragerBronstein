import RischTragerBronstein.Mixed.NKUnitsInf0
import RischTragerBronstein.Mixed.NKRamUnits

/-!
# S-units with classes of roots (ramified places)

`mem_pow_units_cls0`: as `mem_pow_units_inf0`, when the roots above infinity and above `0` are
covered by classes of roots along which every function has the same order (e.g. the rotation
classes of a ramified place, `cover_ram`): rows are one root per class above `0`, and one root per
class above infinity except a last class `p₀`, whose order is forced by the product formula
`N₀ ∑_∞ ord + N ∑_0 ord = 0` (`unit_sum_inf0`). `unitsSpan0_ram`: for a single ramified slope at
infinity (`leadPolyR`) and an unramified split fibre above `0`, `x` and `n/e + n − 2` independent
S-units span the S-units.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential GTors CPoly Sup

section UnitsCls0

variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

variable (S : CurveData C L)

set_option maxHeartbeats 8000000 in
/-- **S-units are power products of `x` and given independent S-units** (classes of roots). -/
theorem mem_pow_units_cls0 [CharZero C]
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (N0 : ℕ) (hN0 : 0 < N0) (l0 : List (LaurentSeries Kb))
    (hl0 : S.F.map (branchSub N0 0) = (l0.map fun r ↦ X - Polynomial.C r).prod)
    {mI m0 : ℕ} (tq : Fin mI → Fin l.length) (p₀ : Fin l.length)
    (hcover : ∀ p : Fin l.length,
      (∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub N) (infSub_injective N hN) (l.get p)
          (S.root_of_mem hl (List.get_mem l p)) f).order =
        (S.embG (infSub N) (infSub_injective N hN) (l.get (tq q))
          (S.root_of_mem hl (List.get_mem l (tq q))) f).order) ∨
      ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub N) (infSub_injective N hN) (l.get p)
          (S.root_of_mem hl (List.get_mem l p)) f).order =
        (S.embG (infSub N) (infSub_injective N hN) (l.get p₀)
          (S.root_of_mem hl (List.get_mem l p₀)) f).order)
    (tq0 : Fin m0 → Fin l0.length)
    (hcover0 : ∀ p : Fin l0.length, ∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯,
      (S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) (l0.get p)
          (S.root_of_mem hl0 (List.get_mem l0 p)) f).order =
        (S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) (l0.get (tq0 q))
          (S.root_of_mem hl0 (List.get_mem l0 (tq0 q))) f).order)
    {mu : ℕ} (hcount : mI + m0 = mu + 1)
    (u : Fin mu → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ (e0 : ℤ) (a : Fin mu → ℤ),
      (∃ c : C, S.x ^ e0 * ∏ i, (u i : L) ^ a i = algebraMap C L c) → e0 = 0 ∧ a = 0)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hfin : ∀ (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) :
    ∃ (N' κ : ℤ) (a : Fin mu → ℤ), N' ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N' = algebraMap C L c * S.x ^ κ * ∏ i, (u i : L) ^ a i := by
  classical
  set v : Fin (mu + 1) → C⟮S.x⟯⟮S.y⟯ := Fin.cons S.xE u with hv
  have hv0 : ∀ i, v i ≠ 0 := fun i ↦ Fin.cases S.xE_ne_zero (fun i ↦ hu i) i
  have hfinv : ∀ i (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (v i)).order = 0 := by
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · intro a ha N hN l hl r hr
      simp only [hv, Fin.cons_zero]
      exact S.order_xE_branch a ha N hN l hl r hr
    · intro a ha N hN l hl r hr
      simp only [hv, Fin.cons_succ]
      exact hfinu i a ha N hN l hl r hr
  set φI : Fin l.length → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb) := fun p ↦
    S.embG (infSub N) (infSub_injective N hN) (l.get p) (S.root_of_mem hl (List.get_mem l p))
    with hφI
  set φ0 : Fin l0.length → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb) := fun p ↦
    S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) (l0.get p)
      (S.root_of_mem hl0 (List.get_mem l0 p)) with hφ0
  -- the rows: class representatives
  have hlt : ∀ p : Fin (mu + 1), ¬ (p : ℕ) < mI → (p : ℕ) - mI < m0 := by
    intro p hp; omega
  set φ : Fin (mu + 1) → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb) := fun p ↦
    if h : (p : ℕ) < mI then φI (tq ⟨p, h⟩) else φ0 (tq0 ⟨p - mI, hlt p h⟩) with hφ
  have hordp : ∀ (g : C[X] →+* LaurentSeries Kb) (hg : Function.Injective g) (Y : LaurentSeries Kb)
      (hY : (S.F.map g).eval Y = 0) (e0 : ℤ) (e : Fin (mu + 1) → ℤ),
      (S.embG g hg Y hY (w ^ e0 * ∏ i, v i ^ e i)).order =
        e0 * (S.embG g hg Y hY w).order + ∑ i, e i * (S.embG g hg Y hY (v i)).order := by
    intro g hg Y hY e0 e
    have hw' : S.embG g hg Y hY w ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hw
    obtain ⟨hp0, hpo⟩ := order_prod_zpow_nk Finset.univ (fun i ↦ S.embG g hg Y hY (v i))
      (fun i _ ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr (hv0 i)) e
    rw [map_mul, map_zpow₀, map_prod]
    simp only [map_zpow₀]
    rw [HahnSeries.order_mul (zpow_ne_zero _ hw') hp0, order_zpow_ls _ hw', hpo]
  have hprod_ne : ∀ (e0 : ℤ) (e : Fin (mu + 1) → ℤ), w ^ e0 * ∏ i, v i ^ e i ≠ 0 := fun e0 e ↦
    mul_ne_zero (zpow_ne_zero _ hw) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hv0 i))
  have hkey : ∀ (e0 : ℤ) (e : Fin (mu + 1) → ℤ),
      (∀ p, e0 * (φ p w).order + ∑ i, e i * (φ p (v i)).order = 0) →
      ∃ c : C, ((w ^ e0 * ∏ i, v i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L c := by
    intro e0 e hzero
    set y := w ^ e0 * ∏ i, v i ^ e i with hy
    have hy1 : ∀ (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S.embG (branchSub N a)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r (S.root_of_mem hl hr) y).order = 0 :=
      fun a ha N hN l hl r hr ↦ by
        rw [hy, hordp, hfin a ha N hN l hl r hr, Finset.sum_eq_zero fun i _ ↦ by
          rw [hfinv i a ha N hN l hl r hr, mul_zero]]; ring
    have hrow : ∀ p, (φ p y).order = 0 := fun p ↦ by
      have := hzero p
      by_cases h : (p : ℕ) < mI
      · have e1 : φ p = S.embG (infSub N) (infSub_injective N hN) (l.get (tq ⟨p, h⟩))
            (S.root_of_mem hl (List.get_mem l _)) := by rw [hφ]; simp only [dif_pos h]; rfl
        rw [e1] at this ⊢; rw [hy, hordp]; exact this
      · have e1 : φ p = S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0)
            (l0.get (tq0 ⟨p - mI, hlt p h⟩)) (S.root_of_mem hl0 (List.get_mem l0 _)) := by
          rw [hφ]; simp only [dif_neg h]; rfl
        rw [e1] at this ⊢; rw [hy, hordp]; exact this
    -- the representatives have order `0`
    have hrepI : ∀ q : Fin mI, (φI (tq q) y).order = 0 := fun q ↦ by
      have := hrow ⟨q, by omega⟩
      simp only [hφ, show ((q : ℕ) < mI) from q.2, dite_true] at this
      exact this
    have hrep0 : ∀ q : Fin m0, (φ0 (tq0 q) y).order = 0 := fun q ↦ by
      have := hrow ⟨mI + q, by omega⟩
      simp only [hφ, show ¬ (mI + (q : ℕ) < mI) by omega, dite_false] at this
      convert this using 4
      simp
    have hzero0 : ∀ p : Fin l0.length, (φ0 p y).order = 0 := fun p ↦ by
      obtain ⟨q, hq⟩ := hcover0 p
      rw [show φ0 p y = S.embG _ _ _ _ y from rfl, hq y]
      exact hrep0 q
    -- the last class above infinity, by the product formula
    have hsum := S.unit_sum_inf0 y (hprod_ne e0 e) hy1 N hN l hl N0 hN0 l0 hl0
    rw [sum_attach_eq_fin l (fun r hr ↦ (S.embG (infSub N) (infSub_injective N hN) r
      (S.root_of_mem hl hr) y).order),
      sum_attach_eq_fin l0 (fun r hr ↦ (S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) r
      (S.root_of_mem hl0 hr) y).order), Finset.sum_eq_zero fun i _ ↦ hzero0 i, mul_zero,
      add_zero] at hsum
    have hN0z : (N0 : ℤ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hsumI : ∑ p : Fin l.length, (φI p y).order = 0 :=
      (mul_eq_zero.mp hsum).resolve_left hN0z
    have hcls : ∀ p : Fin l.length, (φI p y).order =
        if (∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯, (φI p f).order = (φI (tq q) f).order) then 0
        else (φI p₀ y).order := by
      intro p
      split_ifs with h
      · obtain ⟨q, hq⟩ := h
        rw [hq y]; exact hrepI q
      · rcases hcover p with h' | h'
        · exact absurd h' h
        · exact h' y
    have hp0 : (φI p₀ y).order = 0 := by
      by_cases hin : ∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯, (φI p₀ f).order = (φI (tq q) f).order
      · have := hcls p₀; rw [if_pos hin] at this; exact this
      · rw [Finset.sum_congr rfl fun p _ ↦ hcls p, ← Finset.sum_filter_add_sum_filter_not
          Finset.univ (fun p ↦ ∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯, (φI p f).order = (φI (tq q) f).order)]
          at hsumI
        rw [Finset.sum_congr rfl fun p hp ↦ by rw [if_pos (Finset.mem_filter.mp hp).2],
          Finset.sum_const_zero, zero_add, Finset.sum_congr rfl fun p hp ↦ by
            rw [if_neg (Finset.mem_filter.mp hp).2], Finset.sum_const, nsmul_eq_mul] at hsumI
        have hcard : (0 : ℤ) < ((Finset.univ.filter fun p ↦ ¬ ∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯,
            (φI p f).order = (φI (tq q) f).order).card : ℤ) := by
          exact_mod_cast Finset.card_pos.mpr ⟨p₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩⟩
        exact (mul_eq_zero.mp hsumI).resolve_left hcard.ne'
    have hinf : ∀ p : Fin l.length, (φI p y).order = 0 := fun p ↦ by
      rw [hcls p]; split_ifs
      · rfl
      · exact hp0
    -- regular at the finite places
    have hreg : S.RegularFinite Kb y := by
      intro a N' hN' l' hl' r hr
      by_cases ha : a = 0
      · subst ha
        obtain ⟨r0, hr0, htr⟩ := S.order_transfer 0 N0 N' hN0 (Nat.pos_of_ne_zero hN') l0 l' hl0
          hl' r hr
        obtain ⟨i, rfl⟩ := List.get_of_mem hr0
        have h1 := htr y
        rw [show (S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) (l0.get i)
          (S.root_of_mem hl0 hr0) y).order = (φ0 i y).order from rfl, hzero0 i, mul_zero] at h1
        have hN0z' : (0 : ℤ) < N0 := by exact_mod_cast hN0
        nlinarith
      · exact (hy1 a ha N' hN' l' hl' r hr).ge
    obtain ⟨M0, hM0, hyM⟩ := S.algebraic_of_regular_l y hreg N hN l hl fun r hr ↦ by
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (hinf i).ge
    exact S.mem_const_of_alg_geo hgeo y M0 hM0 hyM
  have hindv : ∀ a : Fin (mu + 1) → ℤ, (∃ c : C, ∏ i, (v i : L) ^ a i = algebraMap C L c) →
      a = 0 := by
    intro a ⟨c, hc⟩
    rw [Fin.prod_univ_succ] at hc
    simp only [hv, Fin.cons_zero, Fin.cons_succ, coe_xE] at hc
    obtain ⟨h0, h1⟩ := hind (a 0) (fun i ↦ a i.succ) ⟨c, hc⟩
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact h0
    · exact congrFun h1 i
  obtain ⟨N', a, hN', c, hc⟩ := S.pow_units_cramer (Kb := Kb) v hv0 w φ hkey hindv
  refine ⟨N', a 0, fun i ↦ a i.succ, hN', c, ?_⟩
  rw [hc, Fin.prod_univ_succ]
  simp only [hv, Fin.cons_zero, Fin.cons_succ, coe_xE]
  ring

/-- **`x` and independent S-units span the S-units** (a single ramified slope `s'/e` at infinity
with residual polynomial `∏ₖ (Zᵉ − γₖ)`, any branch system above `0` whose roots are pairwise
distinct places, e.g. a split fibre): `mI + (number of roots above 0) = mu + 1`, `mI + 1` places at
infinity. -/
lemma unitsSpan0_ram [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (e s' : ℕ) (he : 0 < e) (hcop : Nat.Coprime s' e)
    {mI : ℕ} (γ : Fin (mI + 1) → C) (hγinj : Function.Injective γ) (hγ0 : ∀ k, γ k ≠ 0)
    (hmon : S.F.Monic)
    (hdeg : ∀ i < S.F.natDegree, e * (S.F.coeff i).natDegree ≤ s' * (S.F.natDegree - i))
    (hlead : leadPolyR e s' S.F = ∏ k, (X ^ e - Polynomial.C (γ k)))
    (N0 : ℕ) (hN0 : 0 < N0) (l0 : List (LaurentSeries Kb))
    (hl0 : S.F.map (branchSub N0 0) = (l0.map fun r ↦ X - Polynomial.C r).prod)
    {mu : ℕ} (hcount : mI + l0.length = mu + 1)
    (u : Fin mu → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ (e0 : ℤ) (a : Fin mu → ℤ),
      (∃ c : C, S.x ^ e0 * ∏ i, (u i : L) ^ a i = algebraMap C L c) → e0 = 0 ∧ a = 0) :
    S.UnitsSpan0 Kb u := by
  intro w hw hfin
  obtain ⟨Ni, hNi, li, -, hli⟩ := S.hasBranchesInf (K := Kb)
  have hNi' := Nat.pos_of_ne_zero hNi
  have hli' := branchSys_lsub S.F Ni e he li hli
  obtain ⟨tq, p₀, hcov⟩ := S.cover_ram e s' he hcop γ hγinj hγ0 hmon hdeg hlead Ni hNi'
    (li.map (lsub e he)) hli'
  exact S.mem_pow_units_cls0 hgeo (Ni * e) (Nat.mul_pos hNi' he) (li.map (lsub e he)) hli' N0 hN0
    l0 hl0 tq p₀ hcov id (fun p ↦ ⟨p, fun _ ↦ rfl⟩) hcount u hu hfinu hind w hw hfin

end CurveData

end UnitsCls0

end Curves
