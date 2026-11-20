import RischTragerBronstein.Mixed.NKExactTG
import RischTragerBronstein.Mixed.NKExactWR

/-!
# The exact part in a basis `w = T θ` rescaled at infinity

`redC`: a fraction code divided by the gcd of numerator and denominator (or `0` if the
denominator vanishes); its value is unchanged (`sem_redC`), its denominator is non-zero, and it is
squarefree as soon as the value has some squarefree denominator (`redC_den_squarefree`).

`exactTR … r`: the exact test in the basis `w = T θ` (`exactTG`) with `exactWR` (shifts `r`) on the
reduced matrix and coordinates. Correct for every `T`, `T⁻¹` and `r` (`exactTR_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- A fraction code divided by the gcd of its numerator and denominator. -/
def redC (m : ℕ) (c : LC (m + 1)) : LC (m + 1) :=
  if GPoly.isZero (MO Fc ks m) c.2 then (MOr Fc ks (m + 1)).zero else
    let g := (GPoly.egcd (MO Fc ks m) c.1 c.2).1
    ((GPoly.divMod (MO Fc ks m) c.1 g).1, (GPoly.divMod (MO Fc ks m) c.2 g).1)

lemma redC_of_zero (m : ℕ) (c : LC (m + 1)) (hz : GPoly.isZero (MO Fc ks m) c.2 = true) :
    redC Fc ks m c = (MOr Fc ks (m + 1)).zero := by
  unfold redC; simp only [hz, ↓reduceIte]

lemma redC_of_ne (m : ℕ) (c : LC (m + 1)) (hz : ¬GPoly.isZero (MO Fc ks m) c.2 = true) :
    redC Fc ks m c = ((GPoly.divMod (MO Fc ks m) c.1 (GPoly.egcd (MO Fc ks m) c.1 c.2).1).1,
      (GPoly.divMod (MO Fc ks m) c.2 (GPoly.egcd (MO Fc ks m) c.1 c.2).1).1) := by
  unfold redC; simp only [hz, ↓reduceIte, Bool.false_eq_true]; rfl

/-- **The exact-part test in the basis `w = T θ` rescaled by `t^{−r}`.** -/
def exactTR (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) :
    Option Bool :=
  exactTG Fc ks m (fun N Mw fw ↦ exactWR Fc ks m η lim N (Mw.map fun l ↦ l.map (redC Fc ks m))
    (fw.map (redC Fc ks m)) r) P Tc Ti f

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ) (h1 : T.Tr (m + 1))

lemma sem_zeroCode : (T.MPr (m + 1) h1).sem (MOr Fc ks (m + 1)).zero = 0 :=
  (T.MPr (m + 1) h1).sem_zero

/-- **`redC` keeps the value.** -/
lemma sem_redC (htr : Transcendental (T.F m) (T.ts m)) (c : LC (m + 1)) :
    (T.MPr (m + 1) h1).sem (redC Fc ks m c) = (T.MPr (m + 1) h1).sem c := by
  set M := T.MP m h1.of_succ
  by_cases hz : GPoly.isZero (MO Fc ks m) c.2 = true
  · rw [redC_of_zero Fc ks m c hz, T.sem_zeroCode m h1, MPr_sem, T.sem_MP_succ,
      (GPoly.isZero_iff M _).mp hz, map_zero, div_zero]
  · rw [redC_of_ne Fc ks m c hz]
    have hc2 : GPoly.toPoly M c.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    obtain ⟨hg1, hg2⟩ := GPoly.egcd_dvd M c.1 c.2
    set g := (GPoly.egcd (MO Fc ks m) c.1 c.2).1
    have hg0 : GPoly.toPoly M g ≠ 0 := fun h0 ↦ hc2 (zero_dvd_iff.mp (h0 ▸ hg2))
    have e1 := GPoly.div_mul_of_dvd M c.1 g hg0 hg1
    have e2 := GPoly.div_mul_of_dvd M c.2 g hg0 hg2
    change T.phi m (GPoly.toPoly M (GPoly.divMod (MO Fc ks m) c.1 g).1) /
      T.phi m (GPoly.toPoly M (GPoly.divMod (MO Fc ks m) c.2 g).1) =
        T.phi m (GPoly.toPoly M c.1) / T.phi m (GPoly.toPoly M c.2)
    rw [e1, e2, map_mul, map_mul]
    have hφg : T.phi m (GPoly.toPoly M g) ≠ 0 := fun h0 ↦ hg0 (T.phi_injective htr
      (by rw [h0, map_zero]))
    rw [mul_div_mul_right _ _ hφg]

/-- The denominator of `redC c` is non-zero. -/
lemma redC_den_ne_zero (c : LC (m + 1)) :
    GPoly.toPoly (T.MP m h1.of_succ) (redC Fc ks m c).2 ≠ 0 := by
  set M := T.MP m h1.of_succ
  by_cases hz : GPoly.isZero (MO Fc ks m) c.2 = true
  · rw [redC_of_zero Fc ks m c hz]
    show GPoly.toPoly M [(MO Fc ks m).one] ≠ 0
    simp [GPoly.toPoly, M.sem_one]
  · rw [redC_of_ne Fc ks m c hz]
    have hc2 : GPoly.toPoly M c.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    obtain ⟨-, hg2⟩ := GPoly.egcd_dvd M c.1 c.2
    have hg0 : GPoly.toPoly M (GPoly.egcd (MO Fc ks m) c.1 c.2).1 ≠ 0 := fun h0 ↦
      hc2 (zero_dvd_iff.mp (h0 ▸ hg2))
    have e2 := GPoly.div_mul_of_dvd M c.2 _ hg0 hg2
    intro h0
    exact hc2 (by rw [e2, h0, zero_mul])

/-- **The reduced denominator is squarefree** when the value has a squarefree denominator. -/
lemma redC_den_squarefree (htr : Transcendental (T.F m) (T.ts m)) (c : LC (m + 1))
    (A S : (T.F m)[X]) (hS : Squarefree S)
    (hval : (T.MPr (m + 1) h1).sem c = T.phi m A / T.phi m S) :
    Squarefree (GPoly.toPoly (T.MP m h1.of_succ) (redC Fc ks m c).2) := by
  classical
  set M := T.MP m h1.of_succ
  have hS0 : S ≠ 0 := hS.ne_zero
  have hφS : T.phi m S ≠ 0 := fun h0 ↦ hS0 (T.phi_injective htr (by rw [h0, map_zero]))
  by_cases hz : GPoly.isZero (MO Fc ks m) c.2 = true
  · rw [redC_of_zero Fc ks m c hz]
    show Squarefree (GPoly.toPoly M [(MO Fc ks m).one])
    have : GPoly.toPoly M [(MO Fc ks m).one] = 1 := by simp [GPoly.toPoly, M.sem_one]
    rw [this]; exact squarefree_one
  · rw [redC_of_ne Fc ks m c hz]
    have hc2 : GPoly.toPoly M c.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    obtain ⟨hg1, hg2⟩ := GPoly.egcd_dvd M c.1 c.2
    set g := (GPoly.egcd (MO Fc ks m) c.1 c.2).1
    have hg0 : GPoly.toPoly M g ≠ 0 := fun h0 ↦ hc2 (zero_dvd_iff.mp (h0 ▸ hg2))
    have e1 := GPoly.div_mul_of_dvd M c.1 g hg0 hg1
    have e2 := GPoly.div_mul_of_dvd M c.2 g hg0 hg2
    set q1 := GPoly.toPoly M (GPoly.divMod (MO Fc ks m) c.1 g).1
    set q2 := GPoly.toPoly M (GPoly.divMod (MO Fc ks m) c.2 g).1
    have hq2 : q2 ≠ 0 := fun h0 ↦ hc2 (by rw [e2, h0, zero_mul])
    -- `q₁ S = A q₂`
    have hφq2 : T.phi m q2 ≠ 0 := fun h0 ↦ hq2 (T.phi_injective htr (by rw [h0, map_zero]))
    have hφg : T.phi m (GPoly.toPoly M g) ≠ 0 := fun h0 ↦ hg0 (T.phi_injective htr
      (by rw [h0, map_zero]))
    rw [MPr_sem, T.sem_MP_succ] at hval
    change T.phi m (GPoly.toPoly M c.1) / T.phi m (GPoly.toPoly M c.2) = _ at hval
    rw [e1, e2, map_mul, map_mul, mul_div_mul_right _ _ hφg, div_eq_div_iff hφq2 hφS] at hval
    have heq : q1 * S = A * q2 := T.phi_injective htr (by rw [map_mul, map_mul, hval])
    -- `q₁`, `q₂` are coprime
    have hcop : IsCoprime q1 q2 := by
      rw [← EuclideanDomain.gcd_isUnit_iff]
      have hd1 : EuclideanDomain.gcd q1 q2 * GPoly.toPoly M g ∣ GPoly.toPoly M c.1 := by
        rw [e1]; exact mul_dvd_mul_right (EuclideanDomain.gcd_dvd_left _ _) _
      have hd2 : EuclideanDomain.gcd q1 q2 * GPoly.toPoly M g ∣ GPoly.toPoly M c.2 := by
        rw [e2]; exact mul_dvd_mul_right (EuclideanDomain.gcd_dvd_right _ _) _
      have hdg := GPoly.dvd_egcd M c.1 c.2 hd1 hd2
      obtain ⟨u, hu⟩ := hdg
      have : GPoly.toPoly M g * (EuclideanDomain.gcd q1 q2 * u) = GPoly.toPoly M g * 1 := by
        rw [mul_one]; conv_rhs => rw [hu]
        ring
      have h1' := mul_left_cancel₀ hg0 this
      exact IsUnit.of_mul_eq_one _ h1'
    have hdvd : q2 ∣ S := hcop.symm.dvd_of_dvd_mul_left ⟨A, by rw [heq]; ring⟩
    exact hS.squarefree_of_dvd hdvd

lemma sem_getD_map_redC (htr : Transcendental (T.F m) (T.ts m)) (l : List (LC (m + 1))) (j : ℕ) :
    (T.MPr (m + 1) h1).sem ((l.map (redC Fc ks m)).getD j (MOr Fc ks (m + 1)).zero) =
      (T.MPr (m + 1) h1).sem (l.getD j (MOr Fc ks (m + 1)).zero) := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj, T.sem_redC m h1 htr]
  · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by omega)]

lemma getD_map_map_redC (Mw : List (List (LC (m + 1)))) (i : ℕ) :
    (Mw.map fun l ↦ l.map (redC Fc ks m)).getD i [] = (Mw.getD i []).map (redC Fc ks m) := by
  have := List.getD_map (fun l : List (LC (m + 1)) ↦ l.map (redC Fc ks m)) (l := Mw) (n := i) (d := [])
  simpa using this

variable {m}

/-- `exactWR` on reduced codes meets the specification of an exact test in a basis. -/
lemma wexSpec_exactWR (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim) (r : ℕ → ℤ) :
    T.WexSpec m h1 (fun N Mw fw ↦ exactWR Fc ks m η lim N (Mw.map fun l ↦ l.map (redC Fc ks m))
      (fw.map (redC Fc ks m)) r) := by
  intro N Mc f θw hw hind res hres
  have hw' : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (((Mc.map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) * θw j := by
    intro i hi
    rw [hw i hi]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have := T.exactWR_correct h1 hm hk htr lim hlim N _ _ r θw hw' hind res hres
  rw [this]
  simp only [T.sem_getD_map_redC m h1 htr]

/-- **Correctness of `exactTR`**: for any `T`, `T⁻¹` (checked) and shifts `r`, an answer decides
the existence of an antiderivative in `Fₘ₊₁(θ)`. -/
theorem exactTR_correct (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTR Fc ks m η lim r P Tc Ti f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j :=
  T.exactTG_correct m h1 _ (T.wexSpec_exactWR h1 hm hk htr lim hlim r) P f θ hP hind Tc Ti res hres

end MTower

end Curves.MT
