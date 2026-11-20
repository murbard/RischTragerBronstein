import RischTragerBronstein.Jacobian.Existence
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content

/-!
# Helpers for the global torsion argument

* `eval_add_taylor`: `P(x + t) = P(x) + t P′(x) + t² s`;
* `emap`, `escale`, `E0L`: images of divisors, multiples, and the base divisor as a list;
* `wpoly_dvd'`: divisibility by `wpoly Γ` over a commutative ring when the abscissae differ by
  units;
* `hpow`: powers of functions, with vanishing orders and pole bounds;
* `sigma_disc_unique`: a function vanishing at `(x, −y)` and at a nearby `(z, −Y)` with a unit
  first-order coefficient forces `z = x`;
* `exists_integer_pair`: clearing denominators of a pair over the fraction field.
-/

open Polynomial

namespace Jac

section Taylor

variable {R : Type*} [CommRing R]

lemma eval_add_taylor (P : R[X]) (x t : R) :
    ∃ s, P.eval (x + t) = P.eval x + t * P.derivative.eval x + t ^ 2 * s := by
  set Q := taylor x P
  have hQ : X ^ 2 ∣ Q - C (Q.coeff 0) - C (Q.coeff 1) * X := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d <;> simp [coeff_C, coeff_X]
  obtain ⟨S, hS⟩ := hQ
  refine ⟨S.eval t, ?_⟩
  have e := congrArg (eval t) hS
  simp only [eval_sub, eval_C, eval_mul, eval_X, eval_pow] at e
  rw [taylor_eval, taylor_coeff_zero, taylor_coeff_one] at e
  rw [add_comm x t]
  linear_combination e

end Taylor

section Divs

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The image of a divisor under a ring map. -/
def emap (φ : R →+* S) (Γ : EDiv R) : EDiv S := Γ.map fun q ↦ (φ q.1, φ q.2.1, q.2.2)

/-- `n · Γ`. -/
def escale (n : ℕ) (Γ : EDiv R) : EDiv R := Γ.map fun q ↦ (q.1, q.2.1, n * q.2.2)

/-- The divisor `∑ Pᵢ` as a list. -/
def E0L {g : ℕ} (x y : Fin g → R) : EDiv R := List.ofFn fun i ↦ (x i, y i, 1)

lemma edeg_emap (φ : R →+* S) (Γ : EDiv R) : edeg (emap φ Γ) = edeg Γ := by
  simp [edeg, emap, Function.comp_def]

lemma edeg_escale (n : ℕ) (Γ : EDiv R) : edeg (escale n Γ) = n * edeg Γ := by
  unfold edeg escale
  induction Γ with
  | nil => simp
  | cons q Γ ih => simp only [List.map_cons, List.sum_cons, List.map_map] at ih ⊢; rw [ih]; ring

lemma edeg_E0L {g : ℕ} (x y : Fin g → R) : edeg (E0L x y) = g := by
  simp [edeg, E0L, List.sum_ofFn]

lemma edeg_append (Γ Δ : EDiv R) : edeg (Γ ++ Δ) = edeg Γ + edeg Δ := by
  simp [edeg]

lemma wpoly_append (Γ Δ : EDiv R) : wpoly (Γ ++ Δ) = wpoly Γ * wpoly Δ := by
  simp [wpoly]

lemma wpoly_E0L {g : ℕ} (x y : Fin g → R) : wpoly (E0L x y) = ∏ i, (X - C (x i)) := by
  simp [wpoly, E0L, List.prod_ofFn]

lemma wpoly_escale (n : ℕ) (Γ : EDiv R) : wpoly (escale n Γ) = wpoly Γ ^ n := by
  unfold wpoly escale
  induction Γ with
  | nil => simp
  | cons q Γ ih =>
    simp only [List.map_cons, List.prod_cons, List.map_map] at ih ⊢
    rw [ih, mul_pow, ← pow_mul, mul_comm n]

lemma wpoly_emap (φ : R →+* S) (Γ : EDiv R) : wpoly (emap φ Γ) = (wpoly Γ).map φ := by
  unfold wpoly emap
  induction Γ with
  | nil => simp
  | cons q Γ ih =>
    simp only [List.map_cons, List.prod_cons, List.map_map] at ih ⊢
    rw [Polynomial.map_mul, ← ih, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]

lemma econj_append (Γ Δ : EDiv R) : econj (Γ ++ Δ) = econj Γ ++ econj Δ := by
  simp [econj]

lemma Vanishes.append {f : R[X]} {ψ : R[X] × R[X]} {Γ Δ : EDiv R} :
    Vanishes f ψ (Γ ++ Δ) ↔ Vanishes f ψ Γ ∧ Vanishes f ψ Δ := by
  simp only [Vanishes, List.mem_append]
  exact ⟨fun h ↦ ⟨fun q hq ↦ h q (Or.inl hq), fun q hq ↦ h q (Or.inr hq)⟩,
    fun h q hq ↦ hq.elim (h.1 q) (h.2 q)⟩

lemma Vanishes.map {φ : R →+* S} {f : R[X]} {ψ : R[X] × R[X]} {Γ : EDiv R}
    (h : Vanishes f ψ Γ) : Vanishes (f.map φ) (ψ.1.map φ, ψ.2.map φ) (emap φ Γ) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact (h q' hq').map φ

lemma emap_econj (φ : R →+* S) (Γ : EDiv R) : emap φ (econj Γ) = econj (emap φ Γ) := by
  simp [emap, econj, Function.comp_def]

lemma OnCurve.map {φ : R →+* S} {f : R[X]} {Γ : EDiv R} (h : OnCurve f Γ) :
    OnCurve (f.map φ) (emap φ Γ) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  obtain ⟨h1, h2⟩ := h q' hq'
  refine ⟨by have := h1.map φ; rwa [map_mul, map_ofNat] at this, ?_⟩
  rw [eval_map, eval₂_hom, ← h2, map_pow]

lemma OnCurve.append {f : R[X]} {Γ Δ : EDiv R} :
    OnCurve f (Γ ++ Δ) ↔ OnCurve f Γ ∧ OnCurve f Δ := by
  simp only [OnCurve, List.mem_append]
  exact ⟨fun h ↦ ⟨fun q hq ↦ h q (Or.inl hq), fun q hq ↦ h q (Or.inr hq)⟩,
    fun h q hq ↦ hq.elim (h.1 q) (h.2 q)⟩

/-- **Divisibility by `wpoly`** over a commutative ring. -/
lemma wpoly_dvd' {Γ : EDiv R} (hΓ : Γ.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1)) {P : R[X]}
    (h : ∀ q ∈ Γ, (X - C q.1) ^ q.2.2 ∣ P) : wpoly Γ ∣ P := by
  unfold wpoly
  induction Γ with
  | nil => simp
  | cons q Γ ih =>
    rw [List.pairwise_cons] at hΓ
    rw [List.map_cons, List.prod_cons]
    refine IsCoprime.mul_dvd ?_ (h q List.mem_cons_self)
      (ih hΓ.2 fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq'))
    have hcop : ∀ L : EDiv R, (∀ q' ∈ L, IsUnit (q.1 - q'.1)) →
        IsCoprime ((X - C q.1) ^ q.2.2) (L.map fun q ↦ (X - C q.1) ^ q.2.2).prod := by
      intro L hL
      induction L with
      | nil => exact isCoprime_one_right
      | cons r L ihL =>
        rw [List.map_cons, List.prod_cons]
        refine IsCoprime.mul_right ?_ (ihL fun q' hq' ↦ hL q' (List.mem_cons_of_mem _ hq'))
        refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub ?_)
        exact hL r List.mem_cons_self
    exact hcop Γ hΓ.1

end Divs

section Pow

variable {R : Type*} [CommRing R]

/-- `ψⁿ`. -/
noncomputable def hpow (f : R[X]) (ψ : R[X] × R[X]) : ℕ → R[X] × R[X]
  | 0 => (1, 0)
  | n + 1 => hmul f (hpow f ψ n) ψ

lemma VanishAt.zero {f a b : R[X]} {x₀ Y₀ : R} (h2Y : IsUnit (2 * Y₀))
    (hY : Y₀ ^ 2 = f.eval x₀) : VanishAt f a b x₀ Y₀ 0 := by
  obtain ⟨V, hV⟩ := exists_branch h2Y hY 0
  exact ⟨V, hV, by simp⟩

lemma VanishAt.hpow {f : R[X]} {ψ : R[X] × R[X]} {x₀ Y₀ : R} {k : ℕ} (h2Y : IsUnit (2 * Y₀))
    (hY : Y₀ ^ 2 = f.eval x₀) (h : VanishAt f ψ.1 ψ.2 x₀ Y₀ k) :
    ∀ n, VanishAt f (hpow f ψ n).1 (hpow f ψ n).2 x₀ Y₀ (n * k)
  | 0 => by simp only [zero_mul]; exact VanishAt.zero h2Y hY
  | n + 1 => by
    rw [add_mul, one_mul]
    exact VanishAt.hmul h2Y hY (VanishAt.hpow h2Y hY h n) h

lemma PoleLE.hpow {g : ℕ} {f : R[X]} (hf : f.natDegree ≤ 2 * g + 1) {ψ : R[X] × R[X]} {N : ℕ}
    (h : PoleLE g ψ N) : ∀ n, PoleLE g (hpow f ψ n) (n * N)
  | 0 => ⟨by simp [Jac.hpow], Or.inl rfl⟩
  | n + 1 => by
    rw [add_mul, one_mul]
    exact PoleLE.hmul hf (PoleLE.hpow hf h n) h

lemma hpow_ne_zero [IsDomain R] {f : R[X]} (hf : Odd f.natDegree) {ψ : R[X] × R[X]}
    (hψ : ψ ≠ (0, 0)) : ∀ n, hpow f ψ n ≠ (0, 0)
  | 0 => by simp [hpow]
  | n + 1 => hmul_ne_zero hf (hpow_ne_zero hf hψ n) hψ

end Pow

section Disc

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

lemma isUnit_add_mem {u m : O} (hu : IsUnit u) (hm : m ∈ IsLocalRing.maximalIdeal O) :
    IsUnit (u + m) := by
  by_contra h
  have h1 : u + m ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : u ∈ IsLocalRing.maximalIdeal O := by
    have := Ideal.sub_mem _ h1 hm; rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 hu

/-- **Uniqueness in a residue disc.** If `a − b y` vanishes at `(x, y)` and `(z, Y)`, with
`z ≡ x`, `Y ≡ y` and the first-order coefficient `a′(x) − b′(x) y − b(x) f′(x) / (2y)` a unit,
then `z = x`. -/
theorem sigma_disc_unique {f a b : O[X]} {x y z Y w : O} (hw : w * (2 * y) = 1)
    (hy : y ^ 2 = f.eval x) (hY : Y ^ 2 = f.eval z)
    (hz : z - x ∈ IsLocalRing.maximalIdeal O) (hYy : Y - y ∈ IsLocalRing.maximalIdeal O)
    (h1 : a.eval x - b.eval x * y = 0) (h2 : a.eval z - b.eval z * Y = 0)
    (hΛ : IsUnit (a.derivative.eval x - b.derivative.eval x * y -
      b.eval x * f.derivative.eval x * w)) : z = x := by
  set t := z - x with ht
  have hzt : z = x + t := by ring
  obtain ⟨sa, hsa⟩ := eval_add_taylor a x t
  obtain ⟨sb, hsb⟩ := eval_add_taylor b x t
  obtain ⟨sf, hsf⟩ := eval_add_taylor f x t
  set e := Y - y with he
  have h2y : IsUnit (2 * y) := ⟨⟨2 * y, w, by rw [mul_comm]; exact hw, hw⟩, rfl⟩
  have hu : IsUnit (Y + y) := by
    have : Y + y = 2 * y + e := by ring
    rw [this]; exact isUnit_add_mem h2y hYy
  obtain ⟨ui, hui⟩ : ∃ ui, ui * (Y + y) = 1 := ⟨↑(hu.unit⁻¹), by simp⟩
  have hee : e * (Y + y) = t * f.derivative.eval x + t ^ 2 * sf := by
    rw [he, show (Y - y) * (Y + y) = Y ^ 2 - y ^ 2 by ring, hY, hy, hzt, hsf]; ring
  have he' : e = t * (f.derivative.eval x + t * sf) * ui := by
    linear_combination ui * hee - e * hui
  set Λ := a.derivative.eval x + t * sa - b.eval x * (f.derivative.eval x + t * sf) * ui -
    (b.derivative.eval x + t * sb) * (y + e)
  have hkey : t * Λ = 0 := by
    rw [hzt] at h2
    rw [hsa, hsb] at h2
    have hYe : Y = y + e := by ring
    rw [hYe] at h2
    rw [he'] at h2
    simp only [Λ]
    rw [he']
    linear_combination h2 - h1
  have hΛ' : IsUnit Λ := by
    have e1 : Λ = (a.derivative.eval x - b.derivative.eval x * y -
        b.eval x * f.derivative.eval x * w) +
        (t * (sa - b.eval x * sf * ui - sb * (y + e)) +
          e * (b.eval x * f.derivative.eval x * w * ui - b.derivative.eval x)) := by
      simp only [Λ]
      linear_combination (b.eval x * f.derivative.eval x) * (-w * hui + ui * hw - w * ui * he)
    rw [e1]
    refine isUnit_add_mem hΛ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hz)
      (Ideal.mul_mem_right _ _ hYy))
  have ht0 : t = 0 := (mul_eq_zero.mp hkey).resolve_right hΛ'.ne_zero
  rw [hzt, ht0, add_zero]

end Disc

end Jac
