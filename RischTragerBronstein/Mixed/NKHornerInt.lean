import RischTragerBronstein.Mixed.NKLogDecide

/-!
# Integrality certificates in Horner form

A list `cs = [c_{k-1}, …, c₀]` describes the monic polynomial `Z^k + c_{k-1} Z^{k-1} + ⋯ + c₀`
in Horner form (`hornerP`). `hornerD` evaluates `δ^k · q(u/δ)` without division — the form a
certificate check can compute with codes — and `hornerD_eq` relates the two. A root of such a
polynomial whose coefficients are regular Laurent series is regular (`lowerBd_of_horner`).
-/

open Polynomial HahnSeries LaurentSeries

namespace Curves

/-- Horner value `hz cs a`: start from `a`, then `a ↦ a z + c` for each `c ∈ cs`. -/
def hornerZ {R : Type*} [CommRing R] (z : R) : List R → R → R
  | [], a => a
  | c :: cs, a => hornerZ z cs (a * z + c)

/-- The division-free version: `acc ↦ acc u + c Dp δ`, `Dp ↦ Dp δ`. -/
def hornerD {R : Type*} [CommRing R] (u δ : R) : List R → R → R → R
  | [], acc, _ => acc
  | c :: cs, acc, Dp => hornerD u δ cs (acc * u + c * (Dp * δ)) (Dp * δ)

/-- The Horner polynomial: start from `p`, then `p ↦ p X + C c`. -/
noncomputable def hornerP {R : Type*} [CommRing R] : List R → R[X] → R[X]
  | [], p => p
  | c :: cs, p => hornerP cs (p * X + Polynomial.C c)

lemma hornerD_eq {F : Type*} [Field F] (u δ : F) (hδ : δ ≠ 0) :
    ∀ (cs : List F) (acc Dp : F), Dp ≠ 0 →
      hornerD u δ cs acc Dp = Dp * δ ^ cs.length * hornerZ (u / δ) cs (acc / Dp)
  | [], acc, Dp, hD => by simp [hornerD, hornerZ, mul_div_cancel₀ _ hD]
  | c :: cs, acc, Dp, hD => by
    have hD' : Dp * δ ≠ 0 := mul_ne_zero hD hδ
    have hq : (acc * u + c * (Dp * δ)) / (Dp * δ) = acc / Dp * (u / δ) + c := by
      field_simp
    rw [hornerD, hornerD_eq u δ hδ cs _ _ hD', hornerZ, List.length_cons, pow_succ, hq]
    ring

lemma hornerZ_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    ∀ (cs : List R) (a : R), φ (hornerZ z cs a) = hornerZ (φ z) (cs.map φ) (φ a)
  | [], a => rfl
  | c :: cs, a => by
    rw [hornerZ, hornerZ_map φ z cs, List.map_cons, hornerZ, map_add, map_mul]

lemma eval_hornerP {R : Type*} [CommRing R] (z : R) :
    ∀ (cs : List R) (p : R[X]), (hornerP cs p).eval z = hornerZ z cs (p.eval z)
  | [], p => rfl
  | c :: cs, p => by
    rw [hornerP, eval_hornerP z cs, hornerZ, eval_add, eval_mul, eval_X, Polynomial.eval_C]

lemma hornerP_monic {R : Type*} [CommRing R] [Nontrivial R] :
    ∀ (cs : List R) (p : R[X]), p.Monic → (hornerP cs p).Monic
  | [], p, hp => hp
  | c :: cs, p, hp => by
    refine hornerP_monic cs _ ?_
    have hpX : (p * X).Monic := hp.mul monic_X
    refine hpX.add_of_left (lt_of_le_of_lt degree_C_le ?_)
    rw [degree_eq_natDegree hpX.ne_zero, natDegree_mul_X hp.ne_zero]
    exact_mod_cast Nat.succ_pos _

variable {K : Type*} [Field K]

lemma lowerBd_one : LowerBd (1 : LaurentSeries K) 0 := fun k hk ↦ by
  simp [HahnSeries.coeff_one, hk.ne]

lemma hornerP_coeff_lowerBd :
    ∀ (cs : List (LaurentSeries K)) (p : (LaurentSeries K)[X]), (∀ i, LowerBd (p.coeff i) 0) →
      (∀ c ∈ cs, LowerBd c 0) → ∀ i, LowerBd ((hornerP cs p).coeff i) 0
  | [], p, hp, _ => hp
  | c :: cs, p, hp, hcs => by
    refine hornerP_coeff_lowerBd cs _ (fun i ↦ ?_) (fun c' hc' ↦ hcs c' (List.mem_cons_of_mem _ hc'))
    rw [Polynomial.coeff_add, Polynomial.coeff_C]
    rcases i with _ | i
    · simp only [coeff_mul_X_zero, zero_add, ↓reduceIte]; exact hcs c List.mem_cons_self
    · simp only [coeff_mul_X, Nat.succ_ne_zero, ↓reduceIte, add_zero]; exact hp i

/-- **A root of a monic polynomial with regular coefficients is regular.** -/
lemma lowerBd_of_horner (z : LaurentSeries K) (cs : List (LaurentSeries K))
    (hcs : ∀ c ∈ cs, LowerBd c 0) (h : hornerZ z cs 1 = 0) : LowerBd z 0 := by
  refine lowerBd_root (hornerP cs 1) (hornerP_monic cs 1 monic_one)
    (hornerP_coeff_lowerBd cs 1 (fun i ↦ ?_) hcs) z (by rw [eval_hornerP, eval_one]; exact h)
  rw [Polynomial.coeff_one]
  split_ifs
  · exact lowerBd_one
  · exact lowerBd_zero 0

end Curves
