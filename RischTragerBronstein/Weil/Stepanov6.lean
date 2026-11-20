import RischTragerBronstein.Weil.Stepanov4
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Stepanov's method, step 6: many square values

For `p ≥ (16 (d + 2)(L + d + 2))²` (`d = deg f`, `f` with an irreducible factor of odd
multiplicity), `f` takes at least `L` non-zero square values on `𝔽_p` (`many_squares`): Stepanov's
bound with `M = 2⌊√p/2⌋`, `J = M/2 + d + 2`, `K₀ = ⌊(p − d + 1)/2⌋` bounds the non-squares by
`p − d − L`, and the zeros are at most `d`.
-/

open Polynomial

namespace Stepanov

variable {p : ℕ} [hp : Fact p.Prime]

lemma card_zeros_le (f : (ZMod p)[X]) (hf0 : f ≠ 0) :
    (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0).card ≤ f.natDegree := by
  classical
  calc (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0).card ≤ f.roots.toFinset.card := by
        refine Finset.card_le_card fun x hx ↦ ?_
        rw [Multiset.mem_toFinset, mem_roots hf0]
        exact (Finset.mem_filter.mp hx).2
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' f

lemma stepArith (p d L s a K₀ : ℕ) (hs1 : s * s ≤ p) (hsL : 16 * (d + 2) * (L + d + 2) ≤ s)
    (ha1 : 2 * a ≤ s) (ha2 : s ≤ 2 * a + 1) (hK1 : p ≤ 2 * K₀ + d) :
    2 * a * (a + d + 2 + K₀ + 2 * a * d) < (a + d + 2) * (K₀ + K₀) := by
  have hds : 16 * (d + 2) ≤ s := le_trans (by nlinarith) hsL
  have h1 : 4 * (a * a) ≤ p := by nlinarith
  have h2 : 32 * (a * (d + 2)) ≤ p := by nlinarith
  have h3 : 16 * ((d + 2) * (d + 2)) ≤ p := by nlinarith
  have h4 : (d + 2) * p ≤ (d + 2) * (2 * K₀) + (d + 2) * d := by nlinarith
  have h5 : 4 * (a * a) * d ≤ p * d := Nat.mul_le_mul_right _ h1
  have hp : 1 ≤ p := le_trans (by nlinarith) h3
  nlinarith

lemma stepArith2 (p d L s a N K₀ : ℕ) (hs1 : s * s ≤ p) (hsL : 16 * (d + 2) * (L + d + 2) ≤ s)
    (ha1 : 2 * a ≤ s) (ha2 : s ≤ 2 * a + 1) (hKp : K₀ ≤ p)
    (h : 2 * a * N ≤ (a + d + 1) * p + K₀ + (p - 1) / 2 * d) : N + d + L ≤ p := by
  by_contra hcon
  push_neg at hcon
  have hcd : (p - 1) / 2 * d ≤ p * d := Nat.mul_le_mul_right _ (by omega)
  have hds : 16 * (d + 2) ≤ s := le_trans (by nlinarith) hsL
  have h4 : 4 * d + 8 ≤ a := by nlinarith
  have h5 : 8 * (a * (d + L)) ≤ p := by nlinarith
  have h6 : 2 * a * (p + 1) ≤ 2 * a * (N + d + L) := Nat.mul_le_mul_left _ hcon
  nlinarith

/-- **Many square values.** -/
theorem many_squares (hp2 : p ≠ 2) (f : (ZMod p)[X]) (hd : 1 ≤ f.natDegree) (P : (ZMod p)[X])
    (hP : Irreducible P) (e : ℕ) (he : Odd e) (hPe : P ^ e ∣ f) (hPe1 : ¬ P ^ (e + 1) ∣ f)
    (L : ℕ) (hpL : (16 * (f.natDegree + 2) * (L + f.natDegree + 2)) ^ 2 ≤ p) :
    L ≤ (Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ (p / 2) = 1).card := by
  have hf0 : f ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hd; omega
  set d := f.natDegree with hdd
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hc : (p - 1) / 2 = p / 2 := by omega
  set s := Nat.sqrt p with hs
  have hs1 : s * s ≤ p := by have := Nat.sqrt_le' p; rwa [sq] at this
  have hsL : 16 * (d + 2) * (L + d + 2) ≤ s := Nat.le_sqrt'.mpr hpL
  set a := s / 2 with ha
  have ha1 : 2 * a ≤ s := by omega
  have ha2 : s ≤ 2 * a + 1 := by omega
  have hds : d + 2 ≤ s := le_trans (by nlinarith) hsL
  have hdp : d + 2 ≤ p := le_trans hds (by nlinarith)
  set K₀ := (p - d + 1) / 2 with hK
  have hK1 : p ≤ 2 * K₀ + d := by omega
  have hKp : K₀ ≤ p := by omega
  have hcount := stepArith p d L s a K₀ hs1 hsL ha1 ha2 hK1
  have hsp : s ≤ p := by nlinarith
  have hst := stepanov hp2 f hd P hP e he hPe hPe1 (-1) (a + d + 2) K₀ (2 * a) (by omega)
    (by omega) (by omega) (by omega) hcount
    (Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ (p / 2) = -1)
    (fun x hx ↦ by rw [hc]; exact (Finset.mem_filter.mp hx).2)
  set Non := (Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ (p / 2) = -1)
  set Sq := (Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ (p / 2) = 1)
  set Z := (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0)
  have hpart : Z.card + Sq.card + Non.card = p := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : ZMod p ↦ f.eval x = 0)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun x : ZMod p ↦ ¬ f.eval x = 0)
      (fun x : ZMod p ↦ f.eval x ^ (p / 2) = 1)
    rw [Finset.card_univ, ZMod.card] at h1
    have e1 : (Finset.univ.filter fun x : ZMod p ↦ ¬ f.eval x = 0).filter
        (fun x ↦ f.eval x ^ (p / 2) = 1) = Sq := by
      ext x; simp [Sq]
    have e2 : (Finset.univ.filter fun x : ZMod p ↦ ¬ f.eval x = 0).filter
        (fun x ↦ ¬ f.eval x ^ (p / 2) = 1) = Non := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Non]
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨h0, (ZMod.pow_div_two_eq_neg_one_or_one p h0).resolve_left h1⟩
      · rintro ⟨h0, h1⟩
        refine ⟨h0, fun h ↦ ?_⟩
        rw [h] at h1
        have : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h1
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.le_of_dvd (by norm_num) this
        have := hp.out.two_le
        omega
    rw [e1, e2] at h2
    have hZd : Z.card = (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0).card := rfl
    omega
  have hZ : Z.card ≤ d := card_zeros_le f hf0
  have hNon := stepArith2 p d L s a Non.card K₀ hs1 hsL ha1 ha2 hKp (by
    have := hst; rw [show a + d + 2 - 1 = a + d + 1 by omega] at this; exact this)
  omega

end Stepanov
