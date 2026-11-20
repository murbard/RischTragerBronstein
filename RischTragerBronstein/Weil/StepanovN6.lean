import RischTragerBronstein.Weil.StepanovN4
import RischTragerBronstein.Weil.Stepanov6

/-!
# Stepanov's method for `n`-th powers, step 6: many `n`-th power values

For `n ∣ p − 1` and `p ≥ (16 n² (d + 2)(L + d + 2))²` (`d = deg f`, `f` with an irreducible factor of
multiplicity prime to `n`), `f` takes at least `L` non-zero `n`-th power values on `𝔽_p`, i.e.
`f(x) ≠ 0` and `f(x)^{(p−1)/n} = 1` (`many_nth_powers`). For `f(x) ≠ 0`, `f(x)^{(p−1)/n}` is an
`n`-th root of unity; each of the `≤ n − 1` classes `ε ≠ 1` has at most `p/n + O(d √p)` elements
(`stepanovN` with `M = n ⌊√p/n⌋`, `J = M/n + d + 2`, `K₀ = (p − 1)/n − d`).
-/

open Polynomial

namespace Stepanov

/-- Monotonicity facts for the bound `s ≥ 16 n² B`, `B = (d + 2)(L + d + 2)`. -/
lemma nthBase (n d L s : ℕ) (hn : 1 ≤ n) (hsL : 16 * n * n * (d + 2) * (L + d + 2) ≤ s) :
    16 * (n * (d + 2)) ≤ s ∧ 16 * (n * (d + 2) * (n * (d + L + 1))) ≤ s ∧ 16 * (n * n) ≤ s := by
  have hB : n * (d + 2) * (n * (d + L + 1)) ≤ n * n * (d + 2) * (L + d + 2) := by
    have : n * (d + 2) * (n * (d + L + 1)) = n * n * (d + 2) * (d + L + 1) := by ring
    rw [this]; exact Nat.mul_le_mul_left _ (by omega)
  have h1 : n * (d + 2) ≤ n * (d + 2) * (n * (d + L + 1)) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have h2 : n * n ≤ n * n * (d + 2) * (L + d + 2) := by
    have : n * n * (d + 2) * (L + d + 2) = n * n * ((d + 2) * (L + d + 2)) := by ring
    rw [this]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have e : 16 * n * n * (d + 2) * (L + d + 2) = 16 * (n * n * (d + 2) * (L + d + 2)) := by ring
  rw [e] at hsL
  refine ⟨le_trans (Nat.mul_le_mul_left 16 (le_trans h1 hB)) hsL,
    le_trans (Nat.mul_le_mul_left 16 hB) hsL, le_trans (Nat.mul_le_mul_left 16 h2) hsL⟩

lemma nthArith1 (p n d L s a K₀ : ℕ) (hn : 1 ≤ n) (hs1 : s * s ≤ p)
    (hsL : 16 * n * n * (d + 2) * (L + d + 2) ≤ s) (ha1 : n * a ≤ s) (hK : n * K₀ + n * d + 1 = p) :
    n * a * (a + d + 2 + K₀ + n * a * d) < n * (a + d + 2) * K₀ := by
  obtain ⟨hb1, hb2, -⟩ := nthBase n d L s hn hsL
  have h1 : n * a * (n * a) ≤ p := le_trans (Nat.mul_le_mul ha1 ha1) hs1
  have h2 : n * a * a ≤ p := le_trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left a (by omega))) h1
  have h3 : n * a * (n * a) * d ≤ p * d := Nat.mul_le_mul_right _ h1
  have h4 : n * a * (d + 2) ≤ s * (d + 2) := Nat.mul_le_mul_right _ ha1
  have h5 : s * (d + 2) * 16 ≤ s * s := by
    have : 16 * (d + 2) ≤ s := le_trans (Nat.mul_le_mul_left 16 (Nat.le_mul_of_pos_left _ (by omega)))
      hb1
    nlinarith
  have h6 : (d + 2) * (n * d + 1) * 16 ≤ s := by
    have : (d + 2) * (n * d + 1) ≤ n * (d + 2) * (n * (d + L + 1)) := by
      have e1 : n * d + 1 ≤ n * (d + L + 1) := by nlinarith
      calc (d + 2) * (n * d + 1) ≤ (d + 2) * (n * (d + L + 1)) := Nat.mul_le_mul_left _ e1
        _ ≤ n * (d + 2) * (n * (d + L + 1)) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have h7 : 16 ≤ s := by
    have : 1 ≤ n * (d + 2) := Nat.mul_pos (by omega) (by omega)
    omega
  -- `n · LHS ≤ p + s (d + 2) + p d < (d + 2) n K₀`
  have hL : n * a * (a + d + 2 + K₀ + n * a * d) =
      n * a * a + n * a * (d + 2) + n * a * K₀ + n * a * (n * a) * d := by ring
  have hR : n * (a + d + 2) * K₀ = n * a * K₀ + (d + 2) * (n * K₀) := by ring
  rw [hL, hR]
  have hnK : (d + 2) * (n * K₀) + (d + 2) * (n * d + 1) = (d + 2) * p := by rw [← hK]; ring
  nlinarith

lemma nthArith2 (p n d L s a Q : ℕ) (hn : 1 ≤ n) (hs1 : s * s ≤ p)
    (hsL : 16 * n * n * (d + 2) * (L + d + 2) ≤ s) (ha2 : s < n * a + n)
    (hQ : Q = (a + 2 * d + 2) * p) :
    n * a * L + (n - 1) * Q + n * a * d ≤ n * a * p := by
  obtain ⟨hb1, hb2, hb3⟩ := nthBase n d L s hn hsL
  -- `a ≥ 8 (d + 2)(d + L + 1) n` roughly: `n a + n > s ≥ 16 n (d + 2) · n (d + L + 1)`
  have ha : 8 * ((d + 2) * (n * (d + L + 1))) ≤ a := by
    by_contra hcon
    push Not at hcon
    have e1 : n * a + n ≤ n * (8 * ((d + 2) * (n * (d + L + 1)))) := by
      have : a + 1 ≤ 8 * ((d + 2) * (n * (d + L + 1))) := hcon
      calc n * a + n = n * (a + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ this
    have e2 : n * (8 * ((d + 2) * (n * (d + L + 1)))) * 2 ≤ 16 * (n * (d + 2) * (n * (d + L + 1))) :=
      by ring_nf; omega
    omega
  have hp : 2 * n * (d + L) ≤ p := by
    have e1a : n * (d + L) ≤ n * (d + L + 1) := Nat.mul_le_mul_left n (by omega)
    have e1b : n * (d + L + 1) ≤ n * (d + 2) * (n * (d + L + 1)) :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
    have e2 : 2 * n * (d + L) ≤ s := by
      have : 2 * n * (d + L) = 2 * (n * (d + L)) := by ring
      omega
    have e3 : s ≤ s * s := Nat.le_mul_self s
    omega
  subst hQ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hap : 2 * (m * (2 * d + 2)) ≤ a := by
    have e1 : m * (d + 1) ≤ (m + 1) * (d + L + 1) := Nat.mul_le_mul (by omega) (by omega)
    have e2 : (m + 1) * (d + L + 1) ≤ (d + 2) * ((m + 1) * (d + L + 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have e3 : 2 * (m * (2 * d + 2)) = 4 * (m * (d + 1)) := by ring
    omega
  have hap' : 2 * (m * (2 * d + 2)) * p ≤ a * p := Nat.mul_le_mul_right _ hap
  have hap2 : (m + 1) * a * (d + L) * 2 ≤ a * p := by
    have := Nat.mul_le_mul_left a hp
    nlinarith
  have e : (m + 1) * a * L + m * ((a + 2 * d + 2) * p) + (m + 1) * a * d =
      (m + 1) * a * (d + L) + m * a * p + m * (2 * d + 2) * p := by ring
  rw [e]
  have e2 : (m + 1) * a * p = a * p + m * a * p := by ring
  rw [e2]
  nlinarith


variable {p : ℕ} [hp : Fact p.Prime]

lemma card_nthRootsFinset_le (n : ℕ) : (nthRootsFinset n (1 : ZMod p)).card ≤ n := by
  classical
  rw [nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots n 1)

/-- **Many `n`-th power values.** -/
theorem many_nth_powers (n : ℕ) (hn : 1 ≤ n) (hnp : n ∣ p - 1) (f : (ZMod p)[X])
    (hd : 1 ≤ f.natDegree) (P : (ZMod p)[X]) (hP : Irreducible P) (e : ℕ) (hen : Nat.Coprime e n)
    (hPe : P ^ e ∣ f) (hPe1 : ¬ P ^ (e + 1) ∣ f) (L : ℕ)
    (hpL : (16 * n * n * (f.natDegree + 2) * (L + f.natDegree + 2)) ^ 2 ≤ p) :
    L ≤ (Finset.univ.filter fun x : ZMod p ↦
      f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / n) = 1).card := by
  classical
  have hf0 : f ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hd; omega
  set d := f.natDegree with hdd
  set c := (p - 1) / n with hc
  have hnc : n * c = p - 1 := Nat.mul_div_cancel' hnp
  have hp1 := hp.out.one_lt
  set s := Nat.sqrt p with hs
  have hs1 : s * s ≤ p := Nat.sqrt_le p
  have hsL : 16 * n * n * (d + 2) * (L + d + 2) ≤ s := Nat.le_sqrt'.mpr hpL
  obtain ⟨hb1, hb2, hb3⟩ := nthBase n d L s hn hsL
  set a := s / n with ha
  have ha1 : n * a ≤ s := Nat.mul_div_le s n
  have ha2 : s < n * a + n := by
    have := Nat.lt_mul_div_succ s (show 0 < n by omega)
    rw [Nat.mul_add, mul_one] at this
    exact this
  have hapos : 1 ≤ a := by
    by_contra h0
    push Not at h0
    have : a = 0 := Nat.lt_one_iff.mp h0
    rw [this, mul_zero, zero_add] at ha2
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  -- `K₀ = c − d`
  have hcd : d + 1 ≤ c := by
    have h1 : n * (d + 1) < s := by
      have : n * (d + 1) < n * (d + 2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    have h2 : s ≤ s * s := Nat.le_mul_self s
    have h3 : n * (d + 1) < n * c + 1 := by omega
    have h4 : n * (d + 1) = n * d + n := by ring
    by_contra hcon
    push Not at hcon
    have : n * c ≤ n * d := Nat.mul_le_mul_left _ (by omega)
    omega
  set K₀ := c - d with hK₀
  have hK : n * K₀ + n * d + 1 = p := by
    have : n * K₀ + n * d = n * c := by rw [hK₀, ← Nat.mul_add]; congr 1; omega
    omega
  set J := a + d + 2 with hJ
  set M := n * a with hM
  have hMp : M ≤ p := le_trans ha1 (le_trans (Nat.le_mul_self s) hs1)
  have hdeg : n * (d + (K₀ - 1)) < p := by
    have hK1 : 1 ≤ K₀ := by omega
    have : n * (d + (K₀ - 1)) + n = n * d + n * K₀ := by
      obtain ⟨k, hk⟩ : ∃ k, K₀ = k + 1 := ⟨K₀ - 1, by omega⟩
      rw [hk]; simp only [Nat.add_sub_cancel]; ring
    omega
  have hcount : M * (J + K₀ + M * d) < n * J * K₀ := nthArith1 p n d L s a K₀ hn hs1 hsL ha1 hK
  set Q := (a + 2 * d + 2) * p with hQ
  -- each class `ε` is small
  have hclass : ∀ ε : ZMod p, M * (Finset.univ.filter fun x : ZMod p ↦
      f.eval x ≠ 0 ∧ f.eval x ^ c = ε).card ≤ Q := by
    intro ε
    have hst : M * (Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ c = ε).card ≤
        (J - 1) * p + K₀ + (n - 1) * c * d :=
      stepanovN n hn hnp f hd P hP e hen hPe hPe1 ε J K₀ M (by omega) (by omega) hMp
      hdeg hcount (Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ c = ε)
      (fun x hx ↦ (Finset.mem_filter.mp hx).2)
    have hnc1 : (n - 1) * c ≤ p := by
      have h0 : (n - 1) * c ≤ n * c := Nat.mul_le_mul_right c (Nat.sub_le n 1)
      rw [hnc] at h0
      omega
    have h1 : (n - 1) * c * d ≤ p * d := Nat.mul_le_mul_right d hnc1
    have h2 : (J - 1) * p = (a + d + 1) * p := by rw [hJ]; congr 1
    have h3 : K₀ ≤ p := by
      have : c ≤ n * c := Nat.le_mul_of_pos_left c (by omega)
      omega
    have hQe : Q = (a + d + 1) * p + p + p * d := by rw [hQ]; ring
    omega
  -- the partition
  set Z := Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0 with hZ
  set S1 := Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ c = 1 with hS1
  set O := Finset.univ.filter fun x : ZMod p ↦ f.eval x ≠ 0 ∧ f.eval x ^ c ≠ 1 with hO
  have hpart : Z.card + S1.card + O.card = p := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : ZMod p ↦ f.eval x = 0)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun x : ZMod p ↦ ¬ f.eval x = 0)
      (fun x : ZMod p ↦ f.eval x ^ c = 1)
    rw [Finset.card_univ, ZMod.card] at h1
    have e1 : (Finset.univ.filter fun x : ZMod p ↦ ¬ f.eval x = 0).filter
        (fun x ↦ f.eval x ^ c = 1) = S1 := by ext x; simp [hS1]
    have e2 : (Finset.univ.filter fun x : ZMod p ↦ ¬ f.eval x = 0).filter
        (fun x ↦ ¬ f.eval x ^ c = 1) = O := by ext x; simp [hO]
    rw [e1, e2] at h2
    have hZd : Z.card = (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0).card := rfl
    omega
  have hZ' : Z.card ≤ d := card_zeros_le f hf0
  -- the other classes
  set E := (nthRootsFinset n (1 : ZMod p)).erase 1 with hE
  have hEcard : E.card ≤ n - 1 := by
    have h1 : (1 : ZMod p) ∈ nthRootsFinset n (1 : ZMod p) :=
      (mem_nthRootsFinset (by omega) 1).mpr (one_pow n)
    rw [hE, Finset.card_erase_of_mem h1]
    have := card_nthRootsFinset_le (p := p) n
    omega
  have hOsub : O ⊆ E.biUnion fun ε ↦ Finset.univ.filter fun x : ZMod p ↦
      f.eval x ≠ 0 ∧ f.eval x ^ c = ε := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_biUnion.mpr ⟨f.eval x ^ c, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0, rfl⟩⟩
    refine Finset.mem_erase.mpr ⟨hx1, (mem_nthRootsFinset (by omega) 1).mpr ?_⟩
    rw [← pow_mul, mul_comm, hnc]
    exact ZMod.pow_card_sub_one_eq_one hx0
  have hOcard : M * O.card ≤ (n - 1) * Q := by
    have h1 := Finset.card_le_card hOsub
    have h2 := Finset.card_biUnion_le (s := E) (t := fun ε ↦ Finset.univ.filter fun x : ZMod p ↦
      f.eval x ≠ 0 ∧ f.eval x ^ c = ε)
    have h3 : M * ∑ ε ∈ E, (Finset.univ.filter fun x : ZMod p ↦
        f.eval x ≠ 0 ∧ f.eval x ^ c = ε).card ≤ E.card * Q := by
      rw [Finset.mul_sum]
      calc ∑ ε ∈ E, M * (Finset.univ.filter fun x : ZMod p ↦
            f.eval x ≠ 0 ∧ f.eval x ^ c = ε).card ≤ ∑ _ε ∈ E, Q :=
            Finset.sum_le_sum fun ε _ ↦ hclass ε
        _ = E.card * Q := by rw [Finset.sum_const, smul_eq_mul]
    calc M * O.card ≤ M * ∑ ε ∈ E, (Finset.univ.filter fun x : ZMod p ↦
          f.eval x ≠ 0 ∧ f.eval x ^ c = ε).card := Nat.mul_le_mul_left _ (h1.trans h2)
      _ ≤ E.card * Q := h3
      _ ≤ (n - 1) * Q := Nat.mul_le_mul_right _ hEcard
  have hfinal : M * L + (n - 1) * Q + M * d ≤ M * p := nthArith2 p n d L s a Q hn hs1 hsL ha2 hQ
  have hMpos : 0 < M := Nat.mul_pos (by omega) hapos
  have hMp' : M * p = M * Z.card + M * S1.card + M * O.card := by
    have : M * p = M * (Z.card + S1.card + O.card) := by rw [hpart]
    rw [this, Nat.mul_add, Nat.mul_add]
  have hMZ : M * Z.card ≤ M * d := Nat.mul_le_mul_left _ hZ'
  have : M * L ≤ M * S1.card := by omega
  exact Nat.le_of_mul_le_mul_left this hMpos

end Stepanov
