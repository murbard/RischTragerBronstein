import RischTragerBronstein.Algebraic.SupNonSpecial
import RischTragerBronstein.Algebraic.SupRedG

/-!
# Global non-speciality certificates exist

`exists_cert_lists`: over any field with a primitive `n`-th root of unity, among more than
`g + d` candidate abscissae `x` with non-zero `y x` (`g = ((n−1)(d−1)+1)/2`, `gcd(n, d) = 1`),
there are base points `(xᵢ, ζ^{kᵢ} y xᵢ)` with distinct `xᵢ` and a certificate `λ`, in the list
format of the global certificate provider (`globalCert`, `lamK`).
-/

open Polynomial

namespace Sup

variable {F : Type*} [Field F]

lemma getD_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) {i : ℕ} (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

/-- **Global certificates exist.** -/
theorem exists_cert_lists {n d : ℕ} (hn2 : 2 ≤ n) (hcop : Nat.Coprime n d) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (Xs : Finset F) (y : F → F) (hy : ∀ x ∈ Xs, y x ≠ 0)
    (hX : ((n - 1) * (d - 1) + 1) / 2 + d < Xs.card) :
    ∃ (xs ys : List F) (lam : List (List F)), xs.length = ((n - 1) * (d - 1) + 1) / 2 ∧
      ys.length = xs.length ∧ xs.Nodup ∧
      (∀ i < xs.length, xs.getD i 0 ∈ Xs ∧ ∃ k < n, ys.getD i 0 = ζ ^ k * y (xs.getD i 0)) ∧
      ∀ i < xs.length, ∀ ai ∈ basisN n d (n * xs.length),
        xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
          ∑ i' ∈ Finset.range xs.length, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k *
            (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2) := by
  classical
  set g := ((n - 1) * (d - 1) + 1) / 2 with hg
  obtain ⟨sj, hinj, hsj⟩ := exists_hol hcop
  obtain ⟨xsf, ks, hxi, hxX, hkn, hdet⟩ := exists_nonspecial hζ sj hinj hsj Xs y hy hX
  set yf : Fin g → F := fun i ↦ ζ ^ ks i * y (xsf i) with hyf
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hyf0 : ∀ i, yf i ≠ 0 := fun i ↦ mul_ne_zero (pow_ne_zero _ hζ0) (hy _ (hxX i))
  obtain ⟨L, hL⟩ := exists_lam (by omega) hζ xsf yf hxi hyf0 sj hsj hdet
  have hn1 : 0 < n - 1 := by omega
  refine ⟨List.ofFn xsf, List.ofFn yf, List.ofFn fun i : Fin g ↦
    List.ofFn fun q : Fin (g * (n - 1)) ↦
      L i ⟨q / (n - 1), Nat.div_lt_of_lt_mul (lt_of_lt_of_eq q.2 (Nat.mul_comm _ _))⟩
        (q % (n - 1) + 1), by rw [List.length_ofFn], by simp only [List.length_ofFn]; rfl, ?_, ?_, ?_⟩
  · rw [List.nodup_ofFn]; exact hxi
  · intro i hi
    rw [List.length_ofFn] at hi
    rw [getD_ofFn _ _ hi, getD_ofFn _ _ hi]
    exact ⟨hxX _, ks ⟨i, hi⟩, hkn _, rfl⟩
  · intro i hi ai hai
    rw [List.length_ofFn] at hi hai ⊢
    rw [getD_ofFn _ _ hi, getD_ofFn _ _ hi, hL ⟨i, hi⟩ ai hai, ← Fin.sum_univ_eq_sum_range
      (fun i' ↦ ∑ k ∈ Finset.Ico 1 n, lamK _ n i i' k * _)]
    refine Finset.sum_congr rfl fun i' _ ↦ Finset.sum_congr rfl fun k hk ↦ ?_
    obtain ⟨hk1, hkn'⟩ := Finset.mem_Ico.mp hk
    rw [getD_ofFn _ _ i'.2, getD_ofFn _ _ i'.2]
    congr 1
    have hq : i' * (n - 1) + (k - 1) < g * (n - 1) := by
      have := i'.2
      calc i' * (n - 1) + (k - 1) < i' * (n - 1) + (n - 1) := by omega
        _ = (i' + 1) * (n - 1) := by ring
        _ ≤ g * (n - 1) := Nat.mul_le_mul_right _ this
    unfold lamK
    rw [getD_ofFn _ _ hi, getD_ofFn _ _ hq]
    have hdiv : (i' * (n - 1) + (k - 1)) / (n - 1) = i' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn1, Nat.div_eq_of_lt (by omega), zero_add]
    have hmod : (i' * (n - 1) + (k - 1)) % (n - 1) + 1 = k := by
      have : (i' * (n - 1) + (k - 1)) % (n - 1) = k - 1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      omega
    congr 1
    · ext; exact hdiv.symm
    · exact hmod.symm

end Sup
