import RischTragerBronstein.Torsion.NonSpec1

/-!
# Non-special base points exist (2): kernel spaces of configurations

A configuration is `r` admissible fibres `f l` with a chosen root index `j₀ l` each; `kerSp m f j₀` is the
space of `c ∈ Vsp m` vanishing at all non-chosen points `(x_l, y_{l,k})`, `k ≠ j₀ l`.
* `kerSp_nil`: without fibres it is `Vsp m`;
* `e0_mem_kerSp`: `∏ₗ (x − x_l)` (in the coordinate `0`, `δ₀ = 0`) lies in it;
* `exists_div_of_vanish`: a vector of `Vsp (m + 1)` vanishing on a whole fibre is `(x − x₀)` times one of
  `Vsp m`.
-/

open Polynomial Module

namespace Curves

open CPoly Sup GTors

section Kernels

variable {K : Type*} [Field K] {n : ℕ} {B : Fin n → K[X][X]} (δ : Fin n → ℕ)

/-- The kernel space of a configuration. -/
noncomputable def kerSp (m r : ℕ) (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n) :
    Submodule K (Fin n → K[X]) :=
  Vsp K δ m ⊓ ⨅ (l : Fin r) (k : Fin n) (_ : k ≠ j₀ l), LinearMap.ker (evPt B (f l).x ((f l).ys k))

lemma mem_kerSp (m r : ℕ) (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n) (c : Fin n → K[X]) :
    c ∈ kerSp δ m r f j₀ ↔ c ∈ Vsp K δ m ∧ ∀ l k, k ≠ j₀ l → evPt B (f l).x ((f l).ys k) c = 0 := by
  simp [kerSp, Submodule.mem_iInf]

instance (m r : ℕ) (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n) :
    FiniteDimensional K (kerSp δ m r f j₀) :=
  Submodule.finiteDimensional_of_le inf_le_left

/-- The product `∏ₗ (x − x_l)`. -/
noncomputable def prodX {r : ℕ} (f : Fin r → AdmFib B) : K[X] := ∏ l, (X - Polynomial.C (f l).x)

lemma prodX_ne_zero {r : ℕ} (f : Fin r → AdmFib B) : prodX f ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ ↦ X_sub_C_ne_zero _

lemma natDegree_prodX {r : ℕ} (f : Fin r → AdmFib B) : (prodX f).natDegree = r := by
  rw [prodX, natDegree_prod _ _ fun l _ ↦ X_sub_C_ne_zero _]
  simp

lemma prodX_eval {r : ℕ} (f : Fin r → AdmFib B) (l : Fin r) : (prodX f).eval (f l).x = 0 := by
  rw [prodX, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)

variable (hn : 0 < n)

/-- The vector `∏ₗ (x − x_l)` in the coordinate `0`. -/
noncomputable def e0 {r : ℕ} (f : Fin r → AdmFib B) : Fin n → K[X] := Pi.single ⟨0, hn⟩ (prodX f)

lemma e0_ne_zero {r : ℕ} (f : Fin r → AdmFib B) : e0 hn f ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp only [e0, Pi.single_eq_same, Pi.zero_apply] at this
  exact prodX_ne_zero f this

lemma e0_mem_kerSp (hδ0 : δ ⟨0, hn⟩ = 0) (m r : ℕ) (hm : r ≤ m) (f : Fin r → AdmFib B)
    (j₀ : Fin r → Fin n) : e0 hn f ∈ kerSp δ m r f j₀ := by
  classical
  rw [mem_kerSp, mem_Vsp]
  refine ⟨fun j ↦ ?_, fun l k _ ↦ ?_⟩
  · by_cases hj : j = ⟨0, hn⟩
    · subst hj
      rw [e0, Pi.single_eq_same, mem_degreeLT, hδ0]
      calc (prodX f).degree ≤ (prodX f).natDegree := degree_le_natDegree
        _ = (r : WithBot ℕ) := by rw [natDegree_prodX]
        _ < ((m + 1 - 0 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : r < m + 1 - 0)
    · rw [e0, Pi.single_eq_of_ne hj]; exact Submodule.zero_mem _
  · rw [evPt_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hj : j = ⟨0, hn⟩
    · subst hj; rw [e0, Pi.single_eq_same, prodX_eval, zero_mul]
    · rw [e0, Pi.single_eq_of_ne hj, eval_zero, zero_mul]

/-- **The base case**: without fibres the kernel space at level `0` has dimension `1`. -/
lemma finrank_kerSp_nil (hδ0 : δ ⟨0, hn⟩ = 0) (hδ : ∀ j, j ≠ ⟨0, hn⟩ → 1 ≤ δ j)
    (f : Fin 0 → AdmFib B) (j₀ : Fin 0 → Fin n) : finrank K (kerSp δ 0 0 f j₀) = 1 := by
  have h : kerSp δ 0 0 f j₀ = Vsp K δ 0 := by
    rw [kerSp]; simp
  rw [h, finrank_Vsp, Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj ↦ by have := hδ j hj; omega)
    (by simp), hδ0]

/-- **Dividing out a fibre.** -/
lemma exists_div_of_vanish (m : ℕ) (c : Fin n → K[X]) (hc : c ∈ Vsp K δ (m + 1))
    (fb : AdmFib B) (h : ∀ k, evPt B fb.x (fb.ys k) c = 0) :
    ∃ c' ∈ Vsp K δ m, c = fun j ↦ (X - Polynomial.C fb.x) * c' j := by
  have hz := fb.coeff_eval_eq_zero c h
  rw [mem_Vsp] at hc
  have hdiv : ∀ j, (X - Polynomial.C fb.x) ∣ c j := fun j ↦ dvd_iff_isRoot.mpr (hz j)
  choose c' hc' using hdiv
  refine ⟨c', (mem_Vsp δ m c').mpr fun j ↦ ?_, funext hc'⟩
  have h1 := hc j
  rw [mem_degreeLT] at h1 ⊢
  by_cases h0 : c' j = 0
  · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
  rw [hc' j, degree_mul, degree_X_sub_C] at h1
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (c' j).degree = d := ⟨(c' j).natDegree, degree_eq_natDegree h0⟩
  rw [hd] at h1 ⊢
  have : 1 + d < m + 1 + 1 - δ j := by exact_mod_cast h1
  exact_mod_cast (by omega : d < m + 1 - δ j)

end Kernels

end Curves
