import RischTragerBronstein.Weil.Stepanov4
import RischTragerBronstein.Weil.StepanovN3

/-!
# Stepanov's method for `n`-th powers, step 4: the bound

Over `F = 𝔽_p`, `n ∣ p − 1`, `c = (p − 1)/n`, `f` with an irreducible factor of multiplicity prime
to `n`, and `ε ∈ F`: the set `S = {x : f(x) ≠ 0, f(x)^c = ε}` satisfies
`M |S| ≤ (J − 1) p + K₀ + (n − 1) c deg f` whenever `M (J + K₀ + M deg f) < n J K₀`, `M ≤ p`,
`n (deg f + K₀ − 1) < p` (`stepanovN`).

The polynomial `R₀ = ∑_{j<J} ∑_{i<n} rᵢⱼ f^{ci} X^{jp}` (`deg rᵢⱼ < K₀`) is chosen non-zero
(`indepN`) with `Eₖ = ∑ⱼ Xʲ ∑ᵢ εⁱ Tₖ⁽ⁱ⁾ rᵢⱼ = 0` for `k < M`, where `fᵏ D⁽ᵏ⁾(f^{ci} s) = f^{ci} Tₖ⁽ⁱ⁾ s`;
at `x ∈ S`, `f(x)ᵏ (D⁽ᵏ⁾R₀)(x) = Eₖ(x) = 0`, so `R₀` vanishes to order `M` on `S`.
-/

open Polynomial

namespace Stepanov

variable {p : ℕ} [hp : Fact p.Prime]

section MainN

variable (f : (ZMod p)[X]) (U : ℕ → ℕ → (ZMod p)[X]) (ε : (ZMod p)) (n J K₀ M N : ℕ)

/-- `Eₖ(r) = ∑ⱼ Xʲ ∑ᵢ εⁱ Tₖ⁽ⁱ⁾ rᵢⱼ`. -/
noncomputable def EkN (k : ℕ) : (Fin J → Fin n → Fin K₀ → (ZMod p)) →ₗ[(ZMod p)] (ZMod p)[X] :=
  ∑ j : Fin J, ∑ i : Fin n,
    ((LinearMap.mulLeft (ZMod p) (X ^ (j : ℕ) * C (ε ^ (i : ℕ)))).comp
      ((Tk f (U i) k).comp ((polyOf K₀).comp
        ((LinearMap.proj (R := ZMod p) (φ := fun _ : Fin n ↦ Fin K₀ → ZMod p) i).comp
          (LinearMap.proj (R := ZMod p) (φ := fun _ : Fin J ↦ Fin n → Fin K₀ → ZMod p) j)))))

lemma EkN_apply (k : ℕ) (v : Fin J → Fin n → Fin K₀ → (ZMod p)) :
    EkN f U ε n J K₀ k v = ∑ j : Fin J, ∑ i : Fin n,
      X ^ (j : ℕ) * C (ε ^ (i : ℕ)) * Tk f (U i) k (polyOf K₀ (v j i)) := by
  simp only [EkN, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.proj_apply]

/-- The linear conditions: the coefficients `< N` of `E₀, …, E_{M−1}`. -/
noncomputable def ΦN : (Fin J → Fin n → Fin K₀ → (ZMod p)) →ₗ[(ZMod p)] (Fin M → Fin N → (ZMod p)) :=
  LinearMap.pi fun k : Fin M ↦ LinearMap.pi fun t : Fin N ↦
    (lcoeff (ZMod p) t).comp (EkN f U ε n J K₀ k)

end MainN

/-- **Stepanov's bound for `n`-th power classes.** -/
theorem stepanovN (n : ℕ) (hn : 1 ≤ n) (hnp : n ∣ p - 1) (f : (ZMod p)[X]) (hd : 1 ≤ f.natDegree)
    (P : (ZMod p)[X]) (hP : Irreducible P) (e : ℕ) (hen : Nat.Coprime e n) (hPe : P ^ e ∣ f)
    (hPe1 : ¬ P ^ (e + 1) ∣ f) (ε : ZMod p) (J K₀ M : ℕ) (hJ : 1 ≤ J) (hK : 1 ≤ K₀) (hMp : M ≤ p)
    (hdeg : n * (f.natDegree + (K₀ - 1)) < p)
    (hcount : M * (J + K₀ + M * f.natDegree) < n * J * K₀)
    (S : Finset (ZMod p)) (hS : ∀ x ∈ S, f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / n) = ε) :
    M * S.card ≤ (J - 1) * p + K₀ + (n - 1) * ((p - 1) / n) * f.natDegree := by
  classical
  have hf0 : f ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hd; omega
  set c := (p - 1) / n with hc
  set d := f.natDegree with hdd
  choose U hU hUd using fun i a ↦ exists_hasseDeriv_pow f hd (c * i) a
  set N := J + K₀ + M * d with hN
  have hdom : Module.finrank (ZMod p) (Fin J → Fin n → Fin K₀ → ZMod p) = J * (n * K₀) := by
    simp [Module.finrank_pi_fintype]
  have hcod : Module.finrank (ZMod p) (Fin M → Fin N → ZMod p) = M * N := by
    simp [Module.finrank_pi_fintype]
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := ΦN f U ε n J K₀ M N) (by
    rw [hdom, hcod]
    have : J * (n * K₀) = n * J * K₀ := by ring
    rw [this]; exact hcount)
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hvker
  set r : ℕ → ℕ → (ZMod p)[X] := fun i j ↦
    if h : j < J ∧ i < n then polyOf K₀ (v ⟨j, h.1⟩ ⟨i, h.2⟩) else 0 with hr
  have hrd : ∀ i j, (r i j).natDegree ≤ K₀ - 1 := fun i j ↦ by
    rw [hr]; simp only; split_ifs
    · exact polyOf_natDegree _ _
    · simp
  set R₀ := ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range n, X ^ (j * p) * (r i j * f ^ (c * i))
    with hR₀
  -- `R₀ ≠ 0`
  have hR₀ne : R₀ ≠ 0 := by
    intro h0
    have h0' : ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range J, r i j * X ^ (j * p)) *
        f ^ ((p - 1) / n * i) = 0 := by
      rw [← h0, hR₀, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have := indepN n hn hnp f hf0 P hP e hen hPe hPe1 J r
      (fun i _ j _ ↦ by
        have h1 := hrd i j
        have h2 := Nat.mul_le_mul_left n (Nat.add_le_add_left h1 d)
        show n * (d + (r i j).natDegree) < p
        omega) h0'
    apply hv0
    funext j i
    have h1 := this i i.2 j j.2
    simp only [hr, dif_pos (And.intro j.2 i.2), Fin.eta] at h1
    exact polyOf_eq_zero _ _ h1
  -- `Eₖ = 0`
  have hE : ∀ k < M, EkN f U ε n J K₀ k v = 0 := by
    intro k hk
    have hcoef : ∀ t < N, (EkN f U ε n J K₀ k v).coeff t = 0 := fun t ht ↦ by
      have := congrFun (congrFun hvker ⟨k, hk⟩) ⟨t, ht⟩
      simpa [ΦN] using this
    have hdegE : (EkN f U ε n J K₀ k v).natDegree < N := by
      rw [EkN_apply]
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := J - 1 + (K₀ - 1 + k * d))
        fun j _ ↦ natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_) ?_
      · refine (natDegree_mul_le).trans ?_
        have hj : (X ^ (j : ℕ) * C (ε ^ (i : ℕ)) : (ZMod p)[X]).natDegree ≤ J - 1 := by
          refine (natDegree_mul_le).trans ?_
          rw [natDegree_X_pow, natDegree_C]; have := j.2; omega
        refine Nat.add_le_add hj ?_
        refine (Tk_natDegree f (U i) hd (hUd i) k _).trans ?_
        rw [← hdd]
        have := polyOf_natDegree K₀ (v j i)
        have : k * (d - 1) ≤ k * d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        omega
      · have : k * d < M * d + 1 := by
          have := Nat.mul_le_mul_right d (Nat.le_of_lt hk); omega
        omega
    ext t
    rw [coeff_zero]
    by_cases ht : t < N
    · exact hcoef t ht
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  -- vanishing on `S`
  have hvan : ∀ x ∈ S, (X - C x) ^ M ∣ R₀ := by
    intro x hx
    obtain ⟨hfx, hgx⟩ := hS x hx
    refine X_sub_C_pow_dvd_of_hasseDeriv R₀ x M fun k hk ↦ ?_
    have hkp : k < p := lt_of_lt_of_le hk hMp
    have hD : hasseDeriv k R₀ = ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range n,
        X ^ (j * p) * hasseDeriv k (r i j * f ^ (c * i)) := by
      rw [hR₀, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ hasseDeriv_X_pow_mul j k hkp _
    have hEx := congrArg (fun P ↦ P.eval x) (hE k hk)
    simp only [EkN_apply, eval_finset_sum, eval_zero] at hEx
    have hxp : ∀ j : ℕ, x ^ (j * p) = x ^ j := fun j ↦ by
      rw [mul_comm, pow_mul, ZMod.pow_card]
    have hmain : f.eval x ^ k * (hasseDeriv k R₀).eval x = 0 := by
      rw [hD, eval_finset_sum, Finset.mul_sum, ← hEx, Finset.sum_range]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [eval_finset_sum, Finset.mul_sum, Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hrj : r i j = polyOf K₀ (v j i) := by simp [hr, j.2, i.2]
      have hT := Tk_spec f (U i) (c * i) (hU i) k (polyOf K₀ (v j i))
      have hT' := congrArg (fun P ↦ P.eval x) hT
      simp only [eval_mul, eval_pow] at hT'
      rw [hrj, mul_comm (polyOf K₀ (v j i)) (f ^ (c * i)), eval_mul, eval_pow, eval_X, hxp]
      simp only [eval_mul, eval_pow, eval_X, eval_C]
      rw [show f.eval x ^ k * (x ^ (j : ℕ) * (hasseDeriv k (f ^ (c * i) * polyOf K₀ (v j i))).eval x) =
          x ^ (j : ℕ) * (f.eval x ^ k * (hasseDeriv k (f ^ (c * i) * polyOf K₀ (v j i))).eval x) by ring,
        hT', pow_mul, hgx]
      ring
    exact (mul_eq_zero.mp hmain).resolve_left (pow_ne_zero _ hfx)
  -- counting
  have hcnt := mul_card_le_natDegree R₀ hR₀ne M S hvan
  have hdegR : R₀.natDegree ≤ (J - 1) * p + K₀ + (n - 1) * c * d := by
    rw [hR₀]
    refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    have hj' := Finset.mem_range.mp hj
    have hi' := Finset.mem_range.mp hi
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_X_pow]
    have h2 := natDegree_mul_le (p := r i j) (q := f ^ (c * i))
    have h3 : (f ^ (c * i)).natDegree ≤ c * i * d := natDegree_pow_le
    have h4 := hrd i j
    have h6 : j * p ≤ (J - 1) * p := Nat.mul_le_mul_right _ (by omega)
    have h7 : c * i * d ≤ (n - 1) * c * d := by
      have : i ≤ n - 1 := by omega
      calc c * i * d ≤ c * (n - 1) * d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
        _ = (n - 1) * c * d := by ring
    omega
  omega

end Stepanov
