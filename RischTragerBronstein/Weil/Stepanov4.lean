import RischTragerBronstein.Weil.Stepanov3
import RischTragerBronstein.Weil.Stepanov5
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Stepanov's method, step 4: the auxiliary polynomial and the bound

Over `F = 𝔽_p` (`p` odd), for `f` with an irreducible factor of odd multiplicity, `c = (p − 1)/2`
and `ε ∈ F`, the set `S = {x : f(x) ≠ 0, f(x)^c = ε}` satisfies
`M |S| ≤ (J − 1) p + K₀ + c deg f` whenever `2 J K₀ > M (J + K₀ + M deg f)`, `M ≤ p`,
`deg f + 2 (K₀ − 1) < p` (`stepanov`).

The polynomial `R₀ = ∑_{j<J} (rⱼ + sⱼ f^c) X^{jp}` (`deg rⱼ, sⱼ < K₀`) is chosen non-zero
(`indep`) with `Eₖ = ∑ⱼ Xʲ (fᵏ D⁽ᵏ⁾rⱼ + ε Tₖ sⱼ) = 0` for `k < M` (more unknowns than linear
conditions); at `x ∈ S`, `f(x)ᵏ (D⁽ᵏ⁾R₀)(x) = Eₖ(x) = 0` (`X^{jp}` is a constant for `D⁽ᵏ⁾`,
`x^p = x`), so `R₀` vanishes to order `M` on `S`.
-/

open Polynomial

namespace Stepanov

variable {p : ℕ} [hp : Fact p.Prime]


section T

variable (f : (ZMod p)[X]) (U : ℕ → (ZMod p)[X])

/-- `Tₖ s = ∑_{a+b=k} f^b U_a D⁽ᵇ⁾ s` (with `f^a D⁽ᵃ⁾(f^c) = f^c U_a`). -/
noncomputable def Tk (k : ℕ) : (ZMod p)[X] →ₗ[(ZMod p)] (ZMod p)[X] :=
  ∑ ab ∈ Finset.antidiagonal k,
    (((LinearMap.mulLeft (ZMod p) (f ^ ab.2 * U ab.1)).comp (hasseDeriv ab.2) : (ZMod p)[X] →ₗ[(ZMod p)] (ZMod p)[X]))

lemma Tk_apply (k : ℕ) (s : (ZMod p)[X]) :
    Tk f U k s = ∑ ab ∈ Finset.antidiagonal k, f ^ ab.2 * U ab.1 * hasseDeriv ab.2 s := by
  simp [Tk, LinearMap.sum_apply, mul_assoc]

lemma Tk_spec (c : ℕ) (hU : ∀ i, f ^ i * hasseDeriv i (f ^ c) = f ^ c * U i) (k : ℕ) (s : (ZMod p)[X]) :
    f ^ k * hasseDeriv k (f ^ c * s) = f ^ c * Tk f U k s := by
  rw [Tk_apply, hasseDeriv_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab hab ↦ ?_
  have hs := Finset.mem_antidiagonal.mp hab
  have e : f ^ k = f ^ ab.1 * f ^ ab.2 := by rw [← pow_add, hs]
  rw [e]
  calc f ^ ab.1 * f ^ ab.2 * (hasseDeriv ab.1 (f ^ c) * hasseDeriv ab.2 s)
      = (f ^ ab.1 * hasseDeriv ab.1 (f ^ c)) * (f ^ ab.2 * hasseDeriv ab.2 s) := by ring
    _ = f ^ c * (f ^ ab.2 * U ab.1 * hasseDeriv ab.2 s) := by rw [hU]; ring

lemma Tk_natDegree (hd : 1 ≤ f.natDegree) (hUd : ∀ i, (U i).natDegree ≤ i * (f.natDegree - 1))
    (k : ℕ) (s : (ZMod p)[X]) : (Tk f U k s).natDegree ≤ s.natDegree + k * (f.natDegree - 1) := by
  rw [Tk_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun ab hab ↦ ?_
  have hs := Finset.mem_antidiagonal.mp hab
  rcases le_or_gt ab.2 s.natDegree with hle | hlt
  · have h1 := natDegree_mul_le (p := f ^ ab.2 * U ab.1) (q := hasseDeriv ab.2 s)
    have h2 := natDegree_mul_le (p := f ^ ab.2) (q := U ab.1)
    have h3 := natDegree_pow_le (p := f) (n := ab.2)
    have h4 := natDegree_hasseDeriv_le s ab.2
    have h5 := hUd ab.1
    set d := f.natDegree
    have h6 : ab.2 * d + ab.1 * (d - 1) + (s.natDegree - ab.2) ≤ s.natDegree + k * (d - 1) := by
      rw [← hs]
      obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rw [he]; simp only [Nat.add_sub_cancel]
      obtain ⟨t, ht⟩ : ∃ t, s.natDegree = ab.2 + t := ⟨s.natDegree - ab.2, by omega⟩
      rw [ht, show ab.2 + t - ab.2 = t by omega]
      nlinarith
    omega
  · rw [hasseDeriv_eq_zero_of_lt_natDegree s _ hlt, mul_zero, natDegree_zero]
    exact Nat.zero_le _

end T

/-- The polynomial `∑_{i<K} aᵢ Xⁱ` of a coefficient vector. -/
noncomputable def polyOf (K : ℕ) : (Fin K → (ZMod p)) →ₗ[(ZMod p)] (ZMod p)[X] :=
  ∑ i : Fin K, (LinearMap.proj i).smulRight (X ^ (i : ℕ))

lemma polyOf_apply (K : ℕ) (a : Fin K → (ZMod p)) : polyOf K a = ∑ i : Fin K, C (a i) * X ^ (i : ℕ) := by
  simp [polyOf, LinearMap.sum_apply, smul_eq_C_mul]

lemma coeff_polyOf (K : ℕ) (a : Fin K → (ZMod p)) (i : Fin K) : (polyOf K a).coeff i = a i := by
  classical
  rw [polyOf_apply, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i (fun b _ hb ↦ by rw [if_neg (fun h ↦ hb (Fin.ext h.symm)), mul_zero])
    (by simp), if_pos rfl, mul_one]

lemma polyOf_natDegree (K : ℕ) (a : Fin K → (ZMod p)) : (polyOf K a).natDegree ≤ K - 1 := by
  rw [polyOf_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_
  exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)

lemma polyOf_eq_zero (K : ℕ) (a : Fin K → (ZMod p)) (h : polyOf K a = 0) : a = 0 := by
  funext i
  rw [← coeff_polyOf K a i, h, coeff_zero]; rfl

section Main

variable (f : (ZMod p)[X]) (U : ℕ → (ZMod p)[X]) (ε : (ZMod p)) (J K₀ M N : ℕ)

/-- `Eₖ(r, s) = ∑ⱼ Xʲ (fᵏ D⁽ᵏ⁾ rⱼ + ε Tₖ sⱼ)`. -/
noncomputable def Ek (k : ℕ) : (Fin J → (Fin K₀ → (ZMod p)) × (Fin K₀ → (ZMod p))) →ₗ[(ZMod p)] (ZMod p)[X] :=
  ∑ j : Fin J,
    ((((LinearMap.mulLeft (ZMod p) (X ^ (j : ℕ) * f ^ k)).comp
      ((hasseDeriv k).comp ((polyOf K₀).comp ((LinearMap.fst (ZMod p) (Fin K₀ → (ZMod p)) (Fin K₀ → (ZMod p))).comp
        (LinearMap.proj (R := (ZMod p)) (φ := fun _ : Fin J ↦ (Fin K₀ → (ZMod p)) × (Fin K₀ → (ZMod p))) j)))) +
    (LinearMap.mulLeft (ZMod p) (X ^ (j : ℕ) * C ε)).comp
      ((Tk f U k).comp ((polyOf K₀).comp ((LinearMap.snd (ZMod p) (Fin K₀ → (ZMod p)) (Fin K₀ → (ZMod p))).comp
        (LinearMap.proj (R := (ZMod p)) (φ := fun _ : Fin J ↦ (Fin K₀ → (ZMod p)) × (Fin K₀ → (ZMod p))) j))))) :
      (Fin J → (Fin K₀ → (ZMod p)) × (Fin K₀ → (ZMod p))) →ₗ[(ZMod p)] (ZMod p)[X]))

lemma Ek_apply (k : ℕ) (v : Fin J → (Fin K₀ → (ZMod p)) × (Fin K₀ → (ZMod p))) :
    Ek f U ε J K₀ k v = ∑ j : Fin J, X ^ (j : ℕ) * (f ^ k * hasseDeriv k (polyOf K₀ (v j).1) +
      C ε * Tk f U k (polyOf K₀ (v j).2)) := by
  simp only [Ek, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp; ring

/-- The linear conditions: the coefficients `< N` of `E₀, …, E_{M−1}`. -/
noncomputable def Φ : (Fin J → (Fin K₀ → (ZMod p)) × (Fin K₀ → (ZMod p))) →ₗ[(ZMod p)] (Fin M → Fin N → (ZMod p)) :=
  LinearMap.pi fun k : Fin M ↦ LinearMap.pi fun i : Fin N ↦ (lcoeff (ZMod p) i).comp (Ek f U ε J K₀ k)

end Main

/-- **Stepanov's bound.** -/
theorem stepanov (hp2 : p ≠ 2) (f : (ZMod p)[X]) (hd : 1 ≤ f.natDegree) (P : (ZMod p)[X]) (hP : Irreducible P)
    (e : ℕ) (he : Odd e) (hPe : P ^ e ∣ f) (hPe1 : ¬ P ^ (e + 1) ∣ f) (ε : (ZMod p))
    (J K₀ M : ℕ) (hJ : 1 ≤ J) (hK : 1 ≤ K₀) (hMp : M ≤ p)
    (hdeg : f.natDegree + 2 * (K₀ - 1) < p)
    (hcount : M * (J + K₀ + M * f.natDegree) < J * (K₀ + K₀))
    (S : Finset (ZMod p)) (hS : ∀ x ∈ S, f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = ε) :
    M * S.card ≤ (J - 1) * p + K₀ + (p - 1) / 2 * f.natDegree := by
  classical
  have hf0 : f ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hd; omega
  set c := (p - 1) / 2 with hc
  set d := f.natDegree with hdd
  choose U hU hUd using exists_hasseDeriv_pow f hd c
  set N := J + K₀ + M * d with hN
  -- a non-zero kernel vector
  have hdom : Module.finrank (ZMod p) (Fin J → (Fin K₀ → ZMod p) × (Fin K₀ → ZMod p)) =
      J * (K₀ + K₀) := by
    simp [Module.finrank_pi_fintype, Module.finrank_prod]
  have hcod : Module.finrank (ZMod p) (Fin M → Fin N → ZMod p) = M * N := by
    simp [Module.finrank_pi_fintype]
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ f U ε J K₀ M N) (by
    rw [hdom, hcod]; exact hcount)
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hvker
  set r : ℕ → (ZMod p)[X] := fun j ↦ if h : j < J then polyOf K₀ (v ⟨j, h⟩).1 else 0 with hr
  set s : ℕ → (ZMod p)[X] := fun j ↦ if h : j < J then polyOf K₀ (v ⟨j, h⟩).2 else 0 with hs
  have hrd : ∀ j, (r j).natDegree ≤ K₀ - 1 := fun j ↦ by
    rw [hr]; simp only; split_ifs
    · exact polyOf_natDegree _ _
    · simp
  have hsd : ∀ j, (s j).natDegree ≤ K₀ - 1 := fun j ↦ by
    rw [hs]; simp only; split_ifs
    · exact polyOf_natDegree _ _
    · simp
  set R₀ := ∑ j ∈ Finset.range J, (r j + s j * f ^ c) * X ^ (j * p) with hR₀
  -- `R₀ ≠ 0`
  have hR₀ne : R₀ ≠ 0 := by
    intro h0
    have := indep hp2 f hf0 P hP e he hPe hPe1 J r s (fun j _ ↦ by have := hrd j; omega)
      (fun j _ ↦ by have := hsd j; omega) h0
    apply hv0
    funext j
    obtain ⟨h1, h2⟩ := this j j.2
    simp only [hr, hs, dif_pos j.2, Fin.eta] at h1 h2
    exact Prod.ext (polyOf_eq_zero _ _ h1) (polyOf_eq_zero _ _ h2)
  -- `Eₖ = 0`
  have hE : ∀ k < M, Ek f U ε J K₀ k v = 0 := by
    intro k hk
    have hcoef : ∀ i < N, (Ek f U ε J K₀ k v).coeff i = 0 := fun i hi ↦ by
      have := congrFun (congrFun hvker ⟨k, hk⟩) ⟨i, hi⟩
      simpa [Φ] using this
    have hdegE : (Ek f U ε J K₀ k v).natDegree < N := by
      rw [Ek_apply]
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := J - 1 + (K₀ - 1 + k * d))
        fun j _ ↦ ?_) ?_
      · refine (natDegree_mul_le).trans ?_
        have hj : (X ^ (j : ℕ) : (ZMod p)[X]).natDegree ≤ J - 1 := by
          rw [natDegree_X_pow]; have := j.2; omega
        refine Nat.add_le_add hj ?_
        refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_mul_le).trans ?_
          have h1 : (f ^ k).natDegree ≤ k * d := natDegree_pow_le
          have h2 := (natDegree_hasseDeriv_le (polyOf K₀ (v j).1) k).trans
            (Nat.sub_le_sub_right (polyOf_natDegree K₀ _) k)
          have : k * d + (K₀ - 1 - k) ≤ K₀ - 1 + k * d := by omega
          omega
        · refine (natDegree_C_mul_le _ _).trans ?_
          refine (Tk_natDegree f U hd hUd k _).trans ?_
          rw [← hdd]
          have := polyOf_natDegree K₀ (v j).2
          have : k * (d - 1) ≤ k * d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          omega
      · have : k * d < M * d + 1 := by
          have := Nat.mul_le_mul_right d (Nat.le_of_lt hk); omega
        omega
    ext i
    rw [coeff_zero]
    by_cases hi : i < N
    · exact hcoef i hi
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  -- vanishing on `S`
  have hvan : ∀ x ∈ S, (X - C x) ^ M ∣ R₀ := by
    intro x hx
    obtain ⟨hfx, hgx⟩ := hS x hx
    refine X_sub_C_pow_dvd_of_hasseDeriv R₀ x M fun k hk ↦ ?_
    have hkp : k < p := lt_of_lt_of_le hk hMp
    have hD : hasseDeriv k R₀ = ∑ j ∈ Finset.range J,
        X ^ (j * p) * hasseDeriv k (r j + s j * f ^ c) := by
      rw [hR₀, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm, hasseDeriv_X_pow_mul j k hkp]
    have hEx := congrArg (fun P ↦ P.eval x) (hE k hk)
    simp only [Ek_apply, eval_finset_sum, eval_zero] at hEx
    have hxp : ∀ j : ℕ, x ^ (j * p) = x ^ j := fun j ↦ by
      rw [mul_comm, pow_mul, ZMod.pow_card]
    have hmain : f.eval x ^ k * (hasseDeriv k R₀).eval x = 0 := by
      rw [hD, eval_finset_sum, Finset.mul_sum, ← hEx, Finset.sum_range]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hrj : r j = polyOf K₀ (v j).1 := by simp [hr, j.2]
      have hsj : s j = polyOf K₀ (v j).2 := by simp [hs, j.2]
      have hT := Tk_spec f U c hU k (polyOf K₀ (v j).2)
      have hT' := congrArg (fun P ↦ P.eval x) hT
      simp only [eval_mul, eval_pow] at hT'
      rw [hrj, hsj, mul_comm (polyOf K₀ (v j).2) (f ^ c), map_add, eval_mul, eval_add, eval_pow, eval_X, hxp]
      simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
      rw [show f.eval x ^ k * (x ^ (j : ℕ) * ((hasseDeriv k (polyOf K₀ (v j).1)).eval x +
          (hasseDeriv k (f ^ c * polyOf K₀ (v j).2)).eval x)) =
          x ^ (j : ℕ) * (f.eval x ^ k * (hasseDeriv k (polyOf K₀ (v j).1)).eval x +
            f.eval x ^ k * (hasseDeriv k (f ^ c * polyOf K₀ (v j).2)).eval x) by ring]
      have := congrArg (fun P ↦ P.eval x)
        (show f ^ k * hasseDeriv k (f ^ c * polyOf K₀ (v j).2) = _ from hT)
      simp only [eval_mul, eval_pow] at this
      rw [this, hgx]
    exact (mul_eq_zero.mp hmain).resolve_left (pow_ne_zero _ hfx)
  -- counting
  have hcnt := mul_card_le_natDegree R₀ hR₀ne M S hvan
  have hdegR : R₀.natDegree ≤ (J - 1) * p + K₀ + c * d := by
    rw [hR₀]
    refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_X_pow]
    have h1 := natDegree_add_le (r j) (s j * f ^ c)
    have h2 := natDegree_mul_le (p := s j) (q := f ^ c)
    have h3 : (f ^ c).natDegree ≤ c * d := natDegree_pow_le
    have h4 := hrd j
    have h5 := hsd j
    have h6 : j * p ≤ (J - 1) * p := Nat.mul_le_mul_right _ (by omega)
    omega
  omega

end Stepanov
