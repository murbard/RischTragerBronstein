import RischTragerBronstein.Mixed.FFHeight

/-!
# Heights under morphisms of `ℙ¹` over `K(X)`

The naive height `FFHeight.ht` of `x = u / v` with `u, v` coprime is `max (deg u) (deg v)`
(`ht_div_coprime`). For a map `x ↦ F(u, v) / G(u, v)` given by binary forms of degree `d`, the
degrees of the values satisfy

* `deg_form_le`: `deg F(u, v) ≤ c + d · max (deg u) (deg v)` (`c` bounds the coefficient degrees);
* `deg_max_ge`: a resultant identity `A F + B G = R vᵐ`, `A' F + B' G = R uᵐ` with `deg A, … ≤ a`
  forces `m · max (deg u) (deg v) ≤ deg R + a + max (deg F) (deg G)`.

With `m = 2d − 1` and `a = (d − 1) · max + c'` these give `|ht (φ x) − d · ht x| ≤ C`: the doubling
estimate `|h (2P) − 4 h P| ≤ C` needed by `MWTate`, for the Kummer-line duplication map.
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K]

/-- **The height of a fraction in lowest terms.** -/
theorem ht_div_coprime (u v : K[X]) (hv : v ≠ 0) (hc : IsCoprime u v) :
    ht (algebraMap K[X] (RatFunc K) u / algebraMap K[X] (RatFunc K) v) =
      max u.natDegree v.natDegree := by
  set x := algebraMap K[X] (RatFunc K) u / algebraMap K[X] (RatFunc K) v with hx
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hv' : algebraMap K[X] (RatFunc K) v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv
  have hd' : algebraMap K[X] (RatFunc K) (RatFunc.denom x) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.denom_ne_zero x)
  have key : RatFunc.num x * v = u * RatFunc.denom x := by
    apply hinj
    have h1 := RatFunc.num_div_denom x
    rw [map_mul, map_mul]
    have h2 : algebraMap K[X] (RatFunc K) (RatFunc.num x) =
        x * algebraMap K[X] (RatFunc K) (RatFunc.denom x) := (div_eq_iff hd').mp h1
    rw [h2, hx]; field_simp
  have hnd := RatFunc.isCoprime_num_denom x
  by_cases hu : u = 0
  · have hx0 : x = 0 := by rw [hx, hu, map_zero, zero_div]
    have hvu : IsUnit v := by
      rw [hu] at hc; exact isCoprime_zero_left.mp hc
    rw [hx0, ht_zero, hu, natDegree_zero, natDegree_eq_zero_of_isUnit hvu, max_self]
  have hnum0 : RatFunc.num x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at key
    exact mul_ne_zero hu (RatFunc.denom_ne_zero x) key.symm
  -- `num x` and `u` divide each other
  have d1 : u ∣ RatFunc.num x := hc.dvd_of_dvd_mul_right ⟨_, key⟩
  have d2 : RatFunc.num x ∣ u := hnd.dvd_of_dvd_mul_right ⟨v, key.symm⟩
  have d3 : v ∣ RatFunc.denom x :=
    hc.symm.dvd_of_dvd_mul_right ⟨RatFunc.num x, by linear_combination -key⟩
  have d4 : RatFunc.denom x ∣ v := hnd.symm.dvd_of_dvd_mul_right ⟨u, by linear_combination key⟩
  have e1 : (RatFunc.num x).natDegree = u.natDegree :=
    le_antisymm (natDegree_le_of_dvd d2 hu) (natDegree_le_of_dvd d1 hnum0)
  have e2 : (RatFunc.denom x).natDegree = v.natDegree :=
    le_antisymm (natDegree_le_of_dvd d4 hv) (natDegree_le_of_dvd d3 (RatFunc.denom_ne_zero x))
  unfold ht; rw [e1, e2]

/-- A combination bound: `A F + B G = W ≠ 0` ⇒ `deg W ≤ max (deg A + deg F) (deg B + deg G)`. -/
lemma natDegree_le_of_comb {A B F G W : K[X]} (h : A * F + B * G = W) (_hW : W ≠ 0) :
    W.natDegree ≤ max (A.natDegree + F.natDegree) (B.natDegree + G.natDegree) := by
  rw [← h]
  refine (natDegree_add_le _ _).trans (max_le_max ?_ ?_) <;> exact natDegree_mul_le

/-- **Lower bound from a resultant identity.** -/
theorem deg_max_ge (u v F G A B A' B' R : K[X]) (m a : ℕ) (hc : IsCoprime u v)
    (hR : R ≠ 0) (h1 : A * F + B * G = R * v ^ m) (h2 : A' * F + B' * G = R * u ^ m)
    (hA : A.natDegree ≤ a) (hB : B.natDegree ≤ a) (hA' : A'.natDegree ≤ a) (hB' : B'.natDegree ≤ a) :
    m * max u.natDegree v.natDegree ≤ R.natDegree + a + max F.natDegree G.natDegree := by
  have hne : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨rfl, rfl⟩; exact not_isCoprime_zero_zero hc
  -- degree of `R vᵐ` and `R uᵐ`
  have key : ∀ (w : K[X]) (A B : K[X]), w ≠ 0 → A.natDegree ≤ a → B.natDegree ≤ a →
      A * F + B * G = R * w ^ m → m * w.natDegree ≤ R.natDegree + a + max F.natDegree G.natDegree := by
    intro w A B hw hA hB h
    have hW' : R * w ^ m ≠ 0 := mul_ne_zero hR (pow_ne_zero _ hw)
    have := natDegree_le_of_comb h hW'
    rw [natDegree_mul hR (pow_ne_zero _ hw), natDegree_pow] at this
    have : max (A.natDegree + F.natDegree) (B.natDegree + G.natDegree) ≤
        a + max F.natDegree G.natDegree := max_le (by omega) (by omega)
    omega
  rcases le_total u.natDegree v.natDegree with huv | huv
  · rw [max_eq_right huv]
    by_cases hv : v = 0
    · rw [hv, natDegree_zero, mul_zero]; exact Nat.zero_le _
    · exact key v A B hv hA hB h1
  · rw [max_eq_left huv]
    by_cases hu : u = 0
    · rw [hu, natDegree_zero, mul_zero]; exact Nat.zero_le _
    · exact key u A' B' hu hA' hB' h2

/-- The value `F(u, v) = ∑ fᵢ uⁱ v^{d−i}` of a binary form of degree `d`. -/
noncomputable def formVal (f : ℕ → K[X]) (d : ℕ) (u v : K[X]) : K[X] :=
  ∑ i ∈ Finset.range (d + 1), f i * u ^ i * v ^ (d - i)

/-- **Upper bound** for the value of a form. -/
theorem deg_form_le (f : ℕ → K[X]) (d c : ℕ) (hf : ∀ i, (f i).natDegree ≤ c) (u v : K[X]) :
    (formVal f d u v).natDegree ≤ c + d * max u.natDegree v.natDegree := by
  unfold formVal
  refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine natDegree_mul_le.trans ?_
  refine (add_le_add natDegree_mul_le natDegree_pow_le).trans ?_
  have h1 := hf i
  have h2 : (u ^ i).natDegree ≤ i * max u.natDegree v.natDegree :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ (le_max_left _ _))
  have h3 : (d - i) * v.natDegree ≤ (d - i) * max u.natDegree v.natDegree :=
    Nat.mul_le_mul_left _ (le_max_right _ _)
  have h4 : i * max u.natDegree v.natDegree + (d - i) * max u.natDegree v.natDegree =
      d * max u.natDegree v.natDegree := by
    rw [← add_mul, Nat.add_sub_cancel' hi']
  omega

end FFHeight
