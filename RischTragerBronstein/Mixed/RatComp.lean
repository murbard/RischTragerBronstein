import RischTragerBronstein.Mixed.FFMorph
import Mathlib.Algebra.Polynomial.Reverse

/-!
# The height of a composition of rational functions

For a rational function `Q = p / q` with *constant* coefficients (`p, q ∈ K[T]` coprime,
`max (deg p) (deg q) = d`) and `s ∈ K(X)`, **`ht (Q ∘ s) = d · ht s`** (`ht_comp`). This is the
multiplicativity of the degree of maps `ℙ¹ → ℙ¹`, proved with the binary forms of `FFMorph`:
`F = ∑ pᵢ uⁱ v^{d−i}`, `G = ∑ qᵢ uⁱ v^{d−i}` (`s = u / v`); Bézout identities for `p, q` and for
their reflections give `A F + B G = v^{E+d}`, `A' F + B' G = u^{E+d}`, so `F, G` are coprime of
degree exactly `d · max (deg u) (deg v)`.

It is the key to exact canonical heights on **twists of constant elliptic curves**, where the
duplication map is a rational function with constant coefficients on a suitable coordinate.
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- The binary form of degree `e` of `p ∈ K[T]` evaluated at `(u, v)`: `∑ pᵢ uⁱ v^{e−i}`. -/
noncomputable def homog (p : K[X]) (e : ℕ) (u v : K[X]) : K[X] :=
  formVal (fun i ↦ C (p.coeff i)) e u v

/-- **Dehomogenization**: `ι (homog p e u v) = ι v ^ e · p(u / v)`. -/
theorem homog_eval (p : K[X]) (e : ℕ) (hp : p.natDegree ≤ e) (u v : K[X]) (hv : v ≠ 0) :
    ι (homog p e u v) = ι v ^ e * p.eval₂ (algebraMap K (RatFunc K)) (ι u / ι v) := by
  have hv' : ι v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hv
  rw [eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hp), Finset.mul_sum]
  simp only [homog, formVal, map_sum, map_mul, map_pow]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [RatFunc.algebraMap_C, div_pow, ← RatFunc.algebraMap_C]
  conv_rhs => rw [show e = (e - i) + i by omega, pow_add]
  field_simp
  simp only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  ring

theorem homog_swap (p : K[X]) (e : ℕ) (u v : K[X]) :
    homog (reflect e p) e u v = homog p e v u := by
  simp only [homog, formVal]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [coeff_reflect, revAt_le (by omega), show e + 1 - 1 - j = e - j by omega,
    show e - (e - j) = j by omega]
  ring

theorem homog_one (m : ℕ) (u v : K[X]) : homog 1 m u v = v ^ m := by
  simp only [homog, formVal]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [coeff_one, hb]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h

/-- **Homogenized polynomial identities.** -/
theorem homog_comb (a b p q r : K[X]) (E d : ℕ) (ha : a.natDegree ≤ E) (hb : b.natDegree ≤ E)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hr : a * p + b * q = r) (u v : K[X])
    (hv : v ≠ 0) :
    homog a E u v * homog p d u v + homog b E u v * homog q d u v = homog r (E + d) u v := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hrd : r.natDegree ≤ E + d := by
    rw [← hr]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_) <;>
      exact natDegree_mul_le.trans (by omega)
  apply hinj
  rw [map_add, map_mul, map_mul, homog_eval a E ha u v hv, homog_eval p d hp u v hv,
    homog_eval b E hb u v hv, homog_eval q d hq u v hv, homog_eval r (E + d) hrd u v hv, ← hr,
    eval₂_add, eval₂_mul, eval₂_mul, pow_add]
  ring

/-- **Reflections of coprime polynomials of exact joint degree `d` are coprime.** -/
theorem reflect_coprime (p q : K[X]) (hc : IsCoprime p q) (d : ℕ) (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ d) (hd : p.natDegree = d ∨ q.natDegree = d) :
    IsCoprime (reflect d p) (reflect d q) := by
  obtain ⟨a, b, hab⟩ := hc
  set E := max a.natDegree b.natDegree
  have hX : reflect E a * reflect d p + reflect E b * reflect d q = X ^ (E + d) := by
    rw [← reflect_mul _ _ (le_max_left _ _) hp, ← reflect_mul _ _ (le_max_right _ _) hq,
      ← reflect_add, hab, ← C_1, reflect_C, C_1, one_mul]
  -- a coprimality transfer
  have key : ∀ (f g x y : K[X]), IsCoprime f (X ^ (E + d)) → x * f + y * g = X ^ (E + d) →
      IsCoprime f g := by
    intro f g x y hf h
    obtain ⟨s, t, hst⟩ := hf
    exact ⟨s + t * x, t * y, by rw [← hst, ← h]; ring⟩
  have hXc : ∀ f : K[X], f.coeff 0 ≠ 0 → IsCoprime f (X ^ (E + d)) := by
    intro f hf
    refine IsCoprime.pow_right ?_
    rw [isCoprime_comm]
    exact (irreducible_X.coprime_iff_not_dvd).mpr (by rwa [X_dvd_iff])
  have unitCase : ∀ f g : K[X], f = 0 → f.natDegree = d → IsUnit g →
      IsCoprime (reflect d f) (reflect d g) := by
    intro f g hf hfd hg
    rw [hf, natDegree_zero] at hfd
    subst hfd
    rw [hf, reflect_zero]
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hg
    rw [reflect_C, pow_zero, mul_one]
    exact isCoprime_zero_left.mpr (isUnit_C.mpr hc)
  rcases hd with hd | hd
  · by_cases hp0 : p = 0
    · rw [hp0, mul_zero, zero_add] at hab
      exact unitCase p q hp0 hd (IsUnit.of_mul_eq_one_right b hab)
    refine key (reflect d p) (reflect d q) (reflect E a) (reflect E b) (hXc _ ?_) hX
    rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, ← hd]
    exact leadingCoeff_ne_zero.mpr hp0
  · by_cases hq0 : q = 0
    · rw [hq0, mul_zero, add_zero] at hab
      rw [isCoprime_comm]
      exact unitCase q p hq0 hd (IsUnit.of_mul_eq_one_right a hab)
    rw [isCoprime_comm]
    have hX' : reflect E b * reflect d q + reflect E a * reflect d p = X ^ (E + d) := by
      rw [add_comm]; exact hX
    refine key (reflect d q) (reflect d p) (reflect E b) (reflect E a) (hXc _ ?_) hX'
    rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, ← hd]
    exact leadingCoeff_ne_zero.mpr hq0

theorem deg_homog_le (p : K[X]) (e : ℕ) (u v : K[X]) :
    (homog p e u v).natDegree ≤ e * max u.natDegree v.natDegree := by
  have := deg_form_le (fun i ↦ C (p.coeff i)) e 0 (fun i ↦ by simp) u v
  simpa [homog] using this

/-- **The height of a composition**: `ht (Q ∘ s) = deg Q · ht s` for `Q ∈ K(T)` with constant
coefficients (`deg Q = max (deg num) (deg denom)`). -/
theorem ht_comp (Q s : RatFunc K) :
    ht (Q.eval (algebraMap K (RatFunc K)) s) =
      max Q.num.natDegree Q.denom.natDegree * ht s := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  set p := Q.num
  set q := Q.denom
  set d := max p.natDegree q.natDegree with hd
  have hq : q ≠ 0 := RatFunc.denom_ne_zero Q
  have hpq : IsCoprime p q := RatFunc.isCoprime_num_denom Q
  set u := s.num
  set v := s.denom
  have hv : v ≠ 0 := RatFunc.denom_ne_zero s
  have huv : IsCoprime u v := RatFunc.isCoprime_num_denom s
  set n := max u.natDegree v.natDegree with hn
  have hs : ht s = n := rfl
  have hsuv : s = ι u / ι v := (RatFunc.num_div_denom s).symm
  have hv' : ι v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv
  rw [hs]
  have hpd : p.natDegree ≤ d := le_max_left _ _
  have hqd : q.natDegree ≤ d := le_max_right _ _
  -- the constant case
  by_cases hn0 : n = 0
  · rw [hn0, mul_zero]
    have hu0 : u.natDegree = 0 := by omega
    have hv0 : v.natDegree = 0 := by omega
    have hsc : s = algebraMap K (RatFunc K) (u.coeff 0 / v.coeff 0) := by
      rw [hsuv, eq_C_of_natDegree_eq_zero hu0, eq_C_of_natDegree_eq_zero hv0, RatFunc.algebraMap_C,
        RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_div₀, coeff_C_zero, coeff_C_zero]
    rw [RatFunc.eval, hsc, eval₂_at_apply, eval₂_at_apply, ← map_div₀, RatFunc.algebraMap_eq_C]
    exact ht_C _
  -- `u ≠ 0`
  have hu : u ≠ 0 := by
    intro hu0
    rw [hu0] at huv
    have hvu := isCoprime_zero_left.mp huv
    have : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hvu
    rw [hu0, natDegree_zero] at hn
    omega
  -- the forms
  set F := homog p d u v
  set G := homog q d u v
  obtain ⟨a, b, hab⟩ := hpq
  have hdd : p.natDegree = d ∨ q.natDegree = d := by
    rcases le_total p.natDegree q.natDegree with h | h
    · right; exact (max_eq_right h).symm
    · left; exact (max_eq_left h).symm
  obtain ⟨a', b', hab'⟩ := reflect_coprime p q ⟨a, b, hab⟩ d hpd hqd hdd
  set E := max (max a.natDegree b.natDegree) (max a'.natDegree b'.natDegree)
  have hrp : (reflect d p).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl hpd)
  have hrq : (reflect d q).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl hqd)
  have h1 := homog_comb a b p q 1 E d (by omega) (by omega) hpd hqd hab u v hv
  rw [homog_one] at h1
  have h2 := homog_comb a' b' (reflect d p) (reflect d q) 1 E d (by omega) (by omega) hrp hrq hab'
    v u hu
  rw [homog_one, homog_swap, homog_swap] at h2
  -- degrees
  have hlow := deg_max_ge u v F G _ _ _ _ 1 (E + d) (E * n) huv one_ne_zero
    (by rw [one_mul]; exact h1) (by rw [one_mul]; exact h2)
    (deg_homog_le _ _ _ _) (deg_homog_le _ _ _ _)
    ((deg_homog_le _ _ _ _).trans (by rw [max_comm])) ((deg_homog_le _ _ _ _).trans (by rw [max_comm]))
  rw [natDegree_one, zero_add] at hlow
  have hF := deg_homog_le p d u v
  have hG := deg_homog_le q d u v
  -- coprimality
  have hcop : IsCoprime F G := by
    obtain ⟨s0, t0, hst⟩ := (huv.pow (m := E + d) (n := E + d))
    refine ⟨s0 * homog a' E v u + t0 * homog a E u v, s0 * homog b' E v u + t0 * homog b E u v, ?_⟩
    rw [← hst, ← h1, ← h2]; ring
  have hG0 : G ≠ 0 := by
    intro hG0
    have hFu : IsUnit F := isCoprime_zero_right.mp (hG0 ▸ hcop)
    have h0 : F.natDegree = 0 := natDegree_eq_zero_of_isUnit hFu
    rw [hG0, natDegree_zero, h0, max_self] at hlow
    have hd0 : d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact h
      · exfalso; have : 0 < d * n := Nat.mul_pos h (Nat.pos_of_ne_zero hn0); nlinarith
    have hq0 : q.natDegree = 0 := by omega
    apply hq
    have : G = C (q.coeff 0) := by
      simp [G, homog, formVal, hd0]
    rw [eq_C_of_natDegree_eq_zero hq0, ← this, hG0]
  -- the value
  have hval : Q.eval (algebraMap K (RatFunc K)) s = ι F / ι G := by
    have hG' : ι G ≠ 0 := (map_ne_zero_iff _ hinj).mpr hG0
    change eval₂ (algebraMap K (RatFunc K)) s p / eval₂ (algebraMap K (RatFunc K)) s q = _
    rw [homog_eval p d hpd u v hv, homog_eval q d hqd u v hv, hsuv]
    have : eval₂ (algebraMap K (RatFunc K)) (ι u / ι v) q ≠ 0 := by
      intro h0; apply hG'; rw [homog_eval q d hqd u v hv, h0, mul_zero]
    field_simp
  rw [hval, ht_div_coprime F G hG0 hcop]
  rw [← hn, add_mul] at hlow
  exact le_antisymm (max_le hF hG) (by omega)

/-- **`ht_comp` for an explicit coprime pair**: `ht (p(s) / q(s)) = max (deg p) (deg q) · ht s`. -/
theorem ht_comp' (p q : K[X]) (hq : q ≠ 0) (hpq : IsCoprime p q) (s : RatFunc K) :
    ht (p.eval₂ (algebraMap K (RatFunc K)) s / q.eval₂ (algebraMap K (RatFunc K)) s) =
      max p.natDegree q.natDegree * ht s := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  set d := max p.natDegree q.natDegree with hd
  set u := s.num
  set v := s.denom
  have hv : v ≠ 0 := RatFunc.denom_ne_zero s
  have huv : IsCoprime u v := RatFunc.isCoprime_num_denom s
  set n := max u.natDegree v.natDegree with hn
  have hs : ht s = n := rfl
  have hsuv : s = ι u / ι v := (RatFunc.num_div_denom s).symm
  have hv' : ι v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv
  rw [hs]
  have hpd : p.natDegree ≤ d := le_max_left _ _
  have hqd : q.natDegree ≤ d := le_max_right _ _
  -- the constant case
  by_cases hn0 : n = 0
  · rw [hn0, mul_zero]
    have hu0 : u.natDegree = 0 := by omega
    have hv0 : v.natDegree = 0 := by omega
    have hsc : s = algebraMap K (RatFunc K) (u.coeff 0 / v.coeff 0) := by
      rw [hsuv, eq_C_of_natDegree_eq_zero hu0, eq_C_of_natDegree_eq_zero hv0, RatFunc.algebraMap_C,
        RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_div₀, coeff_C_zero, coeff_C_zero]
    rw [hsc, eval₂_at_apply, eval₂_at_apply, ← map_div₀, RatFunc.algebraMap_eq_C]
    exact ht_C _
  -- `u ≠ 0`
  have hu : u ≠ 0 := by
    intro hu0
    rw [hu0] at huv
    have hvu := isCoprime_zero_left.mp huv
    have : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hvu
    rw [hu0, natDegree_zero] at hn
    omega
  -- the forms
  set F := homog p d u v
  set G := homog q d u v
  obtain ⟨a, b, hab⟩ := hpq
  have hdd : p.natDegree = d ∨ q.natDegree = d := by
    rcases le_total p.natDegree q.natDegree with h | h
    · right; exact (max_eq_right h).symm
    · left; exact (max_eq_left h).symm
  obtain ⟨a', b', hab'⟩ := reflect_coprime p q ⟨a, b, hab⟩ d hpd hqd hdd
  set E := max (max a.natDegree b.natDegree) (max a'.natDegree b'.natDegree)
  have hrp : (reflect d p).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl hpd)
  have hrq : (reflect d q).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl hqd)
  have h1 := homog_comb a b p q 1 E d (by omega) (by omega) hpd hqd hab u v hv
  rw [homog_one] at h1
  have h2 := homog_comb a' b' (reflect d p) (reflect d q) 1 E d (by omega) (by omega) hrp hrq hab'
    v u hu
  rw [homog_one, homog_swap, homog_swap] at h2
  -- degrees
  have hlow := deg_max_ge u v F G _ _ _ _ 1 (E + d) (E * n) huv one_ne_zero
    (by rw [one_mul]; exact h1) (by rw [one_mul]; exact h2)
    (deg_homog_le _ _ _ _) (deg_homog_le _ _ _ _)
    ((deg_homog_le _ _ _ _).trans (by rw [max_comm])) ((deg_homog_le _ _ _ _).trans (by rw [max_comm]))
  rw [natDegree_one, zero_add] at hlow
  have hF := deg_homog_le p d u v
  have hG := deg_homog_le q d u v
  -- coprimality
  have hcop : IsCoprime F G := by
    obtain ⟨s0, t0, hst⟩ := (huv.pow (m := E + d) (n := E + d))
    refine ⟨s0 * homog a' E v u + t0 * homog a E u v, s0 * homog b' E v u + t0 * homog b E u v, ?_⟩
    rw [← hst, ← h1, ← h2]; ring
  have hG0 : G ≠ 0 := by
    intro hG0
    have hFu : IsUnit F := isCoprime_zero_right.mp (hG0 ▸ hcop)
    have h0 : F.natDegree = 0 := natDegree_eq_zero_of_isUnit hFu
    rw [hG0, natDegree_zero, h0, max_self] at hlow
    have hd0 : d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact h
      · exfalso; have : 0 < d * n := Nat.mul_pos h (Nat.pos_of_ne_zero hn0); nlinarith
    have hq0 : q.natDegree = 0 := by omega
    apply hq
    have : G = C (q.coeff 0) := by
      simp [G, homog, formVal, hd0]
    rw [eq_C_of_natDegree_eq_zero hq0, ← this, hG0]
  -- the value
  have hval : p.eval₂ (algebraMap K (RatFunc K)) s / q.eval₂ (algebraMap K (RatFunc K)) s =
      ι F / ι G := by
    have hG' : ι G ≠ 0 := (map_ne_zero_iff _ hinj).mpr hG0
    rw [homog_eval p d hpd u v hv, homog_eval q d hqd u v hv, hsuv]
    have : eval₂ (algebraMap K (RatFunc K)) (ι u / ι v) q ≠ 0 := by
      intro h0; apply hG'; rw [homog_eval q d hqd u v hv, h0, mul_zero]
    field_simp
  rw [hval, ht_div_coprime F G hG0 hcop]
  rw [← hn, add_mul] at hlow
  exact le_antisymm (max_le hF hG) (by omega)


end FFHeight




