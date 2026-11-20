import RischTragerBronstein.Algebraic.Ramanujan
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Correlations with the Ramanujan vector: a Galois argument

For `r : ℕ → ℤ` periodic mod `n` and `c = (c_n(k))_k` the Ramanujan vector, the correlation
`v(m) = ∑_{k<n} c(k) r(m + k)` is the "primitive component" of `r`. **If `v ≠ 0`, some integer
correlation of `v` is a non-zero multiple of `c`** (`corr_core`): with the transforms
`ev f ω = ∑ f(k) ωᵏ` (`ω` an `n`-th root of unity), `ev v ω = ev c ω⁻¹ · ev r ω` (`ev_corr`), `ev c ω`
is `n` or `0` (primitive or not), the transform is injective (`ev_inj`), `ev r` vanishes at one
primitive root iff at all (`ev_galois`: the cyclotomic polynomial is the minimal polynomial), and
`h = ∏_{u unit, u ≠ 1} r(X^{n−u})` gives `ev (corr h v) ω = N₀ · ev c ω` with `N₀ = ∏_u ev r (ζ^u) ≠ 0`.
-/

open Finset Polynomial Ramanujan

namespace KRDft

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The transform of an `F`-valued vector. -/
def evF (n : ℕ) (f : ℕ → F) (ω : F) : F := ∑ k ∈ range n, f k * ω ^ k

/-- The correlation `(a ⋆ b)(m) = ∑_{k<n} a(k) b(m + k)`. -/
def corr (n : ℕ) (a b : ℕ → ℤ) (m : ℕ) : ℤ := ∑ k ∈ range n, a k * b (m + k)

lemma sum_shift (g : ℕ → F) (hg : ∀ k, g (k + n) = g k) (k0 : ℕ) :
    ∑ m ∈ range n, g (m + k0) = ∑ m ∈ range n, g m := by
  induction k0 with
  | zero => simp
  | succ k0 ih =>
    rw [← ih]
    rcases n with _ | n
    · simp
    calc ∑ m ∈ range (n + 1), g (m + (k0 + 1))
        = ∑ m ∈ range n, g (m + (k0 + 1)) + g (n + (k0 + 1)) := sum_range_succ _ _
      _ = ∑ m ∈ range n, g (m + 1 + k0) + g (0 + k0) := by
          congr 1
          · exact sum_congr rfl fun m _ ↦ by rw [show m + 1 + k0 = m + (k0 + 1) by ring]
          · rw [show n + (k0 + 1) = k0 + (n + 1) by ring, hg, zero_add]
      _ = ∑ m ∈ range (n + 1), g (m + k0) := (sum_range_succ' (fun m ↦ g (m + k0)) n).symm

lemma evF_corr (hn : 0 < n) (a b : ℕ → ℤ) (hb : ∀ k, b (k + n) = b k) (ω : F) (hω : ω ^ n = 1) :
    evF n (fun m ↦ (corr n a b m : F)) ω =
      evF n (fun k ↦ (a k : F)) ω⁻¹ * evF n (fun k ↦ (b k : F)) ω := by
  have hω0 : ω ≠ 0 := fun h ↦ by rw [h, zero_pow hn.ne'] at hω; exact zero_ne_one hω
  simp only [evF, corr, Int.cast_sum, Int.cast_mul, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  have hs := sum_shift (n := n) (fun l ↦ (b l : F) * ω ^ l) (fun l ↦ by
    rw [hb, pow_add, hω, mul_one]) k
  calc ∑ m ∈ range n, (a k : F) * (b (m + k) : F) * ω ^ m
      = (a k : F) * ω⁻¹ ^ k * ∑ m ∈ range n, (b (m + k) : F) * ω ^ (m + k) := by
        rw [mul_sum]
        refine sum_congr rfl fun m _ ↦ ?_
        rw [pow_add, inv_pow]; field_simp
    _ = (a k : F) * ω⁻¹ ^ k * ∑ m ∈ range n, (b m : F) * ω ^ m := by rw [hs]
    _ = _ := by rw [mul_sum]

/-- **The transform is injective.** -/
lemma evF_inj {ζ : F} (hζ : IsPrimitiveRoot ζ n) (f : ℕ → F)
    (h : ∀ i < n, evF n f (ζ ^ i) = 0) : ∀ k < n, f k = 0 := by
  classical
  set P : F[X] := ∑ k ∈ range n, Polynomial.C (f k) * X ^ k with hP
  have hdeg : P.natDegree < n ∨ P = 0 := by
    by_cases hP0 : P = 0
    · exact Or.inr hP0
    left
    rcases n with _ | n
    · simp [hP] at hP0
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_) (Nat.lt_succ_self n)
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))
  have hP0 : P = 0 := by
    rcases hdeg with hlt | h0
    · refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := fun i : Fin n ↦ ζ ^ (i : ℕ))
        (fun i j hij ↦ Fin.ext (hζ.pow_inj i.2 j.2 hij)) (fun i ↦ ?_) (by simpa using hlt)
      rw [← h i i.2, hP, eval_finset_sum]
      simp [evF]
    · exact h0
  intro k hk
  have := congrArg (fun Q : F[X] ↦ Q.coeff k) hP0
  simp only [hP, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [sum_eq_single k (fun b _ hb ↦ if_neg (Ne.symm hb)) (fun h ↦ absurd (mem_range.mpr hk) h),
    if_pos rfl] at this
  exact this

/-- The polynomial `∑_{k<n} r(k) Xᵏ`. -/
noncomputable def polyR (n : ℕ) (r : ℕ → ℤ) : ℤ[X] := ∑ k ∈ range n, Polynomial.C (r k) * X ^ k

lemma aeval_polyR (r : ℕ → ℤ) (ω : F) : aeval ω (polyR n r) = evF n (fun k ↦ (r k : F)) ω := by
  simp [polyR, evF, map_sum]

/-- **Galois**: `ev r` vanishes at one primitive root iff at all of them. -/
lemma ev_galois (hn : 0 < n) (r : ℕ → ℤ) {ω ω' : F} (hω : IsPrimitiveRoot ω n)
    (hω' : IsPrimitiveRoot ω' n) (h0 : evF n (fun k ↦ (r k : F)) ω = 0) :
    evF n (fun k ↦ (r k : F)) ω' = 0 := by
  rw [← aeval_polyR] at h0 ⊢
  have hdvd := minpoly.isIntegrallyClosed_dvd (hω.isIntegral hn) h0
  rw [← cyclotomic_eq_minpoly hω hn] at hdvd
  obtain ⟨Q, hQ⟩ := hdvd
  rw [hQ, map_mul]
  have : aeval ω' (cyclotomic n ℤ) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (hω'.isRoot_cyclotomic hn)
  rw [this, zero_mul]

open Classical in
lemma evF_ramC (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n) {ω : F} (hω : ω ^ n = 1) :
    evF n (fun k ↦ (ramC n k : F)) ω = if IsPrimitiveRoot ω n then (n : F) else 0 := by
  classical
  rw [evF]
  convert sum_ramC_mul_pow hn hζ hω

/-- **The core**: a non-zero primitive component generates a non-zero multiple of the Ramanujan
vector by an integer correlation. -/
theorem corr_core (hn1 : 1 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n) (r : ℕ → ℤ)
    (hr : ∀ k, r (k + n) = r k) (hv : ∃ m < n, corr n (fun k ↦ ramC n k) r m ≠ 0) :
    ∃ (h : ℕ → ℤ) (p : ℤ) (q : ℕ), p ≠ 0 ∧ 0 < q ∧
      ∀ m < n, (q : ℤ) * corr n h (corr n (fun k ↦ ramC n k) r) m = p * ramC n m := by
  classical
  have hn : 0 < n := by omega
  set c : ℕ → ℤ := fun k ↦ ramC n k with hc
  set v := corr n c r with hvdef
  have hvper : ∀ k, v (k + n) = v k := fun k ↦ by
    simp only [hvdef, corr]
    exact sum_congr rfl fun i _ ↦ by rw [show k + n + i = k + i + n by ring, hr]
  have hevv : ∀ ω : F, ω ^ n = 1 → evF n (fun m ↦ (v m : F)) ω =
      evF n (fun k ↦ (c k : F)) ω⁻¹ * evF n (fun k ↦ (r k : F)) ω :=
    fun ω hω ↦ evF_corr hn c r hr ω hω
  have hpow1 : ∀ i : ℕ, (ζ ^ i) ^ n = 1 := fun i ↦ by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- a root where `ev v` does not vanish
  obtain ⟨i0, hi0, hvi0⟩ : ∃ i < n, evF n (fun m ↦ (v m : F)) (ζ ^ i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hvm⟩ := hv
    exact hvm (by exact_mod_cast evF_inj hζ (fun m ↦ (v m : F)) hcon m hm)
  rw [hevv _ (hpow1 i0)] at hvi0
  obtain ⟨hc0, hr0⟩ := mul_ne_zero_iff.mp hvi0
  have hinvn : (ζ ^ i0)⁻¹ ^ n = 1 := by rw [inv_pow, hpow1, inv_one]
  rw [evF_ramC hn hζ hinvn] at hc0
  have hprim0 : IsPrimitiveRoot (ζ ^ i0) n := by
    by_contra hnp
    exact hc0 (if_neg (fun h ↦ hnp (IsPrimitiveRoot.inv_iff.mp h)))
  have hall : ∀ ω : F, IsPrimitiveRoot ω n → evF n (fun k ↦ (r k : F)) ω ≠ 0 := fun ω hω h0 ↦
    hr0 (ev_galois hn r hω hprim0 h0)
  -- the units and the norm
  set U := (range n).filter (fun u ↦ Nat.Coprime u n) with hU
  have hUprim : ∀ u ∈ U, IsPrimitiveRoot (ζ ^ u) n := fun u hu ↦
    hζ.pow_of_coprime u (mem_filter.mp hu).2
  have h1U : 1 ∈ U := mem_filter.mpr ⟨mem_range.mpr hn1, Nat.coprime_one_left n⟩
  set N₀ : F := ∏ u ∈ U, evF n (fun k ↦ (r k : F)) (ζ ^ u) with hN₀
  have hN0 : N₀ ≠ 0 := prod_ne_zero_iff.mpr fun u hu ↦ hall _ (hUprim u hu)
  -- the correlating vector
  set H : ℤ[X] := ∏ u ∈ U.erase 1, (polyR n r).comp (X ^ (n - u)) with hH
  set h : ℕ → ℤ := fun k ↦ ∑ e ∈ (range (H.natDegree + 1)).filter (fun e ↦ e % n = k), H.coeff e
    with hh
  have hevh : ∀ ω : F, ω ^ n = 1 → evF n (fun k ↦ (h k : F)) ω = aeval ω H := by
    intro ω hω
    rw [aeval_eq_sum_range, evF]
    simp only [hh, Int.cast_sum, sum_mul]
    have e1 : ∀ x ∈ range n, ∑ i ∈ (range (H.natDegree + 1)).filter (fun e ↦ e % n = x),
        (H.coeff i : F) * ω ^ x = ∑ i ∈ (range (H.natDegree + 1)).filter (fun e ↦ e % n = x),
        (H.coeff i : F) * ω ^ (i % n) := fun x _ ↦
      sum_congr rfl fun i hi ↦ by rw [(mem_filter.mp hi).2]
    rw [sum_congr rfl e1, sum_fiberwise_of_maps_to (g := fun e ↦ e % n)
      (fun e _ ↦ mem_range.mpr (Nat.mod_lt e hn)) (fun e ↦ (H.coeff e : F) * ω ^ (e % n))]
    refine sum_congr rfl fun e _ ↦ ?_
    rw [zsmul_eq_mul]
    congr 1
    conv_rhs => rw [← Nat.mod_add_div e n, pow_add, pow_mul, hω, one_pow, mul_one]
  -- `ev r` at the powers of a primitive root: a permutation of the units
  have hperm : ∀ i < n, IsPrimitiveRoot (ζ ^ i) n →
      ∏ u ∈ U, evF n (fun k ↦ (r k : F)) ((ζ ^ i) ^ u) = N₀ := by
    intro i hi hpi
    have hci : Nat.Coprime i n := (hζ.pow_iff_coprime hn i).mp hpi
    obtain ⟨i', -, hi'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hci hn1
    have hpow : ∀ e : ℕ, ζ ^ e = ζ ^ (e % n) := fun e ↦ by
      conv_lhs => rw [← Nat.mod_add_div e n, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    refine prod_nbij' (fun u ↦ i * u % n) (fun u ↦ i' * u % n) (fun u hu ↦ ?_) (fun u hu ↦ ?_)
      (fun u hu ↦ ?_) (fun u hu ↦ ?_) (fun u hu ↦ ?_)
    · obtain ⟨-, hcu⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hn),
        (ZMod.coprime_mod_iff_coprime _ n).mpr (Nat.Coprime.mul_left hci hcu)⟩
    · obtain ⟨-, hcu⟩ := mem_filter.mp hu
      have hii : Nat.Coprime (i * i') n :=
        (ZMod.coprime_mod_iff_coprime (i * i') n).mp (by rw [hi']; exact Nat.coprime_one_left n)
      have hci' : Nat.Coprime i' n := Nat.Coprime.coprime_mul_left hii
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hn),
        (ZMod.coprime_mod_iff_coprime _ n).mpr (Nat.Coprime.mul_left hci' hcu)⟩
    · have hu' := mem_range.mp (mem_filter.mp hu).1
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, mul_comm i' i, hi',
        one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hu']
    · have hu' := mem_range.mp (mem_filter.mp hu).1
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hi',
        one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hu']
    · rw [← pow_mul, hpow (i * u)]
  have hmain : ∀ i < n, evF n (fun m ↦ (corr n h v m : F)) (ζ ^ i) =
      N₀ * evF n (fun k ↦ (c k : F)) (ζ ^ i) := by
    intro i hi
    have hinv : (ζ ^ i)⁻¹ ^ n = 1 := by rw [inv_pow, hpow1, inv_one]
    rw [evF_corr hn h v hvper _ (hpow1 i), hevh _ hinv, hevv _ (hpow1 i),
      evF_ramC hn hζ hinv, evF_ramC hn hζ (hpow1 i)]
    by_cases hpi : IsPrimitiveRoot (ζ ^ i) n
    · rw [if_pos (hpi.inv), if_pos hpi]
      have hH : aeval (ζ ^ i)⁻¹ H * evF n (fun k ↦ (r k : F)) (ζ ^ i) =
          ∏ u ∈ U, evF n (fun k ↦ (r k : F)) ((ζ ^ i) ^ u) := by
        rw [hH, map_prod, ← mul_prod_erase U _ h1U, pow_one, mul_comm]
        congr 1
        refine prod_congr rfl fun u hu ↦ ?_
        have hun : u < n := mem_range.mp (mem_filter.mp (mem_of_mem_erase hu)).1
        rw [aeval_comp, map_pow, aeval_X, aeval_polyR]
        congr 1
        rw [inv_pow, show (ζ ^ i) ^ u = ((ζ ^ i) ^ (n - u))⁻¹ from
          eq_inv_of_mul_eq_one_left (by rw [← pow_add, Nat.add_sub_cancel' hun.le, hpow1])]
      rw [← hperm i hi hpi, ← hH]
      ring
    · rw [if_neg (fun h' ↦ hpi (IsPrimitiveRoot.inv_iff.mp h')), if_neg hpi]
      ring
  -- equality of vectors in `F`
  have hvec : ∀ m < n, (corr n h v m : F) = N₀ * (c m : F) := by
    have := evF_inj hζ (fun m ↦ (corr n h v m : F) - N₀ * (c m : F)) (fun i hi ↦ by
      have e := hmain i hi
      simp only [evF, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum] at e ⊢
      rw [e, sub_self])
    exact fun m hm ↦ sub_eq_zero.mp (this m hm)
  -- `N₀` is rational
  obtain ⟨m0, hm0, hcm0⟩ : ∃ m < n, c m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e := evF_ramC hn hζ (ω := ζ) hζ.pow_eq_one
    rw [if_pos hζ] at e
    have : evF n (fun k ↦ (ramC n k : F)) ζ = 0 :=
      sum_eq_zero fun k hk ↦ by
        show (ramC n k : F) * ζ ^ k = 0
        rw [show (ramC n k : F) = (c k : F) from rfl, hcon k (mem_range.mp hk), Int.cast_zero, zero_mul]
    rw [this] at e
    exact (Nat.cast_ne_zero.mpr hn.ne') e.symm
  set a : ℚ := (corr n h v m0 : ℚ) / c m0 with ha
  have haN : (a : F) = N₀ := by
    have hcF : (c m0 : F) ≠ 0 := by exact_mod_cast hcm0
    rw [ha, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, hvec m0 hm0, mul_div_assoc,
      div_self hcF, mul_one]
  have ha0 : a ≠ 0 := fun h0 ↦ hN0 (by rw [← haN, h0, Rat.cast_zero])
  refine ⟨h, a.num, a.den, Rat.num_ne_zero.mpr ha0, a.den_pos, fun m hm ↦ ?_⟩
  have hF : ((a.den : ℤ) * corr n h v m : F) = (a.num * ramC n m : F) := by
    push_cast
    rw [hvec m hm, ← haN]
    have : (a.den : F) * (a : F) = (a.num : F) := by
      rw [← Rat.cast_natCast, ← Rat.cast_mul, mul_comm, Rat.mul_den_eq_num, Rat.cast_intCast]
    rw [← mul_assoc, this]
  exact_mod_cast hF

end KRDft
