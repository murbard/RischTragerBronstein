import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Ramanujan sums

`ramC n k = ∑_{d ∣ gcd(n, k)} μ(n/d) d ∈ ℤ` is the sum of the `k`-th powers of the primitive
`n`-th roots of unity, in any field containing a primitive `n`-th root of unity (`ramC_eq`).
Consequently `∑_{k < n} ramC n k · ωᵏ = n` for `ω` a primitive `n`-th root and `0` for the other
`n`-th roots of unity (`sum_ramC_mul_pow`); `ramC n k` depends only on `gcd(n, k)`.
-/

open Finset ArithmeticFunction

namespace Ramanujan

/-- **The Ramanujan sum** `c_n(k)`. -/
def ramC (n k : ℕ) : ℤ := ∑ d ∈ (Nat.gcd n k).divisors, (moebius (n / d) : ℤ) * d

variable {F : Type*} [Field F] [DecidableEq F]

/-- The sum of the `k`-th powers of all `d`-th roots of unity. -/
lemma sum_nthRoots_pow {d : ℕ} (hd : 0 < d) {ω : F} (hω : IsPrimitiveRoot ω d) (k : ℕ) :
    ∑ z ∈ Polynomial.nthRootsFinset d (1 : F), z ^ k = if d ∣ k then (d : F) else 0 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have himg : Polynomial.nthRootsFinset d (1 : F) = (range d).image (fun i ↦ ω ^ i) := by
    ext z
    rw [Polynomial.mem_nthRootsFinset hd (1 : F), mem_image]
    constructor
    · intro hz
      obtain ⟨i, hi, rfl⟩ := hω.eq_pow_of_pow_eq_one hz
      exact ⟨i, mem_range.mpr hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  rw [himg, sum_image (fun i hi j hj h ↦ hω.pow_inj (mem_range.mp hi) (mem_range.mp hj) h)]
  simp_rw [← pow_mul, mul_comm _ k, pow_mul]
  split_ifs with hdk
  · obtain ⟨m, rfl⟩ := hdk
    rw [pow_mul, hω.pow_eq_one, one_pow]
    simp
  · have hne : ω ^ k ≠ 1 := fun h ↦ hdk ((hω.pow_eq_one_iff_dvd k).mp h)
    have hpow : (ω ^ k) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have := geom_sum_mul (ω ^ k) d
    rw [hpow, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)

/-- **`ramC` is the sum of the `k`-th powers of the primitive `n`-th roots.** -/
theorem ramC_eq {n : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n) (k : ℕ) :
    (ramC n k : F) = ∑ ω ∈ primitiveRoots n F, ω ^ k := by
  set f : ℕ → F := fun d ↦ ∑ ω ∈ primitiveRoots d F, ω ^ k with hf
  set g : ℕ → F := fun d ↦ if d ∣ k then (d : F) else 0 with hg
  have hs : ∀ m d : ℕ, m ∣ d → d ∈ {d : ℕ | d ∣ n} → m ∈ {d : ℕ | d ∣ n} :=
    fun m d hmd hd ↦ dvd_trans hmd hd
  have hfg : ∀ d > 0, d ∈ {d : ℕ | d ∣ n} → ∑ i ∈ d.divisors, f i = g d := by
    intro d hd hdn
    obtain ⟨e, he⟩ := (hdn : d ∣ n)
    have hωd : IsPrimitiveRoot (ζ ^ e) d := hζ.pow hn (by rw [he, mul_comm])
    simp only [hf, hg]
    rw [← sum_nthRoots_pow hd hωd k, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
      sum_biUnion]
    intro i _ j _ hij
    exact disjoint_left.mpr fun z hzi hzj ↦ by
      have hi := (mem_primitiveRoots (Nat.pos_of_mem_divisors ‹_›)).mp hzi
      have hj := (mem_primitiveRoots (Nat.pos_of_mem_divisors ‹_›)).mp hzj
      exact hij (hi.unique hj)
  have hinv := (sum_eq_iff_sum_mul_moebius_eq_on {d : ℕ | d ∣ n} hs).mp hfg n hn (dvd_refl n)
  show _ = f n
  rw [← hinv, Nat.sum_divisorsAntidiagonal' (fun a b ↦ (moebius a : F) * g b)]
  simp only [hg, ramC, Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun d _ ↦ rfl
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h1, hn.ne'⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left k hn).ne'⟩

/-- `∑_{k < n} zᵏ = n` if `z = 1`, `0` otherwise, for `zⁿ = 1`. -/
lemma geom_root (n : ℕ) {z : F} (hz : z ^ n = 1) :
    ∑ k ∈ range n, z ^ k = if z = 1 then (n : F) else 0 := by
  split_ifs with h
  · simp [h]
  · have := geom_sum_mul z n
    rw [hz, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h)

open Classical in
/-- **Evaluation of the Ramanujan vector** at an `n`-th root of unity `ω`:
`∑_{k < n} c_n(k) ωᵏ = n` if `ω` is primitive, `0` otherwise. -/
theorem sum_ramC_mul_pow {n : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n) {ω : F}
    (hω : ω ^ n = 1) :
    ∑ k ∈ range n, (ramC n k : F) * ω ^ k = if IsPrimitiveRoot ω n then (n : F) else 0 := by
  simp_rw [ramC_eq hn hζ, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ ω' ∈ primitiveRoots n F, ∑ k ∈ range n, ω' ^ k * ω ^ k =
      if ω' * ω = 1 then (n : F) else 0 := fun ω' hω' ↦ by
    have hp := (mem_primitiveRoots hn).mp hω'
    simp_rw [← mul_pow]
    exact geom_root n (by rw [mul_pow, hp.pow_eq_one, hω, one_mul])
  rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  have hω0 : ω ≠ 0 := fun h ↦ by rw [h, zero_pow hn.ne'] at hω; exact zero_ne_one hω
  have hfilt : (primitiveRoots n F).filter (fun ω' ↦ ω' * ω = 1) =
      if IsPrimitiveRoot ω n then {ω⁻¹} else ∅ := by
    ext ω'
    simp only [Finset.mem_filter, mem_primitiveRoots hn]
    split_ifs with hp
    · rw [Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact eq_inv_of_mul_eq_one_left h
      · rintro rfl; exact ⟨hp.inv, inv_mul_cancel₀ hω0⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro h1 h2
      apply hp
      rw [← inv_inv ω, show ω⁻¹ = ω' from (eq_inv_of_mul_eq_one_left h2).symm]
      exact h1.inv
  rw [hfilt]
  split_ifs <;> simp

/-- `c_n(k)` depends only on `gcd(n, k)`. -/
lemma ramC_gcd (n k : ℕ) : ramC n (Nat.gcd n k) = ramC n k := by
  simp only [ramC, Nat.gcd_gcd_self_right_left]

/-- **Symmetry** `c_n(n − k) = c_n(k)`. -/
lemma ramC_sub (n k : ℕ) (hk : k ≤ n) : ramC n (n - k) = ramC n k := by
  simp only [ramC, Nat.gcd_self_sub_right hk]

end Ramanujan
