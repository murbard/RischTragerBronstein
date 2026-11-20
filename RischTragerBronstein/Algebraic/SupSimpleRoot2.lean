import RischTragerBronstein.Algebraic.SupSimpleRoot
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Simultaneous simple roots modulo infinitely many primes

`exists_simple_roots_prime`: two non-constant integer polynomials `a, b`, separable over `ℚ`, have
simple roots modulo the same prime `p`, for infinitely many `p`. Proof: roots `β` of `a` and `ζ` of
`b` in `ℚ̄` generate `ℚ(γ)` (primitive element), `β = A(γ)`, `ζ = B(γ)`; the minimal polynomial `h`
of `γ` divides `a(A(X))` and `b(B(X))`. Clearing denominators (Gauss's lemma) gives integer
identities `hZ · Q = a^hom(A_Z, d_A)`; at a simple root `s` of `hZ` modulo `p` (Schur,
`exists_simple_root_prime_sep`), `A_Z(s)/d_A` is a root of `ā`, simple for `p ∤ Res(a, a′)`.
-/

open Polynomial

namespace Sup

/-- The homogenized composition `∑ᵢ aᵢ A_Zⁱ d^{m−i}` (`m = deg a`). -/
noncomputable def homComp (a AZ : ℤ[X]) (d : ℤ) : ℤ[X] :=
  ∑ i ∈ Finset.range (a.natDegree + 1), C (a.coeff i) * AZ ^ i * C d ^ (a.natDegree - i)

lemma homComp_map (a AZ : ℤ[X]) (d : ℤ) (hd : d ≠ 0) (A : ℚ[X])
    (hA : AZ.map (Int.castRingHom ℚ) = C (d : ℚ) * A) :
    (homComp a AZ d).map (Int.castRingHom ℚ) = C ((d : ℚ) ^ a.natDegree) *
      (a.map (Int.castRingHom ℚ)).comp A := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [homComp, Polynomial.map_sum, comp, eval₂_eq_sum_range' _ (n := a.natDegree + 1)
    (by rw [natDegree_map_eq_of_injective (RingHom.injective_int _)]; omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ a.natDegree := by have := Finset.mem_range.mp hi; omega
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, map_C, map_C,
    hA, coeff_map]
  rw [mul_pow, ← C_pow, ← C_pow]
  have : (d : ℚ) ^ a.natDegree = (d : ℚ) ^ i * (d : ℚ) ^ (a.natDegree - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  rw [this, C_mul]
  simp only [eq_intCast]
  ring

lemma homComp_eval_zmod {p : ℕ} [Fact p.Prime] (a AZ : ℤ[X]) (d : ℤ) (s : ZMod p)
    (hd : (d : ZMod p) ≠ 0) :
    ((homComp a AZ d).map (Int.castRingHom (ZMod p))).eval s =
      (d : ZMod p) ^ a.natDegree * (a.map (Int.castRingHom (ZMod p))).eval
        ((AZ.map (Int.castRingHom (ZMod p))).eval s * (d : ZMod p)⁻¹) := by
  rw [homComp, Polynomial.map_sum, eval_finsetSum,
    eval_eq_sum_range' (n := a.natDegree + 1) (lt_of_le_of_lt (natDegree_map_le) (by omega)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ a.natDegree := by have := Finset.mem_range.mp hi; omega
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, map_C, map_C,
    eval_mul, eval_mul, eval_pow, eval_pow, eval_C, eval_C, coeff_map]
  simp only [eq_intCast]
  rw [mul_pow, inv_pow]
  have : (d : ZMod p) ^ a.natDegree = (d : ZMod p) ^ i * (d : ZMod p) ^ (a.natDegree - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  rw [this]
  field_simp


/-- A root of `hZ` modulo `p` gives a root of `ā` when `hZ ∣ a^hom(A_Z, d)`. -/
lemma root_of_dvd_homComp {p : ℕ} [Fact p.Prime] (a AZ hZ : ℤ[X]) (d : ℤ)
    (hdvd : hZ ∣ homComp a AZ d) (s : ZMod p)
    (hs : (hZ.map (Int.castRingHom (ZMod p))).eval s = 0) (hd : (d : ZMod p) ≠ 0) :
    (a.map (Int.castRingHom (ZMod p))).eval
      ((AZ.map (Int.castRingHom (ZMod p))).eval s * (d : ZMod p)⁻¹) = 0 := by
  obtain ⟨Q, hQ⟩ := hdvd
  have h1 := congrArg (fun P : ℤ[X] ↦ (P.map (Int.castRingHom (ZMod p))).eval s) hQ
  simp only [Polynomial.map_mul, eval_mul, hs, zero_mul] at h1
  rw [homComp_eval_zmod a AZ d s hd] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hd)

/-- Roots modulo `p ∤ Res(a, a′)` are simple. -/
lemma simple_of_not_dvd_res {p : ℕ} [Fact p.Prime] (a : ℤ[X]) (ha0 : 0 < a.natDegree)
    (hpR : ¬ (p : ℤ) ∣ resultant a (derivative a)) (r : ZMod p)
    (hr : (a.map (Int.castRingHom (ZMod p))).eval r = 0) :
    ((derivative a).map (Int.castRingHom (ZMod p))).eval r ≠ 0 := by
  obtain ⟨u', v', -, -, huv'⟩ := exists_mul_add_mul_eq_C_resultant a (derivative a) le_rfl le_rfl
    (Or.inl ha0.ne')
  intro h0
  apply hpR
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := congrArg (fun P : ℤ[X] ↦ (P.map (Int.castRingHom (ZMod p))).eval r) huv'
  simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, map_C, eval_C] at this
  simp only [hr, h0, mul_zero, zero_mul, zero_add, eq_intCast] at this
  exact this.symm

lemma exists_clear_int (P : ℚ[X]) : ∃ D : ℤ, D ≠ 0 ∧ ∃ mZ : ℤ[X],
    mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * P := by
  obtain ⟨b, hb, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors ℤ) P,
    ?_⟩
  rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hbP, zsmul_eq_mul]
  simp

/-- A primitive integer multiple of a non-zero rational polynomial. -/
lemma exists_primitive_int (P : ℚ[X]) (hP : P ≠ 0) : ∃ c : ℚ, c ≠ 0 ∧ ∃ hZ : ℤ[X],
    hZ.IsPrimitive ∧ hZ.map (Int.castRingHom ℚ) = C c * P := by
  obtain ⟨D, hD, mZ, hmZ⟩ := exists_clear_int P
  have hmZ0 : mZ ≠ 0 := by
    intro h; rw [h, Polynomial.map_zero] at hmZ
    exact mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast hD)) hP hmZ.symm
  have hcont : mZ.content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
  refine ⟨D / mZ.content, div_ne_zero (by exact_mod_cast hD) (by exact_mod_cast hcont),
    mZ.primPart, isPrimitive_primPart mZ, ?_⟩
  have e := eq_C_content_mul_primPart mZ
  have e2 := congrArg (Polynomial.map (Int.castRingHom ℚ)) e
  rw [Polynomial.map_mul, map_C, hmZ] at e2
  have hc : ((Int.castRingHom ℚ) mZ.content) ≠ 0 := by simpa using hcont
  rw [div_eq_mul_inv, C_mul, mul_comm (C (D : ℚ)), mul_assoc, e2, ← mul_assoc, ← C_mul,
    show ((mZ.content : ℚ))⁻¹ * (Int.castRingHom ℚ) mZ.content = 1 from
      inv_mul_cancel₀ (by simpa using hc), C_1, one_mul]

lemma resultant_deriv_ne_zero (a : ℤ[X]) (hsep : (a.map (Int.castRingHom ℚ)).Separable) :
    resultant a (derivative a) ≠ 0 := by
  intro h0
  have hmap := resultant_map_map a (derivative a) a.natDegree (derivative a).natDegree
    (Int.castRingHom ℚ)
  rw [h0, map_zero] at hmap
  have hne := resultant_ne_zero (a.map (Int.castRingHom ℚ)) _ (hsep : IsCoprime _ _)
  rw [derivative_map, natDegree_map_eq_of_injective (RingHom.injective_int _),
    natDegree_map_eq_of_injective (RingHom.injective_int _)] at hne
  exact hne hmap

lemma not_dvd_of_natAbs_lt {p : ℕ} {x : ℤ} (hx : x ≠ 0) (h : x.natAbs < p) : ¬ (p : ℤ) ∣ x := by
  intro hd
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hx) (Int.natCast_dvd.mp hd)
  omega

/-- **Simultaneous simple roots**: for two non-constant integer polynomials, separable over `ℚ`,
infinitely many primes admit simple roots of both. -/
theorem exists_simple_roots_prime (a b : ℤ[X]) (ha : (a.map (Int.castRingHom ℚ)).Separable)
    (hb : (b.map (Int.castRingHom ℚ)).Separable) (ha0 : 0 < a.natDegree) (hb0 : 0 < b.natDegree)
    (T : ℕ) : ∃ p, T < p ∧ p.Prime ∧
      (∃ hp : Fact p.Prime, ∃ s : ZMod p, (a.map (Int.castRingHom (ZMod p))).eval s = 0 ∧
        ((derivative a).map (Int.castRingHom (ZMod p))).eval s ≠ 0) ∧
      (∃ hp : Fact p.Prime, ∃ s : ZMod p, (b.map (Int.castRingHom (ZMod p))).eval s = 0 ∧
        ((derivative b).map (Int.castRingHom (ZMod p))).eval s ≠ 0) := by
  classical
  -- roots in `ℚ̄` and a primitive element
  set L := AlgebraicClosure ℚ
  have hroot : ∀ c : ℤ[X], 0 < c.natDegree → ∃ x : L, (c.map (Int.castRingHom L)).eval x = 0 := by
    intro c hc
    have hdeg : (c.map (Int.castRingHom L)).degree ≠ 0 := by
      rw [degree_map_eq_of_injective (RingHom.injective_int _)]
      intro h; rw [degree_eq_natDegree (by rintro rfl; simp at hc)] at h
      exact absurd (by exact_mod_cast h : c.natDegree = 0) (by omega)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨x, hx⟩
  obtain ⟨β, hβ⟩ := hroot a ha0
  obtain ⟨ζ, hζ⟩ := hroot b hb0
  obtain ⟨γ, hγ⟩ := Field.primitive_element_inf_aux ℚ β ζ
  have hγi : IsIntegral ℚ γ := (Algebra.IsIntegral.isIntegral γ)
  have hpoly : ∀ x : L, x ∈ IntermediateField.adjoin ℚ {β, ζ} → ∃ A : ℚ[X], aeval γ A = x := by
    intro x hx
    rw [hγ] at hx
    have hx' : x ∈ (IntermediateField.adjoin ℚ {γ}).toSubalgebra := hx
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hγi.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨A, hA⟩ := hx'
    exact ⟨A, hA⟩
  obtain ⟨A, hA⟩ := hpoly β (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert β {ζ}))
  obtain ⟨B, hB⟩ := hpoly ζ (IntermediateField.subset_adjoin ℚ _
    (Set.mem_insert_of_mem β (Set.mem_singleton ζ)))
  set h := minpoly ℚ γ with hh
  have hh0 : h ≠ 0 := minpoly.ne_zero hγi
  have hhdeg : 0 < h.natDegree := minpoly.natDegree_pos hγi
  have hhsep : h.Separable := (minpoly.irreducible hγi).separable
  have hdvd : ∀ (c : ℤ[X]) (C' : ℚ[X]) (x : L), aeval γ C' = x →
      (c.map (Int.castRingHom L)).eval x = 0 → h ∣ (c.map (Int.castRingHom ℚ)).comp C' := by
    intro c C' x hC hx
    apply minpoly.dvd
    rw [aeval_comp, hC, aeval_def, eval₂_map]
    rw [eval_map] at hx
    convert hx using 2
    exact RingHom.ext_int _ _
  -- integral data
  obtain ⟨c, hc0, hZ, hprim, hhZ⟩ := exists_primitive_int h hh0
  have hZsep : (hZ.map (Int.castRingHom ℚ)).Separable := by
    rw [hhZ, mul_comm]; exact hhsep.mul_unit (isUnit_C.mpr (Ne.isUnit hc0))
  have hZdeg : 0 < hZ.natDegree := by
    rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), hhZ,
      natDegree_C_mul hc0]; exact hhdeg
  have hG : ∀ (c' : ℤ[X]) (C' : ℚ[X]) (x : L), aeval γ C' = x →
      (c'.map (Int.castRingHom L)).eval x = 0 → ∃ d : ℤ, d ≠ 0 ∧ ∃ CZ : ℤ[X],
        hZ ∣ homComp c' CZ d := by
    intro c' C' x hC hx
    obtain ⟨d, hd, CZ, hCZ⟩ := exists_clear_int C'
    refine ⟨d, hd, CZ, (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast hZ _ hprim).mpr ?_⟩
    rw [hhZ, homComp_map c' CZ d hd C' hCZ]
    refine mul_dvd_mul ⟨C ((d : ℚ) ^ c'.natDegree / c), ?_⟩ (hdvd c' C' x hC hx)
    rw [← C_mul, mul_div_cancel₀ _ hc0]
  obtain ⟨dA, hdA, AZ, hAZ⟩ := hG a A β hA hβ
  obtain ⟨dB, hdB, BZ, hBZ⟩ := hG b B ζ hB hζ
  have hRa := resultant_deriv_ne_zero a ha
  have hRb := resultant_deriv_ne_zero b hb
  obtain ⟨p, hpT, hp, s, hs, -⟩ := exists_simple_root_prime_sep hZ hZsep hZdeg
    (T + dA.natAbs + dB.natAbs + (resultant a (derivative a)).natAbs +
      (resultant b (derivative b)).natAbs)
  haveI hF : Fact p.Prime := ⟨hp⟩
  have hdA' : (dA : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_of_natAbs_lt hdA (by omega)
  have hdB' : (dB : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_of_natAbs_lt hdB (by omega)
  refine ⟨p, by omega, hp, ⟨hF, _, root_of_dvd_homComp a AZ hZ dA hAZ s hs hdA',
    simple_of_not_dvd_res a ha0 (not_dvd_of_natAbs_lt hRa (by omega)) _
      (root_of_dvd_homComp a AZ hZ dA hAZ s hs hdA')⟩,
    ⟨hF, _, root_of_dvd_homComp b BZ hZ dB hBZ s hs hdB',
    simple_of_not_dvd_res b hb0 (not_dvd_of_natAbs_lt hRb (by omega)) _
      (root_of_dvd_homComp b BZ hZ dB hBZ s hs hdB')⟩⟩

end Sup
