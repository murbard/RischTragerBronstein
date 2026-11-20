import RischTragerBronstein.Algebraic.SuperDecide
import RischTragerBronstein.Algebraic.EllGen

/-!
# Deciding `∫ B(x) p(x)^{a/n} dx` for every exponent `a/n ∉ ℤ`

On `yⁿ = p(x)` (`p` squarefree, `gcd(n, deg p) = 1`), `B(x) p(x)^{a/n} = B yʲ / pᵏ` with
`0 < j < n`. For `k ≥ 2` a Hermite step on the power of `p` (`supHermStep`, from
`s p + t p′ = c`):

  `B yʲ / pᵏ = (G yʲ / pᵏ⁻¹)′ + B′ yʲ / pᵏ⁻¹`,  `G = B t / (c r)`, `B′ = B s / c − G′`,
  `r = j/n − (k − 1) ≠ 0`,

reduces `k` to `1`, where `super_decides` applies (`super_decides_pow`).
-/

open Polynomial IntermediateField

namespace CPoly

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] [DecidableEq 𝕜]

/-- One Hermite step on `B yʲ / pᵏ` (`r = j/n − (k − 1)`): returns `(G, B′)`. -/
def supHermStep (r : 𝕜) (p B : CPoly 𝕜) : CPoly 𝕜 × CPoly 𝕜 :=
  let e := egcd p (deriv p)
  let c := e.1.getD 0 0
  let S := smul (1 / c) (mul B e.2.1)
  let T := smul (1 / c) (mul B e.2.2)
  let G := smul (1 / r) T
  (G, sub S (deriv G))

lemma egcd_const (p : CPoly 𝕜) (hp : Squarefree (toPoly p)) :
    toPoly (egcd p (deriv p)).1 = Polynomial.C ((egcd p (deriv p)).1.getD 0 0) ∧
      (egcd p (deriv p)).1.getD 0 0 ≠ 0 := by
  obtain ⟨h1, h2⟩ := egcd_dvd p (deriv p)
  have hcop : IsCoprime (toPoly p) (derivative (toPoly p)) :=
    PerfectField.separable_iff_squarefree.mpr hp
  rw [toPoly_deriv] at h2
  have hu : IsUnit (toPoly (egcd p (deriv p)).1) := hcop.isUnit_of_dvd' h1 h2
  obtain ⟨c, hc, hcg⟩ := Polynomial.isUnit_iff.mp hu
  have hc0 : (egcd p (deriv p)).1.getD 0 0 = c := by
    rw [← coeff_toPoly, ← hcg, coeff_C_zero]
  rw [hc0]
  exact ⟨hcg.symm, hc.ne_zero⟩

/-- **Specification of the Hermite step**: `B = p G′ + r G p′ + p B′`. -/
theorem supHermStep_spec (r : 𝕜) (hr : r ≠ 0) (p B : CPoly 𝕜) (hp : Squarefree (toPoly p)) :
    toPoly B = toPoly p * derivative (toPoly (supHermStep r p B).1) +
      Polynomial.C r * (toPoly (supHermStep r p B).1 * derivative (toPoly p)) +
      toPoly p * toPoly (supHermStep r p B).2 := by
  obtain ⟨hg, hc⟩ := egcd_const p hp
  have hb := egcd_spec p (deriv p)
  rw [hg, toPoly_deriv] at hb
  set c := (egcd p (deriv p)).1.getD 0 0
  set s := toPoly (egcd p (deriv p)).2.1
  set t := toPoly (egcd p (deriv p)).2.2
  simp only [supHermStep, toPoly_sub, toPoly_smul, toPoly_mul, toPoly_deriv, derivative_mul,
    derivative_C, zero_mul, zero_add]
  have hC : Polynomial.C r * Polynomial.C (1 / r) = 1 := by rw [← Polynomial.C_mul, mul_one_div_cancel hr, map_one]
  have hC' : Polynomial.C (1 / c) * Polynomial.C c = 1 := by rw [← Polynomial.C_mul, one_div_mul_cancel hc, map_one]
  linear_combination (-(Polynomial.C (1 / c) * toPoly B)) * hb +
    (-(Polynomial.C (1 / c) * toPoly B * t * derivative (toPoly p))) * hC + (-toPoly B) * hC'

/-- The Hermite loop: from `B yʲ / pᵏ` down to `B* yʲ / p`. -/
def supHerm (j n : ℕ) (p B : CPoly 𝕜) : ℕ → CPoly 𝕜
  | 0 => mul B p
  | 1 => B
  | k + 2 => supHerm j n p (supHermStep ((j : 𝕜) / n - (k + 1 : ℕ)) p B).2 (k + 1)

end CPoly

namespace Differential

namespace SuperData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

variable (S : SuperData C L)

/-- `(G yʲ / pᵐ)′ pᵐ⁺¹ = yʲ (p G′ + (j/n − m) G p′)`. -/
lemma deriv_poly_y_div_pow (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (G : C[X]) (j m : ℕ) :
    (aeval S.x G * S.y ^ j / aeval S.x S.p ^ m)′ * aeval S.x S.p ^ (m + 1) = S.y ^ j *
      aeval S.x (S.p * derivative G + Polynomial.C ((j : C) / S.n - m) * (G * derivative S.p)) := by
  have h1 := S.deriv_poly_y_mul hC hx G j
  have hp0 := S.p_ne_zero
  have hdp : (aeval S.x S.p)′ = aeval S.x (derivative S.p) := deriv_aeval_x S.x hC hx S.p
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [pow_zero, div_one, zero_add, pow_one, h1]
    simp
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set P := aeval S.x S.p
  set w := aeval S.x G * S.y ^ j / P ^ (m' + 1)
  have hw : w * P ^ (m' + 1) = aeval S.x G * S.y ^ j := div_mul_cancel₀ _ (pow_ne_zero _ hp0)
  have hd := congrArg (fun z : L ↦ z′) hw
  rw [Derivation.leibniz, Derivation.leibniz_pow, hdp, Nat.add_sub_cancel] at hd
  simp only [smul_eq_mul, nsmul_eq_mul] at hd
  simp only [map_add, map_mul, aeval_C, map_sub, map_div₀, map_natCast] at h1 ⊢
  push_cast at hd ⊢
  linear_combination P * hd + h1 - ((m' : L) + 1) * aeval S.x (derivative S.p) * hw

/-- **The Hermite step identity.** -/
lemma super_herm_eq (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (j m : ℕ) (B G B' : C[X])
    (hB : B = S.p * derivative G + Polynomial.C ((j : C) / S.n - m) * (G * derivative S.p) +
      S.p * B') :
    aeval S.x B * S.y ^ j / aeval S.x S.p ^ (m + 1) =
      (aeval S.x G * S.y ^ j / aeval S.x S.p ^ m)′ + aeval S.x B' * S.y ^ j / aeval S.x S.p ^ m := by
  have h1 := S.deriv_poly_y_div_pow hC hx G j m
  have hp0 := S.p_ne_zero
  rw [eq_div_of_mul_eq (pow_ne_zero _ hp0) h1, hB, map_add, map_mul]
  field_simp
  ring

end SuperData

end Differential

namespace Differential

open CPoly

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma herm_r_ne_zero {F : Type*} [Field F] [CharZero F] (j n k : ℕ) (hj0 : 0 < j) (hjn : j < n) :
    ((j : F) / n - (k + 1 : ℕ)) ≠ 0 := by
  have hn0 : (n : F) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [div_sub' hn0, div_ne_zero_iff]
  refine ⟨?_, hn0⟩
  intro h
  have : ((j : ℤ) : F) = (((k + 1) * n : ℕ) : ℤ) := by push_cast at h ⊢; linear_combination h
  have h2 := Int.cast_injective this
  have : (j : ℤ) < ((k + 1) * n : ℕ) := by push_cast; nlinarith
  omega

/-- **Deciding `∫ B(x) yʲ / p(x)ᵏ dx`** (`k ≥ 1`), i.e. `∫ B(x) p(x)^{j/n − k} dx`. -/
theorem super_decides_pow (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ι : F →+* Kc) (n : ℕ) (p : CPoly F)
    (hp : Squarefree (toPoly p)) (hpd : 0 < (toPoly p).natDegree)
    (hcop : Nat.Coprime n (toPoly p).natDegree)
    (hy : y ^ n = aeval x ((toPoly p).map ι)) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯)
    (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (k : ℕ) (hk : 1 ≤ k) (B : CPoly F) :
    HasElementaryIntegral (aeval x ((toPoly B).map ι) * y ^ j / aeval x ((toPoly p).map ι) ^ k) ↔
      isZero (supRed ((j : F) / n) p (supHerm j n p B k)).2 = true := by
  have hn : 0 < n := by omega
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hsqK : Squarefree ((toPoly p).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hp).map).squarefree
  have hpK : 0 < ((toPoly p).map ι).natDegree := by
    rw [natDegree_map_eq_of_injective ι.injective]; exact hpd
  let SE : SuperData Kc E := ⟨x, y, n, (toPoly p).map ι, htrK, hn, hsqK, hpK, hy,
    Nat.cast_ne_zero.mpr hn.ne'⟩
  induction k, hk using Nat.le_induction generalizing B with
  | base =>
    rw [pow_one]
    exact super_decides hC hCall x y hx ι n p hp hpd hcop hy hgen j hj0 hjn B
  | succ k hk ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hr := herm_r_ne_zero (F := F) j n k' hj0 hjn
    have hspec := supHermStep_spec _ hr p B hp
    set G := toPoly (supHermStep ((j : F) / n - (k' + 1 : ℕ)) p B).1
    set B' := supHermStep ((j : F) / n - (k' + 1 : ℕ)) p B |>.2
    have hBK : (toPoly B).map ι = SE.p * derivative (G.map ι) +
        Polynomial.C ((j : Kc) / SE.n - (k' + 1 : ℕ)) * (G.map ι * derivative SE.p) +
        SE.p * (toPoly B').map ι := by
      rw [hspec]
      simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map, Polynomial.map_C]
      rw [show ι ((j : F) / n - (k' + 1 : ℕ)) = (j : Kc) / SE.n - (k' + 1 : ℕ) by simp [SE],
        show SE.p = (toPoly p).map ι from rfl, derivative_map]
    have heqn := SE.super_herm_eq hC hx j (k' + 1) _ (G.map ι) ((toPoly B').map ι) hBK
    change aeval x ((toPoly B).map ι) * y ^ j / aeval x ((toPoly p).map ι) ^ (k' + 1 + 1) =
      (aeval x (G.map ι) * y ^ j / aeval x ((toPoly p).map ι) ^ (k' + 1))′ +
        aeval x ((toPoly B').map ι) * y ^ j / aeval x ((toPoly p).map ι) ^ (k' + 1) at heqn
    rw [heqn]
    exact (EllAlgo.hasElementaryIntegral_deriv_add_iff' _ _).trans (ih B')

end Differential
