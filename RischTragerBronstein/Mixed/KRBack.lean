import RischTragerBronstein.Mixed.KRCol
import RischTragerBronstein.Mixed.KRLift

/-!
# Radicals over an exponential level: the column is elementary

Over an extension containing `s = ⁿ√κ` and a primitive `n`-th root of unity `ζ` (constants), the
conjugates `Y_k = ζᵏ z θ / s` of the twist satisfy `Y_kⁿ = Â`, and the extended gcd identity of
`krCol` gives `W(Y_k)′/W(Y_k) = D(Y_k)/g` (`twist_dlog_hom`). Summing with the weights `ζ^{(n−j)k}`
(`twist_sum`): `col · θʲ = (sʲ/n) ∑_k ζ^{(n−j)k} W(Y_k)′/W(Y_k)`, elementary (`kr_col_hei`).
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Differential

variable {K1 F : Type*} [Field K1] [Differential K1] [Field F] [Differential F]

/-- `twist_dlog` through a differential ring homomorphism. -/
theorem twist_dlog_hom (φ : K1 →+* F) (hφ : ∀ x, φ x′ = (φ x)′) (n : ℕ) (W Wd s1 s2 Q D : K1[X])
    (Ah r g : K1) (hWd : ∀ i, Wd.coeff i = (W.coeff i)′ + i * r * W.coeff i)
    (hbez : s1 * W + s2 * (X ^ n - Polynomial.C Ah) = Polynomial.C g) (hg : g ≠ 0)
    (hdiv : Wd * s1 = Q * (X ^ n - Polynomial.C Ah) + D) (Y : F) (hY : Y ^ n = φ Ah)
    (hYd : Y′ = φ r * Y) :
    (W.map φ).eval Y ≠ 0 ∧ logDeriv ((W.map φ).eval Y) = (D.map φ).eval Y / φ g := by
  refine twist_dlog n (W.map φ) (Wd.map φ) (s1.map φ) (s2.map φ) (Q.map φ) (D.map φ) (φ Ah) (φ r)
    (φ g) Y hY hYd (fun i ↦ ?_) ?_ ((map_ne_zero φ).mpr hg) ?_
  · rw [coeff_map, coeff_map, hWd, map_add, map_mul, map_mul, hφ, map_natCast]
  · have := congrArg (Polynomial.map φ) hbez
    simpa [Polynomial.map_sub] using this
  · have := congrArg (Polynomial.map φ) hdiv
    simpa [Polynomial.map_sub] using this

variable [CharZero F]

lemma deriv_of_pow_eq (n : ℕ) (hn : 0 < n) (Y a : F) (hY : Y ^ n = a) (ha : a ≠ 0) :
    Y′ = ((1 / n : ℚ) : F) * (a′ * a⁻¹) * Y := by
  have hY0 : Y ≠ 0 := fun h ↦ ha (by rw [← hY, h, zero_pow hn.ne'])
  have hd := congrArg (fun w ↦ w′) hY
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
  rw [← hd, ← hY]
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  rcases n with _ | n
  · omega
  push_cast
  field_simp
  rw [pow_succ]
  ring

lemma hei_logDeriv (c u : F) (hc : c′ = 0) (hu : u ≠ 0) : HasElementaryIntegralIn (c * logDeriv u) :=
  (hasElementaryIntegralIn_logDeriv₂ c 0 u 1 hc (by simp) hu one_ne_zero).congr (by simp)

lemma hei_sum_range (N : ℕ) (f : ℕ → F) (hf : ∀ k < N, HasElementaryIntegralIn (f k)) :
    HasElementaryIntegralIn (∑ k ∈ Finset.range N, f k) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact (hasElementaryIntegralIn_deriv (0 : F)).congr (by simp)
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (ih fun k hk ↦ hf k (by omega)).add (hf N (by omega))

end Differential

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

lemma evP_single (m : ℕ) (a : LC m) : T.evP m [a] = T.ev m a := by
  show T.ev m a + T.ts m * 0 = T.ev m a
  ring

lemma evP_krAh (m n : ℕ) (h : T.Tr m) (A : GPoly (LC m)) (z : LC m) (κ : ℚ) :
    T.evP m (krAh Fc ks m n A z κ) = T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * T.evP m A := by
  rw [krAh, T.evP_mapMul m h, ← T.sem_MP m h, (T.MP m h).sem_mul, sem_powC, T.sem_mcst,
    IntermediateField.coe_mul, IntermediateField.coe_pow, T.sem_MP m h]
  push_cast
  ring

/-- **The column is elementary**: `q · col · θʲ` has an elementary integral. -/
theorem kr_col_hei (m n j : ℕ) (hn : 0 < n) (hj : j < n) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (θ : L) (hθ : θ ^ n = T.evP m A) (hA0 : T.evP m A ≠ 0) (z : LC m) (hz0 : T.ev m z ≠ 0)
    (κ : ℚ) (hκ : κ ≠ 0) (W : BPoly (KF Fc m)) (col : LC (m + 1))
    (h : krCol Fc ks m n (krAh Fc ks m n A z κ) z j W = some col) (q : ℚ) :
    HasElementaryIntegralIn ((q : L) * (T.ev (m + 1) col * θ ^ j)) := by
  obtain ⟨Wd, s1, s2, Q, D, g, hg, hWd, hbez, hdiv, hD, hcol⟩ :=
    T.krCol_spec m n hn hTr _ z j W col h
  obtain ⟨E₂, _, _, _, _, -, halg, s, ζ, hsn, hs', hζ, hζ'⟩ := root_zeta_ext L n hn κ hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap L E₂).injective
  refine HasElementaryIntegralIn.of_isAlgebraic halg ?_
  set ψ := algebraMap L E₂ with hψ
  have hψd : ∀ w : L, (ψ w)′ = ψ w′ := fun w ↦ deriv_algebraMap w
  set φ : T.F (m + 1) →+* E₂ := ψ.comp (algebraMap (T.F (m + 1)) L) with hφdef
  have hφ : ∀ x, φ x′ = (φ x)′ := fun x ↦ by
    simp only [hφdef, RingHom.comp_apply, hψd]
    rfl
  have hφv : ∀ x : T.F (m + 1), φ x = ψ (x : L) := fun x ↦ rfl
  set Av := (T.MP (m + 1) hTr).sem (pcP Fc ks m (krAh Fc ks m n A z κ)) with hAv
  have hAvL : ((Av : T.F (m + 1)) : L) = T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * T.evP m A := by
    rw [hAv, T.sem_MP (m + 1) hTr]
    change T.evP m (krAh Fc ks m n A z κ) / T.evP m [(MO Fc ks m).one] = _
    rw [T.evP_krAh m n hTr.of_succ, T.evP_single, T.ev_one_code m hTr.of_succ, div_one]
  have hκL : (κ : E₂) ≠ 0 := by exact_mod_cast hκ
  have hs0 : s ≠ 0 := fun h0 ↦ hκL (by rw [← hsn, h0, zero_pow hn.ne'])
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow hn.ne'])
  set Y0 : E₂ := ψ (T.ev m z * θ) / s with hY0
  have hY0n : Y0 ^ n = φ Av := by
    rw [hφv, hAvL, hY0, div_pow, hsn, ← map_pow, mul_pow, hθ]
    simp only [map_mul, map_pow, map_ratCast]
    field_simp
    rw [Rat.cast_div, Rat.cast_one]
    field_simp
  have hAv0 : φ Av ≠ 0 := by
    rw [hφv, hAvL]
    refine (map_ne_zero ψ).mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0) ?_) hA0)
    exact_mod_cast inv_ne_zero hκ
  set r : T.F (m + 1) := ((1 / n : ℚ) : T.F (m + 1)) * (Av′ * Av⁻¹) with hr
  have hφr : φ r = ((1 / n : ℚ) : E₂) * ((φ Av)′ * (φ Av)⁻¹) := by
    rw [hr, map_mul, map_mul, map_inv₀, hφ, map_ratCast]
  have hkey : ∀ k : ℕ, ((Polynomial.map φ (toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem
      (pcP Fc ks m (c.map (unTr Fc m)))))).eval (ζ ^ k * Y0)) ≠ 0 ∧
      logDeriv ((Polynomial.map φ (toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem
        (pcP Fc ks m (c.map (unTr Fc m)))))).eval (ζ ^ k * Y0)) =
        (D.map φ).eval (ζ ^ k * Y0) / φ g := fun k ↦ by
    have hYk : (ζ ^ k * Y0) ^ n = φ Av := by
      rw [mul_pow, ← pow_mul, mul_comm k n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hY0n]
    refine twist_dlog_hom φ hφ n _ Wd s1 s2 Q D Av r g hWd hbez hg hdiv _ hYk ?_
    rw [hφr]
    exact deriv_of_pow_eq n hn _ _ hYk hAv0
  have hDn : ∀ i, n ≤ i → (D.map φ).coeff i = 0 := fun i hi ↦ by rw [coeff_map, hD i hi, map_zero]
  have hsum := twist_sum n ζ hζ (D.map φ) hDn j hj Y0
  -- the value of the column
  have hcolL : ψ (T.ev (m + 1) col * θ ^ j) = s ^ j * φ (D.coeff j) * Y0 ^ j / φ g := by
    have e1 : T.ev (m + 1) col = ((((T.MP (m + 1) hTr).sem col : T.F (m + 1))) : L) :=
      (T.sem_MP (m + 1) hTr col).symm
    rw [e1, hcol]
    have e2 : ((((T.MP (m + 1) hTr).sem (pcP Fc ks m [powC (MO Fc ks m) z j]) : T.F (m + 1))) : L) =
        T.ev m z ^ j := by
      rw [T.sem_MP (m + 1) hTr]
      change T.evP m [powC (MO Fc ks m) z j] / T.evP m [(MO Fc ks m).one] = _
      rw [T.evP_single, T.evP_single, T.ev_one_code m hTr.of_succ, div_one, ← T.sem_MP m hTr.of_succ,
        sem_powC, IntermediateField.coe_pow, T.sem_MP m hTr.of_succ]
    rw [IntermediateField.coe_div, IntermediateField.coe_mul, e2, hY0]
    simp only [map_mul, map_div₀, map_pow, ← hφv]
    field_simp
    rw [div_pow, mul_pow]
    field_simp
  have hgoal : ψ ((q : L) * (T.ev (m + 1) col * θ ^ j)) = ∑ k ∈ Finset.range n,
      ((q : E₂) * s ^ j / n * ζ ^ ((n - j) * k)) * logDeriv ((Polynomial.map φ (toPoly
        (W.map fun c ↦ (T.MP (m + 1) hTr).sem (pcP Fc ks m (c.map (unTr Fc m)))))).eval
          (ζ ^ k * Y0)) := by
    simp_rw [fun k ↦ (hkey k).2]
    rw [map_mul, hcolL, map_ratCast]
    have hnE : (n : E₂) ≠ 0 := by exact_mod_cast hn.ne'
    have hg' : φ g ≠ 0 := (map_ne_zero φ).mpr hg
    have e3 : ∑ k ∈ Finset.range n, (q : E₂) * s ^ j / n * ζ ^ ((n - j) * k) *
        ((D.map φ).eval (ζ ^ k * Y0) / φ g) = (q : E₂) * s ^ j / n / φ g *
          ∑ k ∈ Finset.range n, ζ ^ ((n - j) * k) * (D.map φ).eval (ζ ^ k * Y0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      field_simp
    rw [e3, hsum, coeff_map]
    field_simp
  rw [hgoal]
  refine hei_sum_range n _ fun k _ ↦ hei_logDeriv _ _ ?_ (hkey k).1
  have hn' : ((n : ℕ) : E₂)′ = 0 := Derivation.map_natCast _ _
  rw [Derivation.leibniz, Derivation.leibniz_pow, hζ', div_eq_mul_inv, Derivation.leibniz,
    Derivation.leibniz_inv, hn', Derivation.leibniz, Derivation.leibniz_pow, hs',
    Tower.NestP.deriv_ratCastK (K := E₂) q]
  simp
