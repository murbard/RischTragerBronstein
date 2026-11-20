import RischTragerBronstein.Mixed.KRNorm

/-!
# Radicals over an exponential level: the column

* `twist_dlog`: from `s₁ W + s₂ (Xⁿ − Â) = g` (`g ≠ 0`) and `W_d s₁ ≡ D (mod Xⁿ − Â)`,
  `W_d = ∑ (Wᵢ′ + i r Wᵢ) Xⁱ`, at any `Y` with `Yⁿ = Â`, `Y′ = r Y`: `W(Y) ≠ 0` and
  `W(Y)′/W(Y) = D(Y)/g`;
* `twist_sum`: `∑_k ζ^{(n−j)k} D(ζᵏ Y) = n Dⱼ Yʲ` for `deg D < n`.
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Differential

variable {F : Type*} [Field F] [Differential F]

lemma coeff_implicit (W : F[X]) (r : F) (i : ℕ) :
    (mapCoeffs W + Polynomial.C r * X * derivative W).coeff i = (W.coeff i)′ + i * r * W.coeff i := by
  rw [coeff_add, coeff_mapCoeffs, mul_assoc, coeff_C_mul]
  rcases i with _ | i
  · simp
  · rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- **The logarithmic derivative on the twist.** -/
theorem twist_dlog (n : ℕ) (W Wd s1 s2 Q D : F[X]) (Ah r g Y : F) (hY : Y ^ n = Ah)
    (hYd : Y′ = r * Y) (hWd : ∀ i, Wd.coeff i = (W.coeff i)′ + i * r * W.coeff i)
    (hbez : s1 * W + s2 * (X ^ n - Polynomial.C Ah) = Polynomial.C g) (hg : g ≠ 0)
    (hdiv : Wd * s1 = Q * (X ^ n - Polynomial.C Ah) + D) :
    W.eval Y ≠ 0 ∧ logDeriv (W.eval Y) = D.eval Y / g := by
  have hM : (X ^ n - Polynomial.C Ah).eval Y = 0 := by simp [hY]
  have hb := congrArg (eval Y) hbez
  simp only [eval_add, eval_mul, hM, mul_zero, add_zero, eval_C] at hb
  have hW0 : W.eval Y ≠ 0 := fun h ↦ hg (by rw [← hb, h, mul_zero])
  have hWd' : Wd = mapCoeffs W + Polynomial.C r * X * derivative W :=
    Polynomial.ext fun i ↦ by rw [hWd, coeff_implicit]
  have hder : (W.eval Y)′ = Wd.eval Y := by
    have := deriv_aeval_eq Y W
    simp only [coe_aeval_eq_eval] at this
    rw [this, hWd', eval_add, eval_mul, eval_mul, eval_C, eval_X, hYd]
    ring
  have hd := congrArg (eval Y) hdiv
  simp only [eval_add, eval_mul, hM, mul_zero, zero_add] at hd
  refine ⟨hW0, ?_⟩
  rw [logDeriv, hder]
  field_simp
  rw [← hd, ← hb]
  ring

/-- **The `yʲ`-projection of the conjugates.** -/
theorem twist_sum (n : ℕ) (ζ : F) (hζ : IsPrimitiveRoot ζ n) (D : F[X])
    (hD : ∀ i, n ≤ i → D.coeff i = 0) (j : ℕ) (hj : j < n) (Y : F) :
    ∑ k ∈ Finset.range n, ζ ^ ((n - j) * k) * D.eval (ζ ^ k * Y) = n * D.coeff j * Y ^ j := by
  classical
  have hev : ∀ y : F, D.eval y = ∑ i ∈ Finset.range n, D.coeff i * y ^ i := fun y ↦ by
    rw [eval_eq_sum_range' (n := n)]
    by_contra h
    push Not at h
    by_cases hD0 : D = 0
    · subst hD0; simp at h; omega
    exact (leadingCoeff_ne_zero.mpr hD0) (hD _ h)
  simp_rw [hev, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hi : ∀ i ∈ Finset.range n, ∑ k ∈ Finset.range n, ζ ^ ((n - j) * k) * (D.coeff i * (ζ ^ k * Y) ^ i) =
      D.coeff i * Y ^ i * ∑ k ∈ Finset.range n, (ζ ^ (n - j + i)) ^ k := fun i _ ↦ by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, add_mul, pow_add, mul_comm i k]
    ring
  rw [Finset.sum_congr rfl hi, Finset.sum_eq_single j]
  · rw [geom_root n (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]), if_pos]
    · ring
    · rw [Nat.sub_add_cancel hj.le, hζ.pow_eq_one]
  · intro i hi hij
    rw [geom_root n (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]), if_neg,
      mul_zero]
    intro h1
    have hdvd := (hζ.pow_eq_one_iff_dvd _).mp h1
    have hi' := Finset.mem_range.mp hi
    apply hij
    have h2 : n - j + i < 2 * n := by omega
    rcases hdvd with ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  · intro h; exact absurd (Finset.mem_range.mpr hj) h

end Differential

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

lemma toPoly_xnSubC {R : Type*} [Field R] [DecidableEq R] (a : R) (n : ℕ) (hn : 0 < n) :
    toPoly ((-a) :: (List.replicate (n - 1) 0 ++ [1])) = X ^ n - Polynomial.C a := by
  rw [toPoly_cons, toPoly_append]
  have : toPoly (List.replicate (n - 1) (0 : R)) = 0 := by
    induction (n - 1) with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, ih]
  rw [this, List.length_replicate]
  simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_one, zero_add, mul_one]
  rw [← pow_succ', Nat.sub_add_cancel hn, map_neg]
  ring

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

lemma sem_unTr (m : ℕ) (h : T.Tr m) (y : KF Fc m) : (T.MP m h).sem (unTr Fc m y) = T.psiF m h y :=
  Subtype.ext (by rw [T.sem_MP m h, T.ev_unTr m h]; rfl)

lemma sem_normC' (m : ℕ) (hm : T.Tr m) (q : LC m) :
    (T.MP m hm).sem (normC Fc m q) = (T.MP m hm).sem q :=
  Subtype.ext (by rw [T.sem_MP m hm, T.sem_MP m hm, T.ev_normC m hm])

/-- **The column code**: the extended gcd identity over `F_{m+1}` and the value of the column. -/
theorem krCol_spec (m n : ℕ) (hn : 0 < n) (hTr : T.Tr (m + 1)) (Ah : GPoly (LC m)) (z : LC m)
    (j : ℕ) (W : BPoly (KF Fc m)) (col : LC (m + 1)) (h : krCol Fc ks m n Ah z j W = some col) :
    ∃ Wd s1 s2 Q D : (T.F (m + 1))[X], ∃ g : T.F (m + 1), g ≠ 0 ∧
      (∀ i, Wd.coeff i = ((toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem
          (pcP Fc ks m (c.map (unTr Fc m))))).coeff i)′ +
        i * (((1 / n : ℚ) : T.F (m + 1)) * (((T.MP (m + 1) hTr).sem (pcP Fc ks m Ah))′ *
          ((T.MP (m + 1) hTr).sem (pcP Fc ks m Ah))⁻¹)) *
          (toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem (pcP Fc ks m (c.map (unTr Fc m))))).coeff i) ∧
      s1 * toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem (pcP Fc ks m (c.map (unTr Fc m)))) +
        s2 * (X ^ n - Polynomial.C ((T.MP (m + 1) hTr).sem (pcP Fc ks m Ah))) = Polynomial.C g ∧
      Wd * s1 = Q * (X ^ n - Polynomial.C ((T.MP (m + 1) hTr).sem (pcP Fc ks m Ah))) + D ∧
      (∀ i, n ≤ i → D.coeff i = 0) ∧
      (T.MP (m + 1) hTr).sem col =
        (T.MP (m + 1) hTr).sem (pcP Fc ks m [powC (MO Fc ks m) z j]) * D.coeff j / g := by
  unfold krCol at h
  simp only at h
  split_ifs at h with hgl
  obtain rfl := (Option.some.inj h).symm
  set Wl : (T.F (m + 1))[X] := toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem (pcP Fc ks m (c.map (unTr Fc m))))
    with hWldef
  set Av := (T.MP (m + 1) hTr).sem (pcP Fc ks m Ah) with hAv
  set r : T.F (m + 1) := ((1 / n : ℚ) : T.F (m + 1)) * (Av′ * Av⁻¹) with hr
  set tr := trC Fc (m + 1)
  set φ := T.psiF (m + 1) hTr with hφdef
  have hφ : ∀ q, φ (tr q) = (T.MP (m + 1) hTr).sem q := fun q ↦ T.psiF_trC (m + 1) hTr q
  set Wc : List (LC (m + 1)) := W.map fun c ↦ pcP Fc ks m (c.map (unTr Fc m)) with hWc
  set Ahc := pcP Fc ks m Ah with hAhc
  set rc := (MO Fc ks (m + 1)).mul (mcst Fc ks (m + 1) (1 / n)) ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).deriv Ahc) ((MO Fc ks (m + 1)).inv Ahc)) with hrc
  set Wdc : List (LC (m + 1)) := (List.range Wc.length).map fun i ↦
    (MO Fc ks (m + 1)).add ((MO Fc ks (m + 1)).deriv (Wc.getD i (MO Fc ks (m + 1)).zero)) ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).mul (mcst Fc ks (m + 1) i) rc) (Wc.getD i (MO Fc ks (m + 1)).zero))
    with hWdc
  set WK : CPoly (KF Fc (m + 1)) := Wc.map tr with hWK
  set WdK : CPoly (KF Fc (m + 1)) := Wdc.map tr with hWdK
  set MK : CPoly (KF Fc (m + 1)) := (-(tr Ahc)) :: (List.replicate (n - 1) 0 ++ [1]) with hMK
  set e := CPoly.egcd WK MK with he
  set g := CPoly.trim e.1 with hg
  set D := (CPoly.divMod (CPoly.mul WdK e.2.1) MK).2 with hD
  -- the polynomials
  have hMKp : toPoly MK = X ^ n - Polynomial.C (tr Ahc) := toPoly_xnSubC _ n hn
  have hMK0 : toPoly MK ≠ 0 := by
    rw [hMKp]; exact X_pow_sub_C_ne_zero hn _
  have hMKm : (toPoly MK).map φ = X ^ n - Polynomial.C Av := by
    rw [hMKp, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, hφ]
  have hWl : (toPoly WK).map φ = Wl := by
    rw [← toPoly_map', hWK, List.map_map]
    simp only [Wl, hWc, List.map_map]
    congr 1
    exact List.map_congr_left fun c _ ↦ hφ _
  have hsemWc : ∀ i, Wl.coeff i = (T.MP (m + 1) hTr).sem (Wc.getD i (MO Fc ks (m + 1)).zero) := fun i ↦ by
    rw [← hWl, coeff_map, coeff_toPoly, hWK]
    by_cases hi : i < Wc.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, hφ,
        List.getD_eq_getElem _ _ hi]
    · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega),
        map_zero, (T.MP (m + 1) hTr).sem_zero]
  -- the gcd
  have hg1 : g = [g.getD 0 1] := by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hgl
    rw [ha]; rfl
  have hg0 : g.getD 0 1 ≠ 0 := by
    have hgl' : (CPoly.trim e.1).length = 1 := hgl
    have hne : CPoly.trim e.1 ≠ [] := fun h0 ↦ by rw [h0] at hgl'; simp at hgl'
    have h1 := getLast_trim_ne_zero e.1 hne
    rw [List.getLast_eq_getElem] at h1
    simp only [hgl'] at h1
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h1
  have hge : toPoly e.1 = Polynomial.C (g.getD 0 1) := by
    rw [← toPoly_trim, ← hg, hg1]; simp
  have hbez := CPoly.egcd_spec WK MK
  rw [← he, hge] at hbez
  have hdm := CPoly.divMod_spec (CPoly.mul WdK e.2.1) MK
  rw [← hD, CPoly.toPoly_mul] at hdm
  have hdeg := CPoly.divMod_degree_lt (CPoly.mul WdK e.2.1) MK hMK0
  rw [← hD] at hdeg
  have hMKdeg : (toPoly MK).degree = n := by
    rw [hMKp, degree_X_pow_sub_C hn]
  refine ⟨(toPoly WdK).map φ, (toPoly e.2.1).map φ, (toPoly e.2.2).map φ,
    (toPoly (CPoly.divMod (CPoly.mul WdK e.2.1) MK).1).map φ, (toPoly D).map φ, φ (g.getD 0 1),
    (map_ne_zero φ).mpr hg0, fun i ↦ ?_, ?_, ?_, fun i hi ↦ ?_, ?_⟩
  · rw [coeff_map, coeff_toPoly, hWdK, hsemWc]
    by_cases hi : i < Wc.length
    · simp only [hWdc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some]
      rw [hφ, (T.MP (m + 1) hTr).sem_add, (T.MP (m + 1) hTr).sem_deriv, (T.MP (m + 1) hTr).sem_mul, (T.MP (m + 1) hTr).sem_mul,
        T.sem_mcst, hrc, (T.MP (m + 1) hTr).sem_mul, T.sem_mcst, (T.MP (m + 1) hTr).sem_mul, (T.MP (m + 1) hTr).sem_deriv, (T.MP (m + 1) hTr).sem_inv]
      rw [hr, hAv]
      push_cast
      ring
    · rw [List.getD_eq_default _ _ (by simp [hWdc]; omega), List.getD_eq_default _ _ (by omega),
        (T.MP (m + 1) hTr).sem_zero]
      simp
  · rw [← hWl, ← hMKm, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hbez,
      Polynomial.map_C]
  · rw [← hMKm, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, ← hdm]
  · rw [coeff_map, coeff_eq_zero_of_degree_lt, map_zero]
    calc (toPoly D).degree < n := hMKdeg ▸ hdeg
      _ ≤ i := by exact_mod_cast hi
  · rw [T.sem_normC' (m + 1) hTr, (T.MP (m + 1) hTr).sem_mul, T.sem_unTr (m + 1) hTr, map_mul, map_inv₀, coeff_map,
      coeff_toPoly]
    ring

end MTower

end Curves.MT
