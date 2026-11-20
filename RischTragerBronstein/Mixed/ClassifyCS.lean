import RischTragerBronstein.Mixed.PolyRoot
import RischTragerBronstein.Mixed.ConstScaleDescent

/-!
# Detecting curves constant up to scaling

`csData Ac Bc`: a candidate scaling `v` (by `rootP`: a cube root of `B` then a square root if
`A = 0`, two square roots of `A` if `B = 0`, a square root of `B / A` otherwise), verified exactly:
`A = a v⁴`, `B = b v⁶`. **`csData_sound`**: an answer gives `ConstScale` with `u = v`.
**`csData_complete`**: `ConstScale` (with `4A³ + 27B² ≠ 0`) makes `csData` answer — roots in `K[X]` are
unique up to constants (`const_of_pow_ratio`).
-/

open Polynomial CPoly

namespace FFHeight

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- `n`-th roots of the same polynomial agree up to a constant. -/
theorem const_of_pow_ratio (n : ℕ) (hn : 0 < n) (x y : K[X]) (hy : y ≠ 0) (k : K)
    (h : x ^ n = C k * y ^ n) : ∃ e : K, x = C e * y := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hy' : ι y ≠ 0 := (map_ne_zero_iff _ hinj).mpr hy
  obtain ⟨q, hq⟩ := poly_of_pow n hn (ι x / ι y) (C k) (by
    rw [div_pow, ← map_pow, ← map_pow, h, map_mul, map_pow]; field_simp)
  have hqn : q ^ n = C k := by
    apply hinj; rw [map_pow, ← hq, div_pow, ← map_pow, ← map_pow, h, map_mul, map_pow]; field_simp
  have hdeg : q.natDegree = 0 := by
    have := congrArg natDegree hqn
    rw [natDegree_pow, natDegree_C] at this
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | h0
    · exact h0
    · exfalso; have : 0 < n * q.natDegree := Nat.mul_pos hn h0; omega
  refine ⟨q.coeff 0, hinj ?_⟩
  rw [map_mul, ← eq_C_of_natDegree_eq_zero hdeg, ← hq]; field_simp

/-- **The candidate scaling.** -/
def csCand (Ac Bc : CPoly K) : Option (CPoly K) :=
  let fuel := Ac.length + Bc.length + 1
  if isZero Ac then (rootP 3 fuel Bc).bind (fun w ↦ rootP 2 fuel w)
  else if isZero Bc then (rootP 2 fuel Ac).bind (fun w ↦ rootP 2 fuel w)
  else rootP 2 fuel (div Bc Ac)

/-- **The verified scaling data** `(v, a, b)` with `A = a v⁴`, `B = b v⁶`. -/
def csData (Ac Bc : CPoly K) : Option (CPoly K × K × K) :=
  (csCand Ac Bc).bind fun v ↦
    let a := lead (trim Ac) / lead (trim (powCR v 4))
    let b := lead (trim Bc) / lead (trim (powCR v 6))
    if !isZero v && isZero (sub Ac (smul a (powCR v 4))) && isZero (sub Bc (smul b (powCR v 6)))
    then some (v, a, b) else none

theorem csData_sound {Ac Bc : CPoly K} {v : CPoly K} {a b : K} (h : csData Ac Bc = some (v, a, b)) :
    toPoly v ≠ 0 ∧ toPoly Ac = C a * toPoly v ^ 4 ∧ toPoly Bc = C b * toPoly v ^ 6 := by
  unfold csData at h
  obtain ⟨v', -, hv'⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at hv'
  split_ifs at hv' with hc
  cases hv'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨fun h0 ↦ by rw [← isZero_iff] at h0; rw [h0] at h1; exact absurd h1 (by decide), ?_, ?_⟩
  · have := (isZero_iff _).mp h2
    simp only [toPoly_sub, toPoly_smul, toPoly_powCR] at this
    linear_combination this
  · have := (isZero_iff _).mp h3
    simp only [toPoly_sub, toPoly_smul, toPoly_powCR] at this
    linear_combination this

/-- The verification passes on any genuine scaling `v`. -/
theorem csData_of_cand {Ac Bc v : CPoly K} (hc : csCand Ac Bc = some v) (hv : toPoly v ≠ 0)
    (a b : K) (hA : toPoly Ac = C a * toPoly v ^ 4) (hB : toPoly Bc = C b * toPoly v ^ 6) :
    (csData Ac Bc).isSome := by
  unfold csData
  rw [hc]
  simp only [Option.bind_some]
  have hl4 : lead (trim (powCR v 4)) = (toPoly v).leadingCoeff ^ 4 := by
    rw [RFC.lead_trim_eq, toPoly_powCR, leadingCoeff_pow]
  have hl6 : lead (trim (powCR v 6)) = (toPoly v).leadingCoeff ^ 6 := by
    rw [RFC.lead_trim_eq, toPoly_powCR, leadingCoeff_pow]
  have hlv : (toPoly v).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hv
  have ha : lead (trim Ac) / lead (trim (powCR v 4)) = a := by
    rw [hl4, RFC.lead_trim_eq, hA, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow]
    field_simp
  have hb : lead (trim Bc) / lead (trim (powCR v 6)) = b := by
    rw [hl6, RFC.lead_trim_eq, hB, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow]
    field_simp
  rw [ha, hb]
  have e1 : isZero v = false := by
    rw [Bool.eq_false_iff]; intro h; exact hv ((isZero_iff _).mp h)
  have e2 : isZero (sub Ac (smul a (powCR v 4))) = true := by
    rw [isZero_iff, toPoly_sub, toPoly_smul, toPoly_powCR, hA, sub_self]
  have e3 : isZero (sub Bc (smul b (powCR v 6))) = true := by
    rw [isZero_iff, toPoly_sub, toPoly_smul, toPoly_powCR, hB, sub_self]
  simp [e1, e2, e3]

theorem ιC (a : K) : ι (C a) = κ a := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a, Polynomial.algebraMap_eq]

/-- `rootP` on `c wⁿ` returns a constant multiple of `w`. -/
theorem rootP_spec (n : ℕ) (hn : 0 < n) (f : ℕ) (D : CPoly K) (c : K) (w : K[X]) (hc : c ≠ 0)
    (hw : w ≠ 0) (hD : toPoly D = C c * w ^ n) (hf : (toPoly D).natDegree < f) :
    ∃ v e, rootP n f D = some v ∧ e ≠ 0 ∧ toPoly v = C e * w := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (rootP_complete n hn f D c w hc hw hD hf)
  have hD0 : toPoly D ≠ 0 := by rw [hD]; exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ hw)
  obtain ⟨c', hc', hD'⟩ := rootP_sound n f D v hv hD0
  have hvn : toPoly v ^ n = C (c / c') * w ^ n := by
    have h2 : C c' * toPoly v ^ n = C c * w ^ n := by rw [← hD', hD]
    have : C (c / c') * w ^ n = C c'⁻¹ * (C c * w ^ n) := by
      rw [div_eq_mul_inv, C_mul]; ring
    rw [this, ← h2, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc', C_1, one_mul]
  obtain ⟨e, he⟩ := const_of_pow_ratio n hn _ w hw _ hvn
  refine ⟨v, e, hv, fun he0 ↦ ?_, he⟩
  rw [he0, C_0, zero_mul] at he
  rw [he, zero_pow hn.ne', mul_zero] at hD'; exact hD0 hD'

/-- **Completeness**: a curve constant up to scaling is detected. -/
theorem csData_complete {Ac Bc : CPoly K}
    (hdisc : 4 * toPoly Ac ^ 3 + 27 * toPoly Bc ^ 2 ≠ 0) (hcs : ConstScale (toPoly Ac) (toPoly Bc)) :
    (csData Ac Bc).isSome := by
  obtain ⟨u, a, b, hu, hA, hB⟩ := hcs
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  -- `u` is a polynomial
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push_neg at h
    apply hdisc; apply hinj
    simp only [map_add, map_mul, map_pow, hA, hB, h.1, h.2, map_zero]; simp
  obtain ⟨q, hq⟩ : ∃ q : K[X], u = ι q := by
    rcases hab with ha | hb
    · refine poly_of_pow 12 (by norm_num) u ((C a⁻¹ * toPoly Ac) ^ 3) ?_
      have h1 : κ a⁻¹ * κ a = 1 := by rw [← map_mul, inv_mul_cancel₀ ha, map_one]
      rw [map_pow, map_mul, hA, ιC]
      calc u ^ 12 = (u ^ 4 * (κ a⁻¹ * κ a)) ^ 3 := by rw [h1]; ring
        _ = _ := by ring
    · refine poly_of_pow 12 (by norm_num) u ((C b⁻¹ * toPoly Bc) ^ 2) ?_
      have h1 : κ b⁻¹ * κ b = 1 := by rw [← map_mul, inv_mul_cancel₀ hb, map_one]
      rw [map_pow, map_mul, hB, ιC]
      calc u ^ 12 = (u ^ 6 * (κ b⁻¹ * κ b)) ^ 2 := by rw [h1]; ring
        _ = _ := by ring
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact hu hq
  have hA' : toPoly Ac = C a * q ^ 4 := hinj (by rw [hA, hq, map_mul, ιC, map_pow]; ring)
  have hB' : toPoly Bc = C b * q ^ 6 := hinj (by rw [hB, hq, map_mul, ιC, map_pow]; ring)
  have hfA : (toPoly Ac).natDegree < Ac.length + Bc.length + 1 := by
    have := natDegree_toPoly_le_length Ac; omega
  have hfB : (toPoly Bc).natDegree < Ac.length + Bc.length + 1 := by
    have := natDegree_toPoly_le_length Bc; omega
  -- final step: from a candidate `v = C e * q`
  have finish : ∀ v : CPoly K, ∀ e : K, csCand Ac Bc = some v → e ≠ 0 → toPoly v = C e * q →
      (csData Ac Bc).isSome := by
    intro v e hc he hv
    have hqv : q = C e⁻¹ * toPoly v := by
      rw [hv, ← mul_assoc, ← C_mul, inv_mul_cancel₀ he, C_1, one_mul]
    refine csData_of_cand hc (by rw [hv]; exact mul_ne_zero (C_ne_zero.mpr he) hq0)
      (a * e⁻¹ ^ 4) (b * e⁻¹ ^ 6) ?_ ?_
    · rw [hA', hqv, C_mul, C_pow]; ring
    · rw [hB', hqv, C_mul, C_pow]; ring
  by_cases hAz : isZero Ac = true
  · have hA0 : toPoly Ac = 0 := (isZero_iff _).mp hAz
    have ha0 : a = 0 := by
      rw [hA0] at hA'
      rcases mul_eq_zero.mp hA'.symm with h | h
      · exact C_eq_zero.mp h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hq0
    have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha0)
    obtain ⟨w, e1, hw, he1, hwq⟩ := rootP_spec 3 (by norm_num) _ Bc b (q ^ 2) hb
      (pow_ne_zero _ hq0) (by rw [hB']; ring) hfB
    have hwdeg : (toPoly w).natDegree < Ac.length + Bc.length + 1 := by
      have h1 : (toPoly w).natDegree = 2 * q.natDegree := by
        rw [hwq, natDegree_C_mul he1, natDegree_pow]
      have h2 : (toPoly Bc).natDegree = 6 * q.natDegree := by
        rw [hB', natDegree_C_mul hb, natDegree_pow]
      omega
    obtain ⟨v, e2, hv, he2, hvq⟩ := rootP_spec 2 (by norm_num) _ w e1 q he1 hq0 hwq hwdeg
    refine finish v e2 ?_ he2 hvq
    simp only [csCand, hAz, ite_true, hw, Option.bind_some, hv]
  by_cases hBz : isZero Bc = true
  · have hB0 : toPoly Bc = 0 := (isZero_iff _).mp hBz
    have hb0 : b = 0 := by
      rw [hB0] at hB'
      rcases mul_eq_zero.mp hB'.symm with h | h
      · exact C_eq_zero.mp h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hq0
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb0)
    obtain ⟨w, e1, hw, he1, hwq⟩ := rootP_spec 2 (by norm_num) _ Ac a (q ^ 2) ha
      (pow_ne_zero _ hq0) (by rw [hA']; ring) hfA
    have hwdeg : (toPoly w).natDegree < Ac.length + Bc.length + 1 := by
      have h1 : (toPoly w).natDegree = 2 * q.natDegree := by
        rw [hwq, natDegree_C_mul he1, natDegree_pow]
      have h2 : (toPoly Ac).natDegree = 4 * q.natDegree := by
        rw [hA', natDegree_C_mul ha, natDegree_pow]
      omega
    obtain ⟨v, e2, hv, he2, hvq⟩ := rootP_spec 2 (by norm_num) _ w e1 q he1 hq0 hwq hwdeg
    refine finish v e2 ?_ he2 hvq
    simp only [csCand, hAz, hBz, ite_true, ite_false, hw, Option.bind_some, hv, Bool.false_eq_true]
  · have hA0 : toPoly Ac ≠ 0 := fun h ↦ hAz ((isZero_iff _).mpr h)
    have ha : a ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at hA'; exact hA0 hA'
    have hb : b ≠ 0 := by
      rintro rfl; rw [C_0, zero_mul] at hB'; exact hBz ((isZero_iff _).mpr hB')
    have hCb : C b = C a * C (b / a) := by rw [← C_mul, mul_div_cancel₀ _ ha]
    have hdvd : toPoly Ac ∣ toPoly Bc := ⟨C (b / a) * q ^ 2, by
      rw [hA', hB', hCb]; ring⟩
    have hdiv : toPoly (div Bc Ac) = C (b / a) * q ^ 2 := by
      have hs := divMod_spec Bc Ac
      rw [divMod_exact Bc Ac hA0 hdvd, add_zero] at hs
      have : toPoly (div Bc Ac) * toPoly Ac = C (b / a) * q ^ 2 * toPoly Ac := by
        change toPoly (divMod Bc Ac).1 * _ = _
        rw [← hs, hA', hB', hCb]; ring
      exact mul_right_cancel₀ hA0 this
    have hdeg : (toPoly (div Bc Ac)).natDegree < Ac.length + Bc.length + 1 := by
      have h1 : (toPoly (div Bc Ac)).natDegree = 2 * q.natDegree := by
        rw [hdiv, natDegree_C_mul (div_ne_zero hb ha), natDegree_pow]
      have h2 : (toPoly Bc).natDegree = 6 * q.natDegree := by
        rw [hB', natDegree_C_mul hb, natDegree_pow]
      omega
    obtain ⟨v, e2, hv, he2, hvq⟩ := rootP_spec 2 (by norm_num) _ _ (b / a) q (div_ne_zero hb ha)
      hq0 hdiv hdeg
    refine finish v e2 ?_ he2 hvq
    simp only [csCand, hAz, hBz, ite_false, hv, Bool.false_eq_true]

end FFHeight
