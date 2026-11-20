import RischTragerBronstein.Mixed.KFSquare
import RischTragerBronstein.Computable.EuclidDegree
import RischTragerBronstein.Computable.Hermite

/-!
# Rational non-squares over base curves of degree two

For `y² + c₁ y + c₀` with discriminant `D = c₁² − 4c₀` squarefree and non-constant in `ℚ[x]`: if a
rational `q` were a square in `K₀ = ℚ(x)[y]/(y² + c₁y + c₀)`, writing the root as `a + b y` gives
either `q = a²` (so `q` is a square in `ℚ`) or `4q = b²D`, impossible for `D` squarefree non-constant
(`sqfree_not_sq`). So rational non-squares stay non-squares in every `Kₘ` (`not_isSquare_KF_quad`),
and `quadOK` recognizes these bases.
-/

open Polynomial CPoly

namespace Curves.MT

/-- **`q D` is not a square** for `D` squarefree non-constant and `q ≠ 0`. -/
theorem sqfree_not_sq (P : ℚ[X]) (hP : Squarefree P) (hdeg : 0 < P.natDegree) (q : ℚ) (hq : q ≠ 0)
    (s : RatFunc ℚ) (h : s ^ 2 = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C q * P)) : False := by
  set u := s.num
  set v := s.denom
  have hv : v ≠ 0 := RatFunc.denom_ne_zero s
  have hc : IsCoprime u v := RatFunc.isCoprime_num_denom s
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hιv : algebraMap ℚ[X] (RatFunc ℚ) v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv
  have hs : s = algebraMap ℚ[X] (RatFunc ℚ) u / algebraMap ℚ[X] (RatFunc ℚ) v :=
    (RatFunc.num_div_denom s).symm
  have huv : u ^ 2 = Polynomial.C q * P * v ^ 2 := by
    apply hinj
    rw [hs, div_pow, div_eq_iff (pow_ne_zero 2 hιv)] at h
    rw [map_pow, map_mul, map_pow, h]
  have hCu : IsUnit (Polynomial.C q) := Polynomial.isUnit_C.mpr (Ne.isUnit hq)
  have hPu : P ∣ u := (hP.dvd_pow_iff_dvd two_ne_zero).mp ⟨Polynomial.C q * v ^ 2, by
    rw [huv]; ring⟩
  obtain ⟨w, hw⟩ := hPu
  have hP0 : P ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hdeg; omega
  have h2 : P * w ^ 2 = Polynomial.C q * v ^ 2 := by
    apply mul_left_cancel₀ hP0
    rw [← mul_assoc, ← mul_assoc, mul_comm P (Polynomial.C q), ← huv, hw]; ring
  have hPv : P ∣ v := by
    refine (hP.dvd_pow_iff_dvd two_ne_zero).mp ?_
    have : P ∣ Polynomial.C q * v ^ 2 := ⟨w ^ 2, h2.symm⟩
    exact (hCu.dvd_mul_left).mp this
  have hPunit : IsUnit P := hc.isUnit_of_dvd' ⟨w, hw⟩ hPv
  exact absurd (natDegree_eq_zero_of_isUnit hPunit) (by omega)

variable (c0 c1 : CPoly ℚ)

/-- The discriminant `c₁² − 4c₀`. -/
def discQ : CPoly ℚ := CPoly.add (CPoly.mul c1 c1) (CPoly.smul (-4) c0)

lemma toPoly_discQ : toPoly (discQ c0 c1) = toPoly c1 ^ 2 - 4 * toPoly c0 := by
  simp only [discQ, CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_smul]
  rw [show (Polynomial.C (-4 : ℚ)) = -4 by rw [map_neg, map_ofNat]]; ring

/-- **Rational non-squares stay non-squares in every `Kₘ`** (base `y² + c₁y + c₀`, discriminant
squarefree and non-constant). -/
theorem not_isSquare_KF_quad [hF : Fact (Irreducible (toPoly (fKc [c0, c1, [1]])))]
    (hsq : Squarefree (toPoly (discQ c0 c1))) (hdeg : 0 < (toPoly (discQ c0 c1)).natDegree)
    (q : ℚ) (hq : ¬ IsSquare q) (m : ℕ) : ¬ IsSquare ((q : ℚ) : KF [c0, c1, [1]] m) := by
  intro h
  obtain ⟨r, hr⟩ := sq_KF_descend [c0, c1, [1]] q m h
  set K := RFC.RatFuncC ℚ
  set f := toPoly (fKc [c0, c1, [1]])
  set e0 : K := RFC.mk c0 [1]
  set e1 : K := RFC.mk c1 [1]
  have h1 : (RFC.mk [1] [1] : K) = 1 :=
    RFC.toRF_injective (by rw [RFC.toRF_const, map_one, RFC.toRF_one])
  have hf : f = X ^ 2 + Polynomial.C e1 * X + Polynomial.C e0 := by
    simp only [f, fKc, toPoly, List.map_cons, List.map_nil, h1, e0, e1]
    simp; ring
  have hfm : f.Monic := by rw [hf]; monicity!
  have hf0 : f ≠ 0 := hfm.ne_zero
  have hfd : f.natDegree = 2 := by rw [hf]; compute_degree!
  -- the root as `a + b y`
  set ρ := NFK.toARHom (fKc [c0, c1, [1]]) r
  have hρ : ρ * ρ = ((q : ℚ) : AdjoinRoot f) := by rw [← map_mul, ← hr, map_ratCast]
  obtain ⟨g, hgρ⟩ := AdjoinRoot.mk_surjective ρ
  rw [← hgρ] at hρ
  set g' := g %ₘ f
  have hgg : AdjoinRoot.mk f g = AdjoinRoot.mk f g' := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨g /ₘ f, by have := modByMonic_add_div g f; linear_combination -this⟩
  have hg'd : g'.natDegree < 2 := by
    rw [← hfd]; exact natDegree_modByMonic_lt g hfm (fun h1 ↦ by rw [h1] at hfd; simp at hfd)
  set a := g'.coeff 0
  set b := g'.coeff 1
  have hg'e : g' = Polynomial.C a + Polynomial.C b * X := by
    ext i
    rcases i with _ | _ | i
    · simp [a]
    · simp [b]
    · simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X]
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  rw [hgg, hg'e, ← map_mul, show ((q : ℚ) : AdjoinRoot f) = AdjoinRoot.mk f (Polynomial.C (q : K)) by
    rw [AdjoinRoot.mk_C, map_ratCast]] at hρ
  rw [AdjoinRoot.mk_eq_mk] at hρ
  -- the remainder vanishes
  have hrem : (Polynomial.C a + Polynomial.C b * X) * (Polynomial.C a + Polynomial.C b * X) -
      Polynomial.C (q : K) - Polynomial.C (b * b) * f =
      Polynomial.C (a * a - q - b * b * e0) + Polynomial.C (2 * a * b - b * b * e1) * X := by
    rw [hf]; simp only [map_sub, map_mul, map_ofNat]; ring
  have hdvd : f ∣ Polynomial.C (a * a - q - b * b * e0) + Polynomial.C (2 * a * b - b * b * e1) * X := by
    rw [← hrem]; exact dvd_sub hρ (dvd_mul_left f _)
  have hzero := eq_zero_of_dvd_of_natDegree_lt hdvd (by
    rw [hfd]
    calc _ ≤ 1 := by rw [add_comm]; exact natDegree_linear_le
      _ < 2 := by norm_num)
  have hA : a * a - q - b * b * e0 = 0 := by
    have := congrArg (fun P ↦ P.coeff 0) hzero; simpa using this
  have hB : 2 * a * b - b * b * e1 = 0 := by
    have := congrArg (fun P ↦ P.coeff 1) hzero; simpa using this
  by_cases hb : b = 0
  · apply hq
    refine sq_const_RFC (K := ℚ) a q ?_
    rw [hb] at hA; rw [sq]; linear_combination hA
  · -- `4q = b² D`
    have ha : a = b * e1 / 2 := by
      field_simp
      have : b * (2 * a - b * e1) = 0 := by linear_combination hB
      have := (mul_eq_zero.mp this).resolve_left hb
      linear_combination this
    have hqD : (b * (e1 * e1 - 4 * e0) / 2) ^ 2 = (q : K) * (e1 * e1 - 4 * e0) := by
      rw [ha] at hA
      linear_combination (e1 * e1 - 4 * e0) * hA
    have hq0 : q ≠ 0 := fun h0 ↦ hq ⟨0, by rw [h0]; ring⟩
    have hm : ∀ c : CPoly ℚ, RFC.toRFHom (K := ℚ) (RFC.mk c [1] : K) =
        algebraMap ℚ[X] (RatFunc ℚ) (toPoly c) := by
      intro c
      show RFC.toRF (K := ℚ) (RFC.mk c [1]) = _
      rw [RFC.toRF_mk]; simp [CPoly.toPoly]
    have hD : RFC.toRFHom (e1 * e1 - 4 * e0) =
        algebraMap ℚ[X] (RatFunc ℚ) (toPoly (discQ c0 c1)) := by
      rw [map_sub, map_mul, map_mul, map_ofNat, hm c1, hm c0, toPoly_discQ, map_sub, map_pow,
        map_mul, map_ofNat]; ring
    refine sqfree_not_sq (toPoly (discQ c0 c1)) hsq hdeg q hq0
      (RFC.toRFHom (b * (e1 * e1 - 4 * e0) / 2)) ?_
    have := congrArg RFC.toRFHom hqD
    rw [map_pow, map_mul, map_ratCast, hD] at this
    rw [this, map_mul, RatFunc.algebraMap_C, eq_ratCast RatFunc.C q]

/-- Base curves `y² + c₁y + c₀` with squarefree non-constant discriminant. -/
def quadOK (Fc : Sup.BPoly ℚ) : Bool :=
  Fc.length == 3 && Fc.getD 2 [] == [1] &&
    CPoly.squarefreeCheck (discQ (Fc.getD 0 []) (Fc.getD 1 [])) &&
    decide (2 ≤ (CPoly.trim (discQ (Fc.getD 0 []) (Fc.getD 1 []))).length)

theorem not_isSquare_KF_quadOK (Fc : Sup.BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]
    (h : quadOK Fc = true) (q : ℚ) (hq : ¬ IsSquare q) (m : ℕ) : ¬ IsSquare ((q : ℚ) : KF Fc m) := by
  simp only [quadOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, h2⟩, hs⟩, hd⟩ := h
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, Fc = [c0, c1, [1]] := by
    match Fc, hl, h2 with
    | [a, b, c], _, h2 => exact ⟨a, b, by simp at h2; rw [h2]⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hs hd
  have hsq := CPoly.squarefreeCheck_sound hs
  have htr : CPoly.trim (discQ c0 c1) ≠ [] := fun h0 ↦ by rw [h0] at hd; simp at hd
  have hlen := CPoly.length_trim htr
  exact not_isSquare_KF_quad c0 c1 hsq (by omega) q hq m

end Curves.MT
