import RischTragerBronstein.Mixed.ExHGlobal

/-!
# Exact doubling of the weighted height on points of everywhere non-singular reduction

For `x = a/e` in lowest terms let `sH n x = max (deg a) (deg e + 2n)` (`n = nInf A B`).
**`sH_double`**: if `P = (x, y)` (`y ≠ 0`) on `y² = x³ + A x + B` over `K(X)` has non-singular
reduction at every irreducible polynomial and at infinity, then `sH n (x(2P)) = 4 · sH n (x(P))`.

Indeed `x(2P) = Φ / (4 e F)` with `F = a³ + A a e² + B e³`, `Φ = a⁴ − 2A a²e² − 8B a e³ + A²e⁴`;
a common irreducible factor of `Φ` and `e F` would make `P` singular there
(`Φ = G² − 8 a F`, `G = 3a² + A e²`), and a simultaneous drop of the weighted degrees of `Φ` and
`e F` would make `P` singular at infinity.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

section Deg

variable {K : Type*} [Field K] {p q : K[X]} {k l : ℕ}

lemma nd_add (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ l) : (p + q).natDegree ≤ max k l :=
  (natDegree_add_le p q).trans (max_le_max hp hq)

lemma nd_sub (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ l) : (p - q).natDegree ≤ max k l :=
  (natDegree_sub_le p q).trans (max_le_max hp hq)

lemma nd_neg (hp : p.natDegree ≤ k) : (-p).natDegree ≤ k := by rwa [natDegree_neg]

lemma nd_mul (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ l) : (p * q).natDegree ≤ k + l :=
  natDegree_mul_le.trans (add_le_add hp hq)

lemma nd_pow (hp : p.natDegree ≤ k) (m : ℕ) : (p ^ m).natDegree ≤ m * k :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left m hp)

lemma nd_ofNat (m : ℕ) [m.AtLeastTwo] : (OfNat.ofNat m : K[X]).natDegree ≤ 0 :=
  (natDegree_ofNat m).le

end Deg

/-- `dgs [h₁, …]`: synthesize `natDegree e ≤ ?k` for a polynomial expression `e`. -/
syntax "dgs" "[" term,* "]" : tactic

macro_rules
  | `(tactic| dgs [$hs,*]) => `(tactic| first
      | with_reducible dvl [$hs,*]
      | with_reducible exact nd_ofNat _
      | (with_reducible apply nd_add; dgs [$hs,*]; dgs [$hs,*])
      | (with_reducible apply nd_sub; dgs [$hs,*]; dgs [$hs,*])
      | (with_reducible apply nd_neg; dgs [$hs,*])
      | (with_reducible apply nd_mul; dgs [$hs,*]; dgs [$hs,*])
      | (with_reducible apply nd_pow; dgs [$hs,*]))

/-- `dgt [h₁, …]`: prove `natDegree e ≤ k`. -/
syntax "dgt" "[" term,* "]" : tactic

macro_rules
  | `(tactic| dgt [$hs,*]) => `(tactic| (apply le_trans; dgs [$hs,*]; omega))

/-- `dglt [h₁, …]`: prove `natDegree e < k`. -/
syntax "dglt" "[" term,* "]" : tactic

macro_rules
  | `(tactic| dglt [$hs,*]) => `(tactic| (apply lt_of_le_of_lt; dgs [$hs,*]; omega))

variable {K : Type*} [Field K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- The weighted height `max (deg num) (deg den + 2n)`. -/
noncomputable def sH (n : ℕ) (x : RatFunc K) : ℕ :=
  max x.num.natDegree (x.denom.natDegree + 2 * n)

/-- The weighted height of a fraction in lowest terms. -/
theorem sH_div_coprime (n : ℕ) (u v : K[X]) (hv : v ≠ 0) (hc : IsCoprime u v) :
    sH n (ι u / ι v) = max u.natDegree (v.natDegree + 2 * n) := by
  set x := ι u / ι v with hx
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hv' : ι v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv
  have hd' : ι (RatFunc.denom x) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (RatFunc.denom_ne_zero x)
  have key : RatFunc.num x * v = u * RatFunc.denom x := by
    apply hinj
    have h1 := RatFunc.num_div_denom x
    rw [map_mul, map_mul]
    have h2 : ι (RatFunc.num x) = x * ι (RatFunc.denom x) := (div_eq_iff hd').mp h1
    rw [h2, hx]; field_simp
  have hnd := RatFunc.isCoprime_num_denom x
  by_cases hu : u = 0
  · have hx0 : x = 0 := by rw [hx, hu, map_zero, zero_div]
    have hvu : IsUnit v := by
      rw [hu] at hc; exact isCoprime_zero_left.mp hc
    rw [hx0]
    simp [sH, hu, natDegree_eq_zero_of_isUnit hvu]
  have hnum0 : RatFunc.num x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at key
    exact mul_ne_zero hu (RatFunc.denom_ne_zero x) key.symm
  have d1 : u ∣ RatFunc.num x := hc.dvd_of_dvd_mul_right ⟨_, key⟩
  have d2 : RatFunc.num x ∣ u := hnd.dvd_of_dvd_mul_right ⟨v, key.symm⟩
  have d3 : v ∣ RatFunc.denom x :=
    hc.symm.dvd_of_dvd_mul_right ⟨RatFunc.num x, by linear_combination -key⟩
  have d4 : RatFunc.denom x ∣ v := hnd.symm.dvd_of_dvd_mul_right ⟨u, by linear_combination key⟩
  have e1 : (RatFunc.num x).natDegree = u.natDegree :=
    le_antisymm (natDegree_le_of_dvd d2 hu) (natDegree_le_of_dvd d1 hnum0)
  have e2 : (RatFunc.denom x).natDegree = v.natDegree :=
    le_antisymm (natDegree_le_of_dvd d4 hv) (natDegree_le_of_dvd d3 (RatFunc.denom_ne_zero x))
  unfold sH; rw [e1, e2]

variable [CharZero K]

/-- **Exact doubling.** -/
theorem sH_double (A B : K[X]) {x y : RatFunc K}
    (h : (shortF (ι A) (ι B)).toAffine.Nonsingular x y) (hy : y ≠ 0)
    (hfin : ∀ (p : K[X]) (hp : Irreducible p), ¬Sing (Vp p hp) (ι A) (ι B) (.some x y h))
    (hinf : ¬Sing Vinf (uInf (nInf A B) ^ 4 * ι A) (uInf (nInf A B) ^ 6 * ι B)
      (scaleHom (ι A) (ι B) (uInf (nInf A B)) (uInf_ne _) (.some x y h))) :
    ∃ (x2 y2 : RatFunc K) (h2 : (shortF (ι A) (ι B)).toAffine.Nonsingular x2 y2),
      Point.some x y h + Point.some x y h = Point.some x2 y2 h2 ∧
        sH (nInf A B) x2 = 4 * sH (nInf A B) x := by
  have hdA : A.natDegree ≤ 4 * nInf A B := degA_le A B
  have hdB : B.natDegree ≤ 6 * nInf A B := degB_le A B
  generalize nInf A B = n at hinf hdA hdB ⊢
  have heq := ((ns_short (ι A) (ι B) x y).mp h).1
  have hyn : y ≠ (shortF (ι A) (ι B)).toAffine.negY x y := by
    rw [negY_shortF]
    intro h0
    apply hy
    have h2 : (2 : RatFunc K) * y = 0 := by linear_combination h0
    simpa using h2
  refine ⟨_, _, _, Point.add_self_of_Y_ne hyn, ?_⟩
  have hf0 : x ^ 3 + ι A * x + ι B ≠ 0 := by rw [← heq]; exact pow_ne_zero 2 hy
  have key : (shortF (ι A) (ι B)).toAffine.addX x x ((shortF (ι A) (ι B)).toAffine.slope x x y y) =
      ((3 * x ^ 2 + ι A) ^ 2 - 8 * x * (x ^ 3 + ι A * x + ι B)) /
        (4 * (x ^ 3 + ι A * x + ι B)) := by
    rw [addX_short, slope_of_Y_ne rfl hyn, negY_shortF]
    simp only [shortF]
    rw [← heq, show y - -y = 2 * y by ring]
    field_simp
    ring
  rw [key]
  -- numerator and denominator of `x`
  obtain ⟨a, ha⟩ : ∃ a : K[X], a = x.num := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : K[X], e = x.denom := ⟨_, rfl⟩
  have he0 : e ≠ 0 := he ▸ RatFunc.denom_ne_zero x
  have hc : IsCoprime a e := by rw [ha, he]; exact RatFunc.isCoprime_num_denom x
  have hx : x = ι a / ι e := by rw [ha, he]; exact (RatFunc.num_div_denom x).symm
  have hιe : ι e ≠ 0 := ι_ne he0
  have hsx : sH n x = max a.natDegree (e.natDegree + 2 * n) := by rw [ha, he]; rfl
  obtain ⟨F, hFdef⟩ : ∃ F : K[X], F = a ^ 3 + A * a * e ^ 2 + B * e ^ 3 := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : K[X], G = 3 * a ^ 2 + A * e ^ 2 := ⟨_, rfl⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : K[X],
      Φ = a ^ 4 - 2 * A * a ^ 2 * e ^ 2 - 8 * B * a * e ^ 3 + A ^ 2 * e ^ 4 := ⟨_, rfl⟩
  have hF : ι F = (ι e) ^ 3 * (x ^ 3 + ι A * x + ι B) := by
    rw [hx, hFdef]; simp only [map_add, map_mul, map_pow]; field_simp
  have hG : ι G = (ι e) ^ 2 * (3 * x ^ 2 + ι A) := by
    rw [hx, hGdef]; simp only [map_add, map_mul, map_pow, map_ofNat]; field_simp
  have hΦ : ι Φ = (ι e) ^ 4 * ((3 * x ^ 2 + ι A) ^ 2 - 8 * x * (x ^ 3 + ι A * x + ι B)) := by
    rw [hx, hΦdef]; simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]; field_simp; ring
  have hF0 : F ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hF
    exact mul_ne_zero (pow_ne_zero 3 hιe) hf0 hF.symm
  have h4 : (4 : K[X]) ≠ 0 := by norm_num
  have h4eF : 4 * e * F ≠ 0 := mul_ne_zero (mul_ne_zero h4 he0) hF0
  have key2 : ((3 * x ^ 2 + ι A) ^ 2 - 8 * x * (x ^ 3 + ι A * x + ι B)) /
      (4 * (x ^ 3 + ι A * x + ι B)) = ι Φ / ι (4 * e * F) := by
    rw [map_mul, map_mul, map_ofNat, hF, hΦ]
    field_simp
  have hGsq : G ^ 2 = Φ + 8 * a * F := by rw [hGdef, hΦdef, hFdef]; ring
  -- coprimality from non-singular reduction at the finite places
  have hcop : IsCoprime Φ (4 * e * F) := by
    refine isCoprime_of_irreducible_dvd (fun h0 ↦ h4eF h0.2) (fun p hp hpΦ hpd ↦ ?_)
    have hpr := hp.prime
    by_cases hpe : p ∣ e
    · have hpa4 : p ∣ a ^ 4 := by
        have e1 : a ^ 4 = Φ - e * (-(2 * A * a ^ 2 * e) - 8 * B * a * e ^ 2 + A ^ 2 * e ^ 3) := by
          rw [hΦdef]; ring
        rw [e1]
        exact dvd_sub hpΦ (hpe.mul_right _)
      exact hp.not_isUnit (hc.isUnit_of_dvd' (hpr.dvd_of_dvd_pow hpa4) hpe)
    · have hpF : p ∣ F := by
        rcases hpr.dvd_or_dvd hpd with h4e | hpF
        · rcases hpr.dvd_or_dvd h4e with hp4 | hpe'
          · exfalso
            have hu4 : IsUnit (4 : K[X]) := by
              rw [show (4 : K[X]) = C (4 : K) from (map_ofNat C 4).symm]
              exact isUnit_C.mpr (IsUnit.mk0 _ (by norm_num))
            exact hp.not_isUnit (isUnit_of_dvd_unit hp4 hu4)
          · exact absurd hpe' hpe
        · exact hpF
      apply hfin p hp
      have ue : Ex (Vp p hp) 0 (ι e) := ex_vp_unit hp he0 hpe
      have hpG : p ∣ G := by
        refine hpr.dvd_of_dvd_pow (n := 2) ?_
        rw [hGsq]
        exact dvd_add hpΦ (hpF.mul_left _)
      refine ⟨?_, ?_, ?_⟩
      · rw [hx]; exact ((dv_vp_int hp a).div_ex ue).mono (by norm_num)
      · have e2 : x ^ 3 + ι A * x + ι B = ι F / (ι e) ^ 3 := by rw [hF]; field_simp
        rw [e2]
        exact ((dv_vp_one hp hpF).div_ex (ue.pow 3)).mono (by norm_num)
      · have e2 : 3 * x ^ 2 + ι A = ι G / (ι e) ^ 2 := by rw [hG]; field_simp
        rw [e2]
        exact ((dv_vp_one hp hpG).div_ex (ue.pow 2)).mono (by norm_num)
  rw [key2, sH_div_coprime n Φ (4 * e * F) h4eF hcop, hsx]
  -- degrees
  have hdeg : (4 * e * F).natDegree = e.natDegree + F.natDegree := by
    rw [show (4 : K[X]) = C (4 : K) from (map_ofNat C 4).symm, mul_assoc,
      natDegree_C_mul (by norm_num), natDegree_mul he0 hF0]
  have la := le_refl a.natDegree
  have le' := le_refl e.natDegree
  have hΦle : Φ.natDegree ≤ 4 * max a.natDegree (e.natDegree + 2 * n) := by
    rw [hΦdef]; dgt [la, le', hdA, hdB]
  have hFle : F.natDegree ≤ 4 * max a.natDegree (e.natDegree + 2 * n) - (e.natDegree + 2 * n) := by
    rw [hFdef]; dgt [la, le', hdA, hdB]
  by_cases hcase : e.natDegree + 2 * n < a.natDegree
  · have hΦeq : Φ.natDegree = 4 * a.natDegree := by
      have e1 : Φ = a ^ 4 + (-(2 * A * a ^ 2 * e ^ 2) - 8 * B * a * e ^ 3 + A ^ 2 * e ^ 4) := by
        rw [hΦdef]; ring
      have ha0 : a ≠ 0 := by
        intro h0; rw [h0, natDegree_zero] at hcase; omega
      rw [e1, natDegree_add_eq_left_of_natDegree_lt, natDegree_pow]
      rw [natDegree_pow]
      dglt [la, le', hdA, hdB]
    omega
  · by_contra hne
    apply hinf
    rw [scaleHom_apply]
    have hFlt : F.natDegree < 3 * e.natDegree + 6 * n := by omega
    have hΦlt : Φ.natDegree < 4 * (e.natDegree + 2 * n) := by omega
    refine ⟨?_, ?_, ?_⟩
    · by_cases ha0 : a = 0
      · rw [hx, ha0]; simp [dv_zero]
      · have hE : Ex Vinf (2 * (n : ℤ) - a.natDegree + e.natDegree)
            (uInf n ^ 2 * (ι a / ι e)) := by
          exq [ex_uInf (K := K) n, ex_vinf_poly ha0, ex_vinf_poly he0]
        rw [hx]
        exact hE.dv.mono (by omega)
    · have e2 : (uInf n ^ 2 * x) ^ 3 + uInf n ^ 4 * ι A * (uInf n ^ 2 * x) + uInf n ^ 6 * ι B =
          uInf n ^ 6 * (ι F / (ι e) ^ 3) := by
        rw [hF]; field_simp
      have hE : Ex Vinf (6 * (n : ℤ) - F.natDegree + 3 * e.natDegree)
          (uInf n ^ 6 * (ι F / (ι e) ^ 3)) := by
        exq [ex_uInf (K := K) n, ex_vinf_poly hF0, ex_vinf_poly he0]
      rw [e2]
      exact hE.dv.mono (by omega)
    · have e2 : 3 * (uInf n ^ 2 * x) ^ 2 + uInf n ^ 4 * ι A =
          uInf n ^ 4 * (ι G / (ι e) ^ 2) := by
        rw [hG]; field_simp
      rw [e2]
      by_cases hG0 : G = 0
      · rw [hG0]; simp [dv_zero]
      · have hGd : 2 * G.natDegree ≤ max Φ.natDegree (0 + a.natDegree + F.natDegree) := by
          rw [← natDegree_pow, hGsq]
          exact nd_add (le_refl _) (nd_mul (nd_mul (nd_ofNat 8) (le_refl _)) (le_refl _))
        have hE : Ex Vinf (4 * (n : ℤ) - G.natDegree + 2 * e.natDegree)
            (uInf n ^ 4 * (ι G / (ι e) ^ 2)) := by
          exq [ex_uInf (K := K) n, ex_vinf_poly hG0, ex_vinf_poly he0]
        exact hE.dv.mono (by omega)

end ExH
