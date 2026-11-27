import RischTragerBronstein.Mixed.ExHStar

/-!
# Multiplicative reduction

`a`, `b` units and `N = v(Δ) ≥ 1`. With the centre `e = −3b/(2a)` (`f′(e) = Δ/(4a²)`,
`f(e) = −bΔ/(8a³)`, both of valuation `N`), every singular `x` is congruent to `e`
(`mult_cent`). Singular points are classified by `i = v(x − e)` when `2i < N` (any two with the
same `i` are related: `4·3e·z₁z₂` dominates the sum numerator), and one top class `2i ≥ N` (related:
`−4·f(e)·3e` dominates the product numerator). Hence `index_mult`: every point has a multiple
`m • P`, `0 < m ≤ 2N + 4`, of non-singular reduction.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {V : LVal K} {a b : K}

lemma cen_e {α β : ℤ} (hae : Ex V α a) (hbe : Ex V β b) :
    Ex V (β - α) (-(3 * b) / (2 * a)) := by
  exq [hae, hbe]

lemma cen_eps {α N : ℤ} (hae : Ex V α a) (hN : Ex V N (4 * a ^ 3 + 27 * b ^ 2)) :
    Ex V (N - 2 * α) (3 * (-(3 * b) / (2 * a)) ^ 2 + a) := by
  have h : 3 * (-(3 * b) / (2 * a)) ^ 2 + a = (4 * a ^ 3 + 27 * b ^ 2) / (4 * a ^ 2) := by
    have := hae.ne
    field_simp
    ring
  rw [h]
  exq [hN, hae]

lemma cen_del {α β N : ℤ} (hae : Ex V α a) (hbe : Ex V β b)
    (hN : Ex V N (4 * a ^ 3 + 27 * b ^ 2)) :
    Ex V (β + N - 3 * α) ((-(3 * b) / (2 * a)) ^ 3 + a * (-(3 * b) / (2 * a)) + b) := by
  have h : (-(3 * b) / (2 * a)) ^ 3 + a * (-(3 * b) / (2 * a)) + b =
      -(b * (4 * a ^ 3 + 27 * b ^ 2)) / (8 * a ^ 3) := by
    have := hae.ne
    field_simp
    ring
  rw [h]
  exq [hN, hae, hbe]

omit [CharZero K] in
lemma dv_mul_of_sq {N : ℤ} {u w : K} (t1 : Dv V N (u ^ 2)) (t2 : Dv V N (w ^ 2)) :
    Dv V N (u * w) := by
  apply dv_of_sq (k := N)
  rw [show (u * w) ^ 2 = u ^ 2 * w ^ 2 by ring]
  exact (t1.mul t2).mono (by omega)

section Centre

variable (e : K) {N : ℤ}

/-- Singular points are congruent to the centre. -/
lemma mult_cent (ha0 : Dv V 0 a) (he : Ex V 0 e) (hε : Ex V N (3 * e ^ 2 + a))
    (hδ : Ex V N (e ^ 3 + a * e + b)) (hb0 : Ex V 0 b) (hN1 : 1 ≤ N) {x : K} (hx : Dv V 0 x)
    (hf : Dv V 1 (x ^ 3 + a * x + b)) (hg : Dv V 1 (3 * x ^ 2 + a)) : Dv V 1 (x - e) := by
  have hprod : Dv V (1 + 1 - 1) ((x - e) * (x + e)) := by
    have h : Dv V (1 + 0) ((x - e) * (x + e) * 3) := by
      rw [show (x - e) * (x + e) * 3 = (3 * x ^ 2 + a) - (3 * e ^ 2 + a) by ring]
      exact (hg.sub (hε.dv.mono (by omega))).mono (by norm_num)
    exact (dv_of_mul_ex h (ex_ofNat V 3)).mono (by norm_num)
  rcases dv_or_of_mul hprod with h | h
  · exact h
  · exfalso
    have h0 : Ex V 0 (x ^ 3 + a * x + b) := by
      rw [show x ^ 3 + a * x + b = 2 * b + ((x + e) * (x ^ 2 - x * e + e ^ 2 + a) -
        (e ^ 3 + a * e + b)) by ring]
      domt [hb0] [h, hx, he.dv, ha0, hδ.dv]
    exact h0.not_dv (by norm_num) hf

/-- Same `i = v(x − e)`, `2i < N`: the sum criterion. -/
lemma mult_critS (he : Ex V 0 e) (hε : Ex V N (3 * e ^ 2 + a))
    (hδ : Ex V N (e ^ 3 + a * e + b)) {i : ℤ} (hi1 : 1 ≤ i) (hiN : 2 * i < N) {x1 x2 : K}
    (h1 : Ex V i (x1 - e)) (h2 : Ex V i (x2 - e)) :
    Ex V (2 * i) (Ns a b x1 x2 - 2 * e * (x1 - x2) ^ 2) := by
  rw [show Ns a b x1 x2 - 2 * e * (x1 - x2) ^ 2 = 4 * (3 * e) * ((x1 - e) * (x2 - e)) +
    (2 * ((x1 - e) * (x2 - e)) * ((x1 - e) + (x2 - e)) +
      2 * (3 * e ^ 2 + a) * ((x1 - e) + (x2 - e)) + 4 * (e ^ 3 + a * e + b)) by unfold Ns; ring]
  domt [he, h1, h2] [h1.dv, h2.dv, hε.dv, hδ.dv]

/-- Top class `2 v(x − e) ≥ N`: the product criterion. -/
lemma mult_critP (he : Ex V 0 e) (hε : Ex V N (3 * e ^ 2 + a))
    (hδ : Ex V N (e ^ 3 + a * e + b)) (hN1 : 1 ≤ N) {x1 x2 : K} (z1 : Dv V 1 (x1 - e))
    (z2 : Dv V 1 (x2 - e)) (t1 : Dv V N ((x1 - e) ^ 2)) (t2 : Dv V N ((x2 - e) ^ 2)) :
    Ex V N (Np a b x1 x2 - e * Ns a b x1 x2 + e ^ 2 * (x1 - x2) ^ 2) := by
  have t12 : Dv V N ((x1 - e) * (x2 - e)) := dv_mul_of_sq t1 t2
  rw [show Np a b x1 x2 - e * Ns a b x1 x2 + e ^ 2 * (x1 - x2) ^ 2 =
    -(4 * (e ^ 3 + a * e + b) * (3 * e)) + (((x1 - e) * (x2 - e) - (3 * e ^ 2 + a)) ^ 2 -
      4 * (e ^ 3 + a * e + b) * ((x1 - e) + (x2 - e))) by unfold Np Ns; ring]
  domt [hδ, he] [t12, z1, z2, hε.dv, hδ.dv]

end Centre

/-- The class of a singular point for multiplicative reduction. -/
noncomputable def cMult (V : LVal K) (a b e : K) (N : ℤ) (P : (shortF a b).toAffine.Point) : ℕ :=
  if xOf P - e ≠ 0 ∧ 2 * V.v (xOf P - e) < N then (V.v (xOf P - e)).toNat else N.toNat

/-- **Multiplicative reduction**: every point has a multiple `m ≤ 2N + 4` of non-singular
reduction. -/
theorem index_mult (ha : Dv V 0 a) (hb : Dv V 0 b) (hae : Ex V 0 a) (hbe : Ex V 0 b) {N : ℤ}
    (hN : Ex V N (4 * a ^ 3 + 27 * b ^ 2)) (hN1 : 1 ≤ N) (P : (shortF a b).toAffine.Point) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2 * N.toNat + 4 ∧ m • P ∈ E0 V a b ha hb := by
  obtain ⟨e, hedef⟩ : ∃ e : K, e = -(3 * b) / (2 * a) := ⟨_, rfl⟩
  have he : Ex V 0 e := by rw [hedef]; exact (cen_e hae hbe).congr (by omega)
  have hε : Ex V N (3 * e ^ 2 + a) := by rw [hedef]; exact (cen_eps hae hN).congr (by omega)
  have hδ : Ex V N (e ^ 3 + a * e + b) := by
    rw [hedef]; exact (cen_del hae hbe hN).congr (by omega)
  have hcent : ∀ {t u : K} (ht : (shortF a b).toAffine.Nonsingular t u),
      Sing V a b (.some t u ht) → Dv V 1 (t - e) := fun ht hs ↦
    mult_cent e ha he hε hδ hbe hN1 hs.1 hs.2.1 hs.2.2
  have hcentP : ∀ P : (shortF a b).toAffine.Point, Sing V a b P → Dv V 1 (xOf P - e) := by
    intro P hP
    obtain ⟨x, y, h, rfl, -⟩ := sing_coords hP
    exact hcent h hP
  have relg : ∀ P Q : (shortF a b).toAffine.Point, Sing V a b P → Sing V a b Q →
      (xOf P ≠ xOf Q → ∃ k j : ℤ, j ≤ k ∧ Ex V k ((xOf P - xOf Q) ^ 2) ∧
        (Ex V j (Ns a b (xOf P) (xOf Q) - 2 * e * (xOf P - xOf Q) ^ 2) ∨
          Ex V j (Np a b (xOf P) (xOf Q) - e * Ns a b (xOf P) (xOf Q) +
            e ^ 2 * (xOf P - xOf Q) ^ 2))) →
      (Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb) := by
    intro P Q hP hQ h
    obtain ⟨x1, y1, h1, rfl, -⟩ := sing_coords hP
    obtain ⟨x2, y2, h2, rfl, -⟩ := sing_coords hQ
    exact rel_of_crit ha hb e hcent h1 h2 h
  have key := index_of_pair ha hb (N.toNat + 1) (cMult V a b e N)
    (fun P ↦ by unfold cMult; split_ifs with h <;> omega) (fun P Q hP hQ hc ↦ ?_) P
  · obtain ⟨m, h1, h2, h3⟩ := key
    exact ⟨m, h1, by omega, h3⟩
  have z1 := hcentP P hP
  have z2 := hcentP Q hQ
  refine relg P Q hP hQ fun hx ↦ ?_
  by_cases c1 : xOf P - e ≠ 0 ∧ 2 * V.v (xOf P - e) < N
  · -- the class `i = v(x − e)`, `2i < N`
    have c12 := c1.2
    have hv1 : 1 ≤ V.v (xOf P - e) := dv_of_ne z1 c1.1
    have c2 : xOf Q - e ≠ 0 ∧ 2 * V.v (xOf Q - e) < N := by
      by_contra c2
      unfold cMult at hc
      rw [if_pos c1, if_neg c2] at hc
      omega
    have c22 := c2.2
    have hv2 := dv_of_ne z2 c2.1
    have hveq : V.v (xOf Q - e) = V.v (xOf P - e) := by
      unfold cMult at hc
      rw [if_pos c1, if_pos c2] at hc
      omega
    have E1 : Ex V (V.v (xOf P - e)) (xOf P - e) := ⟨c1.1, rfl⟩
    have E2 : Ex V (V.v (xOf P - e)) (xOf Q - e) := ⟨c2.1, hveq⟩
    obtain ⟨k, hk, hd⟩ := ex_d (V := V) hx (m := V.v (xOf P - e)) (by
      rw [show xOf P - xOf Q = (xOf P - e) - (xOf Q - e) by ring]
      exact E1.dv.sub E2.dv)
    exact ⟨k, 2 * V.v (xOf P - e), by omega, hd, Or.inl (mult_critS e he hε hδ hv1 c12 E1 E2)⟩
  · -- the top class
    have c2 : ¬(xOf Q - e ≠ 0 ∧ 2 * V.v (xOf Q - e) < N) := by
      intro c2
      have c22 := c2.2
      unfold cMult at hc
      rw [if_neg c1, if_pos c2] at hc
      have := dv_of_ne z2 c2.1
      omega
    have top : ∀ z : K, ¬(z ≠ 0 ∧ 2 * V.v z < N) → Dv V N (z ^ 2) := by
      intro z hz
      by_cases h0 : z = 0
      · simp [h0, dv_zero]
      · right
        rw [V.pow _ h0]
        push_cast
        have : ¬(2 * V.v z < N) := fun h ↦ hz ⟨h0, h⟩
        omega
    have t1 := top _ c1
    have t2 := top _ c2
    have hne : (xOf P - xOf Q) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
    have hdN : Dv V N ((xOf P - xOf Q) ^ 2) := by
      have t12 : Dv V N ((xOf P - e) * (xOf Q - e)) := dv_mul_of_sq t1 t2
      rw [show (xOf P - xOf Q) ^ 2 = (xOf P - e) ^ 2 - 2 * ((xOf P - e) * (xOf Q - e)) +
        (xOf Q - e) ^ 2 by ring]
      dvt [t1, t2, t12]
    exact ⟨V.v ((xOf P - xOf Q) ^ 2), N, dv_of_ne hdN hne, ⟨hne, rfl⟩,
      Or.inr (mult_critP e he hε hδ hN1 z1 z2 t1 t2)⟩

/-- **Good reduction**: no singular points. -/
theorem no_sing_good (ha : Dv V 0 a) (hb : Dv V 0 b) (hΔ : Ex V 0 (4 * a ^ 3 + 27 * b ^ 2))
    (P : (shortF a b).toAffine.Point) : ¬Sing V a b P := by
  intro h
  obtain ⟨y, -, hx, hf, hg⟩ := sing_x h
  refine hΔ.not_dv (l := 1) (by norm_num) ?_
  rw [show 4 * a ^ 3 + 27 * b ^ 2 = 4 * a ^ 2 * (3 * xOf P ^ 2 + a) -
    3 * (3 * (xOf P ^ 3 + a * xOf P + b) - xOf P * (3 * xOf P ^ 2 + a)) *
      (2 * a * xOf P - 3 * b) by ring]
  dvt [hg, hf, hx, ha, hb]

end ExH
