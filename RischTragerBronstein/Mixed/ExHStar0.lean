import RischTragerBronstein.Mixed.ExHStar

/-!
# Additive reduction of types I₀* and Iₙ*

Assume `a ∈ 𝔭²`, `b ∈ 𝔭³`, not (`a ∈ 𝔭³` and `b ∈ 𝔭⁴`). Singular points fall into two classes:

* *simple* (`v(f′(x)) = 2`): among four of them two have congruent `x` (`lagrange4`) and are
  related (`simple_crit`);
* *double* (`f′(x) ∈ 𝔭³`, only for type Iₙ*): then `v(a) = 2`, `v(b) = 3`, `N = v(Δ) ≥ 7`, and with
  the centre `e = −3b/(2a)` (`v(e) = 1`, `v(f′(e)) = N − 4`, `v(f(e)) = N − 3`) the parity of
  `v(y²)` forces `x − e ∈ 𝔭ᵐ`: for `N` odd (`2m = N − 3`) any two double points are related, for
  `N` even (`2m = N − 4`) two of any three are (`dbl_triple`).

Hence `index_star0`: every point has a multiple `m • P`, `0 < m ≤ 14`, of non-singular reduction.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {V : LVal K} {a b : K}

/-- Facts forced by a double singular point. -/
lemma dbl_setup (ha2 : Dv V 2 a) (hb3 : Dv V 3 b) (hnot : ¬(Dv V 3 a ∧ Dv V 4 b))
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {x y : K} (heq : y ^ 2 = x ^ 3 + a * x + b)
    (hx : Dv V 1 x) (hg3 : Dv V 3 (3 * x ^ 2 + a)) :
    Ex V 2 a ∧ Ex V 3 b ∧ 7 ≤ V.v (4 * a ^ 3 + 27 * b ^ 2) := by
  have f4 := star_f4 ha2 hb3 heq hx
  have ha2e : Ex V 2 a := by
    refine ex_of_dv_not ha2 (fun ha3 ↦ hnot ⟨ha3, ?_⟩) (by norm_num)
    have h3 : Dv V (3 + 0) (x ^ 2 * 3) := by
      rw [show x ^ 2 * 3 = (3 * x ^ 2 + a) - a by ring]
      exact (hg3.sub ha3).mono (by norm_num)
    have hx2 : Dv V 3 (x ^ 2) := dv_of_mul_ex h3 (ex_ofNat V 3)
    have hx' : Dv V 2 x := dv_of_sq (k := 2) ((dv_sq_succ hx2 (by norm_num)).mono (by norm_num))
    rw [show b = (x ^ 3 + a * x + b) - (x ^ 3 + a * x) by ring]
    dvt [f4, hx', ha3]
  have hx2e : Ex V 2 (x ^ 2 * 3) := by
    rw [show x ^ 2 * 3 = -a + (3 * x ^ 2 + a) by ring]
    domt [ha2e] [hg3]
  have hxsq : Ex V 2 (x ^ 2) := by
    have := hx2e.div (ex_ofNat V 3)
    rw [mul_div_assoc, div_self (ex_ofNat V 3).ne, mul_one] at this
    simpa using this
  have hxe : Ex V 1 x := ex_of_sq (by simpa using hxsq)
  have h2 : Ex V 2 (-(2 * x ^ 2) + (3 * x ^ 2 + a)) := by domt [hxsq] [hg3]
  have hb3e : Ex V 3 b := by
    rw [show b = -(x * (-(2 * x ^ 2) + (3 * x ^ 2 + a))) + (x ^ 3 + a * x + b) by ring]
    domt [hxe, h2] [f4]
  have hD : Dv V 7 (4 * a ^ 3 + 27 * b ^ 2) := by
    rw [show 4 * a ^ 3 + 27 * b ^ 2 = 4 * a ^ 2 * (3 * x ^ 2 + a) -
      3 * (3 * (x ^ 3 + a * x + b) - x * (3 * x ^ 2 + a)) * (2 * a * x - 3 * b) by ring]
    dvt [hg3, f4, hx, ha2, hb3]
  exact ⟨ha2e, hb3e, dv_of_ne hD hΔ⟩

lemma dbl_e (ha2e : Ex V 2 a) (hb3e : Ex V 3 b) : Ex V 1 (-(3 * b) / (2 * a)) := by
  exq [ha2e, hb3e]

lemma dbl_eps {N : ℤ} (ha2e : Ex V 2 a) (hN : Ex V N (4 * a ^ 3 + 27 * b ^ 2)) :
    Ex V (N - 4) (3 * (-(3 * b) / (2 * a)) ^ 2 + a) := by
  have h : 3 * (-(3 * b) / (2 * a)) ^ 2 + a = (4 * a ^ 3 + 27 * b ^ 2) / (4 * a ^ 2) := by
    have := ha2e.ne
    field_simp
    ring
  rw [h]
  exq [hN, ha2e]

lemma dbl_del {N : ℤ} (ha2e : Ex V 2 a) (hb3e : Ex V 3 b)
    (hN : Ex V N (4 * a ^ 3 + 27 * b ^ 2)) :
    Ex V (N - 3) ((-(3 * b) / (2 * a)) ^ 3 + a * (-(3 * b) / (2 * a)) + b) := by
  have h : (-(3 * b) / (2 * a)) ^ 3 + a * (-(3 * b) / (2 * a)) + b =
      -(b * (4 * a ^ 3 + 27 * b ^ 2)) / (8 * a ^ 3) := by
    have := ha2e.ne
    field_simp
    ring
  rw [h]
  exq [hN, ha2e, hb3e]

section Centre

variable (e : K) {N : ℤ}

/-- A double point is congruent to the centre modulo `𝔭²`. -/
lemma dbl_z (ha2 : Dv V 2 a) (hb3 : Dv V 3 b) (he1 : Ex V 1 e)
    (hε : Ex V (N - 4) (3 * e ^ 2 + a)) (hδ : Ex V (N - 3) (e ^ 3 + a * e + b))
    (hb3e : Ex V 3 b) (hN7 : 7 ≤ N) {x y : K} (heq : y ^ 2 = x ^ 3 + a * x + b)
    (hx : Dv V 1 x) (hg3 : Dv V 3 (3 * x ^ 2 + a)) : Dv V 2 (x - e) := by
  have f4 := star_f4 ha2 hb3 heq hx
  have hprod : Dv V (2 + 2 - 1) ((x - e) * (x + e)) := by
    have h : Dv V (3 + 0) ((x - e) * (x + e) * 3) := by
      rw [show (x - e) * (x + e) * 3 = (3 * x ^ 2 + a) - (3 * e ^ 2 + a) by ring]
      exact (hg3.sub (hε.dv.mono (by omega))).mono (by norm_num)
    exact (dv_of_mul_ex h (ex_ofNat V 3)).mono (by norm_num)
  rcases dv_or_of_mul hprod with h | h
  · exact h
  · exfalso
    have h3 : Ex V 3 (x ^ 3 + a * x + b) := by
      rw [show x ^ 3 + a * x + b = 2 * b + ((x + e) * (x ^ 2 - x * e + e ^ 2 + a) -
        (e ^ 3 + a * e + b)) by ring]
      domt [hb3e] [h, hx, he1.dv, ha2, hδ.dv]
    exact h3.not_dv (by norm_num) f4

/-- Parity: `x − e ∈ 𝔭ᵐ` whenever `2m ≤ N − 3`. -/
lemma dbl_zm (he1 : Ex V 1 e) (hε : Ex V (N - 4) (3 * e ^ 2 + a))
    (hδ : Ex V (N - 3) (e ^ 3 + a * e + b)) {x y : K} (heq : y ^ 2 = x ^ 3 + a * x + b)
    (hz2 : Dv V 2 (x - e)) {m : ℤ} (hm : 2 * m ≤ N - 3) : Dv V m (x - e) := by
  rcases dv_or_ex (V := V) (x - e) m with h | ⟨i, hi, hzi⟩
  · exact h
  exfalso
  have hi2 : 2 ≤ i := by
    have := dv_of_ne hz2 hzi.1
    have := hzi.2
    omega
  have h : Ex V (1 + 2 * i) (y ^ 2) := by
    rw [heq, show x ^ 3 + a * x + b = 3 * e * (x - e) ^ 2 +
      ((x - e) ^ 3 + (3 * e ^ 2 + a) * (x - e) + (e ^ 3 + a * e + b)) by ring]
    domt [he1, hzi] [hzi.dv, hε.dv, hδ.dv]
  have := h.sq_even
  omega

/-- `N` even, `2m = N − 4`: the leading terms cancel. -/
lemma dbl_zB (he1 : Ex V 1 e) (hε : Ex V (N - 4) (3 * e ^ 2 + a))
    (hδ : Ex V (N - 3) (e ^ 3 + a * e + b)) (hN7 : 7 ≤ N) {x y : K}
    (heq : y ^ 2 = x ^ 3 + a * x + b) {m : ℤ} (hm : 2 * m = N - 4) (hzm : Dv V m (x - e)) :
    Dv V (N - 2) (3 * e * (x - e) ^ 2 + (e ^ 3 + a * e + b)) := by
  have hf : Dv V (N - 3) (x ^ 3 + a * x + b) := by
    rw [show x ^ 3 + a * x + b = 3 * e * (x - e) ^ 2 + (e ^ 3 + a * e + b) +
      ((x - e) ^ 3 + (3 * e ^ 2 + a) * (x - e)) by ring]
    dvt [he1.dv, hzm, hε.dv, hδ.dv]
  have hf' : Dv V (N - 2) (x ^ 3 + a * x + b) := by
    rw [← heq] at hf ⊢
    exact (dv_sq_succ hf (by omega)).mono (by omega)
  rw [show 3 * e * (x - e) ^ 2 + (e ^ 3 + a * e + b) = (x ^ 3 + a * x + b) -
    ((x - e) ^ 3 + (3 * e ^ 2 + a) * (x - e)) by ring]
  dvt [hf', hzm, hε.dv]

/-- `N` odd: the sum criterion. -/
lemma dbl_critA (he1 : Ex V 1 e) (hε : Ex V (N - 4) (3 * e ^ 2 + a))
    (hδ : Ex V (N - 3) (e ^ 3 + a * e + b)) (hN7 : 7 ≤ N) {x1 x2 : K} {m : ℤ}
    (hm : 2 * m = N - 3) (h1 : Dv V m (x1 - e)) (h2 : Dv V m (x2 - e)) :
    Ex V (N - 3) (Ns a b x1 x2 - 2 * e * (x1 - x2) ^ 2) := by
  rw [show Ns a b x1 x2 - 2 * e * (x1 - x2) ^ 2 = 4 * (e ^ 3 + a * e + b) +
    (2 * ((x1 - e) * (x2 - e)) * ((x1 - e) + (x2 - e)) + 4 * (3 * e) * ((x1 - e) * (x2 - e)) +
      2 * (3 * e ^ 2 + a) * ((x1 - e) + (x2 - e))) by unfold Ns; ring]
  domt [hδ] [h1, h2, he1.dv, hε.dv]

/-- `N` even: the product criterion. -/
lemma dbl_critB (he1 : Ex V 1 e) (hε : Ex V (N - 4) (3 * e ^ 2 + a))
    (hδ : Ex V (N - 3) (e ^ 3 + a * e + b)) (hN7 : 7 ≤ N) {x1 x2 : K} {m : ℤ}
    (hm : 2 * m = N - 4) (h1 : Dv V m (x1 - e)) (h2 : Dv V m (x2 - e)) :
    Ex V (N - 2) (Np a b x1 x2 - e * Ns a b x1 x2 + e ^ 2 * (x1 - x2) ^ 2) := by
  rw [show Np a b x1 x2 - e * Ns a b x1 x2 + e ^ 2 * (x1 - x2) ^ 2 =
    -(4 * (e ^ 3 + a * e + b) * (3 * e)) + (((x1 - e) * (x2 - e) - (3 * e ^ 2 + a)) ^ 2 -
      4 * (e ^ 3 + a * e + b) * ((x1 - e) + (x2 - e))) by unfold Np Ns; ring]
  domt [hδ, he1] [h1, h2, hε.dv, hδ.dv]

end Centre

/-- **Double points**: two of any three are related. -/
theorem dbl_triple (ha : Dv V 0 a) (hb : Dv V 0 b) (ha2 : Dv V 2 a) (hb3 : Dv V 3 b)
    (hnot : ¬(Dv V 3 a ∧ Dv V 4 b)) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (P1 P2 P3 : (shortF a b).toAffine.Point) (hS1 : Sing V a b P1) (hS2 : Sing V a b P2)
    (hS3 : Sing V a b P3) (hd1 : Dv V 3 (3 * xOf P1 ^ 2 + a)) (hd2 : Dv V 3 (3 * xOf P2 ^ 2 + a))
    (hd3 : Dv V 3 (3 * xOf P3 ^ 2 + a)) :
    (P2 - P1 ∈ E0 V a b ha hb ∨ P2 + P1 ∈ E0 V a b ha hb) ∨
      (P3 - P1 ∈ E0 V a b ha hb ∨ P3 + P1 ∈ E0 V a b ha hb) ∨
      (P3 - P2 ∈ E0 V a b ha hb ∨ P3 + P2 ∈ E0 V a b ha hb) := by
  have ha1 : Dv V 1 a := ha2.mono (by norm_num)
  obtain ⟨y1, heq1, -, -, hg1⟩ := sing_x hS1
  obtain ⟨y2, heq2, -, -, hg2⟩ := sing_x hS2
  obtain ⟨y3, heq3, -, -, hg3⟩ := sing_x hS3
  have hx1 := sing_x_small ha1 hg1
  have hx2 := sing_x_small ha1 hg2
  have hx3 := sing_x_small ha1 hg3
  obtain ⟨ha2e, hb3e, hN7⟩ := dbl_setup ha2 hb3 hnot hΔ heq1 hx1 hd1
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = V.v (4 * a ^ 3 + 27 * b ^ 2) := ⟨_, rfl⟩
  rw [← hNdef] at hN7
  have hN : Ex V N (4 * a ^ 3 + 27 * b ^ 2) := ⟨hΔ, hNdef.symm⟩
  obtain ⟨e, hedef⟩ : ∃ e : K, e = -(3 * b) / (2 * a) := ⟨_, rfl⟩
  have he1 : Ex V 1 e := hedef ▸ dbl_e ha2e hb3e
  have hε : Ex V (N - 4) (3 * e ^ 2 + a) := hedef ▸ dbl_eps ha2e hN
  have hδ : Ex V (N - 3) (e ^ 3 + a * e + b) := hedef ▸ dbl_del ha2e hb3e hN
  have hz1 := dbl_z e ha2 hb3 he1 hε hδ hb3e hN7 heq1 hx1 hd1
  have hz2 := dbl_z e ha2 hb3 he1 hε hδ hb3e hN7 heq2 hx2 hd2
  have hz3 := dbl_z e ha2 hb3 he1 hε hδ hb3e hN7 heq3 hx3 hd3
  have pair : ∀ (P Q : (shortF a b).toAffine.Point), Sing V a b P → Sing V a b Q →
      ∀ j m : ℤ, j ≤ 2 * m → Dv V m (xOf P - xOf Q) →
      (Ex V j (Ns a b (xOf P) (xOf Q) - 2 * e * (xOf P - xOf Q) ^ 2) ∨
        Ex V j (Np a b (xOf P) (xOf Q) - e * Ns a b (xOf P) (xOf Q) +
          e ^ 2 * (xOf P - xOf Q) ^ 2)) →
      (Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb) := by
    intro P Q hP hQ j m hjm hpq hc
    refine rel_pts ha hb ha1 e he1.dv P Q hP hQ fun hx ↦ ?_
    obtain ⟨k, hk, hd⟩ := ex_d (V := V) hx hpq
    exact ⟨k, j, by omega, hd, hc⟩
  rcases Int.emod_two_eq_zero_or_one N with hpar | hpar
  · -- `N` even
    obtain ⟨m, hm⟩ : ∃ m : ℤ, 2 * m = N - 4 := ⟨(N - 4) / 2, by omega⟩
    have w1 := dbl_zm e he1 hε hδ heq1 hz1 (m := m) (by omega)
    have w2 := dbl_zm e he1 hε hδ heq2 hz2 (m := m) (by omega)
    have w3 := dbl_zm e he1 hε hδ heq3 hz3 (m := m) (by omega)
    have B1 := dbl_zB e he1 hε hδ hN7 heq1 hm w1
    have B2 := dbl_zB e he1 hε hδ hN7 heq2 hm w2
    have B3 := dbl_zB e he1 hε hδ hN7 heq3 hm w3
    have cong : ∀ {u v : K}, Dv V (N - 2) (3 * e * (u - e) ^ 2 + (e ^ 3 + a * e + b)) →
        Dv V (N - 2) (3 * e * (v - e) ^ 2 + (e ^ 3 + a * e + b)) →
        Dv V (m + 1) (u - v) ∨ Dv V (m + 1) ((u - e) + (v - e)) := by
      intro u v hu hv
      have h : Dv V ((m + 1) + (m + 1) - 1 + (0 + 1)) ((u - v) * ((u - e) + (v - e)) * (3 * e)) := by
        rw [show (u - v) * ((u - e) + (v - e)) * (3 * e) =
          (3 * e * (u - e) ^ 2 + (e ^ 3 + a * e + b)) -
            (3 * e * (v - e) ^ 2 + (e ^ 3 + a * e + b)) by ring]
        exact (hu.sub hv).mono (by omega)
      exact dv_or_of_mul (dv_of_mul_ex h ((ex_ofNat V 3).mul he1))
    have fin : ∀ (P Q : (shortF a b).toAffine.Point), Sing V a b P → Sing V a b Q →
        Dv V m (xOf P - e) → Dv V m (xOf Q - e) → Dv V (m + 1) (xOf P - xOf Q) →
        (Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb) := fun P Q hP hQ h1 h2 h12 ↦
      pair P Q hP hQ (N - 2) (m + 1) (by omega) h12
        (Or.inr (dbl_critB e he1 hε hδ hN7 hm h1 h2))
    rcases cong B1 B2 with c12 | c12
    · exact Or.inl (fin P1 P2 hS1 hS2 w1 w2 c12)
    rcases cong B1 B3 with c13 | c13
    · exact Or.inr (Or.inl (fin P1 P3 hS1 hS3 w1 w3 c13))
    · right; right
      refine fin P2 P3 hS2 hS3 w2 w3 ?_
      rw [show xOf P2 - xOf P3 = ((xOf P1 - e) + (xOf P2 - e)) - ((xOf P1 - e) + (xOf P3 - e)) by
        ring]
      exact c12.sub c13
  · -- `N` odd
    obtain ⟨m, hm⟩ : ∃ m : ℤ, 2 * m = N - 3 := ⟨(N - 3) / 2, by omega⟩
    have w1 := dbl_zm e he1 hε hδ heq1 hz1 (m := m) (by omega)
    have w2 := dbl_zm e he1 hε hδ heq2 hz2 (m := m) (by omega)
    left
    refine pair P1 P2 hS1 hS2 (N - 3) m (by omega) ?_
      (Or.inl (dbl_critA e he1 hε hδ hN7 hm w1 w2))
    rw [show xOf P1 - xOf P2 = (xOf P1 - e) - (xOf P2 - e) by ring]
    exact w1.sub w2

/-- The class of a singular point: `0` for simple, `1` for double. -/
noncomputable def cStar (V : LVal K) (a b : K) (P : (shortF a b).toAffine.Point) : ℕ :=
  if Ex V 2 (3 * xOf P ^ 2 + a) then 0 else 1

/-- **Types I₀\*, Iₙ\***: every point has a multiple `m ≤ 14` of non-singular reduction. -/
theorem index_star0 (ha : Dv V 0 a) (hb : Dv V 0 b) (ha2 : Dv V 2 a) (hb3 : Dv V 3 b)
    (hnot : ¬(Dv V 3 a ∧ Dv V 4 b)) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (P : (shortF a b).toAffine.Point) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 14 ∧ m • P ∈ E0 V a b ha hb := by
  have ha1 : Dv V 1 a := ha2.mono (by norm_num)
  have key := exists_nsmul_mem (E0 V a b ha hb) 2 3 (cStar V a b)
    (fun g ↦ by unfold cStar; split_ifs <;> omega) (fun Q hQ hcl ↦ ?_) P
  · obtain ⟨m, h1, h2, h3⟩ := key
    exact ⟨m, h1, by omega, h3⟩
  have hS : ∀ i, Sing V a b (Q i) := fun i ↦ by_contra fun h ↦ hQ i h
  have hdat : ∀ i, Dv V 1 (xOf (Q i)) ∧ Dv V 4 (xOf (Q i) ^ 3 + a * xOf (Q i) + b) := fun i ↦ by
    obtain ⟨y, heq, -, -, hg⟩ := sing_x (hS i)
    have hx := sing_x_small ha1 hg
    exact ⟨hx, star_f4 ha2 hb3 heq hx⟩
  have hg2 : ∀ i, Dv V 2 (3 * xOf (Q i) ^ 2 + a) := fun i ↦ by dvt [(hdat i).1, ha2]
  by_cases h0 : Ex V 2 (3 * xOf (Q 0) ^ 2 + a)
  · have hall : ∀ i, Ex V 2 (3 * xOf (Q i) ^ 2 + a) := fun i ↦ by
      have := hcl i 0
      unfold cStar at this
      rw [if_pos h0] at this
      by_contra hn
      rw [if_neg hn] at this
      exact one_ne_zero this
    have simp_rel : ∀ i j, Dv V 2 (xOf (Q i) - xOf (Q j)) →
        (Q j - Q i ∈ E0 V a b ha hb ∨ Q j + Q i ∈ E0 V a b ha hb) := fun i j hij ↦ by
      refine rel_pts0 ha hb ha1 (Q i) (Q j) (hS i) (hS j) fun hx ↦ ?_
      obtain ⟨k, hk, hd⟩ := ex_d (V := V) hx hij
      exact ⟨k, 4, by omega, hd, Or.inr (simple_crit ha2 hb3 (hdat i).1 (hdat j).1 (hdat i).2
        (hall i) hij)⟩
    rcases lagrange4 (hdat 0).1 (hdat 1).1 (hdat 2).1 (hdat 3).1 (hdat 0).2 (hdat 1).2
      (hdat 2).2 (hdat 3).2 with h | h | h | h | h | h
    · exact ⟨0, 1, by decide, simp_rel 0 1 h⟩
    · exact ⟨0, 2, by decide, simp_rel 0 2 h⟩
    · exact ⟨1, 2, by decide, simp_rel 1 2 h⟩
    · exact ⟨0, 3, by decide, simp_rel 0 3 h⟩
    · exact ⟨1, 3, by decide, simp_rel 1 3 h⟩
    · exact ⟨2, 3, by decide, simp_rel 2 3 h⟩
  · have hall : ∀ i, Dv V 3 (3 * xOf (Q i) ^ 2 + a) := fun i ↦ by
      have hn : ¬Ex V 2 (3 * xOf (Q i) ^ 2 + a) := by
        intro hi
        have := hcl i 0
        unfold cStar at this
        rw [if_pos hi, if_neg h0] at this
        exact zero_ne_one this
      by_contra h3
      exact hn (ex_of_dv_not (hg2 i) h3 (by norm_num))
    rcases dbl_triple ha hb ha2 hb3 hnot hΔ (Q 0) (Q 1) (Q 2) (hS 0) (hS 1) (hS 2) (hall 0)
      (hall 1) (hall 2) with h | h | h
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨0, 2, by decide, h⟩
    · exact ⟨1, 2, by decide, h⟩

end ExH
