import RischTragerBronstein.Mixed.ExHAdd

/-!
# Additive reduction with `a ∈ 𝔭²`, `b ∈ 𝔭³` (starred types): tools and types IV*, III*, II*

Tactics `exs`/`exq`/`domt` compute exact valuations of monomials and of sums with a dominant
term. For starred types every singular `x` has `f(x) ∈ 𝔭⁴` (`star_f4`, parity), and

* among four singular points two have `x`-coordinates congruent modulo `𝔭²` (`lagrange4`);
* two singular points with `v(f′(x)) = 2` (a simple root of the reduced scaled cubic) and
  congruent `x`-coordinates are related (`simple_crit`);
* type IV* (`a ∈ 𝔭³`, `v(b) = 4`), type III* (`v(a) = 3`, `b ∈ 𝔭⁵`): any two singular points are
  related; type II* (`a ∈ 𝔭⁴`, `v(b) = 5`): no singular points.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

section Tactic

variable {K : Type*} [Field K] {V : LVal K}

lemma Ex.congr {k k' : ℤ} {q : K} (h : Ex V k q) (hk : k = k') : Ex V k' q := hk ▸ h

lemma Ex.add_dv' {k l j : ℤ} {q r : K} (hq : Ex V k q) (hr : Dv V l r) (hj : k = j ∧ k < l) :
    Ex V j (q + r) := hj.1 ▸ hq.add_dv hr hj.2

lemma ex_of_dv_not {k k' : ℤ} {q : K} (h : Dv V k q) (hn : ¬Dv V k' q) (hk : k' = k + 1) :
    Ex V k q := by
  have hq : q ≠ 0 := fun h0 ↦ hn (Or.inl h0)
  refine ⟨hq, ?_⟩
  have := dv_of_ne h hq
  by_contra hne
  exact hn (Or.inr (by omega))

lemma ex_of_sq {k : ℤ} {y : K} (h : Ex V (2 * k) (y ^ 2)) : Ex V k y := by
  have hy : y ≠ 0 := fun h0 ↦ h.1 (by simp [h0])
  refine ⟨hy, ?_⟩
  have := h.2
  rw [V.pow _ hy] at this
  push_cast at this
  omega

end Tactic

/-- `exs [h₁, …]`: synthesize `Ex V ?k e` for a monomial `e` in atoms of known exact valuation. -/
syntax "exs" "[" term,* "]" : tactic

macro_rules
  | `(tactic| exs [$hs,*]) => `(tactic| first
      | dvl [$hs,*]
      | exact ex_ofNat _ _
      | exact ex_one _
      | (apply Ex.neg; exs [$hs,*])
      | (apply Ex.mul; exs [$hs,*]; exs [$hs,*])
      | (apply Ex.div; exs [$hs,*]; exs [$hs,*])
      | (apply Ex.pow; exs [$hs,*]))

/-- `exq [h₁, …]`: prove `Ex V k e` for a monomial `e`. -/
syntax "exq" "[" term,* "]" : tactic

macro_rules
  | `(tactic| exq [$hs,*]) => `(tactic| (apply Ex.congr; exs [$hs,*]; omega))

/-- `domt [e₁, …] [h₁, …]`: prove `Ex V j (dom + rest)` where the monomial `dom` has exact
valuation `j` (from the `eᵢ`) and `rest` has larger valuation (from the `hᵢ`). -/
syntax "domt" "[" term,* "]" "[" term,* "]" : tactic

macro_rules
  | `(tactic| domt [$es,*] [$hs,*]) =>
    `(tactic| (apply Ex.add_dv'; exs [$es,*]; dvs [$hs,*]; omega))

variable {K : Type*} [Field K] {V : LVal K} {a b : K}

/-- The `x`-coordinate (`0` at the origin). -/
def xOf : (shortF a b).toAffine.Point → K
  | .zero => 0
  | .some x _ _ => x

lemma sing_x {P : (shortF a b).toAffine.Point} (h : Sing V a b P) :
    ∃ y : K, y ^ 2 = xOf P ^ 3 + a * xOf P + b ∧ Dv V 0 (xOf P) ∧
      Dv V 1 (xOf P ^ 3 + a * xOf P + b) ∧ Dv V 1 (3 * xOf P ^ 2 + a) := by
  obtain ⟨x, y, hns, rfl, heq, h0, hf, hg⟩ := sing_coords h
  exact ⟨y, heq, h0, hf, hg⟩

variable [CharZero K]

/-- Relatedness of singular points, additive reduction, centre `e ∈ 𝔭`. -/
theorem rel_pts (ha : Dv V 0 a) (hb : Dv V 0 b) (ha1 : Dv V 1 a) (e : K) (he : Dv V 1 e)
    (P Q : (shortF a b).toAffine.Point) (hP : Sing V a b P) (hQ : Sing V a b Q)
    (h : xOf P ≠ xOf Q → ∃ k j : ℤ, j ≤ k ∧ Ex V k ((xOf P - xOf Q) ^ 2) ∧
      (Ex V j (Ns a b (xOf P) (xOf Q) - 2 * e * (xOf P - xOf Q) ^ 2) ∨
        Ex V j (Np a b (xOf P) (xOf Q) - e * Ns a b (xOf P) (xOf Q) +
          e ^ 2 * (xOf P - xOf Q) ^ 2))) :
    Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb := by
  obtain ⟨x1, y1, h1, rfl, -⟩ := sing_coords hP
  obtain ⟨x2, y2, h2, rfl, -⟩ := sing_coords hQ
  exact rel_of_crit ha hb e (fun ht hs ↦ (sing_x_small ha1 hs.2.2).sub he) h1 h2 h

/-- Relatedness of singular points, additive reduction, centre `0`. -/
theorem rel_pts0 (ha : Dv V 0 a) (hb : Dv V 0 b) (ha1 : Dv V 1 a)
    (P Q : (shortF a b).toAffine.Point) (hP : Sing V a b P) (hQ : Sing V a b Q)
    (h : xOf P ≠ xOf Q → ∃ k j : ℤ, j ≤ k ∧ Ex V k ((xOf P - xOf Q) ^ 2) ∧
      (Ex V j (Ns a b (xOf P) (xOf Q)) ∨ Ex V j (Np a b (xOf P) (xOf Q)))) :
    Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb := by
  refine rel_pts ha hb ha1 0 (dv_zero _) P Q hP hQ fun hx ↦ ?_
  obtain ⟨k, j, hjk, hd, hc⟩ := h hx
  refine ⟨k, j, hjk, hd, ?_⟩
  have e1 : Ns a b (xOf P) (xOf Q) - 2 * 0 * (xOf P - xOf Q) ^ 2 = Ns a b (xOf P) (xOf Q) := by
    ring
  have e2 : Np a b (xOf P) (xOf Q) - 0 * Ns a b (xOf P) (xOf Q) + 0 ^ 2 * (xOf P - xOf Q) ^ 2 =
      Np a b (xOf P) (xOf Q) := by ring
  rw [e1, e2]; exact hc

/-- Starred types: `f(x) ∈ 𝔭⁴` at singular points. -/
lemma star_f4 (ha2 : Dv V 2 a) (hb3 : Dv V 3 b) {x y : K} (heq : y ^ 2 = x ^ 3 + a * x + b)
    (hx : Dv V 1 x) : Dv V 4 (x ^ 3 + a * x + b) := by
  have h3 : Dv V 3 (x ^ 3 + a * x + b) := by dvt [hx, ha2, hb3]
  rw [← heq] at h3 ⊢
  exact (dv_sq_succ h3 (by norm_num)).mono (by norm_num)

/-- **Among four singular `x`-coordinates two are congruent modulo `𝔭²`** (Lagrange
interpolation: otherwise `v(f(x₄)) = 3`). -/
lemma lagrange4 {x1 x2 x3 x4 : K} (h1 : Dv V 1 x1) (h2 : Dv V 1 x2) (h3 : Dv V 1 x3)
    (h4 : Dv V 1 x4) (f1 : Dv V 4 (x1 ^ 3 + a * x1 + b)) (f2 : Dv V 4 (x2 ^ 3 + a * x2 + b))
    (f3 : Dv V 4 (x3 ^ 3 + a * x3 + b)) (f4 : Dv V 4 (x4 ^ 3 + a * x4 + b)) :
    Dv V 2 (x1 - x2) ∨ Dv V 2 (x1 - x3) ∨ Dv V 2 (x2 - x3) ∨ Dv V 2 (x1 - x4) ∨
      Dv V 2 (x2 - x4) ∨ Dv V 2 (x3 - x4) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n13, n23, n14, n24, n34⟩ := hcon
  have e12 := ex_of_dv_not (h1.sub h2) n12 (by norm_num)
  have e13 := ex_of_dv_not (h1.sub h3) n13 (by norm_num)
  have e23 := ex_of_dv_not (h2.sub h3) n23 (by norm_num)
  have e41 : Ex V 1 (x4 - x1) := by
    have := (ex_of_dv_not (h1.sub h4) n14 (by norm_num)).neg; rwa [neg_sub] at this
  have e42 : Ex V 1 (x4 - x2) := by
    have := (ex_of_dv_not (h2.sub h4) n24 (by norm_num)).neg; rwa [neg_sub] at this
  have e43 : Ex V 1 (x4 - x3) := by
    have := (ex_of_dv_not (h3.sub h4) n34 (by norm_num)).neg; rwa [neg_sub] at this
  have T1 : Ex V 0 ((x4 - x2) * (x4 - x3) / ((x1 - x2) * (x1 - x3))) := by
    exq [e42, e43, e12, e13]
  have T2 : Ex V 0 ((x4 - x1) * (x4 - x3) / ((x1 - x2) * (x2 - x3))) := by
    exq [e41, e43, e12, e23]
  have T3 : Ex V 0 ((x4 - x1) * (x4 - x2) / ((x1 - x3) * (x2 - x3))) := by
    exq [e41, e42, e13, e23]
  have key : x4 ^ 3 + a * x4 + b = (x4 - x1) * (x4 - x2) * (x4 - x3) +
      ((x1 ^ 3 + a * x1 + b) * ((x4 - x2) * (x4 - x3) / ((x1 - x2) * (x1 - x3))) -
        (x2 ^ 3 + a * x2 + b) * ((x4 - x1) * (x4 - x3) / ((x1 - x2) * (x2 - x3))) +
        (x3 ^ 3 + a * x3 + b) * ((x4 - x1) * (x4 - x2) / ((x1 - x3) * (x2 - x3)))) := by
    have := e12.ne
    have := e13.ne
    have := e23.ne
    field_simp
    ring
  have hE : Ex V 3 (x4 ^ 3 + a * x4 + b) := by
    rw [key]
    domt [e41, e42, e43] [f1, f2, f3, T1.dv, T2.dv, T3.dv]
  exact hE.not_dv (by norm_num) f4

/-- **Simple singular points with congruent `x` are related**: `v(N_p) = 4`. -/
lemma simple_crit (ha2 : Dv V 2 a) (hb3 : Dv V 3 b) {x1 x2 : K} (h1 : Dv V 1 x1)
    (h2 : Dv V 1 x2) (f1 : Dv V 4 (x1 ^ 3 + a * x1 + b)) (g1 : Ex V 2 (3 * x1 ^ 2 + a))
    (h12 : Dv V 2 (x1 - x2)) : Ex V 4 (Np a b x1 x2) := by
  have h21 : Dv V 2 (x2 - x1) := by simpa using h12.neg
  rw [show Np a b x1 x2 = (3 * x1 ^ 2 + a) ^ 2 +
    ((x2 - x1) * (x1 * (x1 * x2 + x1 ^ 2 - 2 * a) - 4 * b) -
      8 * x1 * (x1 ^ 3 + a * x1 + b)) by unfold Np; ring]
  domt [g1] [h21, f1, h1, h2, ha2, hb3]

/-- `a ∈ 𝔭³`, `b ∈ 𝔭⁴`: singular points have `x ∈ 𝔭²`. -/
lemma star2_x (ha3 : Dv V 3 a) (hb4 : Dv V 4 b) {x y : K} (heq : y ^ 2 = x ^ 3 + a * x + b)
    (hx : Dv V 1 x) : Dv V 2 x := by
  by_contra hn
  have ex := ex_of_dv_not hx hn (by norm_num)
  have h3 : Ex V 3 (y ^ 2) := by
    rw [heq, show x ^ 3 + a * x + b = x ^ 3 + (a * x + b) by ring]
    domt [ex] [ha3, hb4, hx]
  have := h3.sq_even
  omega

/-- **Type IV\***: any two singular points are related. -/
theorem pair_IVs (ha : Dv V 0 a) (hb : Dv V 0 b) (ha3 : Dv V 3 a) (hb4 : Ex V 4 b)
    (P Q : (shortF a b).toAffine.Point) (hP : Sing V a b P) (hQ : Sing V a b Q) :
    Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb := by
  have ha1 : Dv V 1 a := ha3.mono (by norm_num)
  obtain ⟨y1, heq1, -, -, hg1⟩ := sing_x hP
  obtain ⟨y2, heq2, -, -, hg2⟩ := sing_x hQ
  have hx1 := star2_x ha3 hb4.dv heq1 (sing_x_small ha1 hg1)
  have hx2 := star2_x ha3 hb4.dv heq2 (sing_x_small ha1 hg2)
  refine rel_pts0 ha hb ha1 P Q hP hQ fun hx ↦ ?_
  obtain ⟨k, hk, hd⟩ := ex_d (V := V) hx (hx1.sub hx2)
  refine ⟨k, 4, by omega, hd, Or.inl ?_⟩
  rw [show Ns a b (xOf P) (xOf Q) = 4 * b + 2 * (xOf P * xOf Q + a) * (xOf P + xOf Q) by
    unfold Ns; ring]
  domt [hb4] [hx1, hx2, ha3]

/-- Type III*: `a x + b ∈ 𝔭⁶` at singular points. -/
lemma star3_lin (ha3 : Ex V 3 a) (hb5 : Dv V 5 b) {x y : K} (heq : y ^ 2 = x ^ 3 + a * x + b)
    (hx2 : Dv V 2 x) : Dv V 6 (a * x + b) := by
  have h5 : Dv V 5 (x ^ 3 + a * x + b) := by dvt [hx2, ha3.dv, hb5]
  have h6 : Dv V 6 (x ^ 3 + a * x + b) := by
    rw [← heq] at h5 ⊢
    exact (dv_sq_succ h5 (by norm_num)).mono (by norm_num)
  rw [show a * x + b = (x ^ 3 + a * x + b) - x ^ 3 by ring]
  dvt [h6, hx2]

/-- **Type III\***: any two singular points are related. -/
theorem pair_IIIs (ha : Dv V 0 a) (hb : Dv V 0 b) (ha3 : Ex V 3 a) (hb5 : Dv V 5 b)
    (P Q : (shortF a b).toAffine.Point) (hP : Sing V a b P) (hQ : Sing V a b Q) :
    Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb := by
  have ha1 : Dv V 1 a := ha3.dv.mono (by norm_num)
  have hb4 : Dv V 4 b := hb5.mono (by norm_num)
  obtain ⟨y1, heq1, -, -, hg1⟩ := sing_x hP
  obtain ⟨y2, heq2, -, -, hg2⟩ := sing_x hQ
  have hx1 := star2_x ha3.dv hb4 heq1 (sing_x_small ha1 hg1)
  have hx2 := star2_x ha3.dv hb4 heq2 (sing_x_small ha1 hg2)
  have l1 := star3_lin ha3 hb5 heq1 hx1
  have l2 := star3_lin ha3 hb5 heq2 hx2
  have h12 : Dv V 3 (xOf P - xOf Q) := by
    have h6 : Dv V (3 + 3) ((xOf P - xOf Q) * a) := by
      rw [show (xOf P - xOf Q) * a = (a * xOf P + b) - (a * xOf Q + b) by ring]
      exact (l1.sub l2).mono (by norm_num)
    exact dv_of_mul_ex h6 ha3
  refine rel_pts0 ha hb ha1 P Q hP hQ fun hx ↦ ?_
  obtain ⟨k, hk, hd⟩ := ex_d (V := V) hx h12
  refine ⟨k, 6, by omega, hd, Or.inr ?_⟩
  rw [show Np a b (xOf P) (xOf Q) = a ^ 2 + ((xOf P * xOf Q) ^ 2 - 2 * a * (xOf P * xOf Q) -
    4 * b * (xOf P + xOf Q)) by unfold Np; ring]
  domt [ha3] [hx1, hx2, ha3.dv, hb5]

/-- **Type II\***: no singular points. -/
theorem no_sing_IIs (ha4 : Dv V 4 a) (hb5 : Ex V 5 b) (P : (shortF a b).toAffine.Point) :
    ¬Sing V a b P := by
  intro h
  obtain ⟨y, heq, -, -, hg⟩ := sing_x h
  have hx2 := star2_x (ha4.mono (by norm_num)) (hb5.dv.mono (by norm_num)) heq
    (sing_x_small (ha4.mono (by norm_num)) hg)
  have h5 : Ex V 5 (y ^ 2) := by
    rw [heq, show xOf P ^ 3 + a * xOf P + b = b + (xOf P ^ 3 + a * xOf P) by ring]
    domt [hb5] [hx2, ha4]
  have := h5.sq_even
  omega

end ExH
