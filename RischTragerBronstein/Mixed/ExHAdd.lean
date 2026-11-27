import RischTragerBronstein.Mixed.ExHLocal
import RischTragerBronstein.Mixed.ExHPigeon

/-!
# Finite index of the non-singular points: tools, and additive reduction of types II, III, IV

`rel_of_crit` turns the criterion `related` into the statement `Q − P ∈ E0 ∨ Q + P ∈ E0` needed by
the pigeonhole bound `exists_nsmul_mem`; `index_of_pair` is that bound when any two singular points
of one class are related. Valuations of polynomial expressions are bounded by the tactic `dvs`.

For additive reduction (`a, b ∈ 𝔭`) singular points have `x ∈ 𝔭`:
* type II (`v(b) = 1`): no singular points (`v(y²)` would be odd);
* type III (`v(a) = 1`, `v(b) ≥ 2`): any two singular points are related (`a²` dominates `N_p`);
* type IV (`v(a) ≥ 2`, `v(b) = 2`): any two singular points are related (`4b` dominates `N_s`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

section Tactic

variable {K : Type*} [Field K] {V : LVal K}

lemma Dv.add_min {k l : ℤ} {q r : K} (hq : Dv V k q) (hr : Dv V l r) :
    Dv V (min k l) (q + r) := (hq.mono (min_le_left _ _)).add (hr.mono (min_le_right _ _))

lemma Dv.sub_min {k l : ℤ} {q r : K} (hq : Dv V k q) (hr : Dv V l r) :
    Dv V (min k l) (q - r) := (hq.mono (min_le_left _ _)).sub (hr.mono (min_le_right _ _))

end Tactic

/-- `dvl [h₁, …]`: close the goal with one of the given terms. -/
syntax "dvl" "[" term,* "]" : tactic

macro_rules
  | `(tactic| dvl []) => `(tactic| fail "dvl: no hypothesis applies")
  | `(tactic| dvl [$h]) => `(tactic| exact $h)
  | `(tactic| dvl [$h, $hs,*]) => `(tactic| first | exact $h | dvl [$hs,*])

/-- `dvs [h₁, …]`: synthesize `Dv V ?k e` for a polynomial expression `e` in atoms whose bounds are
the given terms; the exponent `?k` is computed (`min` for sums, `+` for products). -/
syntax "dvs" "[" term,* "]" : tactic

macro_rules
  | `(tactic| dvs [$hs,*]) => `(tactic| first
      | dvl [$hs,*]
      | exact dv_ofNat _ _
      | exact dv_one _
      | (apply Dv.add_min; dvs [$hs,*]; dvs [$hs,*])
      | (apply Dv.sub_min; dvs [$hs,*]; dvs [$hs,*])
      | (apply Dv.neg; dvs [$hs,*])
      | (apply Dv.mul; dvs [$hs,*]; dvs [$hs,*])
      | (apply Dv.pow; dvs [$hs,*]))

/-- `dvt [h₁, …]`: prove `Dv V k e` from the synthesized bound and `omega`. -/
syntax "dvt" "[" term,* "]" : tactic

macro_rules
  | `(tactic| dvt [$hs,*]) => `(tactic| (apply Dv.mono; dvs [$hs,*]; omega))

variable {K : Type*} [Field K] {V : LVal K} {a b : K}

/-- Numerator of `x(P+Q) + x(P−Q)`. -/
def Ns (a b x1 x2 : K) : K := 2 * (x1 * x2 + a) * (x1 + x2) + 4 * b

/-- Numerator of `x(P+Q) · x(P−Q)`. -/
def Np (a b x1 x2 : K) : K := (x1 * x2 - a) ^ 2 - 4 * b * (x1 + x2)

/-- Coordinates of a singular point. -/
lemma sing_coords {P : (shortF a b).toAffine.Point} (h : Sing V a b P) :
    ∃ (x y : K) (hns : (shortF a b).toAffine.Nonsingular x y), P = .some x y hns ∧
      y ^ 2 = x ^ 3 + a * x + b ∧ Dv V 0 x ∧ Dv V 1 (x ^ 3 + a * x + b) ∧
      Dv V 1 (3 * x ^ 2 + a) := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact h.elim
  · exact ⟨x, y, hns, rfl, ((ns_short a b x y).mp hns).1, h⟩

/-- **From the criterion to relatedness in the group.** -/
theorem rel_of_crit (ha : Dv V 0 a) (hb : Dv V 0 b) (e : K)
    (hcent : ∀ {t u : K} (ht : (shortF a b).toAffine.Nonsingular t u),
      Sing V a b (.some t u ht) → Dv V 1 (t - e))
    {x1 y1 x2 y2 : K} (h1 : (shortF a b).toAffine.Nonsingular x1 y1)
    (h2 : (shortF a b).toAffine.Nonsingular x2 y2)
    (h : x1 ≠ x2 → ∃ k j : ℤ, j ≤ k ∧ Ex V k ((x1 - x2) ^ 2) ∧
      (Ex V j (Ns a b x1 x2 - 2 * e * (x1 - x2) ^ 2) ∨
        Ex V j (Np a b x1 x2 - e * Ns a b x1 x2 + e ^ 2 * (x1 - x2) ^ 2))) :
    Point.some _ _ h2 - Point.some _ _ h1 ∈ E0 V a b ha hb ∨
      Point.some _ _ h2 + Point.some _ _ h1 ∈ E0 V a b ha hb := by
  by_cases hx : x1 = x2
  · rcases (Point.X_eq_iff (h₁ := h1) (h₂ := h2)).mp hx with h | h
    · left; rw [h, sub_self]; exact zero_mem _
    · right; rw [h, add_neg_cancel]; exact zero_mem _
  · obtain ⟨k, j, hjk, hd, hc⟩ := h hx
    obtain ⟨t, u, ht, hte, hor⟩ := related h1 h2 e hjk hd hc
    have hns : ¬Sing V a b (.some t u ht) := fun hs ↦ hte (hcent ht hs)
    rcases hor with hor | hor
    · right; rw [add_comm, hor]; exact hns
    · left
      have e1 : Point.some _ _ h2 - Point.some _ _ h1 =
          -(Point.some _ _ h1 - Point.some _ _ h2) := (neg_sub _ _).symm
      rw [e1, hor]
      exact (E0 V a b ha hb).neg_mem hns

/-- The exact valuation of `(x₁ − x₂)²`. -/
lemma ex_d {x1 x2 : K} (hx : x1 ≠ x2) {m : ℤ} (h : Dv V m (x1 - x2)) :
    ∃ k, 2 * m ≤ k ∧ Ex V k ((x1 - x2) ^ 2) := by
  have hne := sub_ne_zero.mpr hx
  refine ⟨2 * V.v (x1 - x2), ?_, ?_⟩
  · have := dv_of_ne h hne; omega
  · simpa using (ex_of_ne (V := V) _ hne).pow 2

/-- **The index bound when any two singular points of a class are related.** -/
theorem index_of_pair (ha : Dv V 0 a) (hb : Dv V 0 b) (t : ℕ)
    (c : (shortF a b).toAffine.Point → ℕ) (hc : ∀ P, c P < t)
    (hpair : ∀ P Q, Sing V a b P → Sing V a b Q → c P = c Q →
      (Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb)) (P : (shortF a b).toAffine.Point) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2 * (t + 1) ∧ m • P ∈ E0 V a b ha hb := by
  have := exists_nsmul_mem (E0 V a b ha hb) t 1 c hc (fun Q hQ hcl ↦
    ⟨0, 1, by decide, hpair (Q 0) (Q 1) (by_contra fun h ↦ hQ 0 h) (by_contra fun h ↦ hQ 1 h)
      (hcl 0 1)⟩) P
  simpa using this

variable [CharZero K]

/-- Additive reduction: singular points have `x ∈ 𝔭`. -/
lemma sing_x_small (ha1 : Dv V 1 a) {x : K} (hg : Dv V 1 (3 * x ^ 2 + a)) : Dv V 1 x := by
  have h3 : Dv V (1 + 0) (x ^ 2 * 3) := by
    have := hg.sub ha1
    have e : 3 * x ^ 2 + a - a = x ^ 2 * 3 := by ring
    rw [e] at this
    simpa using this
  have h2 : Dv V 1 (x ^ 2) := dv_of_mul_ex h3 (ex_ofNat V 3)
  exact dv_of_sq (k := 1) ((dv_sq_succ h2 (by norm_num)).mono (by norm_num))

/-- Relatedness for additive reduction (centre `0`). -/
theorem rel_add (ha : Dv V 0 a) (hb : Dv V 0 b) (ha1 : Dv V 1 a)
    {x1 y1 x2 y2 : K} (h1 : (shortF a b).toAffine.Nonsingular x1 y1)
    (h2 : (shortF a b).toAffine.Nonsingular x2 y2)
    (h : x1 ≠ x2 → ∃ k j : ℤ, j ≤ k ∧ Ex V k ((x1 - x2) ^ 2) ∧
      (Ex V j (Ns a b x1 x2) ∨ Ex V j (Np a b x1 x2))) :
    Point.some _ _ h2 - Point.some _ _ h1 ∈ E0 V a b ha hb ∨
      Point.some _ _ h2 + Point.some _ _ h1 ∈ E0 V a b ha hb := by
  refine rel_of_crit ha hb 0 (fun ht hs ↦ ?_) h1 h2 (fun hx ↦ ?_)
  · rw [sub_zero]; exact sing_x_small ha1 hs.2.2
  · obtain ⟨k, j, hjk, hd, hc⟩ := h hx
    refine ⟨k, j, hjk, hd, ?_⟩
    have e1 : Ns a b x1 x2 - 2 * 0 * (x1 - x2) ^ 2 = Ns a b x1 x2 := by ring
    have e2 : Np a b x1 x2 - 0 * Ns a b x1 x2 + 0 ^ 2 * (x1 - x2) ^ 2 = Np a b x1 x2 := by ring
    rw [e1, e2]; exact hc

/-- **Type II**: no singular points. -/
theorem no_sing_II (ha1 : Dv V 1 a) (hb1 : Ex V 1 b) (P : (shortF a b).toAffine.Point) :
    ¬Sing V a b P := by
  intro h
  obtain ⟨x, y, hns, rfl, heq, -, -, hg⟩ := sing_coords h
  have hx := sing_x_small ha1 hg
  have hy : Ex V 1 (y ^ 2) := by
    rw [heq, show x ^ 3 + a * x + b = b + (x ^ 3 + a * x) by ring]
    apply Ex.add_dv hb1
    · dvs [hx, ha1]
    · omega
  have := hy.sq_even
  omega

/-- **Type III**: any two singular points are related. -/
theorem pair_III (ha : Dv V 0 a) (hb : Dv V 0 b) (ha1 : Ex V 1 a) (hb2 : Dv V 2 b)
    (P Q : (shortF a b).toAffine.Point) (hP : Sing V a b P) (hQ : Sing V a b Q) :
    Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb := by
  obtain ⟨x1, y1, h1, rfl, -, -, -, hg1⟩ := sing_coords hP
  obtain ⟨x2, y2, h2, rfl, -, -, -, hg2⟩ := sing_coords hQ
  have hx1 := sing_x_small ha1.dv hg1
  have hx2 := sing_x_small ha1.dv hg2
  refine rel_add ha hb ha1.dv h1 h2 fun hx ↦ ?_
  obtain ⟨k, hk, hd⟩ := ex_d (V := V) hx (hx1.sub hx2)
  refine ⟨k, 2, by omega, hd, Or.inr ?_⟩
  rw [show Np a b x1 x2 = a ^ 2 + ((x1 * x2) ^ 2 - 2 * a * (x1 * x2) - 4 * b * (x1 + x2)) by
    unfold Np; ring]
  apply Ex.add_dv (show Ex V 2 (a ^ 2) by simpa using ha1.pow 2)
  · dvs [hx1, hx2, ha1.dv, hb2]
  · omega

/-- **Type IV**: any two singular points are related. -/
theorem pair_IV (ha : Dv V 0 a) (hb : Dv V 0 b) (ha2 : Dv V 2 a) (hb2 : Ex V 2 b)
    (P Q : (shortF a b).toAffine.Point) (hP : Sing V a b P) (hQ : Sing V a b Q) :
    Q - P ∈ E0 V a b ha hb ∨ Q + P ∈ E0 V a b ha hb := by
  have ha1 : Dv V 1 a := ha2.mono (by norm_num)
  obtain ⟨x1, y1, h1, rfl, -, -, -, hg1⟩ := sing_coords hP
  obtain ⟨x2, y2, h2, rfl, -, -, -, hg2⟩ := sing_coords hQ
  have hx1 := sing_x_small ha1 hg1
  have hx2 := sing_x_small ha1 hg2
  refine rel_add ha hb ha1 h1 h2 fun hx ↦ ?_
  obtain ⟨k, hk, hd⟩ := ex_d (V := V) hx (hx1.sub hx2)
  refine ⟨k, 2, by omega, hd, Or.inl ?_⟩
  rw [show Ns a b x1 x2 = 4 * b + 2 * (x1 * x2 + a) * (x1 + x2) by unfold Ns; ring]
  apply Ex.add_dv (show Ex V 2 (4 * b) by simpa using (ex_ofNat V 4).mul hb2)
  · dvs [hx1, hx2, ha2]
  · omega

end ExH
