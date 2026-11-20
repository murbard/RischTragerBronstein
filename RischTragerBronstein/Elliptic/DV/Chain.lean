import RischTragerBronstein.Elliptic.DV.Embed
import RischTragerBronstein.Algebraic.EllOrbitComplete

/-!
# Verified point arithmetic over `K = ℚ[x]/(f)` and the torsion test

Points of `y² = x³ + ax² + bx + c` over `K = ℚ[x]/(f)` (`f` irreducible) are represented by
polynomials reduced modulo `f`; `addPt` computes the chord–tangent law (inverses by the extended
Euclidean algorithm), `mulPt k P = k • P`. `addPt_spec`/`mulPt_spec`: the computation agrees with
Mathlib's group law on `W K a b c`. With the bound `torsion_order_le_adjoin`:
`torsionTestK_spec` decides whether a point of `E(K)` has finite order.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine CPoly

namespace EllDV

open scoped Classical

/-! ### Arithmetic modulo `f` -/

/-- Equality modulo `f`. -/
def eqMod (f q r : CPoly ℚ) : Bool := isZero (divMod (sub q r) f).2

/-- Reduction modulo `f`. -/
def rmod (f q : CPoly ℚ) : CPoly ℚ := (divMod q f).2

/-- The chord–tangent sum, `none` for the origin. -/
def addPt (f : CPoly ℚ) (a b c : ℤ) :
    Option (CPoly ℚ × CPoly ℚ) → Option (CPoly ℚ × CPoly ℚ) → Option (CPoly ℚ × CPoly ℚ)
  | none, Q => Q
  | P, none => P
  | some (x1, y1), some (x2, y2) =>
    if eqMod f x1 x2 then
      if eqMod f y1 (smul (-1) y2) then none
      else
        let lam := rmod f (mul (add (add (smul 3 (mul x1 x1)) (smul (2 * a) x1)) [(b : ℚ)])
          (EllAlgo.modInv (smul 2 y1) f))
        let x3 := rmod f (sub (sub (sub (mul lam lam) [(a : ℚ)]) x1) x2)
        some (x3, rmod f (smul (-1) (add (mul lam (sub x3 x1)) y1)))
    else
      let lam := rmod f (mul (sub y1 y2) (EllAlgo.modInv (sub x1 x2) f))
      let x3 := rmod f (sub (sub (sub (mul lam lam) [(a : ℚ)]) x1) x2)
      some (x3, rmod f (smul (-1) (add (mul lam (sub x3 x1)) y1)))

/-- `k • P`. -/
def mulPt (f : CPoly ℚ) (a b c : ℤ) (P : Option (CPoly ℚ × CPoly ℚ)) :
    ℕ → Option (CPoly ℚ × CPoly ℚ)
  | 0 => none
  | k + 1 => addPt f a b c (mulPt f a b c P k) P

/-! ### Semantics -/

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))] (a b c : ℤ)

local notation "K" => AdjoinRoot (toPoly f)

/-- The value in `K`. -/
noncomputable def ev (q : CPoly ℚ) : K := AdjoinRoot.mk (toPoly f) (toPoly q)

variable {f}

lemma ev_eq_iff (q r : CPoly ℚ) : ev f q = ev f r ↔ eqMod f q r = true := by
  have hf0 : toPoly f ≠ 0 := hf.out.ne_zero
  rw [ev, ev, AdjoinRoot.mk_eq_mk, eqMod, isZero_iff]
  constructor
  · intro h
    exact CPoly.divMod_exact _ _ hf0 (by rw [toPoly_sub]; exact h)
  · intro h
    have := divMod_spec (sub q r) f
    rw [h, add_zero, toPoly_sub] at this
    exact ⟨_, by rw [this, mul_comm]⟩

lemma ev_rmod (q : CPoly ℚ) : ev f (rmod f q) = ev f q := by
  rw [ev, ev, AdjoinRoot.mk_eq_mk, rmod]
  exact EllAlgo.rem_dvd q f

lemma ev_add (q r : CPoly ℚ) : ev f (add q r) = ev f q + ev f r := by simp [ev, toPoly_add]
lemma ev_sub (q r : CPoly ℚ) : ev f (sub q r) = ev f q - ev f r := by simp [ev, toPoly_sub]
lemma ev_mul (q r : CPoly ℚ) : ev f (mul q r) = ev f q * ev f r := by simp [ev, toPoly_mul]
lemma ev_smul (t : ℚ) (q : CPoly ℚ) : ev f (smul t q) = (t : K) * ev f q := by
  simp [ev, toPoly_smul, AdjoinRoot.mk_C]
lemma ev_const (t : ℚ) : ev f [t] = (t : K) := by simp [ev, toPoly]

/-- The modular inverse is an inverse in `K`. -/
lemma ev_modInv (u : CPoly ℚ) (hu : ev f u ≠ 0) : ev f u * ev f (EllAlgo.modInv u f) = 1 := by
  have hf0 : toPoly f ≠ 0 := hf.out.ne_zero
  have hnd : ¬toPoly f ∣ toPoly u := fun h ↦ hu (by rw [ev, AdjoinRoot.mk_eq_zero]; exact h)
  have hcop : IsCoprime (toPoly u) (toPoly f) :=
    ((hf.out.coprime_iff_not_dvd).mpr hnd).symm
  have := EllAlgo.modInv_spec u f hf0 hcop
  rw [← sub_eq_zero, ev, ev, ← map_mul, ← map_one (AdjoinRoot.mk (toPoly f)), ← map_sub,
    AdjoinRoot.mk_eq_zero]
  exact this

/-- The representation relation. -/
def Rep (o : Option (CPoly ℚ × CPoly ℚ)) (P : (W K a b c).toAffine.Point) : Prop :=
  match o with
  | none => P = 0
  | some (x, y) => ∃ h, P = Point.some (ev f x) (ev f y) h

lemma W_a₁ : (W K a b c).toAffine.a₁ = 0 := by
  simp [W, W0, WeierstrassCurve.baseChange, WeierstrassCurve.map]
lemma W_a₂ : (W K a b c).toAffine.a₂ = (a : K) := by
  simp [W, W0, WeierstrassCurve.baseChange, WeierstrassCurve.map]
lemma W_a₄ : (W K a b c).toAffine.a₄ = (b : K) := by
  simp [W, W0, WeierstrassCurve.baseChange, WeierstrassCurve.map]

lemma some_congr {x y x' y' : K} {h : (W K a b c).toAffine.Nonsingular x y}
    {h' : (W K a b c).toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx; subst hy; rfl

set_option maxHeartbeats 1600000 in
/-- **The computed sum is the sum.** -/
theorem addPt_spec {o₁ o₂ : Option (CPoly ℚ × CPoly ℚ)} {P₁ P₂ : (W K a b c).toAffine.Point}
    (h₁ : Rep a b c o₁ P₁) (h₂ : Rep a b c o₂ P₂) : Rep a b c (addPt f a b c o₁ o₂) (P₁ + P₂) := by
  rcases o₁ with _ | ⟨x1, y1⟩ <;> rcases o₂ with _ | ⟨x2, y2⟩
  · simp only [Rep, addPt] at h₁ h₂ ⊢; subst h₁; subst h₂; rfl
  · simp only [Rep, addPt] at h₁ h₂ ⊢
    subst h₁; obtain ⟨h, rfl⟩ := h₂; exact ⟨h, rfl⟩
  · simp only [Rep, addPt] at h₁ h₂ ⊢
    subst h₂; obtain ⟨h, rfl⟩ := h₁; exact ⟨h, rfl⟩
  obtain ⟨hn1, rfl⟩ := h₁
  obtain ⟨hn2, rfl⟩ := h₂
  have e1 := (equation_W a b c).mp hn1.1
  have e2 := (equation_W a b c).mp hn2.1
  unfold OnCurve at e1 e2
  have hnegY : ∀ u v : K, (W K a b c).toAffine.negY u v = -v := fun u v ↦ negY_W a b c u v
  have hX : ∀ u v L : K, (W K a b c).toAffine.addX u v L = L ^ 2 - a - u - v := by
    intro u v L; simp [addX, W, W0]
  have hY : ∀ u v w L : K, (W K a b c).toAffine.addY u v w L =
      -(L * ((L ^ 2 - a - u - v) - u) + w) := by
    intro u v w L; simp only [addY, negAddY, hX, hnegY]
  simp only [addPt]
  by_cases hx : eqMod f x1 x2 = true
  · rw [if_pos hx]
    have hxK : ev f x1 = ev f x2 := (ev_eq_iff x1 x2).mpr hx
    by_cases hy : eqMod f y1 (smul (-1) y2) = true
    · rw [if_pos hy]
      have hyK : ev f y1 = -ev f y2 := by
        rw [(ev_eq_iff _ _).mpr hy, ev_smul]; push_cast; ring
      simp only [Rep]
      exact Point.add_of_Y_eq hxK (by rw [hyK, hnegY])
    · rw [if_neg hy]
      have hyK : ev f y1 ≠ -ev f y2 := fun h ↦ hy ((ev_eq_iff _ _).mp (by
        rw [h, ev_smul]; push_cast; ring))
      -- `y₁ = y₂`
      have hyy : ev f y1 = ev f y2 := by
        have : (ev f y1 - ev f y2) * (ev f y1 + ev f y2) = 0 := by
          rw [← hxK] at e2; linear_combination e1 - e2
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd (by linear_combination h) hyK
      have hy20 : ev f (smul 2 y1) ≠ 0 := by
        rw [ev_smul]; push_cast
        intro h0
        apply hyK
        have : ev f y1 = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · norm_num at h
          · exact h
        rw [← hyy, this, neg_zero]
      have hinv := ev_modInv _ hy20
      rw [ev_smul] at hinv
      have hxy : ¬(ev f x1 = ev f x2 ∧ ev f y1 = (W K a b c).toAffine.negY (ev f x2) (ev f y2)) := by
        rintro ⟨-, h⟩; rw [hnegY] at h; exact hyK h
      set lam := rmod f (mul (add (add (smul 3 (mul x1 x1)) (smul (2 * a) x1)) [(b : ℚ)])
          (EllAlgo.modInv (smul 2 y1) f)) with hlam
      have h2y : (2 : K) * ev f y1 ≠ 0 := by
        intro h0; apply hy20; rw [ev_smul]; push_cast; exact h0
      have hsl : (W K a b c).toAffine.slope (ev f x1) (ev f x2) (ev f y1) (ev f y2) = ev f lam := by
        rw [slope_of_Y_ne hxK (by rw [hnegY]; exact hyK), hlam, ev_rmod, ev_mul, ev_add, ev_add,
          ev_smul, ev_smul, ev_mul, ev_const, hnegY]
        rw [W_a₁, W_a₂, W_a₄, zero_mul, sub_zero]
        push_cast at hinv ⊢
        rw [div_eq_iff (by rw [sub_neg_eq_add]; intro h0; apply h2y; linear_combination h0)]
        linear_combination (-(3 * ev f x1 ^ 2 + 2 * (a : K) * ev f x1 + b)) * hinv
      clear_value lam
      have hx3 : (W K a b c).toAffine.addX (ev f x1) (ev f x2)
          ((W K a b c).toAffine.slope (ev f x1) (ev f x2) (ev f y1) (ev f y2)) =
          ev f (rmod f (sub (sub (sub (mul lam lam) [(a : ℚ)]) x1) x2)) := by
        rw [hX, hsl, ev_rmod]; simp only [ev_sub, ev_mul, ev_const]; push_cast; ring
      have hy3 : (W K a b c).toAffine.addY (ev f x1) (ev f x2) (ev f y1)
          ((W K a b c).toAffine.slope (ev f x1) (ev f x2) (ev f y1) (ev f y2)) =
          ev f (rmod f (smul (-1) (add (mul lam (sub (rmod f (sub (sub (sub (mul lam lam)
            [(a : ℚ)]) x1) x2)) x1)) y1))) := by
        rw [hY, hsl, ev_rmod, ev_smul, ev_add, ev_mul, ev_sub, ev_rmod]
        simp only [ev_sub, ev_mul, ev_const]; push_cast; ring
      exact ⟨by rw [← hx3, ← hy3]; exact nonsingular_add hn1 hn2 hxy, by
        rw [Point.add_some hxy]; exact some_congr a b c hx3 hy3⟩
  · rw [if_neg hx]
    have hxK : ev f x1 ≠ ev f x2 := fun h ↦ hx ((ev_eq_iff _ _).mp h)
    have hd0 : ev f (sub x1 x2) ≠ 0 := by rw [ev_sub]; exact sub_ne_zero.mpr hxK
    have hinv := ev_modInv _ hd0
    have hxy : ¬(ev f x1 = ev f x2 ∧ ev f y1 = (W K a b c).toAffine.negY (ev f x2) (ev f y2)) :=
      fun h ↦ hxK h.1
    set lam := rmod f (mul (sub y1 y2) (EllAlgo.modInv (sub x1 x2) f)) with hlam
    have hsl : (W K a b c).toAffine.slope (ev f x1) (ev f x2) (ev f y1) (ev f y2) = ev f lam := by
      rw [slope_of_X_ne hxK, hlam, ev_rmod, ev_mul, ev_sub]
      rw [ev_sub] at hinv
      rw [div_eq_iff (sub_ne_zero.mpr hxK)]
      linear_combination (-(ev f y1 - ev f y2)) * hinv
    clear_value lam
    have hx3 : (W K a b c).toAffine.addX (ev f x1) (ev f x2)
        ((W K a b c).toAffine.slope (ev f x1) (ev f x2) (ev f y1) (ev f y2)) =
        ev f (rmod f (sub (sub (sub (mul lam lam) [(a : ℚ)]) x1) x2)) := by
      rw [hX, hsl, ev_rmod]; simp only [ev_sub, ev_mul, ev_const]; push_cast; ring
    have hy3 : (W K a b c).toAffine.addY (ev f x1) (ev f x2) (ev f y1)
        ((W K a b c).toAffine.slope (ev f x1) (ev f x2) (ev f y1) (ev f y2)) =
        ev f (rmod f (smul (-1) (add (mul lam (sub (rmod f (sub (sub (sub (mul lam lam)
          [(a : ℚ)]) x1) x2)) x1)) y1))) := by
      rw [hY, hsl, ev_rmod, ev_smul, ev_add, ev_mul, ev_sub, ev_rmod]
      simp only [ev_sub, ev_mul, ev_const]; push_cast; ring
    exact ⟨by rw [← hx3, ← hy3]; exact nonsingular_add hn1 hn2 hxy, by
      rw [Point.add_some hxy]; exact some_congr a b c hx3 hy3⟩

/-- **`mulPt` computes multiples.** -/
theorem mulPt_spec {o : Option (CPoly ℚ × CPoly ℚ)} {P : (W K a b c).toAffine.Point}
    (h : Rep a b c o P) : ∀ k : ℕ, Rep a b c (mulPt f a b c o k) (k • P)
  | 0 => by simp only [mulPt, Rep]; exact zero_nsmul P
  | k + 1 => by
    rw [succ_nsmul]
    exact addPt_spec a b c (mulPt_spec h k) h

/-- **The torsion test**: some multiple `(k + 1) P`, `k < N`, is the origin. -/
def torsionTestK (f : CPoly ℚ) (a b c : ℤ) (o : Option (CPoly ℚ × CPoly ℚ)) (N : ℕ) : Bool :=
  (List.range N).any fun k ↦ (mulPt f a b c o (k + 1)).isNone

/-- **The torsion test decides**: with `N` at least the reduction bound at a prime `p` (odd, good
reduction, `f` with a simple root modulo `p`), `torsionTestK` is `true` iff `P` has finite order. -/
theorem torsionTestK_spec {p : ℕ} [Fact p.Prime] (fZ : ℤ[X])
    (hfZ : toPoly f = fZ.map (Int.castRingHom ℚ)) (s : ZMod p)
    (hs : (fZ.map (Int.castRingHom (ZMod p))).eval s = 0)
    (hs' : ((derivative fZ).map (Int.castRingHom (ZMod p))).eval s ≠ 0)
    (hp2 : p ≠ 2) (hgood : goodRedMod p a b c)
    {o : Option (CPoly ℚ × CPoly ℚ)} {P : (W K a b c).toAffine.Point} (h : Rep a b c o P)
    (N : ℕ) (hN : Fintype.card (Option (RedPts p a b c)) ≤ N) :
    torsionTestK f a b c o N = true ↔ IsOfFinAddOrder P := by
  constructor
  · intro ht
    simp only [torsionTestK, List.any_eq_true, List.mem_range] at ht
    obtain ⟨k, -, hk⟩ := ht
    have hr := mulPt_spec a b c h (k + 1)
    rcases hm : mulPt f a b c o (k + 1) with _ | ⟨x, y⟩
    · rw [hm] at hr
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k + 1, k.succ_pos, hr⟩
    · rw [hm] at hk; simp at hk
  · intro ht
    have hb := torsion_order_le_adjoin a b (c := c) (toPoly f) fZ hfZ s hs hs' hp2 hgood P ht
    have hpos := ht.addOrderOf_pos
    simp only [torsionTestK, List.any_eq_true, List.mem_range]
    refine ⟨addOrderOf P - 1, by omega, ?_⟩
    have hr := mulPt_spec a b c h (addOrderOf P - 1 + 1)
    rw [Nat.sub_add_cancel hpos, addOrderOf_nsmul_eq_zero] at hr
    rw [Nat.sub_add_cancel hpos]
    rcases hm : mulPt f a b c o (addOrderOf P) with _ | ⟨x, y⟩
    · rfl
    · rw [hm] at hr
      obtain ⟨h', hh⟩ := hr
      exact absurd hh.symm (by simp)

end EllDV
