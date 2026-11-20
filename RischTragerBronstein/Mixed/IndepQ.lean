import RischTragerBronstein.Mixed.IndepLift
import RischTragerBronstein.Mixed.QIndepExists
import RischTragerBronstein.Mixed.QHeightExists

/-!
# The bottom of the recursion: curves over `ℚ`

`E_{a,b}` over `ℚ` is scaled to an integral model `y² = x³ + a' x + b'` (`qScale`: `a' = d⁴ a`,
`b' = d⁶ b`, `d` = product of the denominators); independence (infinite order) is certified by
`QHeight.certG` (`certH`) at some level `< kmax`. **`recQ_sound`**, **`recQ_complete`** (Néron–Tate
heights over `ℚ`, Northcott: `certG_exists`, `certH_exists`), and the one-point versions.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

/-- The integral scaling `(a', b', d)`. -/
def qScale (a b : ℚ) : ℤ × ℤ × ℚ :=
  (a.num * (a.den : ℤ) ^ 3 * (b.den : ℤ) ^ 4, b.num * (b.den : ℤ) ^ 5 * (a.den : ℤ) ^ 6,
    ((a.den : ℚ) * b.den))

lemma qScale_d (a b : ℚ) : (qScale a b).2.2 ≠ 0 := by
  simp only [qScale]; positivity

lemma qScale_a (a b : ℚ) : (((qScale a b).1 : ℤ) : ℚ) = (qScale a b).2.2 ^ 4 * a := by
  have h := Rat.mul_den_eq_num a
  simp only [qScale]; push_cast; rw [← h]; ring

lemma qScale_b (a b : ℚ) : (((qScale a b).2.1 : ℤ) : ℚ) = (qScale a b).2.2 ^ 6 * b := by
  have h := Rat.mul_den_eq_num b
  simp only [qScale]; push_cast; rw [← h]; ring

lemma qScale_disc (a b : ℚ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    4 * (qScale a b).1 ^ 3 + 27 * (qScale a b).2.1 ^ 2 ≠ 0 := by
  intro h0
  have h1 : ((4 * (qScale a b).1 ^ 3 + 27 * (qScale a b).2.1 ^ 2 : ℤ) : ℚ) = 0 := by
    rw [h0]; simp
  push_cast at h1
  rw [qScale_a, qScale_b] at h1
  have hd := qScale_d a b
  have : (qScale a b).2.2 ^ 12 * (4 * a ^ 3 + 27 * b ^ 2) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact hd (pow_eq_zero_iff (by norm_num) |>.mp h)
  · exact hΔ h

/-- **The two-point check over `ℚ`.** -/
def recQ (kmax : ℕ) (a b : ℚ) : Option (ℚ × ℚ) → Option (ℚ × ℚ) → Bool
  | some (x1, y1), some (x2, y2) =>
    let s := qScale a b
    (List.range kmax).any fun k ↦
      QHeight.certG s.1 s.2.1 k (s.2.2 ^ 2 * x1) (s.2.2 ^ 3 * y1) (s.2.2 ^ 2 * x2) (s.2.2 ^ 3 * y2)
  | _, _ => false

/-- **The one-point check over `ℚ`.** -/
def recQ1 (kmax : ℕ) (a b : ℚ) : Option (ℚ × ℚ) → Bool
  | some (x, _) =>
    let s := qScale a b
    (List.range kmax).any fun k ↦ QHeight.certH s.1 s.2.1 k (s.2.2 ^ 2 * x)
  | none => false

section Gen

variable {K' : Type*} [Field K']

open scoped Classical

lemma ne_zero_of_indL {W : WeierstrassCurve.Affine K'} {P Q : W.Point}
    (h : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) : P ≠ 0 := by
  intro h0; have := h 1 0 (by rw [h0]; simp); simp at this

lemma ne_zero_of_indR {W : WeierstrassCurve.Affine K'} {P Q : W.Point}
    (h : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) : Q ≠ 0 := by
  intro h0; have := h 0 1 (by rw [h0]; simp); simp at this

lemma ne_zero_of_nt {W : WeierstrassCurve.Affine K'} {P : W.Point}
    (h : ∀ n : ℤ, n • P = 0 → n = 0) : P ≠ 0 := by
  intro h0; have := h 1 (by rw [h0]; simp); simp at this

lemma sH_zsmul (a b a' b' u : K') (hu : u ≠ 0) (ha : a' = u ^ 4 * a) (hb : b' = u ^ 6 * b)
    (P : (shortF a b).toAffine.Point) (n : ℤ) :
    scaleHomEq a b a' b' u hu ha hb (n • P) = n • scaleHomEq a b a' b' u hu ha hb P :=
  map_zsmul _ _ _

lemma sH_zero (a b a' b' u : K') (hu : u ≠ 0) (ha : a' = u ^ 4 * a) (hb : b' = u ^ 6 * b) :
    scaleHomEq a b a' b' u hu ha hb 0 = 0 := map_zero _

lemma inst_irrel {W : WeierstrassCurve.Affine K'} (i j : DecidableEq K') (P Q : W.Point) (m n : ℤ) :
    (letI : DecidableEq K' := i; m • P = n • Q) ↔ (letI : DecidableEq K' := j; m • P = n • Q) := by
  obtain rfl : i = j := Subsingleton.elim _ _; rfl

lemma inst_irrel0 {W : WeierstrassCurve.Affine K'} (i j : DecidableEq K') (P : W.Point) (n : ℤ) :
    (letI : DecidableEq K' := i; n • P = 0) ↔ (letI : DecidableEq K' := j; n • P = 0) := by
  obtain rfl : i = j := Subsingleton.elim _ _; rfl

lemma inst_irrel0N {W : WeierstrassCurve.Affine K'} (i j : DecidableEq K') (P : W.Point) (n : ℕ) :
    (letI : DecidableEq K' := i; n • P = 0) ↔ (letI : DecidableEq K' := j; (n : ℤ) • P = 0) := by
  obtain rfl : i = j := Subsingleton.elim _ _; rw [natCast_zsmul]

end Gen

open scoped Classical

/-- The scaled curve. -/
abbrev qWs (a b : ℚ) : WeierstrassCurve.Affine ℚ :=
  (shortF (((qScale a b).1 : ℤ) : ℚ) (((qScale a b).2.1 : ℤ) : ℚ)).toAffine

local notation "cI" => (fun a b : ℚ ↦ Classical.propDecidable (a = b))

local notation "qH" a:max b:max =>
  scaleHomEq a b _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b)

/-- **Soundness over `ℚ`.** -/
theorem recQ_sound : RecS recQ := by
  intro k a b p q h hΔ P Q hP hQ m n hmn
  rcases p with _ | ⟨x1, y1⟩ <;> rcases q with _ | ⟨x2, y2⟩ <;> simp only [recQ] at h <;>
    try exact absurd h (by decide)
  rcases P with _ | ⟨x1', y1', h1⟩
  · exact absurd hP (by simp [RelC])
  rcases Q with _ | ⟨x2', y2', h2⟩
  · exact absurd hQ (by simp [RelC])
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨rfl, rfl⟩ := hQ
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨kk, -, hc⟩ := h
  obtain ⟨g1, e1⟩ := scaleHomEq_some _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b) h1
  obtain ⟨g2, e2⟩ := scaleHomEq_some _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b) h2
  have hrel := congrArg (qH a b) hmn
  rw [sH_zsmul, sH_zsmul, e1, e2] at hrel
  exact QHeight.indepQ_of_certG _ _ (qScale_disc a b hΔ) kk _ _ _ _ g1 g2 hc m n
    ((inst_irrel (W := qWs a b) instDecidableEqRat cI _ _ m n).mpr hrel)

/-- **Soundness over `ℚ`, one point.** -/
theorem recQ1_sound : RecS1 recQ1 := by
  intro k a b p h hΔ P hP n hn
  rcases p with _ | ⟨x1, y1⟩ <;> simp only [recQ1] at h <;> try exact absurd h (by decide)
  rcases P with _ | ⟨x1', y1', h1⟩
  · exact absurd hP (by simp [RelC])
  obtain ⟨rfl, rfl⟩ := hP
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨kk, -, hc⟩ := h
  obtain ⟨g1, e1⟩ := scaleHomEq_some _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b) h1
  have hrel := congrArg (qH a b) hn
  rw [sH_zsmul, e1, sH_zero] at hrel
  exact QHeight.nontors_of_certH _ _ (qScale_disc a b hΔ) kk _ _ g1 hc n
    ((inst_irrel0 (W := qWs a b) instDecidableEqRat cI _ n).mpr hrel)

/-- **Completeness over `ℚ`.** -/
theorem recQ_complete : RecC recQ := by
  intro a b p q P Q hΔ hP hQ hind
  rcases P with _ | ⟨x1, y1, h1⟩
  · exact absurd rfl (ne_zero_of_indL hind)
  rcases Q with _ | ⟨x2, y2, h2⟩
  · exact absurd rfl (ne_zero_of_indR hind)
  rcases p with _ | ⟨x1', y1'⟩
  · exact absurd hP (by simp [RelC])
  rcases q with _ | ⟨x2', y2'⟩
  · exact absurd hQ (by simp [RelC])
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨rfl, rfl⟩ := hQ
  obtain ⟨g1, e1⟩ := scaleHomEq_some _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b) h1
  obtain ⟨g2, e2⟩ := scaleHomEq_some _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b) h2
  obtain ⟨kk, hk⟩ := QHeight.certG_exists _ _ (qScale_disc a b hΔ) _ _ _ _ g1 g2 (by
    intro m n hmn
    apply hind m n
    apply scaleHomEq_injective _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b)
    rw [sH_zsmul, sH_zsmul, e1, e2]
    exact (inst_irrel (W := qWs a b) instDecidableEqRat cI _ _ m n).mp hmn)
  refine ⟨kk + 1, fun k hk' ↦ ?_⟩
  simp only [recQ, List.any_eq_true, List.mem_range]
  exact ⟨kk, by omega, hk⟩

/-- **Completeness over `ℚ`, one point.** -/
theorem recQ1_complete : RecC1 recQ1 := by
  intro a b p P hΔ hP hnt
  rcases P with _ | ⟨x1, y1, h1⟩
  · exact absurd rfl (ne_zero_of_nt hnt)
  rcases p with _ | ⟨x1', y1'⟩
  · exact absurd hP (by simp [RelC])
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨g1, e1⟩ := scaleHomEq_some _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b) h1
  obtain ⟨kk, hk⟩ := QHeight.certH_exists _ _ _ _ g1 (by
    intro n hn hz
    have := hnt n (by
      apply scaleHomEq_injective _ _ _ _ _ (qScale_d a b) (qScale_a a b) (qScale_b a b)
      rw [sH_zsmul, e1, sH_zero]
      exact (inst_irrel0N (W := qWs a b) instDecidableEqRat cI _ n).mp hz)
    omega)
  refine ⟨kk + 1, fun k hk' ↦ ?_⟩
  simp only [recQ1, List.any_eq_true, List.mem_range]
  exact ⟨kk, by omega, hk⟩

end FFHeight
