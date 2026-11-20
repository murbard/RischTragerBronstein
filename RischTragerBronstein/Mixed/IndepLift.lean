import RischTragerBronstein.Mixed.IndepStep2

/-!
# Lifting a curve over `K` to a polynomial short model over `K'(X)`

Given an embedding `K → K'(X)` (an `Algebra` instance) with executable codes `fr : K → Fr K'`
(`ok`, value = the embedding), the curve `E_{a,b}` over `K` is mapped to the polynomial model
`y² = x³ + A x + B`, `A = d⁴ a`, `B = d⁶ b` (`d` = product of the denominators of `a`, `b`), by the
injective hom `ΛL` (base change, then scaling by `d`). Point codes are mapped by `liftPt`.

`lvlI` / `lvlI1`: the step `stepI` / `stepI1` on the lifted data. **`lvlI_sound`**, **`lvlI_complete`**
(and one-point versions) transport soundness and completeness from the step to the curve over `K`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine CPoly

namespace FFHeight

section Lift

variable {K K' : Type*} [Field K] [Field K'] [DecidableEq K'] [CharZero K'] [Algebra K (RatFunc K')]

local notation "ι" => algebraMap K'[X] (RatFunc K')
local notation "τL" => algebraMap K (RatFunc K')

/-- **The lifted polynomial model** `(A, B, d)`. -/
def liftM (fr : K → Fr K') (a b : K) : CPoly K' × CPoly K' × CPoly K' :=
  let fa := fr a
  let fb := fr b
  (mul fa.1 (mul (powCR fa.2 3) (powCR fb.2 4)), mul fb.1 (mul (powCR fb.2 5) (powCR fa.2 6)),
    mul fa.2 fb.2)

/-- **Lifted point codes.** -/
def liftPt (fr : K → Fr K') (d : CPoly K') : Option (K × K) → PtC K'
  | none => none
  | some (x, y) => some ((mul (fr x).1 (powCR d 2), (fr x).2), (mul (fr y).1 (powCR d 3), (fr y).2))

/-- The step on the lifted data. -/
def lvlI (fr : K → Fr K') (isRat : K' → Bool)
    (rec : ℕ → K' → K' → Option (K' × K') → Option (K' × K') → Bool) (kmax : ℕ) (a b : K)
    (p q : Option (K × K)) : Bool :=
  let M := liftM fr a b
  stepI isRat rec kmax M.1 M.2.1 (liftPt fr M.2.2 p) (liftPt fr M.2.2 q)

/-- The one-point step on the lifted data. -/
def lvlI1 (fr : K → Fr K') (rec1 : ℕ → K' → K' → Option (K' × K') → Bool) (kmax : ℕ) (a b : K)
    (p : Option (K × K)) : Bool :=
  let M := liftM fr a b
  stepI1 rec1 kmax M.1 M.2.1 (liftPt fr M.2.2 p)

open scoped Classical

lemma shortF_baseChangeL (a b : K) :
    ((shortF a b).toAffine⁄(RatFunc K')) = (shortF (τL a) (τL b)).toAffine := by
  simp [shortF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- The base change `E_{a,b}(K) → E_{a,b}(K'(X))`. -/
noncomputable def ιL (a b : K) :
    (shortF a b).toAffine.Point →+ (shortF (τL a) (τL b)).toAffine.Point :=
  have hself : (shortF a b).toAffine = ((shortF a b).toAffine⁄K) := by
    simp [shortF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  (castHom (shortF_baseChangeL a b)).comp
    ((Point.map (W' := (shortF a b).toAffine) (Algebra.ofId K (RatFunc K'))).comp (castHom hself))

lemma ιL_injective (a b : K) : Function.Injective (ιL (K' := K') a b) :=
  (castHom_injective _).comp ((Point.map_injective _).comp (castHom_injective _))

lemma ιL_some (a b : K) (x y : K) (h : (shortF a b).toAffine.Nonsingular x y) :
    ∃ h', ιL (K' := K') a b (Point.some x y h) = Point.some (τL x) (τL y) h' := by
  unfold ιL
  simp only [AddMonoidHom.comp_apply]
  erw [castHom_some]
  refine ⟨?w, ?e⟩
  case e => rfl
  case w =>
    rw [← shortF_baseChangeL]
    exact (Affine.map_nonsingular (W := (shortF a b).toAffine) (algebraMap K (RatFunc K')).injective
      x y).mpr h

variable (fr : K → Fr K') (hfr : ∀ z : K, Fr.ok (fr z) ∧ Fr.val (fr z) = algebraMap K (RatFunc K') z)
include hfr

lemma liftM_d (a b : K) : toPoly (liftM fr a b).2.2 ≠ 0 := by
  simp only [liftM, toPoly_mul]; exact mul_ne_zero (hfr a).1 (hfr b).1

lemma liftM_A (a b : K) :
    ι (toPoly (liftM fr a b).1) = ι (toPoly (liftM fr a b).2.2) ^ 4 * τL a := by
  have ha := (hfr a).2; have hb := (hfr b).2
  have h1 := Fr.ι_ne (hfr a).1; have h2 := Fr.ι_ne (hfr b).1
  simp only [Fr.val] at ha hb
  simp only [liftM, toPoly_mul, toPoly_powCR, map_mul, map_pow]
  rw [← ha]; field_simp

lemma liftM_B (a b : K) :
    ι (toPoly (liftM fr a b).2.1) = ι (toPoly (liftM fr a b).2.2) ^ 6 * τL b := by
  have ha := (hfr a).2; have hb := (hfr b).2
  have h1 := Fr.ι_ne (hfr a).1; have h2 := Fr.ι_ne (hfr b).1
  simp only [Fr.val] at ha hb
  simp only [liftM, toPoly_mul, toPoly_powCR, map_mul, map_pow]
  rw [← hb]; field_simp

lemma liftM_disc (a b : K) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    4 * toPoly (liftM fr a b).1 ^ 3 + 27 * toPoly (liftM fr a b).2.1 ^ 2 ≠ 0 := by
  intro h0
  have hd := Fr.ι_ne (liftM_d fr hfr a b)
  have := congrArg ι h0
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero, liftM_A fr hfr, liftM_B fr hfr] at this
  have e : ι (toPoly (liftM fr a b).2.2) ^ 12 * τL (4 * a ^ 3 + 27 * b ^ 2) = 0 := by
    simp only [map_add, map_mul, map_pow, map_ofNat]; linear_combination this
  rcases mul_eq_zero.mp e with h | h
  · exact hd (pow_eq_zero_iff (by norm_num) |>.mp h)
  · exact hΔ ((map_eq_zero_iff _ (algebraMap K (RatFunc K')).injective).mp h)

/-- **The lift of points.** -/
noncomputable def ΛL (a b : K) :
    (shortF a b).toAffine.Point →+
      (shortW (toPoly (liftM fr a b).1) (toPoly (liftM fr a b).2.1)).toAffine.Point :=
  (castHom (shortW_eq_shortF _ _).symm).comp
    ((scaleHomEq (τL a) (τL b) _ _ _ (Fr.ι_ne (liftM_d fr hfr a b)) (liftM_A fr hfr a b)
      (liftM_B fr hfr a b)).comp (ιL a b))

lemma ΛL_injective (a b : K) : Function.Injective (ΛL fr hfr a b) := by
  intro P Q h
  unfold ΛL at h
  simp only [AddMonoidHom.comp_apply] at h
  exact ιL_injective a b (scaleHomEq_injective _ _ _ _ _ _ _ _ (castHom_injective _ h))

lemma rel_ΛL (a b : K) (p : Option (K × K)) (P : (shortF a b).toAffine.Point) (hR : RelC a b p P) :
    Rel _ _ (liftPt fr (liftM fr a b).2.2 p) (ΛL fr hfr a b P) := by
  rcases p with _ | ⟨x, y⟩ <;> rcases P with _ | ⟨x', y', h⟩
  · show Rel _ _ none (ΛL fr hfr a b 0); rw [map_zero]; trivial
  · exact absurd hR (by simp [RelC])
  · exact absurd hR (by simp [RelC])
  obtain ⟨rfl, rfl⟩ := hR
  obtain ⟨h1, e1⟩ := ιL_some (K' := K') a b x y h
  obtain ⟨h2, e2⟩ := scaleHomEq_some (τL a) (τL b) _ _ _ (Fr.ι_ne (liftM_d fr hfr a b))
    (liftM_A fr hfr a b) (liftM_B fr hfr a b) h1
  have e : ∃ h', ΛL fr hfr a b (Point.some x y h) = Point.some
      (ι (toPoly (liftM fr a b).2.2) ^ 2 * τL x) (ι (toPoly (liftM fr a b).2.2) ^ 3 * τL y) h' := by
    unfold ΛL; simp only [AddMonoidHom.comp_apply]; rw [e1, e2, castHom_some]; exact ⟨h2, rfl⟩
  obtain ⟨h', e⟩ := e
  rw [e]
  have hd := liftM_d fr hfr a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hfr x).1
  · exact (hfr y).1
  · simp only [Fr.val, toPoly_mul, toPoly_powCR, map_mul, map_pow]
    rw [← (hfr x).2]; simp only [Fr.val]; ring
  · simp only [Fr.val, toPoly_mul, toPoly_powCR, map_mul, map_pow]
    rw [← (hfr y).2]; simp only [Fr.val]; ring

end Lift

section Transfer

variable {K K' : Type*} [Field K] [CharZero K] [Field K'] [DecidableEq K'] [CharZero K']
  [Algebra K (RatFunc K')]

/-- Soundness predicate of a recursive two-point check. -/
def RecS {K₀ : Type*} [Field K₀] [CharZero K₀]
    (rec : ℕ → K₀ → K₀ → Option (K₀ × K₀) → Option (K₀ × K₀) → Bool) : Prop :=
  ∀ k a b p q, rec k a b p q = true → 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → IndC a b p q

/-- Soundness predicate of a recursive one-point check. -/
def RecS1 {K₀ : Type*} [Field K₀] [CharZero K₀] (rec1 : ℕ → K₀ → K₀ → Option (K₀ × K₀) → Bool) :
    Prop :=
  ∀ k a b p, rec1 k a b p = true → 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → NTC a b p

open scoped Classical

variable (fr : K → Fr K') (hfr : ∀ z : K, Fr.ok (fr z) ∧ Fr.val (fr z) = algebraMap K (RatFunc K') z)
include hfr

/-- **Soundness of a level.** -/
theorem lvlI_sound {isRat : K' → Bool} (hRat : ∀ q : ℚ, isRat (q : K') = true)
    {rec : ℕ → K' → K' → Option (K' × K') → Option (K' × K') → Bool} (hrec : RecS rec) :
    RecS (lvlI fr isRat rec) := by
  intro kmax a b p q h hΔ P Q hP hQ m n hmn
  exact stepI_sound hRat hrec kmax _ _ _ _ (liftM_disc fr hfr a b hΔ) (ΛL fr hfr a b P)
    (ΛL fr hfr a b Q) (rel_ΛL fr hfr a b p P hP) (rel_ΛL fr hfr a b q Q hQ) h m n
    (by rw [← map_zsmul, ← map_zsmul, hmn])

/-- **Soundness of a one-point level.** -/
theorem lvlI1_sound {rec1 : ℕ → K' → K' → Option (K' × K') → Bool} (hrec : RecS1 rec1) :
    RecS1 (lvlI1 fr rec1) := by
  intro kmax a b p h hΔ P hP n hn
  exact stepI1_sound hrec kmax _ _ _ (liftM_disc fr hfr a b hΔ) (ΛL fr hfr a b P)
    (rel_ΛL fr hfr a b p P hP) h n (by rw [← map_zsmul, hn, map_zero])

/-- **Completeness of a level.** -/
theorem lvlI_complete (hM : Manin.MKT K') {isRat : K' → Bool}
    (hRat : ∀ x, isRat x = true ↔ ∃ q : ℚ, x = q)
    {rec : ℕ → K' → K' → Option (K' × K') → Option (K' × K') → Bool} (hrec : RecC rec) :
    RecC (lvlI fr isRat rec) := by
  intro a b p q P Q hΔ hP hQ hind
  exact stepI_complete hM hRat hrec _ _ _ _ (liftM_disc fr hfr a b hΔ) (ΛL fr hfr a b P)
    (ΛL fr hfr a b Q) (rel_ΛL fr hfr a b p P hP) (rel_ΛL fr hfr a b q Q hQ) (fun m n h ↦
      hind m n (ΛL_injective fr hfr a b (by rw [map_zsmul, map_zsmul]; exact h)))

/-- **Completeness of a one-point level.** -/
theorem lvlI1_complete (hM : Manin.MKT K')
    {rec1 : ℕ → K' → K' → Option (K' × K') → Bool} (hrec : RecC1 rec1) :
    RecC1 (lvlI1 fr rec1) := by
  intro a b p P hΔ hP hnt
  exact stepI1_complete hM hrec _ _ _ (liftM_disc fr hfr a b hΔ) (ΛL fr hfr a b P)
    (rel_ΛL fr hfr a b p P hP) (fun n h ↦
      hnt n (ΛL_injective fr hfr a b (by rw [map_zsmul, map_zero]; exact h)))

end Transfer

end FFHeight
