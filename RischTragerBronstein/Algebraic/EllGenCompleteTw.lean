import RischTragerBronstein.Algebraic.EllGenComplete

/-!
# Completeness of the twisted front end and of the dispatcher

If all roots `α` of the (split) denominator `D` off the branch points have `p(α)` in one class
`d₀ · ℚ²`, `ellDecideAny` answers (with `fuelAny` fuel): either all residues vanish (then
`ellDecideGen` answers), or the first non-zero one fixes the twist and `ellDecideGenTw` answers.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- The twist attached to a root `α`. -/
def twistOf (a b c : ℤ) (α : ℚ) : ℤ :=
  (residuePts.evalQ (pOf a b c) α).num * (residuePts.evalQ (pOf a b c) α).den

/-- **Enough fuel for `ellDecideAny`**: the untwisted bound and the bound of every candidate
twist. -/
def fuelAny (a b c : ℤ) (D : CPoly ℚ) : ℕ :=
  (ratRootsQ D).foldr (fun α m ↦ max m (EllNL.fuelBound (a * twistOf a b c α)
    (b * twistOf a b c α ^ 2) (c * twistOf a b c α ^ 3))) (EllNL.fuelBound a b c)

lemma le_foldr_max (f : ℚ → ℕ) (z : ℕ) : ∀ l : List ℚ,
    z ≤ l.foldr (fun α m ↦ max m (f α)) z ∧ ∀ α ∈ l, f α ≤ l.foldr (fun α m ↦ max m (f α)) z
  | [] => ⟨le_rfl, by simp⟩
  | β :: t => by
    obtain ⟨h1, h2⟩ := le_foldr_max f z t
    rw [List.foldr_cons]
    refine ⟨h1.trans (le_max_left _ _), fun α hα ↦ ?_⟩
    rcases List.mem_cons.mp hα with rfl | h
    · exact le_max_right _ _
    · exact (h2 α h).trans (le_max_left _ _)

lemma fuelBound_le_fuelAny (a b c : ℤ) (D : CPoly ℚ) : EllNL.fuelBound a b c ≤ fuelAny a b c D :=
  (le_foldr_max _ _ _).1

lemma fuelTw_le_fuelAny (a b c : ℤ) (D : CPoly ℚ) {α : ℚ} (hα : α ∈ ratRootsQ D) :
    EllNL.fuelBound (a * twistOf a b c α) (b * twistOf a b c α ^ 2) (c * twistOf a b c α ^ 3) ≤
      fuelAny a b c D :=
  (le_foldr_max (fun α ↦ EllNL.fuelBound (a * twistOf a b c α) (b * twistOf a b c α ^ 2)
    (c * twistOf a b c α ^ 3)) _ _).2 α hα

lemma twist_val (v : ℚ) : ((v.num * v.den : ℤ) : ℚ) = v * (v.den : ℚ) ^ 2 := by
  rw [sq, ← mul_assoc, Rat.mul_den_eq_num]; push_cast; ring

/-- **The twisted residue step** succeeds when the residues lie over one quadratic class. -/
lemma residuePtsTw_ok (p : CPoly ℚ) (αs cs : List ℚ) (q₀ : ℚ × ℚ) (rest : List (ℚ × ℚ))
    (hdata : ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) = q₀ :: rest)
    (hnz : ∀ q ∈ q₀ :: rest, residuePts.evalQ p q.1 ≠ 0)
    (hcls : ∀ q ∈ q₀ :: rest, ∃ γ : ℚ, residuePts.evalQ p q.1 = residuePts.evalQ p q₀.1 * γ ^ 2) :
    ∃ pts D', residuePtsTw p αs cs = some (pts, D',
        (residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den) ∧ D' ≠ 0 ∧
      (∀ q ∈ pts, (((residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den : ℤ) : ℚ) *
        q.2.1 ^ 2 = residuePts.evalQ p q.1 ∧ q.2.1 ≠ 0) ∧
      pts.map Prod.fst = (q₀ :: rest).map Prod.fst ∧
      ((twPts ((residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den) pts).map
        fun q ↦ ((q.2.2 : ℚ) / D' * q.2.1, q.1)) = (q₀ :: rest).map fun q ↦ (q.2, q.1) := by
  have h0 := hnz q₀ List.mem_cons_self
  set v₀ := residuePts.evalQ p q₀.1
  set d : ℤ := v₀.num * v₀.den with hd
  have hdv : (d : ℚ) = v₀ * (v₀.den : ℚ) ^ 2 := twist_val v₀
  have hden : (v₀.den : ℚ) ≠ 0 := by exact_mod_cast v₀.den_ne_zero
  have hd0q : (d : ℚ) ≠ 0 := by rw [hdv]; exact mul_ne_zero h0 (pow_ne_zero _ hden)
  have hd0 : d ≠ 0 := by exact_mod_cast hd0q
  set data := q₀ :: rest
  set gf : ℚ × ℚ → ℚ := fun q ↦ (qsqrt (residuePts.evalQ p q.1 / d)).getD 1
  have hgf : ∀ q ∈ data, qsqrt (residuePts.evalQ p q.1 / d) = some (gf q) ∧
      (d : ℚ) * gf q ^ 2 = residuePts.evalQ p q.1 ∧ gf q ≠ 0 := fun q hq ↦ by
    obtain ⟨γ, hγ⟩ := hcls q hq
    have hval : residuePts.evalQ p q.1 / d = (γ / v₀.den) ^ 2 := by
      rw [hγ, hdv]; field_simp
    have hs := qsqrt_sq (γ / v₀.den)
    rw [← hval] at hs
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hs
    have hg2 := qsqrt_spec hg
    have hq0 := hnz q hq
    refine ⟨by simp [gf, hg], ?_, ?_⟩
    · simp only [gf, hg, Option.getD_some]; rw [hg2]; field_simp
    · simp only [gf, hg, Option.getD_some]
      rintro rfl
      apply hq0
      have : residuePts.evalQ p q.1 / d = 0 := by rw [← hg2]; ring
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h hd0q
  set D' := (data.map fun q ↦ (q.2 / (gf q * d)).den).foldr Nat.lcm 1 with hD'
  have hD'0 : D' ≠ 0 := foldr_lcm_ne_zero _ fun a ha ↦ by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; exact Rat.den_ne_zero _
  unfold residuePtsTw
  simp only
  rw [hdata]
  simp only [data]
  rw [← hd, if_pos]
  swap
  · refine ⟨hd0, ?_⟩
    rw [List.all_eq_true]
    intro o ho
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
    obtain ⟨h1, -, h3⟩ := hgf q hq
    rw [h1]; simpa using h3
  refine ⟨_, _, rfl, ?_⟩
  rw [zip_map_self]
  simp only [List.map_map, Function.comp_def]
  have hD'eq : (data.map fun x ↦ (x.2 / ((qsqrt (residuePts.evalQ p x.1 / d)).getD 1 * d)).den) =
      data.map fun q ↦ (q.2 / (gf q * d)).den := rfl
  rw [hD'eq, ← hD']
  unfold twPts
  simp only [List.map_map, Function.comp_def]
  refine ⟨hD'0, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨-, h2, h3⟩ := hgf r hr
    exact ⟨h2, h3⟩
  · trivial
  · refine List.map_congr_left fun q hq ↦ ?_
    obtain ⟨-, -, h3⟩ := hgf q hq
    have hdvd : (q.2 / (gf q * d)).den ∣ D' := dvd_foldr_lcm (List.mem_map_of_mem hq)
    have hq1 : (qsqrt (residuePts.evalQ p q.1 / d)).getD 1 = gf q := rfl
    simp only [hq1, Prod.mk.injEq, and_true]
    rw [num_mul_of_den_dvd _ _ hdvd]
    have : (D' : ℚ) ≠ 0 := by exact_mod_cast hD'0
    field_simp

lemma ellDecideGenTw_ne_none_of (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (W B₀ : CPoly ℚ) (αs cs : List ℚ)
    (hH : ellHermiteRaw (pOf a b c) A D = some (W, B₀, αs, cs)) (q₀ : ℚ × ℚ)
    (rest : List (ℚ × ℚ)) (hdata : ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) = q₀ :: rest)
    (hnz : ∀ q ∈ q₀ :: rest, residuePts.evalQ (pOf a b c) q.1 ≠ 0)
    (hcls : ∀ q ∈ q₀ :: rest, ∃ γ : ℚ, residuePts.evalQ (pOf a b c) q.1 =
      residuePts.evalQ (pOf a b c) q₀.1 * γ ^ 2)
    (fuel : ℕ) (hfuel : EllNL.fuelBound (a * twistOf a b c q₀.1) (b * twistOf a b c q₀.1 ^ 2)
      (c * twistOf a b c q₀.1 ^ 3) ≤ fuel) :
    ellDecideGenTw a b c A D fuel ≠ none := by
  obtain ⟨hαs, hl, hid⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  have hnd : αs.Nodup := hαs ▸ (List.nodup_dedup _).filter _
  obtain ⟨pts, D', hR, hD'0, hon, hfst, hres⟩ :=
    residuePtsTw_ok (pOf a b c) αs cs q₀ rest hdata hnz hcls
  have hd0 : twistOf a b c q₀.1 ≠ 0 := by
    intro h
    have h' : ((twistOf a b c q₀.1 : ℤ) : ℚ) = 0 := by rw [h]; simp
    rw [twistOf, twist_val] at h'
    have hden : ((residuePts.evalQ (pOf a b c) q₀.1).den : ℚ) ≠ 0 := by
      exact_mod_cast (residuePts.evalQ (pOf a b c) q₀.1).den_ne_zero
    exact mul_ne_zero (hnz q₀ List.mem_cons_self) (pow_ne_zero 2 hden) h'
  rw [← hdata] at hres hfst
  obtain ⟨hG2, hG⟩ := fracG_poly B₀ D' _ αs cs hl (by rw [hres])
  have hchk := genCheck_of_poly (pOf a b c) A D W B₀ _ αs cs hD hG2 hid hG
  unfold ellDecideGenTw
  rw [hH]
  dsimp only
  rw [hR]
  dsimp only
  rw [if_pos hchk]
  refine ellDecideTw_ne_none a b c _ hd0 hsq B₀ pts (fun q hq ↦ ?_) ?_ D' hD'0 fuel hfuel
  · obtain ⟨h1, h2⟩ := hon q hq
    exact ⟨by rw [← evalQ_pOf]; exact h1, h2⟩
  · rw [hfst]; exact nodup_data αs cs hnd hl

/-- **Completeness of the dispatcher**: for a split denominator whose roots `α` (off the branch
points) have `p(α)` in one quadratic class `d₀ · ℚ²`, `ellDecideAny` answers with `fuelAny`
fuel. -/
theorem ellDecideAny_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hcls : ∃ d₀ : ℚ, ∀ α : ℚ, (toPoly D).eval α = 0 → α ^ 3 + a * α ^ 2 + b * α + c ≠ 0 →
      ∃ γ : ℚ, α ^ 3 + a * α ^ 2 + b * α + c = d₀ * γ ^ 2)
    (fuel : ℕ) (hfuel : fuelAny a b c D ≤ fuel) :
    ellDecideAny a b c A D fuel ≠ none := by
  obtain ⟨d₀, hd₀⟩ := hcls
  obtain ⟨hsqP, hp1⟩ := sq_pOf a b c hsq
  obtain ⟨⟨W, B₀, αs, cs⟩, hH⟩ := Option.ne_none_iff_exists'.mp
    (ellHermiteRaw_ne_none (pOf a b c) A D hsqP hp1 hD hsplit)
  obtain ⟨hαs, -, -⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  -- facts about the poles
  have hpole : ∀ q ∈ αs.zip cs, (toPoly D).eval q.1 = 0 ∧
      residuePts.evalQ (pOf a b c) q.1 ≠ 0 ∧ q.1 ∈ ratRootsQ D := fun q hq ↦ by
    have hα := (List.of_mem_zip hq).1
    obtain ⟨h1, h2⟩ := mem_αs (hαs ▸ hα)
    refine ⟨h1, by rw [evalQ_eq']; exact h2, ?_⟩
    rw [hαs, List.mem_filter, List.mem_dedup] at hα
    exact hα.1
  unfold ellDecideAny
  split
  · simp
  rename_i hG
  rcases hdata : ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) with _ | ⟨q₀, rest⟩
  · exfalso
    refine ellDecideGen_ne_none_of a b c hsq A D hD W B₀ αs cs hH (fun q hq hq0 ↦ ?_) fuel
      ((fuelBound_le_fuelAny a b c D).trans hfuel) hG
    have : q ∈ ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) := List.mem_filter.mpr ⟨hq, by simpa using hq0⟩
    rw [hdata] at this; simp at this
  · have hmem : ∀ q ∈ q₀ :: rest, q ∈ αs.zip cs := fun q hq ↦ by
      rw [← hdata] at hq; exact (List.mem_filter.mp hq).1
    have hnz : ∀ q ∈ q₀ :: rest, residuePts.evalQ (pOf a b c) q.1 ≠ 0 :=
      fun q hq ↦ (hpole q (hmem q hq)).2.1
    have hγ : ∀ q ∈ q₀ :: rest, ∃ γ : ℚ, residuePts.evalQ (pOf a b c) q.1 = d₀ * γ ^ 2 :=
      fun q hq ↦ by
        obtain ⟨h1, h2, -⟩ := hpole q (hmem q hq)
        rw [evalQ_pOf] at h2 ⊢
        exact hd₀ q.1 h1 h2
    refine ellDecideGenTw_ne_none_of a b c hsq A D hD W B₀ αs cs hH q₀ rest hdata hnz
      (fun q hq ↦ ?_) fuel ((fuelTw_le_fuelAny a b c D
        (hpole q₀ (hmem q₀ List.mem_cons_self)).2.2).trans hfuel)
    obtain ⟨γ, hγq⟩ := hγ q hq
    obtain ⟨γ₀, hγ₀⟩ := hγ q₀ List.mem_cons_self
    have hγ₀0 : γ₀ ≠ 0 := by
      rintro rfl; exact hnz q₀ List.mem_cons_self (by rw [hγ₀]; ring)
    refine ⟨γ / γ₀, ?_⟩
    rw [hγq, hγ₀]
    field_simp

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for `∫ A / (D √p)` with residues in one twist class**
(`p = x³ + ax² + bx + c` squarefree, `D` split over `ℚ`, `p(α) ∈ d₀ ℚ²` at every root `α` of `D`
off the branch points): `ellDecideAny` answers `some b`, and `b = true` iff the integral is
elementary. -/
theorem ellDecideAny_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hcls : ∃ d₀ : ℚ, ∀ α : ℚ, (toPoly D).eval α = 0 → α ^ 3 + a * α ^ 2 + b * α + c ≠ 0 →
      ∃ γ : ℚ, α ^ 3 + a * α ^ 2 + b * α + c = d₀ * γ ^ 2) :
    ∃ ans : Bool, ellDecideAny a b c A D (fuelAny a b c D) = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideAny_ne_none a b c hsq A D hD hsplit hcls _ le_rfl)
  exact ⟨ans, hans, ellDecideAny_spec hC hCall x y hx a b c hsq hy hgen A D _ ans hans⟩

end Decision

end EllAlgo
