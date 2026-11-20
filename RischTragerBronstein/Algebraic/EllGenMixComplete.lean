import RischTragerBronstein.Algebraic.EllGenMix
import RischTragerBronstein.Algebraic.EllGenCompleteTw

/-!
# Completeness of the two-class front end

If the values `p(α)` at the roots `α` of the split denominator `D` (off the branch points) lie in
at most two quadratic classes, `ellDecideAll` answers with `fuelAny` fuel (`ellDecideAll_decides`):
either all residues vanish or lie in one class (`ellDecideAny`), or `residuePtsMix` splits them into
the class of the first one and the rest, and `ellDecideMix` answers.
-/

open Polynomial

namespace EllAlgo

open CPoly

lemma inCls_true {p : CPoly ℚ} {d : ℤ} {q : ℚ × ℚ} (h : inCls p d q = true) (hd : (d : ℚ) ≠ 0) :
    ∃ g : ℚ, qsqrt (residuePts.evalQ p q.1 / d) = some g ∧
      (d : ℚ) * g ^ 2 = residuePts.evalQ p q.1 ∧ g ≠ 0 := by
  unfold inCls at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp h1
  refine ⟨g, hg, ?_, ?_⟩
  · rw [qsqrt_spec hg]; field_simp
  · rintro rfl; rw [hg] at h2; simp at h2

lemma inCls_of {p : CPoly ℚ} {d : ℤ} {q : ℚ × ℚ} (hd : (d : ℚ) ≠ 0) (g : ℚ)
    (hg : residuePts.evalQ p q.1 = d * g ^ 2) (hv : residuePts.evalQ p q.1 ≠ 0) :
    inCls p d q = true := by
  have hval : residuePts.evalQ p q.1 / d = g ^ 2 := by rw [hg]; field_simp
  have hs := qsqrt_sq g
  rw [← hval] at hs
  obtain ⟨g', hg'⟩ := Option.isSome_iff_exists.mp hs
  have h2 := qsqrt_spec hg'
  unfold inCls
  rw [hg']
  simp only [Option.isSome_some, Bool.true_and, bne_iff_ne, ne_eq, Option.some.injEq]
  rintro rfl
  apply hv
  have : residuePts.evalQ p q.1 / d = 0 := by rw [← h2]; ring
  rcases div_eq_zero_iff.mp this with h | h
  · exact h
  · exact absurd h hd

lemma twist_ne_zero (v : ℚ) (hv : v ≠ 0) : ((v.num * v.den : ℤ) : ℚ) ≠ 0 := by
  rw [twist_val]
  exact mul_ne_zero hv (pow_ne_zero _ (by exact_mod_cast v.den_ne_zero))

/-- **The two-class residue step succeeds** when the residues outside the class of the first one
exist and lie in one class. -/
lemma residuePtsMix_ok (p : CPoly ℚ) (αs cs : List ℚ) (q₀ : ℚ × ℚ) (rest : List (ℚ × ℚ))
    (hdata : ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) = q₀ :: rest)
    (hnz : ∀ q ∈ q₀ :: rest, residuePts.evalQ p q.1 ≠ 0)
    (hnd : ((q₀ :: rest).map Prod.fst).Nodup)
    (hr : ∃ r ∈ q₀ :: rest, inCls p ((residuePts.evalQ p q₀.1).num *
      (residuePts.evalQ p q₀.1).den) r = false)
    (hpair : ∀ q ∈ q₀ :: rest, ∀ r ∈ q₀ :: rest,
      inCls p ((residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den) q = false →
      inCls p ((residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den) r = false →
      ∃ γ : ℚ, residuePts.evalQ p q.1 = residuePts.evalQ p r.1 * γ ^ 2) :
    ∃ (pts₁ pts₂ : List (ℚ × ℚ × ℤ)) (D' : ℕ) (r₀ : ℚ × ℚ), r₀ ∈ q₀ :: rest ∧
      residuePtsMix p αs cs = some (pts₁, pts₂, D',
        (residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den,
        (residuePts.evalQ p r₀.1).num * (residuePts.evalQ p r₀.1).den) ∧ D' ≠ 0 ∧
      (∀ q ∈ pts₁, (((residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den : ℤ) : ℚ) *
        q.2.1 ^ 2 = residuePts.evalQ p q.1 ∧ q.2.1 ≠ 0) ∧ (pts₁.map Prod.fst).Nodup ∧
      (∀ q ∈ pts₂, (((residuePts.evalQ p r₀.1).num * (residuePts.evalQ p r₀.1).den : ℤ) : ℚ) *
        q.2.1 ^ 2 = residuePts.evalQ p q.1 ∧ q.2.1 ≠ 0) ∧ (pts₂.map Prod.fst).Nodup ∧
      qsqrt ((((residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den) *
        ((residuePts.evalQ p r₀.1).num * (residuePts.evalQ p r₀.1).den) : ℤ) : ℚ) = none ∧
      ((twPts ((residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den) pts₁ ++
        twPts ((residuePts.evalQ p r₀.1).num * (residuePts.evalQ p r₀.1).den) pts₂).map
          fun q ↦ ((q.2.2 : ℚ) / D' * q.2.1, q.1)).Perm
        ((q₀ :: rest).map fun q ↦ (q.2, q.1)) := by
  set data := q₀ :: rest with hdataL
  set v₀ := residuePts.evalQ p q₀.1
  set d₁ : ℤ := v₀.num * v₀.den with hd₁
  have hdv₁ : (d₁ : ℚ) = v₀ * (v₀.den : ℚ) ^ 2 := twist_val v₀
  have hd₁q : (d₁ : ℚ) ≠ 0 := twist_ne_zero v₀ (hnz q₀ List.mem_cons_self)
  have hd₁0 : d₁ ≠ 0 := by exact_mod_cast hd₁q
  set cls₁ := data.filter (inCls p d₁) with hcls₁
  set restL := data.filter fun q ↦ !inCls p d₁ q with hrestL
  obtain ⟨r₀, rest', hrr⟩ : ∃ r₀ rest', restL = r₀ :: rest' := by
    obtain ⟨r, hr1, hr2⟩ := hr
    have : r ∈ restL := List.mem_filter.mpr ⟨hr1, by simp [hr2]⟩
    cases h : restL with
    | nil => rw [h] at this; simp at this
    | cons a t => exact ⟨a, t, rfl⟩
  have hr₀ : r₀ ∈ restL := by rw [hrr]; exact List.mem_cons_self
  have hr₀d : r₀ ∈ data := (List.mem_filter.mp hr₀).1
  have hr₀c : inCls p d₁ r₀ = false := by simpa using (List.mem_filter.mp hr₀).2
  set v₂ := residuePts.evalQ p r₀.1
  set d₂ : ℤ := v₂.num * v₂.den with hd₂
  have hv₂ : v₂ ≠ 0 := hnz r₀ hr₀d
  have hdv₂ : (d₂ : ℚ) = v₂ * (v₂.den : ℚ) ^ 2 := twist_val v₂
  have hd₂q : (d₂ : ℚ) ≠ 0 := twist_ne_zero v₂ hv₂
  have hd₂0 : d₂ ≠ 0 := by exact_mod_cast hd₂q
  have hden₂ : (v₂.den : ℚ) ≠ 0 := by exact_mod_cast v₂.den_ne_zero
  -- the rest lies in the class `d₂`
  have hrest₂ : ∀ q ∈ restL, inCls p d₂ q = true := by
    intro q hq
    have hqd := (List.mem_filter.mp hq).1
    have hqc : inCls p d₁ q = false := by simpa using (List.mem_filter.mp hq).2
    obtain ⟨γ, hγ⟩ := hpair q hqd r₀ hr₀d hqc hr₀c
    refine inCls_of hd₂q (γ / v₂.den) ?_ (hnz q hqd)
    rw [show residuePts.evalQ p q.1 = v₂ * γ ^ 2 from hγ, hdv₂]; field_simp
  have hall₂ : restL.all (inCls p d₂) = true := List.all_eq_true.mpr hrest₂
  -- `d₁ d₂` is not a square
  have hns : qsqrt ((d₁ * d₂ : ℤ) : ℚ) = none := by
    by_contra hne
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.mp hne
    have hg2 := qsqrt_spec hg
    push_cast at hg2
    have hden₁ : (v₀.den : ℚ) ≠ 0 := by exact_mod_cast v₀.den_ne_zero
    apply Bool.false_ne_true
    rw [← hr₀c]
    refine inCls_of hd₁q (g / (d₁ * v₂.den)) ?_ hv₂
    rw [div_pow, mul_pow, hg2, hdv₂]
    field_simp
    rfl
  -- the residue data
  set g : ℤ → ℚ × ℚ → ℚ := fun d q ↦ (qsqrt (residuePts.evalQ p q.1 / d)).getD 1 with hg
  have hg₁ : ∀ q ∈ cls₁, (d₁ : ℚ) * g d₁ q ^ 2 = residuePts.evalQ p q.1 ∧ g d₁ q ≠ 0 := by
    intro q hq
    obtain ⟨g', hg', h1, h2⟩ := inCls_true (List.mem_filter.mp hq).2 hd₁q
    simp only [g, hg', Option.getD_some]
    exact ⟨h1, h2⟩
  have hg₂ : ∀ q ∈ restL, (d₂ : ℚ) * g d₂ q ^ 2 = residuePts.evalQ p q.1 ∧ g d₂ q ≠ 0 := by
    intro q hq
    obtain ⟨g', hg', h1, h2⟩ := inCls_true (hrest₂ q hq) hd₂q
    simp only [g, hg', Option.getD_some]
    exact ⟨h1, h2⟩
  set rs₁ := cls₁.map fun q ↦ (q.1, g d₁ q, q.2 / (g d₁ q * d₁))
  set rs₂ := restL.map fun q ↦ (q.1, g d₂ q, q.2 / (g d₂ q * d₂))
  set D' := ((rs₁ ++ rs₂).map fun q ↦ q.2.2.den).foldr Nat.lcm 1 with hD'
  have hD'0 : D' ≠ 0 := foldr_lcm_ne_zero _ fun a ha ↦ by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; exact Rat.den_ne_zero _
  have hdvd : ∀ q ∈ rs₁ ++ rs₂, q.2.2.den ∣ D' := fun q hq ↦
    dvd_foldr_lcm (List.mem_map_of_mem hq)
  have hDq : (D' : ℚ) ≠ 0 := by exact_mod_cast hD'0
  have hres : ∀ (d : ℤ) (q : ℚ × ℚ), (d : ℚ) ≠ 0 → g d q ≠ 0 →
      (q.1, g d q, q.2 / (g d q * d)) ∈ rs₁ ++ rs₂ →
      (((q.2 / (g d q * d) * D').num : ℤ) : ℚ) / D' * (g d q * d) = q.2 := by
    intro d q hd hgq hmem
    rw [num_mul_of_den_dvd _ _ (hdvd _ hmem)]
    field_simp
  have hmem₁ : ∀ q ∈ cls₁, (q.1, g d₁ q, q.2 / (g d₁ q * d₁)) ∈ rs₁ ++ rs₂ := fun q hq ↦
    List.mem_append_left _ (List.mem_map_of_mem hq)
  have hmem₂ : ∀ q ∈ restL, (q.1, g d₂ q, q.2 / (g d₂ q * d₂)) ∈ rs₁ ++ rs₂ := fun q hq ↦
    List.mem_append_right _ (List.mem_map_of_mem hq)
  refine ⟨rs₁.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num),
    rs₂.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num), D', r₀, hr₀d, ?_, hD'0, ?_, ?_, ?_, ?_,
    hns, ?_⟩
  · unfold residuePtsMix
    simp only
    rw [hdata]
    simp only [data]
    rw [← hd₁, ← hcls₁]
    rw [show List.filter (fun q ↦ !inCls p d₁ q) (q₀ :: rest) = r₀ :: rest' from hrr]
    dsimp only
    rw [← hd₂]
    have hall₂' : (r₀ :: rest').all (inCls p d₂) = true := hrr ▸ hall₂
    rw [if_pos ⟨hd₁0, hd₂0, hall₂', hns⟩]
    rw [← hrr]
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
    exact hg₁ q' hq'
  · have e : ((rs₁.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num)).map Prod.fst) =
        cls₁.map Prod.fst := by simp [rs₁, List.map_map, Function.comp_def]
    rw [e]
    exact hnd.sublist (List.filter_sublist.map _)
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
    exact hg₂ q' hq'
  · have e : ((rs₂.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num)).map Prod.fst) =
        restL.map Prod.fst := by simp [rs₂, List.map_map, Function.comp_def]
    rw [e]
    exact hnd.sublist (List.filter_sublist.map _)
  · have e : ((twPts d₁ (rs₁.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num)) ++
        twPts d₂ (rs₂.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num))).map
          fun q ↦ ((q.2.2 : ℚ) / D' * q.2.1, q.1)) =
        (cls₁.map fun q ↦ (q.2, q.1)) ++ (restL.map fun q ↦ (q.2, q.1)) := by
      rw [List.map_append]
      congr 1
      · simp only [twPts, rs₁, List.map_map, Function.comp_def]
        refine List.map_congr_left fun q hq ↦ ?_
        simp only [Prod.mk.injEq, and_true]
        exact hres d₁ q hd₁q (hg₁ q hq).2 (hmem₁ q hq)
      · simp only [twPts, rs₂, List.map_map, Function.comp_def]
        refine List.map_congr_left fun q hq ↦ ?_
        simp only [Prod.mk.injEq, and_true]
        exact hres d₂ q hd₂q (hg₂ q hq).2 (hmem₂ q hq)
    rw [e, ← List.map_append]
    exact (List.filter_append_perm _ _).map _

lemma ellDecideGenMix_ne_none_of (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (W B₀ : CPoly ℚ) (αs cs : List ℚ)
    (hH : ellHermiteRaw (pOf a b c) A D = some (W, B₀, αs, cs)) (q₀ : ℚ × ℚ)
    (rest : List (ℚ × ℚ)) (hdata : ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) = q₀ :: rest)
    (hnz : ∀ q ∈ q₀ :: rest, residuePts.evalQ (pOf a b c) q.1 ≠ 0)
    (hr : ∃ r ∈ q₀ :: rest, inCls (pOf a b c) (twistOf a b c q₀.1) r = false)
    (hpair : ∀ q ∈ q₀ :: rest, ∀ r ∈ q₀ :: rest,
      inCls (pOf a b c) (twistOf a b c q₀.1) q = false →
      inCls (pOf a b c) (twistOf a b c q₀.1) r = false →
      ∃ γ : ℚ, residuePts.evalQ (pOf a b c) q.1 = residuePts.evalQ (pOf a b c) r.1 * γ ^ 2)
    (fuel : ℕ) (hfuel : ∀ q ∈ q₀ :: rest, EllNL.fuelBound (a * twistOf a b c q.1)
      (b * twistOf a b c q.1 ^ 2) (c * twistOf a b c q.1 ^ 3) ≤ fuel) :
    ellDecideGenMix a b c A D fuel ≠ none := by
  obtain ⟨hαs, hl, hid⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  have hndα : αs.Nodup := hαs ▸ (List.nodup_dedup _).filter _
  have hnd : ((q₀ :: rest).map Prod.fst).Nodup := hdata ▸ nodup_data αs cs hndα hl
  obtain ⟨pts₁, pts₂, D', r₀, hr₀, hR, hD'0, hon₁, hnd₁, hon₂, hnd₂, hns, hperm⟩ :=
    residuePtsMix_ok (pOf a b c) αs cs q₀ rest hdata hnz hnd hr hpair
  obtain ⟨hG2, hG⟩ := fracG_poly B₀ D' _ αs cs hl (by rw [hdata]; exact hperm)
  have hchk := genCheck_of_poly (pOf a b c) A D W B₀ _ αs cs hD hG2 hid hG
  unfold ellDecideGenMix
  rw [hH]
  dsimp only
  rw [hR]
  dsimp only
  rw [if_pos hchk]
  have hcv : ∀ (d : ℤ) (pts : List (ℚ × ℚ × ℤ)), d ≠ 0 →
      (∀ q ∈ pts, (d : ℚ) * q.2.1 ^ 2 = residuePts.evalQ (pOf a b c) q.1 ∧ q.2.1 ≠ 0) →
      (pts.map Prod.fst).Nodup → classValid a b c d pts = true := fun d pts hd hon hnd ↦
    classValid_iff.mpr ⟨hd, fun q hq ↦ by rw [← evalQ_pOf]; exact hon q hq, hnd⟩
  have hd₁ : (residuePts.evalQ (pOf a b c) q₀.1).num *
      ((residuePts.evalQ (pOf a b c) q₀.1).den : ℤ) ≠ 0 := by
    exact_mod_cast twist_ne_zero _ (hnz q₀ List.mem_cons_self)
  have hd₂ : (residuePts.evalQ (pOf a b c) r₀.1).num *
      ((residuePts.evalQ (pOf a b c) r₀.1).den : ℤ) ≠ 0 := by
    exact_mod_cast twist_ne_zero _ (hnz r₀ hr₀)
  exact ellDecideMix_ne_none a b c _ _ hsq B₀ pts₁ pts₂ (hcv _ _ hd₁ hon₁ hnd₁)
    (hcv _ _ hd₂ hon₂ hnd₂) D' hD'0 hns fuel (hfuel q₀ List.mem_cons_self) (hfuel r₀ hr₀)

lemma same_class {v w d γ δ : ℚ} (hv : v = d * γ ^ 2) (hw : w = d * δ ^ 2) (hw0 : w ≠ 0) :
    ∃ ε : ℚ, v = w * ε ^ 2 := by
  have hδ : δ ≠ 0 := by rintro rfl; apply hw0; rw [hw]; ring
  exact ⟨γ / δ, by rw [hv, hw]; field_simp⟩

/-- **Completeness of the dispatcher with two classes**: for a split denominator whose roots `α`
(off the branch points) have `p(α)` in at most two quadratic classes, `ellDecideAll` answers with
`fuelAny` fuel. -/
theorem ellDecideAll_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hcls : ∃ d₁ d₂ : ℚ, ∀ α : ℚ, (toPoly D).eval α = 0 → α ^ 3 + a * α ^ 2 + b * α + c ≠ 0 →
      (∃ γ : ℚ, α ^ 3 + a * α ^ 2 + b * α + c = d₁ * γ ^ 2) ∨
      (∃ γ : ℚ, α ^ 3 + a * α ^ 2 + b * α + c = d₂ * γ ^ 2))
    (fuel : ℕ) (hfuel : fuelAny a b c D ≤ fuel) :
    ellDecideAll a b c A D fuel ≠ none := by
  obtain ⟨d₁, d₂, hd⟩ := hcls
  obtain ⟨hsqP, hp1⟩ := sq_pOf a b c hsq
  obtain ⟨⟨W, B₀, αs, cs⟩, hH⟩ := Option.ne_none_iff_exists'.mp
    (ellHermiteRaw_ne_none (pOf a b c) A D hsqP hp1 hD hsplit)
  obtain ⟨hαs, -, -⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  have hpole : ∀ q ∈ αs.zip cs, (toPoly D).eval q.1 = 0 ∧
      residuePts.evalQ (pOf a b c) q.1 ≠ 0 ∧ q.1 ∈ ratRootsQ D := fun q hq ↦ by
    have hα := (List.of_mem_zip hq).1
    obtain ⟨h1, h2⟩ := mem_αs (hαs ▸ hα)
    refine ⟨h1, by rw [evalQ_eq']; exact h2, ?_⟩
    rw [hαs, List.mem_filter, List.mem_dedup] at hα
    exact hα.1
  -- the class of each pole
  have hcl : ∀ q ∈ αs.zip cs,
      (∃ γ : ℚ, residuePts.evalQ (pOf a b c) q.1 = d₁ * γ ^ 2) ∨
      (∃ γ : ℚ, residuePts.evalQ (pOf a b c) q.1 = d₂ * γ ^ 2) := fun q hq ↦ by
    obtain ⟨h1, h2, -⟩ := hpole q hq
    rw [evalQ_pOf] at h2 ⊢
    exact hd q.1 h1 h2
  unfold ellDecideAll
  split
  · simp
  rename_i hA
  have hAny : ellDecideGen a b c A D fuel = none ∧ ellDecideGenTw a b c A D fuel = none := by
    unfold ellDecideAny at hA
    split at hA
    · exact absurd hA (by simp)
    · exact ⟨by assumption, hA⟩
  rcases hdata : ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) with _ | ⟨q₀, rest⟩
  · exfalso
    refine ellDecideGen_ne_none_of a b c hsq A D hD W B₀ αs cs hH (fun q hq hq0 ↦ ?_) fuel
      ((fuelBound_le_fuelAny a b c D).trans hfuel) hAny.1
    have : q ∈ ((αs.zip cs).filter fun q ↦ q.2 ≠ 0) := List.mem_filter.mpr ⟨hq, by simpa using hq0⟩
    rw [hdata] at this; simp at this
  have hmem : ∀ q ∈ q₀ :: rest, q ∈ αs.zip cs := fun q hq ↦ by
    rw [← hdata] at hq; exact (List.mem_filter.mp hq).1
  have hnz : ∀ q ∈ q₀ :: rest, residuePts.evalQ (pOf a b c) q.1 ≠ 0 :=
    fun q hq ↦ (hpole q (hmem q hq)).2.1
  have hq₀ : q₀ ∈ q₀ :: rest := List.mem_cons_self
  set v₀ := residuePts.evalQ (pOf a b c) q₀.1
  have hv₀ : v₀ ≠ 0 := hnz q₀ hq₀
  have hden₀ : (v₀.den : ℚ) ≠ 0 := by exact_mod_cast v₀.den_ne_zero
  have htw : ((twistOf a b c q₀.1 : ℤ) : ℚ) = v₀ * (v₀.den : ℚ) ^ 2 := twist_val v₀
  have htw0 : ((twistOf a b c q₀.1 : ℤ) : ℚ) ≠ 0 := twist_ne_zero v₀ hv₀
  -- being in the class of `q₀`
  have hin : ∀ q ∈ q₀ :: rest, (∃ ε : ℚ, residuePts.evalQ (pOf a b c) q.1 = v₀ * ε ^ 2) →
      inCls (pOf a b c) (twistOf a b c q₀.1) q = true := fun q hq ⟨ε, hε⟩ ↦
    inCls_of htw0 (ε / v₀.den) (by rw [hε, htw]; field_simp) (hnz q hq)
  have hfuel' : ∀ q ∈ q₀ :: rest, EllNL.fuelBound (a * twistOf a b c q.1)
      (b * twistOf a b c q.1 ^ 2) (c * twistOf a b c q.1 ^ 3) ≤ fuel := fun q hq ↦
    (fuelTw_le_fuelAny a b c D (hpole q (hmem q hq)).2.2).trans hfuel
  by_cases hall : ∀ q ∈ q₀ :: rest, inCls (pOf a b c) (twistOf a b c q₀.1) q = true
  · exfalso
    refine ellDecideGenTw_ne_none_of a b c hsq A D hD W B₀ αs cs hH q₀ rest hdata hnz
      (fun q hq ↦ ?_) fuel (hfuel' q₀ hq₀) hAny.2
    obtain ⟨g, -, hg, -⟩ := inCls_true (hall q hq) htw0
    exact ⟨v₀.den * g, by rw [← hg, htw]; ring⟩
  push_neg at hall
  obtain ⟨r, hr, hr'⟩ := hall
  refine ellDecideGenMix_ne_none_of a b c hsq A D hD W B₀ αs cs hH q₀ rest hdata hnz
    ⟨r, hr, by simpa using hr'⟩ (fun q hq r hr hqc hrc ↦ ?_) fuel hfuel'
  -- `q` and `r` both lie outside the class of `q₀`, hence in the other one
  have hout : ∀ q ∈ q₀ :: rest, inCls (pOf a b c) (twistOf a b c q₀.1) q = false →
      ∀ (d d' : ℚ), (∃ γ, v₀ = d * γ ^ 2) →
        ((∃ γ, residuePts.evalQ (pOf a b c) q.1 = d * γ ^ 2) ∨
          (∃ γ, residuePts.evalQ (pOf a b c) q.1 = d' * γ ^ 2)) →
        ∃ γ, residuePts.evalQ (pOf a b c) q.1 = d' * γ ^ 2 := by
    intro q hq hqc d d' ⟨γ₀, h₀⟩ hq'
    rcases hq' with ⟨γ, h⟩ | h
    · exfalso
      rw [hin q hq (same_class h h₀ hv₀)] at hqc
      exact Bool.noConfusion hqc
    · exact h
  rcases hcl q₀ (hmem q₀ hq₀) with h₀ | h₀
  · obtain ⟨γ, hγ⟩ := hout q hq hqc d₁ d₂ h₀ (hcl q (hmem q hq))
    obtain ⟨δ, hδ⟩ := hout r hr hrc d₁ d₂ h₀ (hcl r (hmem r hr))
    exact same_class hγ hδ (hnz r hr)
  · obtain ⟨γ, hγ⟩ := hout q hq hqc d₂ d₁ h₀ (hcl q (hmem q hq)).symm
    obtain ⟨δ, hδ⟩ := hout r hr hrc d₂ d₁ h₀ (hcl r (hmem r hr)).symm
    exact same_class hγ hδ (hnz r hr)

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for `∫ A / (D √p)` with residues in at most two quadratic classes**
(`p = x³ + ax² + bx + c` squarefree, `D` split over `ℚ`, the values `p(α)` at the roots of `D`
off the branch points in `d₁ ℚ² ∪ d₂ ℚ²`): `ellDecideAll` answers `some b`, and `b = true` iff the
integral is elementary. -/
theorem ellDecideAll_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hcls : ∃ d₁ d₂ : ℚ, ∀ α : ℚ, (toPoly D).eval α = 0 → α ^ 3 + a * α ^ 2 + b * α + c ≠ 0 →
      (∃ γ : ℚ, α ^ 3 + a * α ^ 2 + b * α + c = d₁ * γ ^ 2) ∨
      (∃ γ : ℚ, α ^ 3 + a * α ^ 2 + b * α + c = d₂ * γ ^ 2)) :
    ∃ ans : Bool, ellDecideAll a b c A D (fuelAny a b c D) = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideAll_ne_none a b c hsq A D hD hsplit hcls _ le_rfl)
  exact ⟨ans, hans, ellDecideAll_spec hC hCall x y hx a b c hsq hy hgen A D _ ans hans⟩

end Decision

end EllAlgo
