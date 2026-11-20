import RischTragerBronstein.Algebraic.EllGenMulti
import RischTragerBronstein.Algebraic.EllGenMixComplete

/-!
# Completeness of the elliptic algorithm for split denominators

For `y² = x³ + ax² + bx + c` (squarefree) and any `∫ A(x) / (D(x) y) dx` with `D` split over `ℚ`,
`ellDecideEll` answers with `fuelAny` fuel, and the answer is the truth (`ellDecideEll_decides`):
the residues are grouped into square classes (`groupCls`: a permutation of the data, each group in
one class, the classes pairwise distinct), every class is valid, and `ellDecideMulti` answers.
-/

open Polynomial

namespace EllAlgo

open CPoly

lemma inCls_self {p : CPoly ℚ} {q : ℚ × ℚ} (hv : residuePts.evalQ p q.1 ≠ 0) :
    inCls p ((residuePts.evalQ p q.1).num * (residuePts.evalQ p q.1).den) q = true := by
  set v := residuePts.evalQ p q.1
  have hden : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_ne_zero
  refine inCls_of (twist_ne_zero v hv) (1 / v.den) ?_ hv
  show v = _
  rw [twist_val]; field_simp

lemma qsqrt_none_of_not_inCls {p : CPoly ℚ} {d : ℤ} {q : ℚ × ℚ}
    (hv : residuePts.evalQ p q.1 ≠ 0) (hd : (d : ℚ) ≠ 0) (hnot : inCls p d q = false) :
    qsqrt ((d * ((residuePts.evalQ p q.1).num * (residuePts.evalQ p q.1).den) : ℤ) : ℚ) =
      none := by
  set v := residuePts.evalQ p q.1
  by_contra hne
  obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.mp hne
  have hg2 := qsqrt_spec hg
  have htw := twist_val v
  push_cast at hg2 htw
  rw [htw] at hg2
  have hden : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_ne_zero
  apply Bool.false_ne_true
  rw [← hnot]
  refine inCls_of hd (g / (d * v.den)) ?_ hv
  show v = _
  rw [div_pow, mul_pow, hg2]
  field_simp

/-- **The grouping**: a permutation of the data into pairwise distinct classes. -/
lemma groupCls_spec (p : CPoly ℚ) : ∀ (n : ℕ) (l : List (ℚ × ℚ)), l.length ≤ n →
    (∀ q ∈ l, residuePts.evalQ p q.1 ≠ 0) →
    ((groupCls p n l).flatMap (·.2)).Perm l ∧
    (∀ g ∈ groupCls p n l, (∀ q ∈ g.2, inCls p g.1 q = true) ∧
      ∃ q ∈ l, g.1 = (residuePts.evalQ p q.1).num * (residuePts.evalQ p q.1).den) ∧
    (groupCls p n l).Pairwise (fun g g' ↦ qsqrt ((g.1 * g'.1 : ℤ) : ℚ) = none)
  | 0, l, hl, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    simp [groupCls]
  | _ + 1, [], _, _ => by simp [groupCls]
  | n + 1, q₀ :: t, hl, hnz => by
    set d : ℤ := (residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den with hd
    have hd0 : (d : ℚ) ≠ 0 := twist_ne_zero _ (hnz q₀ List.mem_cons_self)
    set out := (q₀ :: t).filter fun q ↦ !inCls p d q with hout
    have hq₀ : inCls p d q₀ = true := inCls_self (hnz q₀ List.mem_cons_self)
    have hout_t : out = t.filter fun q ↦ !inCls p d q := by
      rw [hout, List.filter_cons, if_neg (by simp [hq₀])]
    have hlen : out.length ≤ n := by
      rw [hout_t]
      have := List.length_filter_le (fun q ↦ !inCls p d q) t
      simp only [List.length_cons] at hl
      omega
    have hnz' : ∀ q ∈ out, residuePts.evalQ p q.1 ≠ 0 := fun q hq ↦
      hnz q (List.mem_of_mem_filter hq)
    obtain ⟨ih1, ih2, ih3⟩ := groupCls_spec p n out hlen hnz'
    simp only [groupCls]
    rw [← hd, ← hout]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.flatMap_cons]
      exact (ih1.append_left _).trans (List.filter_append_perm _ _)
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨fun q hq ↦ (List.mem_filter.mp hq).2, q₀, List.mem_cons_self, rfl⟩
      · obtain ⟨h1, q, hq, h2⟩ := ih2 g hg
        exact ⟨h1, q, List.mem_of_mem_filter hq, h2⟩
    · refine List.Pairwise.cons (fun g hg ↦ ?_) ih3
      obtain ⟨-, q, hq, h2⟩ := ih2 g hg
      rw [h2]
      have hnot : inCls p d q = false := by simpa using (List.mem_filter.mp hq).2
      exact qsqrt_none_of_not_inCls (hnz' q hq) hd0 hnot

/-- **The residue step in classes**: the output passes every check of `ellDecideMulti` and of
the kernel identity. -/
lemma residuePtsMulti_ok (p : CPoly ℚ) (αs cs : List ℚ)
    (hnz : ∀ q ∈ (αs.zip cs).filter (fun q ↦ q.2 ≠ 0), residuePts.evalQ p q.1 ≠ 0)
    (hnd : (((αs.zip cs).filter fun q ↦ q.2 ≠ 0).map Prod.fst).Nodup) :
    (residuePtsMulti p αs cs).1 ≠ [] ∧ (residuePtsMulti p αs cs).2 ≠ 0 ∧
    (∀ g ∈ (residuePtsMulti p αs cs).1, g.1 ≠ 0 ∧
      (∀ q ∈ g.2, (g.1 : ℚ) * q.2.1 ^ 2 = residuePts.evalQ p q.1 ∧ q.2.1 ≠ 0) ∧
      (g.2.map Prod.fst).Nodup) ∧
    (residuePtsMulti p αs cs).1.Pairwise (fun g g' ↦ qsqrt ((g.1 * g'.1 : ℤ) : ℚ) = none) ∧
    ((flatPts (residuePtsMulti p αs cs).1).map fun r ↦ r.2.1).Nodup ∧
    ((allTw (residuePtsMulti p αs cs).1).map
      fun q ↦ ((q.2.2 : ℚ) / (residuePtsMulti p αs cs).2 * q.2.1, q.1)).Perm
      (((αs.zip cs).filter fun q ↦ q.2 ≠ 0).map fun q ↦ (q.2, q.1)) ∧
    (∀ g ∈ (residuePtsMulti p αs cs).1, g.1 = 1 ∨ ∃ q ∈ (αs.zip cs).filter (fun q ↦ q.2 ≠ 0),
      g.1 = (residuePts.evalQ p q.1).num * (residuePts.evalQ p q.1).den) := by
  set data := (αs.zip cs).filter fun q ↦ q.2 ≠ 0 with hdata
  set G := groupCls p data.length data with hG
  obtain ⟨hperm, hcls, hpw⟩ := groupCls_spec p data.length data le_rfl hnz
  rw [← hG] at hperm hcls hpw
  set g : ℤ → ℚ × ℚ → ℚ := fun d q ↦ (qsqrt (residuePts.evalQ p q.1 / d)).getD 1 with hgdef
  set D' := (G.flatMap fun gr ↦ gr.2.map fun q ↦ (q.2 / (g gr.1 q * gr.1)).den).foldr Nat.lcm 1
    with hD'
  have hD'0 : D' ≠ 0 := foldr_lcm_ne_zero _ fun a ha ↦ by
    obtain ⟨gr, -, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
    exact Rat.den_ne_zero _
  have hDq : (D' : ℚ) ≠ 0 := by exact_mod_cast hD'0
  have hr : residuePtsMulti p αs cs =
      (if G = [] then [(1, [])] else G.map fun gr ↦ (gr.1, classPts p D' gr.1 gr.2), D') := rfl
  rw [hr]
  -- facts about a group
  have hgr : ∀ gr ∈ G, (gr.1 : ℚ) ≠ 0 ∧ ∀ q ∈ gr.2, (gr.1 : ℚ) * g gr.1 q ^ 2 =
      residuePts.evalQ p q.1 ∧ g gr.1 q ≠ 0 := by
    intro gr hgrG
    obtain ⟨hin, q₀, hq₀, hd⟩ := hcls gr hgrG
    have hd0 : (gr.1 : ℚ) ≠ 0 := by rw [hd]; exact twist_ne_zero _ (hnz q₀ hq₀)
    refine ⟨hd0, fun q hq ↦ ?_⟩
    obtain ⟨g', hg', h1, h2⟩ := inCls_true (hin q hq) hd0
    simp only [g, hg', Option.getD_some]
    exact ⟨h1, h2⟩
  have hnd_all : (G.flatMap fun gr ↦ gr.2.map Prod.fst).Nodup := by
    rw [← List.map_flatMap]
    exact (hperm.map _).nodup_iff.mpr hnd
  have hres : ∀ gr ∈ G, ∀ q ∈ gr.2,
      ((((q.2 / (g gr.1 q * gr.1) * D').num : ℤ) : ℚ) / D' * (g gr.1 q * gr.1) = q.2) := by
    intro gr hgrG q hq
    have hdvd : (q.2 / (g gr.1 q * gr.1)).den ∣ D' :=
      dvd_foldr_lcm (List.mem_flatMap.mpr ⟨gr, hgrG, List.mem_map_of_mem hq⟩)
    rw [num_mul_of_den_dvd _ _ hdvd]
    obtain ⟨hd0, hq'⟩ := hgr gr hgrG
    have := (hq' q hq).2
    field_simp
  by_cases hG0 : G = []
  · -- no residues at all
    have hdata0 : data = [] := by
      rw [hG0] at hperm; exact (List.Perm.nil_eq hperm).symm
    rw [if_pos hG0]
    refine ⟨by simp, hD'0, ?_, by simp, by simp [flatPts], ?_, ?_⟩
    · intro gr hgr
      simp only [List.mem_singleton] at hgr
      subst hgr
      simp
    · rw [hdata0]; simp [allTw, twPts]
    · intro gr hgr; simp only [List.mem_singleton] at hgr; subst hgr; exact Or.inl rfl
  rw [if_neg hG0]
  refine ⟨by simpa using hG0, hD'0, ?_, ?_, ?_, ?_, ?_⟩
  · intro gr' hgr'
    obtain ⟨gr, hgrG, rfl⟩ := List.mem_map.mp hgr'
    obtain ⟨hd0, hq'⟩ := hgr gr hgrG
    refine ⟨by exact_mod_cast hd0, fun q hq ↦ ?_, ?_⟩
    · obtain ⟨q', hq'm, rfl⟩ := List.mem_map.mp hq
      exact hq' q' hq'm
    · have e : (classPts p D' gr.1 gr.2).map Prod.fst = gr.2.map Prod.fst := by
        simp [classPts, List.map_map, Function.comp_def]
      rw [e]
      exact (List.nodup_flatMap.mp hnd_all).1 gr hgrG
  · exact List.pairwise_map.mpr (hpw.imp fun h ↦ h)
  · have e : (flatPts (G.map fun gr ↦ (gr.1, classPts p D' gr.1 gr.2))).map (fun r ↦ r.2.1) =
        G.flatMap fun gr ↦ gr.2.map Prod.fst := by
      simp [flatPts, classPts, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
    rw [e]; exact hnd_all
  · have e : (allTw (G.map fun gr ↦ (gr.1, classPts p D' gr.1 gr.2))).map
        (fun q ↦ ((q.2.2 : ℚ) / D' * q.2.1, q.1)) =
        (G.flatMap fun gr ↦ gr.2).map fun q ↦ (q.2, q.1) := by
      rw [allTw, List.flatMap_map, List.map_flatMap, List.map_flatMap]
      refine List.flatMap_congr fun gr hgrG ↦ ?_
      simp only [twPts, classPts, List.map_map, Function.comp_def]
      refine List.map_congr_left fun q hq ↦ ?_
      simp only [Prod.mk.injEq, and_true]
      rw [← mul_assoc] at *
      convert hres gr hgrG q hq using 1
      push_cast; ring
    rw [e]
    exact hperm.map _
  · intro gr' hgr'
    obtain ⟨gr, hgrG, rfl⟩ := List.mem_map.mp hgr'
    obtain ⟨-, q, hq, hd⟩ := hcls gr hgrG
    exact Or.inr ⟨q, hq, hd⟩

/-- **Completeness of `ellDecideGenMulti`**: for any split denominator it answers with `fuelAny`
fuel — no condition on the residues. -/
theorem ellDecideGenMulti_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (fuel : ℕ) (hfuel : fuelAny a b c D ≤ fuel) :
    ellDecideGenMulti a b c A D fuel ≠ none := by
  obtain ⟨hsqP, hp1⟩ := sq_pOf a b c hsq
  obtain ⟨⟨W, B₀, αs, cs⟩, hH⟩ := Option.ne_none_iff_exists'.mp
    (ellHermiteRaw_ne_none (pOf a b c) A D hsqP hp1 hD hsplit)
  obtain ⟨hαs, hl, hid⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  have hndα : αs.Nodup := hαs ▸ (List.nodup_dedup _).filter _
  set data := (αs.zip cs).filter fun q ↦ q.2 ≠ 0 with hdata
  have hpole : ∀ q ∈ data, residuePts.evalQ (pOf a b c) q.1 ≠ 0 ∧ q.1 ∈ ratRootsQ D :=
    fun q hq ↦ by
      have hα := (List.of_mem_zip (List.mem_of_mem_filter hq)).1
      obtain ⟨-, h2⟩ := mem_αs (hαs ▸ hα)
      refine ⟨by rw [evalQ_eq']; exact h2, ?_⟩
      rw [hαs, List.mem_filter, List.mem_dedup] at hα
      exact hα.1
  obtain ⟨hne, hD'0, hcl, hpw, hnd, hperm, hd⟩ := residuePtsMulti_ok (pOf a b c) αs cs
    (fun q hq ↦ (hpole q hq).1) (nodup_data αs cs hndα hl)
  set r := residuePtsMulti (pOf a b c) αs cs
  obtain ⟨hG2, hG⟩ := fracG_poly B₀ r.2 (allTw r.1) αs cs hl hperm
  have hchk := genCheck_of_poly (pOf a b c) A D W B₀ _ αs cs hD hG2 hid hG
  unfold ellDecideGenMulti
  rw [hH]
  dsimp only
  rw [if_pos hchk]
  refine ellDecideMulti_ne_none a b c hsq B₀ r.1 hne ?_ r.2 hD'0 fuel ?_
  · rw [classesOk_iff]
    refine ⟨fun g hg ↦ ?_, hpw, hnd⟩
    obtain ⟨h1, h2, h3⟩ := hcl g hg
    exact classValid_iff.mpr ⟨h1, fun q hq ↦ by rw [← evalQ_pOf]; exact h2 q hq, h3⟩
  · intro g hg
    rcases hd g hg with h | ⟨q, hq, h⟩
    · rw [h]
      simpa only [mul_one, one_pow] using (fuelBound_le_fuelAny a b c D).trans hfuel
    · rw [h]
      exact (fuelTw_le_fuelAny a b c D (hpole q hq).2).trans hfuel

/-- **Completeness of `ellDecideEll`.** -/
theorem ellDecideEll_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (fuel : ℕ) (hfuel : fuelAny a b c D ≤ fuel) :
    ellDecideEll a b c A D fuel ≠ none := by
  unfold ellDecideEll
  split
  · simp
  · exact ellDecideGenMulti_ne_none a b c hsq A D hD hsplit fuel hfuel

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for elliptic integrals with split denominator.** For
`y² = x³ + ax² + bx + c` (`a, b, c ∈ ℤ`, squarefree), in any differential field `Kc(x, y)` with
constants `Kc`, and any `A, D ∈ ℚ[x]` with `D ≠ 0` split over `ℚ`: `ellDecideEll` returns
`some b`, and `b = true` iff `∫ A(x) / (D(x) y) dx` is elementary. -/
theorem ellDecideEll_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits) :
    ∃ ans : Bool, ellDecideEll a b c A D (fuelAny a b c D) = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideEll_ne_none a b c hsq A D hD hsplit _ le_rfl)
  exact ⟨ans, hans, ellDecideEll_spec hC hCall x y hx a b c hsq hy hgen A D _ ans hans⟩

end Decision

end EllAlgo
