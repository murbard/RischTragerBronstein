import RischTragerBronstein.Torsion.RootCheckComplete

/-!
# Raising the precision of branch certificates

A branch certificate passing `certCheck` over a field `F` determines exact roots in `F⟦T⟧`
(Hensel, `rep_root_field` with `ψ = id`). **`raise_certCheck`**: for every bound `B` there is a
certificate over the same field, with the same `N`, precision `≥ B`, agreeing with the old one below
the old precision, and passing `certCheck`.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Raise

variable {F : Type*} [Field F] [DecidableEq F]

/-- The truncation of a series to length `L`. -/
noncomputable def truncL (ρ : PowerSeries F) (L : ℕ) : CPoly F :=
  (List.range L).map fun i ↦ PowerSeries.coeff i ρ

lemma truncL_getD (ρ : PowerSeries F) (L i : ℕ) :
    (truncL ρ L).getD i 0 = if i < L then PowerSeries.coeff i ρ else 0 := by
  rw [truncL]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]
  · exact List.getD_eq_default _ _ (by simp; omega)

lemma X_pow_dvd_sub_truncL (ρ : PowerSeries F) (L : ℕ) :
    (PowerSeries.X : PowerSeries F) ^ L ∣ ρ - thetaT (RingHom.id F) (toPoly (truncL ρ L)) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  rw [map_sub, coeff_thetaT, truncL_getD, if_pos hi, RingHom.id_apply, sub_self]

/-- One root raised: an exact root through the approximation, truncated further. -/
lemma raise_root {Fc : BPoly F} {a : F} {N prec : ℕ} {y : CPoly F}
    (h : rootCheck Fc a N prec y = true) (B : ℕ) :
    ∃ y' : CPoly F, rootCheck Fc a N (max B prec) y' = true ∧
      ∀ i < prec, y'.getD i 0 = y.getD i 0 := by
  obtain ⟨h1, h2, -⟩ := rootCheck_spec h
  obtain ⟨ρ, hρ, hd⟩ := rep_root_field (RingHom.id F) h
  set D := bivEval (derivYB Fc) (shiftC a N) y with hD
  set d := ordC D with hd'
  -- the derivative along `ρ` agrees with `D` below `prec`
  have hDρ : ∀ i < prec, PowerSeries.coeff i ((derivative (repEq (RingHom.id F) Fc a N)).eval ρ) =
      D.getD i 0 := by
    intro i hi
    have h3 : (PowerSeries.X : PowerSeries F) ^ prec ∣
        (derivative (repEq (RingHom.id F) Fc a N)).eval ρ - thetaT (RingHom.id F) (toPoly D) := by
      rw [hD, ← repEq_deriv]
      exact hd.trans (sub_dvd_eval_sub _ _ _)
    have := (PowerSeries.X_pow_dvd_iff.mp h3) i hi
    rw [map_sub, coeff_thetaT, RingHom.id_apply, sub_eq_zero] at this
    exact this
  set P' := max B prec with hP'
  refine ⟨truncL ρ (d + P'), rootCheck_of_root (RingHom.id F) ρ hρ d (fun i hi ↦ ?_) ?_
    (by omega) (X_pow_dvd_sub_truncL ρ _), fun i hi ↦ ?_⟩
  · rw [hDρ i (by omega)]; exact getD_lt_ordC D i hi
  · rw [hDρ d (by omega)]; exact getD_ordC D h2
  · rw [truncL_getD, if_pos (by omega)]
    have := (PowerSeries.X_pow_dvd_iff.mp hd) i hi
    rw [map_sub, coeff_thetaT, RingHom.id_apply, sub_eq_zero] at this
    exact this

/-- **Raising the precision of a branch certificate.** -/
theorem raise_certCheck {Fc : BPoly F} {n : ℕ} {a : F} {c : BranchCert F}
    (hc : certCheck Fc n a c = true) (B : ℕ) :
    ∃ c' : BranchCert F, c'.N = c.N ∧ B ≤ c'.prec ∧ c.prec ≤ c'.prec ∧
      c'.ys.length = c.ys.length ∧
      (∀ k i, i < c.prec → (c'.ys.getD k []).getD i 0 = (c.ys.getD k []).getD i 0) ∧
      certCheck Fc n a c' = true := by
  classical
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hN, hlen⟩, hroots⟩, hsep⟩ := hc
  have hr : ∀ y ∈ c.ys, ∃ y' : CPoly F, rootCheck Fc a c.N (max B c.prec) y' = true ∧
      ∀ i < c.prec, y'.getD i 0 = y.getD i 0 := fun y hy ↦ raise_root (hroots y hy) B
  choose f hf1 hf2 using hr
  set ys' := c.ys.attach.map fun y ↦ f y.1 y.2 with hys'
  have hlen' : ys'.length = c.ys.length := by simp [hys']
  have hget : ∀ k i, i < c.prec → (ys'.getD k []).getD i 0 = (c.ys.getD k []).getD i 0 := by
    intro k i hi
    by_cases hk : k < c.ys.length
    · rw [List.getD_eq_getElem (l := ys') _ (by rw [hlen']; exact hk),
        List.getD_eq_getElem (l := c.ys) _ hk]
      simp only [hys', List.getElem_map, List.getElem_attach]
      exact hf2 _ _ i hi
    · rw [List.getD_eq_default (l := ys') _ (by rw [hlen']; omega),
        List.getD_eq_default (l := c.ys) _ (by omega)]
  refine ⟨⟨c.N, ys', max B c.prec⟩, rfl, le_max_left _ _, le_max_right _ _, hlen', hget, ?_⟩
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨hN, by rw [hlen', hlen]⟩, fun y' hy' ↦ ?_⟩, ?_⟩
  · obtain ⟨⟨y, hy⟩, -, rfl⟩ := List.mem_map.mp hy'
    exact hf1 y hy
  · simp only [sepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true] at hsep ⊢
    intro k hk l hl
    rw [hlen'] at hk hl
    rcases hsep k hk l hl with h | ⟨i, hi, hne⟩
    · exact Or.inl h
    · refine Or.inr ⟨i, lt_of_lt_of_le hi (le_max_right _ _), ?_⟩
      rw [hget k i hi, hget l i hi]
      exact hne

end Raise

end Curves
