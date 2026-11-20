import RischTragerBronstein.Mixed.MTFinal

/-!
# `elM` is sound at every bound

`decideTotal` searches the first `N` certificates in a fixed order (`findSome?` over
`List.range N`), so an answer persists for larger bounds (`decideTotal_mono`); `elM` passes the bound
down unchanged, so its answers persist too (`elM_mono`). With the eventual correctness
`elM_decides_any`: **every answer of `elM`, at any bound, is correct** (`elM_sound`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open CPoly Sup

lemma findSome?_range_mono {β : Type*} (f : ℕ → Option β) {N N' : ℕ} {b : β}
    (h : (List.range N).findSome? f = some b) (hN : N ≤ N') :
    (List.range N').findSome? f = some b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [List.range_add, List.findSome?_append, h, Option.some_or]

lemma decideTotal_mono {Fc A : BPoly ℚ} {D : CPoly ℚ} {N N' : ℕ} {b : Bool}
    (h : decideTotal Fc A D N = some b) (hN : N ≤ N') : decideTotal Fc A D N' = some b := by
  unfold decideTotal at h ⊢
  cases h1 : decideCurveQ Fc A D with
  | some b' => rw [h1, Option.some_or] at h; rw [Option.some_or]; exact h
  | none =>
    rw [h1, Option.none_or] at h; rw [Option.none_or]
    unfold decideEnum at h ⊢
    exact findSome?_range_mono _ h hN

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}

/-- **Answers of `elM` persist for larger bounds.** -/
lemma elM_mono : ∀ (m : ℕ) (q : LC m) {N N' : ℕ} {b : Bool}, elM Fc ks lv m q N = some b →
    N ≤ N' → elM Fc ks lv m q N' = some b
  | 0, q, N, N', b, h, hN => by
    simp only [elM] at h ⊢
    exact decideTotal_mono h hN
  | m + 1, q, N, N', b, h, hN => by
    rcases hk : ks m with η | a
    · simp only [elM, hk] at h ⊢
      split_ifs at h ⊢ with h1 h2
      · exact h
      · exact h
      · rcases hmc : mchain Fc ks lv m η _ _ _ with _ | Q1
        · rw [hmc] at h; exact h
        · rw [hmc] at h; exact elM_mono m _ h hN
    · simp only [elM, hk] at h ⊢
      split_ifs at h ⊢ with h1 h2 h3
      · exact h
      · exact h
      · exact h
      · exact elM_mono m _ h hN

universe u

open Classical in
/-- **`elM` is sound at every bound**: for a realization of height `k` generating `L` with
certified tower, every answer `some b` is correct. -/
theorem elM_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L]
    [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
    (T : MTower Fc ks Cc L) (k : ℕ) (hn : T.n = k) (hc : certC Fc ks lv k = true)
    (hgen : ∀ z : L, z ∈ T.F k) (q : LC k) (N : ℕ) (b : Bool)
    (h : elM Fc ks lv k q N = some b) :
    (HasElementaryIntegral (T.ev k q) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn (T.ev k q)) := by
  obtain ⟨N₀, hN⟩ := elM_decides_any hmon hdeg hsh T k hn hc hgen q
  obtain ⟨b', hb', hiff, hin⟩ := hN (max N N₀) (le_max_right _ _)
  have := elM_mono k q h (le_max_left N N₀)
  rw [this] at hb'
  obtain rfl := Option.some.inj hb'
  exact ⟨hiff, hin⟩

end Curves.MT
