import Mathlib.Data.Nat.Pairing

/-!
# A finite prefix of a possibly non-monotone search

Keep the first answer. Soundness needs only sound stages; eventual success needs just one
successful stage. No monotonicity of the individual stages is assumed.
-/

namespace CPoly

/-- Search stages `0, …, N - 1`, stopping at the first answer. -/
def prefixSearch {α : Type*} (f : ℕ → Option α) : ℕ → Option α
  | 0 => none
  | N + 1 => (prefixSearch f N).orElse fun _ ↦ f N

theorem prefixSearch_sound {α : Type*} {f : ℕ → Option α} {N : ℕ} {a : α}
    (h : prefixSearch f N = some a) : ∃ i < N, f i = some a := by
  induction N with
  | zero => simp [prefixSearch] at h
  | succ N ih =>
    cases hp : prefixSearch f N with
    | none =>
      exact ⟨N, Nat.lt_succ_self N, by simpa [prefixSearch, hp] using h⟩
    | some b =>
      have hab : b = a := by simpa [prefixSearch, hp] using h
      subst b
      obtain ⟨i, hi, hf⟩ := ih hp
      exact ⟨i, Nat.lt_succ_of_lt hi, hf⟩

/-- An answer persists unchanged at every larger bound. -/
theorem prefixSearch_mono {α : Type*} {f : ℕ → Option α} {N M : ℕ} {a : α}
    (hNM : N ≤ M) (h : prefixSearch f N = some a) : prefixSearch f M = some a := by
  induction M, hNM using Nat.le_induction with
  | base => exact h
  | succ M hNM ih => simp [prefixSearch, ih]

/-- Any successful stage is reached, even if all later stages fail. -/
theorem prefixSearch_complete {α : Type*} {f : ℕ → Option α} {i : ℕ} {a : α}
    (h : f i = some a) : ∃ b, ∀ N, i < N → prefixSearch f N = some b := by
  have hs : ∃ b, prefixSearch f (i + 1) = some b := by
    cases hp : prefixSearch f i with
    | none => exact ⟨a, by simp [prefixSearch, hp, h]⟩
    | some b => exact ⟨b, by simp [prefixSearch, hp]⟩
  obtain ⟨b, hb⟩ := hs
  exact ⟨b, fun N hN ↦ prefixSearch_mono (by omega) hb⟩

end CPoly
