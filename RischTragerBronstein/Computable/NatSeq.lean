import Mathlib.Data.Nat.Pairing

/-!
# Enumerating finite prefixes of natural-number sequences

Repeated unpairing decodes a natural number into a sequence. Every prescribed finite prefix
occurs, even though the family cannot enumerate all infinite sequences.
-/

namespace CPoly

/-- Decode successive entries by repeated natural-number unpairing. -/
def natSeq : ℕ → ℕ → ℕ
  | c, 0 => (Nat.unpair c).1
  | c, j + 1 => natSeq (Nat.unpair c).2 j

/-- Encode the first `n` entries of a sequence. The tail is discarded. -/
def natSeqCode : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => Nat.pair (f 0) (natSeqCode n (fun j ↦ f (j + 1)))

/-- Decoding an encoded prefix recovers every entry in that prefix. -/
theorem natSeq_code (n : ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j < n) :
    natSeq (natSeqCode n f) j = f j := by
  induction n generalizing f j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [natSeqCode, natSeq, Nat.unpair_pair]
    | succ j =>
      simpa only [natSeqCode, natSeq, Nat.unpair_pair] using
        ih (fun i ↦ f (i + 1)) j (by omega)

/-- Every finite prefix occurs in the enumeration. -/
theorem natSeq_complete (n : ℕ) (f : ℕ → ℕ) :
    ∃ c, ∀ j < n, natSeq c j = f j :=
  ⟨natSeqCode n f, fun j hj ↦ natSeq_code n f j hj⟩

end CPoly
