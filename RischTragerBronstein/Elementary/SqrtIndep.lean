import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Square roots of distinct square classes are linearly independent over `ℚ`

`sqrt_indep`: in a field of characteristic zero, if `sᵢ² = dᵢ ∈ ℚ*` and `dᵢ dⱼ` is never a
rational square for `i ≠ j`, then `∑ aᵢ sᵢ = 0` (`aᵢ ∈ ℚ`) forces all `aᵢ = 0`.

Proof: `E = ℚ(sᵢ)` is Galois over `ℚ` (the compositum of the splitting fields of `X² − dᵢ`); an
automorphism acts on each `sᵢ` by a sign `εᵢ`, and for `i ≠ j` some automorphism moves `sᵢ sⱼ ∉ ℚ`,
i.e. separates `εᵢ ≠ εⱼ`; a minimal relation `∑ aₖ sₖ = 0` then yields the shorter relation
`∑ aₖ (εₖ − εⱼ) sₖ = 0`.
-/

open Polynomial IntermediateField

namespace SqrtIndep

theorem sqrt_indep {K : Type*} [Field K] [CharZero K] {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (s : ι → K) (d : ι → ℚ) (hs : ∀ i ∈ S, s i ^ 2 = (d i : K)) (hd : ∀ i ∈ S, d i ≠ 0)
    (hcls : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ q : ℚ, d i * d j ≠ q ^ 2)
    (a : ι → ℚ) (hrel : ∑ i ∈ S, (a i : K) * s i = 0) : ∀ i ∈ S, a i = 0 := by
  classical
  -- the Galois extension `E = ℚ(sᵢ : i ∈ S)`
  set P : S → ℚ[X] := fun i ↦ X ^ 2 - C (d i) with hP
  have hP0 : ∀ i, P i ≠ 0 := fun i ↦ by
    simp only [hP]; exact X_pow_sub_C_ne_zero (by norm_num) _
  have hroot : ∀ i : S, s i ∈ (P i).rootSet K := fun i ↦ by
    rw [mem_rootSet_of_ne (hP0 i)]
    simp only [hP, map_sub, map_pow, aeval_X, aeval_C, eq_ratCast]
    rw [hs i i.2, sub_self]
  have hsplit : ∀ i : S, ((P i).map (algebraMap ℚ K)).Splits := fun i ↦ by
    have hfac : (P i).map (algebraMap ℚ K) = (X - C (s i)) * (X - C (-s i)) := by
      simp only [hP, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eq_ratCast]
      rw [← hs i i.2, C_pow]; simp only [map_neg]; ring
    rw [hfac]
    exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)
  set T : S → IntermediateField ℚ K := fun i ↦ adjoin ℚ ((P i).rootSet K) with hT
  have : ∀ i, IsSplittingField ℚ (T i) (P i) := fun i ↦ adjoin_rootSet_isSplittingField (hsplit i)
  have : ∀ i, Normal ℚ (T i) := fun i ↦ Normal.of_isSplittingField (P i)
  have : ∀ i, FiniteDimensional ℚ (T i) := fun i ↦ IsSplittingField.finiteDimensional _ (P i)
  set E : IntermediateField ℚ K := ⨆ i, T i with hE
  have : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_iSup_of_finite
  have : Normal ℚ E := IntermediateField.normal_iSup ℚ K T
  have : IsGalois ℚ E := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hmem : ∀ i : S, s i ∈ E := fun i ↦
    (le_iSup T i) (subset_adjoin ℚ _ (hroot i))
  set t : S → E := fun i ↦ ⟨s i, hmem i⟩ with htdef
  have ht2 : ∀ i : S, t i ^ 2 = ((d i : ℚ) : E) := fun i ↦ by
    apply Subtype.ext; push_cast [t]; exact hs i i.2
  have ht0 : ∀ i : S, t i ≠ 0 := fun i h ↦ by
    have := ht2 i; rw [h] at this
    exact hd i i.2 (by exact_mod_cast (by rw [← this]; ring : ((d i : ℚ) : E) = 0))
  -- automorphisms act by signs
  have hsign : ∀ (σ : Gal(E/ℚ)) (i : S), σ (t i) = t i ∨ σ (t i) = -t i := fun σ i ↦ by
    have : σ (t i) ^ 2 = t i ^ 2 := by rw [← map_pow, ht2, map_ratCast]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  -- automorphisms separate distinct classes
  have hsep : ∀ i j : S, i ≠ j → ∃ σ : Gal(E/ℚ), σ (t i * t j) ≠ t i * t j := fun i j hij ↦ by
    by_contra hall
    push_neg at hall
    have hbot := (IsGalois.mem_bot_iff_fixed (t i * t j)).mpr hall
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
    apply hcls i i.2 j j.2 (fun h ↦ hij (Subtype.ext h)) q
    have : ((d i * d j : ℚ) : E) = ((q ^ 2 : ℚ) : E) := by
      push_cast
      rw [← ht2, ← ht2, show t i ^ 2 * t j ^ 2 = (t i * t j) ^ 2 by ring, ← hq, eq_ratCast]
      exact (map_pow (Rat.castHom E) q 2).symm
    exact_mod_cast this
  -- the relation inside `E`
  have hrelE : ∀ b : ι → ℚ, ∑ i ∈ S, (b i : K) * s i = 0 →
      ∑ i : S, ((b i : ℚ) : E) * t i = 0 := fun b hb ↦ by
    apply Subtype.ext
    push_cast [t]
    rw [← hb, ← Finset.sum_coe_sort S]
  -- strong induction on the support
  have key : ∀ n : ℕ, ∀ b : ι → ℚ, (S.filter fun i ↦ b i ≠ 0).card ≤ n →
      ∑ i : S, ((b i : ℚ) : E) * t i = 0 → ∀ i ∈ S, b i = 0 := by
    intro n
    induction n with
    | zero =>
      intro b hb _ i hi
      by_contra h
      have : i ∈ S.filter fun i ↦ b i ≠ 0 := Finset.mem_filter.mpr ⟨hi, h⟩
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hb)] at this
      simp at this
    | succ n ih =>
      intro b hb hrel' i hi
      by_contra hbi
      by_cases hj : ∃ j ∈ S, j ≠ i ∧ b j ≠ 0
      · obtain ⟨j, hjS, hji, hbj⟩ := hj
        obtain ⟨σ, hσ⟩ := hsep ⟨i, hi⟩ ⟨j, hjS⟩ (fun h ↦ hji (congrArg Subtype.val h).symm)
        choose ε hε using fun k : S ↦ (show ∃ e : ℚ, (e = 1 ∨ e = -1) ∧ σ (t k) = (e : E) * t k by
          rcases hsign σ k with h | h
          · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
          · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩)
        set εj := ε ⟨j, hjS⟩
        have hεij : ε ⟨i, hi⟩ ≠ εj := by
          intro h
          apply hσ
          rw [map_mul, (hε _).2, (hε _).2, h]
          rcases (hε ⟨j, hjS⟩).1 with h1 | h1 <;> simp only [εj, h1] <;> push_cast <;> ring
        set b' : ι → ℚ := fun k ↦ if hk : k ∈ S then b k * (ε ⟨k, hk⟩ - εj) else 0 with hb'
        have hrel2 : ∑ k : S, ((b' k : ℚ) : E) * t k = 0 := by
          have h1 := congrArg σ hrel'
          rw [map_sum, map_zero] at h1
          have e : ∑ k : S, ((b' k : ℚ) : E) * t k =
              ∑ k : S, σ (((b k : ℚ) : E) * t k) - (εj : E) * ∑ k : S, ((b k : ℚ) : E) * t k := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [map_mul, map_ratCast, (hε k).2]
            simp only [b', dif_pos k.2]
            push_cast; ring
          rw [e, h1, hrel', mul_zero, sub_zero]
        have hsupp : (S.filter fun k ↦ b' k ≠ 0).card ≤ n := by
          have hsub : (S.filter fun k ↦ b' k ≠ 0) ⊆ (S.filter fun k ↦ b k ≠ 0).erase j := by
            intro k hk
            simp only [Finset.mem_filter, b'] at hk
            obtain ⟨hkS, hk⟩ := hk
            rw [dif_pos hkS] at hk
            refine Finset.mem_erase.mpr ⟨fun hkj ↦ ?_, Finset.mem_filter.mpr ⟨hkS, ?_⟩⟩
            · subst hkj; exact hk (by simp [εj])
            · exact fun h ↦ hk (by rw [h, zero_mul])
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hjS, hbj⟩)] at this
          omega
        have := ih b' hsupp hrel2 i hi
        simp only [b', dif_pos hi] at this
        rcases mul_eq_zero.mp this with h | h
        · exact hbi h
        · exact hεij (sub_eq_zero.mp h)
      · push_neg at hj
        have hsum : ∑ k : S, ((b k : ℚ) : E) * t k = ((b i : ℚ) : E) * t ⟨i, hi⟩ := by
          rw [Finset.sum_eq_single ⟨i, hi⟩]
          · intro k _ hk
            rw [hj k k.2 (fun h ↦ hk (Subtype.ext h)), Rat.cast_zero, zero_mul]
          · simp
        rw [hsum] at hrel'
        rcases mul_eq_zero.mp hrel' with h | h
        · exact hbi (by exact_mod_cast h)
        · exact ht0 _ h
  exact key _ a le_rfl (hrelE a hrel)

end SqrtIndep
