import RischTragerBronstein.Computable.LimitedCritN
import RischTragerBronstein.Rational.RationalPart

/-!
# Limited integration over `R(x)` with several parameters: the negative answer

If `limitedCritN` fails on the Hermite data of `f` and `η₁, …, η_m`, then for **no** constants
`c₁, …, c_m` in any extension `S` of the constant field does `f - ∑ cᵢ ηᵢ` have an antiderivative in
`S(x)`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

variable {R S K : Type*} [Field R] [DecidableEq R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

lemma sum_zipWith_eq_sum_fin {α β M : Type*} [AddCommMonoid M] (f : α → β → M) :
    ∀ (l₁ : List α) (l₂ : List β) (h : l₁.length = l₂.length),
    (List.zipWith f l₁ l₂).sum = ∑ i : Fin l₁.length, f l₁[i] (l₂[i]'(h ▸ i.2))
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    have ih := sum_zipWith_eq_sum_fin f l₁ l₂ (by simpa using h)
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, ih]
    rw [Fin.sum_univ_succ]
    simp

/-- The cleared combination over `S`, as a fraction identity times `∏ sᵢ`. -/
lemma lcombS_clearedNum (ι : R →+* S) (cs : List S) (ηs : List (CPoly R × CPoly R))
    (hs : ∀ η ∈ ηs, φ ((toPoly η.2).map ι) ≠ 0) :
    φ (lcombS ι cs (clearedNum ηs)) =
      (List.zipWith (fun c (η : CPoly R × CPoly R) ↦ φ (C c) *
        (φ ((toPoly η.1).map ι) / φ ((toPoly η.2).map ι))) cs ηs).sum *
        φ ((toPoly (prodDen ηs)).map ι) := by
  induction cs generalizing ηs with
  | nil => simp [lcombS]
  | cons c cs ih =>
    cases ηs with
    | nil => simp [lcombS, clearedNum]
    | cons η ηs =>
      have h1 := hs η (List.mem_cons_self ..)
      have := ih ηs fun η' hη' ↦ hs η' (List.mem_cons_of_mem _ hη')
      have hl := lcombS_map_mul ι η.2 cs (clearedNum ηs)
      simp only [lcombS, clearedNum, prodDen, List.zipWith_cons_cons, List.sum_cons, toPoly_mul,
        Polynomial.map_mul, map_add, map_mul] at this hl ⊢
      rw [hl, map_mul, this]
      field_simp

theorem limitedCritN_none (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {rf sf : CPoly R} {ηs : List (CPoly R × CPoly R)}
    (hsf : Squarefree ((toPoly sf).map ι))
    (hdf : ((toPoly rf).map ι).degree < ((toPoly sf).map ι).degree)
    (hηs : ∀ η ∈ ηs, Squarefree ((toPoly η.2).map ι) ∧
      ((toPoly η.1).map ι).degree < ((toPoly η.2).map ι).degree)
    (h : limitedCritN rf sf ηs = none) (g_f : K) (g : Fin ηs.length → K)
    (c : Fin ηs.length → S) (y : K) :
    y′ ≠ (g_f′ + φ ((toPoly rf).map ι) / φ ((toPoly sf).map ι)) -
      ∑ i : Fin ηs.length, φ (C (c i)) *
        ((g i)′ + φ ((toPoly ηs[i].1).map ι) / φ ((toPoly ηs[i].2).map ι)) := by
  intro hy
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hrel := (limited_integral_iff_multi (K := K) hD g_f _ _ hsf hdf Finset.univ g
    (fun i ↦ (toPoly ηs[i].1).map ι) (fun i ↦ (toPoly ηs[i].2).map ι) c
    (fun i _ ↦ (hηs _ (List.getElem_mem i.2)).1)
    (fun i _ ↦ (hηs _ (List.getElem_mem i.2)).2)).mp ⟨y, hy⟩
  have hφs : ∀ η ∈ ηs, φ ((toPoly η.2).map ι) ≠ 0 := fun η hη ↦
    (map_ne_zero_iff _ hinj).mpr (hηs η hη).1.ne_zero
  have hφsf : φ ((toPoly sf).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsf.ne_zero
  refine limitedCritN_complete_map ι (List.ofFn c) (by simp) (hinj ?_) h
  rw [map_mul, map_mul, lcombS_clearedNum ι _ _ hφs,
    sum_zipWith_eq_sum_fin _ _ _ (by simp)]
  have hsum : ∑ i : Fin (List.ofFn c).length,
      φ (C (List.ofFn c)[i]) * (φ ((toPoly (ηs[i]'(by simpa using i.2)).1).map ι) /
        φ ((toPoly (ηs[i]'(by simpa using i.2)).2).map ι)) =
      ∑ i : Fin ηs.length, φ (C (c i)) *
        (φ ((toPoly ηs[i].1).map ι) / φ ((toPoly ηs[i].2).map ι)) := by
    refine Fintype.sum_equiv (finCongr (by simp)) _ _ fun i ↦ ?_
    simp only [List.getElem_ofFn, finCongr_apply, Fin.getElem_fin, Fin.val_cast]
    rfl
  rw [hsum, ← hrel]
  field_simp

lemma lcombS_map (ι : R →+* S) (cs : List R) (vs : List (CPoly R)) :
    lcombS ι (cs.map ι) vs = (lcomb cs vs).map ι := by
  induction cs generalizing vs with
  | nil => simp [lcombS, lcomb]
  | cons c cs ih =>
    cases vs with
    | nil => simp [lcombS, lcomb]
    | cons v vs =>
      have := ih vs
      simp only [lcombS, lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons,
        Polynomial.map_add, Polynomial.map_mul, map_C] at this ⊢
      rw [this]

/-- If `limitedCritN` returns constants `cs`, the logarithmic parts cancel:
`r_f / s_f = ∑ cᵢ rᵢ / sᵢ`. -/
theorem limitedCritN_frac (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {rf sf : CPoly R} {ηs : List (CPoly R × CPoly R)}
    (hsf : Squarefree ((toPoly sf).map ι))
    (hdf : ((toPoly rf).map ι).degree < ((toPoly sf).map ι).degree)
    (hηs : ∀ η ∈ ηs, Squarefree ((toPoly η.2).map ι) ∧
      ((toPoly η.1).map ι).degree < ((toPoly η.2).map ι).degree)
    {cs : List R} (h : limitedCritN rf sf ηs = some cs) :
    φ ((toPoly rf).map ι) / φ ((toPoly sf).map ι) =
      ∑ i : Fin ηs.length, φ (C (ι (cs.getD i 0))) *
        (φ ((toPoly ηs[i].1).map ι) / φ ((toPoly ηs[i].2).map ι)) := by
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  obtain ⟨hl, hc⟩ := limitedCritN_sound h
  have hφs : ∀ η ∈ ηs, φ ((toPoly η.2).map ι) ≠ 0 := fun η hη ↦
    (map_ne_zero_iff _ hinj).mpr (hηs η hη).1.ne_zero
  have hφsf : φ ((toPoly sf).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsf.ne_zero
  have hP0 : φ ((toPoly (prodDen ηs)).map ι) ≠ 0 := by
    clear h hc hl
    induction ηs with
    | nil => simp [prodDen]
    | cons η ηs ih =>
      simp only [prodDen, toPoly_mul, Polynomial.map_mul, map_mul]
      exact mul_ne_zero (hφs η (List.mem_cons_self ..))
        (ih (fun η' hη' ↦ hηs η' (List.mem_cons_of_mem _ hη'))
          fun η' hη' ↦ hφs η' (List.mem_cons_of_mem _ hη'))
  have hmap := congrArg (fun P : R[X] ↦ φ (P.map ι)) hc
  simp only [Polynomial.map_mul, map_mul, ← lcombS_map] at hmap
  rw [lcombS_clearedNum ι _ _ hφs,
    sum_zipWith_eq_sum_fin _ _ _ (by rw [List.length_map, hl])] at hmap
  have hsum : ∑ i : Fin (cs.map ι).length,
      φ (C (cs.map ι)[i]) * (φ ((toPoly (ηs[i]'(by
        have := i.2; simp only [List.length_map] at this; omega)).1).map ι) /
        φ ((toPoly (ηs[i]'(by
        have := i.2; simp only [List.length_map] at this; omega)).2).map ι)) =
      ∑ i : Fin ηs.length, φ (C (ι (cs.getD i 0))) *
        (φ ((toPoly ηs[i].1).map ι) / φ ((toPoly ηs[i].2).map ι)) := by
    refine Fintype.sum_equiv (finCongr (by rw [List.length_map, hl])) _ _ fun i ↦ ?_
    have hi : (i : ℕ) < cs.length := by
      have := i.2; simp only [List.length_map] at this; exact this
    simp only [List.getElem_map, finCongr_apply, Fin.getElem_fin, Fin.val_cast,
      List.getD_eq_getElem _ _ hi]
  rw [hsum] at hmap
  have hcancel := mul_right_cancel₀ hP0 (hmap.trans (mul_assoc _ _ _).symm)
  rw [div_eq_iff hφsf, hcancel]
  ring


/-- **The positive answer.** If `limitedCritN` returns constants `cs`, then
`f - ∑ cᵢ ηᵢ` has an antiderivative in `S(x)` (namely `G_f - ∑ cᵢ Gᵢ`). -/
theorem limitedCritN_some (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {rf sf : CPoly R} {ηs : List (CPoly R × CPoly R)}
    (hsf : Squarefree ((toPoly sf).map ι))
    (hdf : ((toPoly rf).map ι).degree < ((toPoly sf).map ι).degree)
    (hηs : ∀ η ∈ ηs, Squarefree ((toPoly η.2).map ι) ∧
      ((toPoly η.1).map ι).degree < ((toPoly η.2).map ι).degree)
    {cs : List R} (h : limitedCritN rf sf ηs = some cs) (g_f : K) (g : Fin ηs.length → K) :
    ∃ y : K, y′ = (g_f′ + φ ((toPoly rf).map ι) / φ ((toPoly sf).map ι)) -
      ∑ i : Fin ηs.length, φ (C (ι (cs.getD i 0))) *
        ((g i)′ + φ ((toPoly ηs[i].1).map ι) / φ ((toPoly ηs[i].2).map ι)) :=
  (limited_integral_iff_multi (K := K) hD g_f _ _ hsf hdf Finset.univ g
    (fun i ↦ (toPoly ηs[i].1).map ι) (fun i ↦ (toPoly ηs[i].2).map ι)
    (fun i ↦ ι (cs.getD i 0))
    (fun i _ ↦ (hηs _ (List.getElem_mem i.2)).1)
    (fun i _ ↦ (hηs _ (List.getElem_mem i.2)).2)).mpr
    (limitedCritN_frac (K := K) ι hD hsf hdf hηs h)

end CPoly
