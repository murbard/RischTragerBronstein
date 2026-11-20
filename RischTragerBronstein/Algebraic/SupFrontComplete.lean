import RischTragerBronstein.Algebraic.SupFrontSpec

/-!
# Completeness of the superelliptic front end

`pfSplit_ne_none`: the partial fractions succeed when `S = lc ∏ (X − aᵢ)` with distinct `aᵢ`
off the branch points. `superLogDecide_ne_none`: the logarithmic-part procedure answers when the
torsion oracle answers on every component. `superFront_ne_none`: hence the front end answers.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac

namespace Sup

section PF

variable {F : Type*} [Field F] [DecidableEq F]

lemma rem_zero_of_dvd (R S : CPoly F) (hS : toPoly S ≠ 0) (h : toPoly S ∣ toPoly R) :
    toPoly (divMod R S).2 = 0 := by
  have hspec := divMod_spec R S
  have hlt := divMod_degree_lt R S hS
  have hd : toPoly S ∣ toPoly (divMod R S).2 := by
    have : toPoly (divMod R S).2 = toPoly R - toPoly (divMod R S).1 * toPoly S := by
      rw [hspec]; ring
    rw [this]; exact dvd_sub h (dvd_mul_left _ _)
  by_contra h0
  exact absurd (Polynomial.degree_le_of_dvd hd h0) (not_le.mpr hlt)

lemma quot_linC (S : CPoly F) (a : F) (ha : (toPoly S).eval a = 0) :
    toPoly (divMod S (linC a)).2 = 0 ∧
      toPoly S = (X - Polynomial.C a) * toPoly (divMod S (linC a)).1 := by
  have hr := rem_zero_of_dvd S (linC a) (by rw [toPoly_linC]; exact X_sub_C_ne_zero a)
    (by rw [toPoly_linC]; exact dvd_iff_isRoot.mpr ha)
  refine ⟨hr, ?_⟩
  have := divMod_spec S (linC a)
  rw [hr, add_zero, toPoly_linC] at this
  rw [this]; ring

/-- **The partial fractions always succeed** on a split `S` with simple roots off `f = 0`. -/
theorem pfSplit_ne_none (f S : CPoly F) {m : ℕ} (a : Fin m → F) (T : CPoly F)
    (ha : Function.Injective a) (lc : F) (hlc : lc ≠ 0)
    (hS : toPoly S = Polynomial.C lc * ∏ i, (X - Polynomial.C (a i)))
    (hf : ∀ i, (toPoly f).eval (a i) ≠ 0) : pfSplit f S a T ≠ none := by
  classical
  have hS0 : toPoly S ≠ 0 := by
    rw [hS]; exact mul_ne_zero (Polynomial.C_ne_zero.mpr hlc)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _)
  have hroot : ∀ i, (toPoly S).eval (a i) = 0 := fun i ↦ by
    rw [hS, eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp), mul_zero]
  have hq := fun i ↦ quot_linC S (a i) (hroot i)
  set Si : Fin m → F[X] := fun i ↦ toPoly (divMod S (linC (a i))).1 with hSi
  have hSi_eq : ∀ i, Si i = Polynomial.C lc * ∏ k ∈ Finset.univ.erase i, (X - Polynomial.C (a k)) := by
    intro i
    have h1 := (hq i).2
    rw [hS, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h1
    have := mul_left_cancel₀ (X_sub_C_ne_zero (a i)) (by rw [← h1]; ring :
      (X - Polynomial.C (a i)) * (Polynomial.C lc * ∏ k ∈ Finset.univ.erase i, (X - Polynomial.C (a k))) =
      (X - Polynomial.C (a i)) * Si i)
    exact this.symm
  have hSii : ∀ i, (Si i).eval (a i) ≠ 0 := fun i ↦ by
    rw [hSi_eq, eval_mul, eval_C, eval_prod]
    exact mul_ne_zero hlc (Finset.prod_ne_zero_iff.mpr fun k hk ↦ by
      simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact fun h ↦ (Finset.ne_of_mem_erase hk) (ha h).symm)
  have hSik : ∀ i k, i ≠ k → (Si i).eval (a k) = 0 := fun i k hik ↦ by
    rw [hSi_eq, eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik.symm,
      Finset.mem_univ k⟩) (by simp), mul_zero]
  unfold pfSplit
  simp only
  rw [if_pos (List.all_eq_true.mpr fun i _ ↦ (isZero_iff _).mpr (hq i).1)]
  set R := sub T (mul f (((List.finRange m).map fun i ↦
    smul (pfRes f S T a i) (divMod S (linC (a i))).1).foldr add []))
  have hRval : toPoly R = toPoly T - toPoly f * ∑ i, Polynomial.C (pfRes f S T a i) * Si i := by
    simp only [R, toPoly_sub, toPoly_mul, Sup.toPoly_foldr_add, List.map_map, ← Fin.sum_univ_def]
    congr 2
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [toPoly_smul, Si]
  have hRroot : ∀ k, (toPoly R).eval (a k) = 0 := by
    intro k
    rw [hRval, eval_sub, eval_mul, eval_finset_sum,
      Finset.sum_eq_single k (fun i _ hik ↦ by rw [eval_mul, hSik i k hik, mul_zero])
        (fun h ↦ absurd (Finset.mem_univ k) h)]
    rw [eval_mul, eval_C, pfRes, evalC_eq, evalC_eq, evalC_eq]
    have h1 := hf k
    have h2 := hSii k
    simp only [Si] at h2 ⊢
    field_simp
    ring
  have hdvd : toPoly S ∣ toPoly R := by
    rw [hS]
    refine (IsUnit.mul_left_dvd (Polynomial.isUnit_C.mpr hlc.isUnit)).mpr ?_
    exact Finset.prod_dvd_of_coprime
      ((pairwise_coprime_X_sub_C (s := a) ha).set_pairwise _)
      fun k _ ↦ dvd_iff_isRoot.mpr (hRroot k)
  rw [if_pos ((isZero_iff _).mpr (rem_zero_of_dvd R S hS0 hdvd))]
  simp

end PF

section Main

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

open EllQuad.QCoords

/-- The oracle answers on every valid divisor. -/
def TorsAnswers (f : CPoly F) (n : ℕ) (tors : List (F × F × ℕ) → Option (Option ℕ)) : Prop :=
  ∀ (r : ℕ) (α β : Fin r → F) (mq : Fin r → ℕ), (∀ q, β q ≠ 0 ∧ β q ^ n = (toPoly f).eval (α q)) →
    Function.Injective (fun q ↦ (α q, β q)) → (tors (gammaL α β mq 1)).isSome

/-- **The logarithmic-part procedure answers** when the oracle answers on every component. -/
theorem superLogDecide_ne_none_of (f : CPoly F) {n : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (htors : TorsSpecN f n tors)
    (B B₁ : BPoly F) {m : ℕ} (a b : Fin m → F)
    (G : Fin m → BPoly F) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i))
    (hsome : ∀ j, (torsJ n ζ a b G tors j).isSome) :
    superLogDecide f n ζ tors B B₁ a b G ≠ none := by
  have hvalid : ∀ q, ptB n ζ b q ≠ 0 ∧ ptB n ζ b q ^ n = (toPoly f).eval (ptA n a q) :=
    fun q ↦ ⟨pt_ne_zero hn hζ b hb q, pt_valid _ hζ a b hbf q⟩
  have hinj := pt_injective hζ a b ha hb
  unfold superLogDecide
  rw [dif_pos hn, if_neg (by
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true, Option.isNone_iff_eq_none]
    intro j _ h
    have := hsome j
    rw [h] at this; exact Bool.false_ne_true this)]
  split_ifs with hB hAll
  · simp
  · simp
  · exfalso
    apply hAll
    refine List.all_eq_true.mpr fun j _ ↦ ?_
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hsome j)
    rcases o with _ | N
    · exact absurd (List.any_eq_true.mpr ⟨j, List.mem_finRange j, by simp [ho]⟩) hB
    obtain ⟨-, hP⟩ := (htors _ _ _ _ hvalid hinj).1 N ho
    have hw := witW_ne_none f n hn (f.length - 1) (ptA n a) (ptB n ζ b) (mqJ n ζ a b G j) N
      (fun q ↦ ⟨mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ (hvalid q).1),
        (hvalid q).2⟩) hP
    obtain ⟨W, hW⟩ := Option.ne_none_iff_exists'.mp hw
    simp [logJ, torsJ] at ho ⊢
    simp [ho, hW]

/-- **The logarithmic-part procedure answers** when the oracle does. -/
theorem superLogDecide_ne_none (f : CPoly F) {n : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (htors : TorsSpecN f n tors)
    (hans : TorsAnswers f n tors) (B B₁ : BPoly F) {m : ℕ} (a b : Fin m → F)
    (G : Fin m → BPoly F) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i)) :
    superLogDecide f n ζ tors B B₁ a b G ≠ none :=
  superLogDecide_ne_none_of f hn hζ tors htors B B₁ a b G ha hb hbf fun j ↦
    hans _ _ _ (mqJ n ζ a b G j) (fun q ↦ ⟨pt_ne_zero hn hζ b hb q, pt_valid _ hζ a b hbf q⟩)
      (pt_injective hζ a b ha hb)

/-- The residue data `G` computed by the front end. -/
def frontG (f : CPoly F) (n : ℕ) (A : List (CPoly F)) (D : CPoly F) {m : ℕ} (a : Fin m → F) :
    Fin m → BPoly F := fun i ↦
  [] :: (List.range (n - 1)).map fun k ↦ [(frontDat f n A D a k).2.1.getD i 0]

/-- **The front end answers** on valid splitting data when the oracle answers on its
components. -/
theorem superFront_ne_none_of (f : CPoly F) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hp1 : 1 ≤ (toPoly f).natDegree) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (htors : TorsSpecN f n tors)
    (A : List (CPoly F)) (D : CPoly F) (hD : toPoly D ≠ 0)
    {m : ℕ} (a b : Fin m → F) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i)) (lc : F) (hlc : lc ≠ 0)
    (hS : toPoly (nbPartK f D) = Polynomial.C lc * ∏ i, (X - Polynomial.C (a i)))
    (hsome : ∀ j, (torsJ n ζ a b (frontG f n A D a) tors j).isSome) :
    superFront f n ζ tors A D a b ≠ none := by
  unfold superFront
  rw [if_pos]
  · exact superLogDecide_ne_none_of f hn hζ tors htors _ _ a b _ ha hb hbf hsome
  refine List.all_eq_true.mpr fun k hk ↦ ?_
  have hk' := List.mem_range.mp hk
  have hμ : ∀ k' : ℕ, ((k + 1 : ℕ) : F) / n ≠ k' + 1 := by
    intro k' h
    have hn0 : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [div_eq_iff hn0] at h
    have h2 : ((k + 1 : ℕ) : F) = ((n * (k' + 1) : ℕ) : F) := by rw [h]; push_cast; ring
    have h3 := Nat.cast_injective h2
    have : n ≤ n * (k' + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hlin := hermiteS_solve_ne_none (((k + 1 : ℕ) : F) / n) hμ f (mul f (A.getD (k + 1) [])) D
    hsq hp1 hD
  unfold compData
  obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hlin
  simp only
  rw [hcs]
  have hf : ∀ i, (toPoly f).eval (a i) ≠ 0 := fun i h ↦ hb i (by
    have := hbf i; rw [h] at this; exact pow_eq_zero_iff hn.ne' |>.mp this)
  have hpf := pfSplit_ne_none f (nbPartK f D) a (cs.drop D.length) ha lc hlc hS hf
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hpf
  simp [hr]

/-- **The front end answers** on valid splitting data when the oracle does. -/
theorem superFront_ne_none (f : CPoly F) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hp1 : 1 ≤ (toPoly f).natDegree) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (htors : TorsSpecN f n tors)
    (hans : TorsAnswers f n tors) (A : List (CPoly F)) (D : CPoly F) (hD : toPoly D ≠ 0)
    {m : ℕ} (a b : Fin m → F) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i)) (lc : F) (hlc : lc ≠ 0)
    (hS : toPoly (nbPartK f D) = Polynomial.C lc * ∏ i, (X - Polynomial.C (a i))) :
    superFront f n ζ tors A D a b ≠ none :=
  superFront_ne_none_of f hn hsq hp1 hζ tors htors A D hD a b ha hb hbf lc hlc hS fun j ↦
    hans _ _ _ _ (fun q ↦ ⟨pt_ne_zero hn hζ b hb q, pt_valid _ hζ a b hbf q⟩)
      (pt_injective hζ a b ha hb)

end Main

end Sup
