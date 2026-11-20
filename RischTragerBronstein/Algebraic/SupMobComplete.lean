import RischTragerBronstein.Algebraic.SupFieldComplete
import RischTragerBronstein.Algebraic.SupDecideAll

/-!
# The `n ∣ deg f` procedure answers

Facts about the transformed curve of `mobData` (`t = 1/(x − e)`): `P = rev(R)` with
`f(x + e) = x R(x)` is squarefree of degree `deg f − 1` with non-zero constant term `lc f`, and
`P(β) = βᵈ f(e + 1/β)` for `β ≠ 0`. These give `superFrontMob_ne_none`: when the field contains
the non-branch roots of `D`, `n`-th roots of `f` there and an `n`-th root of `lc f`, the procedure
answers whenever the torsion oracle does.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

section Facts

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- The shifted polynomial `f(x + e)` as a trimmed list. -/
lemma toPoly_trimShift (f : CPoly F) (e : F) :
    toPoly (trim (shiftPoly f e)) = (toPoly f).comp (X + C e) := by
  rw [toPoly_trim, toPoly_shiftPoly]

lemma natDegree_comp_shift (p : F[X]) (e : F) : (p.comp (X + C e)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

lemma length_trimShift {f : CPoly F} (e : F) (hf0 : toPoly f ≠ 0) :
    (trim (shiftPoly f e)).length = (toPoly f).natDegree + 1 := by
  have hne : trim (shiftPoly f e) ≠ [] := by
    intro h
    have := congrArg toPoly h
    rw [toPoly_trimShift, toPoly_nil] at this
    rcases comp_eq_zero_iff.mp this with h0 | ⟨-, h0⟩
    · exact hf0 h0
    · have := congrArg natDegree h0
      rw [natDegree_X_add_C, natDegree_C] at this
      exact one_ne_zero this
  rw [length_trim hne, toPoly_shiftPoly, natDegree_comp_shift]

variable (f : CPoly F) (e : F) {d : ℕ} (hfd : (toPoly f).natDegree = d) (hd : 1 ≤ d)
  (he : (toPoly f).eval e = 0)
include hfd hd he

lemma trimShift_eq_cons :
    trim (shiftPoly f e) = 0 :: (trim (shiftPoly f e)).drop 1 := by
  have hf0 : toPoly f ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hfd; omega
  have hlen := length_trimShift e hf0
  obtain ⟨c, L, hcL⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega :
    0 < (trim (shiftPoly f e)).length))
  have hc : c = 0 := by
    have := coeff_toPoly (trim (shiftPoly f e)) 0
    rw [toPoly_trimShift, coeff_zero_eq_eval_zero, eval_comp] at this
    simp only [eval_add, eval_X, eval_C, zero_add, he, hcL, List.getD_cons_zero] at this
    exact this.symm
  rw [hcL, hc]; simp

lemma toPoly_shift_eq_X_mul :
    (toPoly f).comp (X + C e) = X * toPoly ((trim (shiftPoly f e)).drop 1) := by
  calc (toPoly f).comp (X + C e) = toPoly (trim (shiftPoly f e)) := (toPoly_trimShift f e).symm
    _ = toPoly (0 :: (trim (shiftPoly f e)).drop 1) := congrArg toPoly (trimShift_eq_cons f e hfd hd he)
    _ = X * toPoly ((trim (shiftPoly f e)).drop 1) := by rw [toPoly_cons]; simp

lemma length_R : ((trim (shiftPoly f e)).drop 1).length = d := by
  have hf0 : toPoly f ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hfd; omega
  rw [List.length_drop, length_trimShift e hf0, hfd]; omega

lemma natDegree_R : (toPoly ((trim (shiftPoly f e)).drop 1)).natDegree = d - 1 := by
  have hf0 : toPoly f ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hfd; omega
  have h1 := toPoly_shift_eq_X_mul f e hfd hd he
  have hR0 : toPoly ((trim (shiftPoly f e)).drop 1) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    have := congrArg natDegree h1
    rw [natDegree_comp_shift, natDegree_zero, hfd] at this; omega
  have := congrArg natDegree h1
  rw [natDegree_comp_shift, natDegree_mul X_ne_zero hR0, natDegree_X, hfd] at this
  omega

lemma R_coeff_zero_ne (hsq : Squarefree (toPoly f)) :
    (toPoly ((trim (shiftPoly f e)).drop 1)).coeff 0 ≠ 0 := by
  intro h0
  have hX : X ∣ toPoly ((trim (shiftPoly f e)).drop 1) := X_dvd_iff.mpr h0
  have hfe := squarefree_comp_add_CK hsq e
  rw [toPoly_shift_eq_X_mul f e hfd hd he] at hfe
  exact not_isUnit_X (hfe X (mul_dvd_mul_left X hX))

lemma squarefree_P (hsq : Squarefree (toPoly f)) :
    Squarefree (toPoly ((trim (shiftPoly f e)).drop 1).reverse) := by
  have hfe := squarefree_comp_add_CK hsq e
  rw [toPoly_shift_eq_X_mul f e hfd hd he] at hfe
  have hR := hfe.of_mul_right
  rw [toPoly_reverseK, length_R f e hfd hd he, ← natDegree_R f e hfd hd he]
  exact squarefree_reflectK hR

lemma P_last_ne (hsq : Squarefree (toPoly f)) :
    ((trim (shiftPoly f e)).drop 1).reverse.getD
      (((trim (shiftPoly f e)).drop 1).reverse.length - 1) 0 ≠ 0 := by
  have hlen := length_R f e hfd hd he
  have h := R_coeff_zero_ne f e hfd hd he hsq
  rw [coeff_toPoly] at h
  rw [List.length_reverse, List.getD_eq_getElem _ _ (by rw [List.length_reverse, hlen]; omega),
    List.getElem_reverse]
  rw [List.getD_eq_getElem _ _ (by omega)] at h
  convert h using 2
  omega

lemma P_coeff_zero : (toPoly ((trim (shiftPoly f e)).drop 1).reverse).coeff 0 =
    (toPoly f).leadingCoeff := by
  rw [toPoly_reverseK, length_R f e hfd hd he, coeff_reflect, revAt_zero,
    ← natDegree_R f e hfd hd he]
  change (toPoly ((trim (shiftPoly f e)).drop 1)).leadingCoeff = _
  have h1 := congrArg leadingCoeff (toPoly_shift_eq_X_mul f e hfd hd he)
  rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C,
    one_pow, mul_one, leadingCoeff_mul, leadingCoeff_X, one_mul] at h1
  exact h1.symm

end Facts

section Eval

variable {F L : Type*} [Field F] [Field L] (ι : F →+* L)

lemma natDegree_toPoly_le' (l : CPoly F) : (toPoly l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_toPoly, List.getD_eq_default _ _ (by
    have : l.length - 1 < k := by exact_mod_cast hk
    omega)]

/-- Evaluating a reversed list: `L.reverse(β) = β^{len − 1} L(1/β)`. -/
lemma eval_reverse [DecidableEq F] [CharZero F] (l : CPoly F) {β : L} (hβ : β ≠ 0) :
    ((toPoly l.reverse).map ι).eval β = β ^ (l.length - 1) * ((toPoly l).map ι).eval β⁻¹ := by
  letI : Invertible β⁻¹ := invertibleOfNonzero (inv_ne_zero hβ)
  have h := eval₂_reflect_mul_pow ι β⁻¹ (l.length - 1) (toPoly l) (natDegree_toPoly_le' l)
  rw [invOf_eq_inv, inv_inv] at h
  rw [toPoly_reverseK, eval_map, eval_map, ← h, inv_pow]
  field_simp

end Eval

section Ident

variable {F L : Type*} [Field F] [DecidableEq F] [CharZero F] [Field L] (ι : F →+* L)

lemma eval_shift_map (p : CPoly F) (e : F) (y : L) :
    ((toPoly (trim (shiftPoly p e))).map ι).eval y = ((toPoly p).map ι).eval (y + ι e) := by
  rw [toPoly_trimShift, Polynomial.map_comp, eval_comp]
  simp

/-- **`P(β) = βᵈ f(e + 1/β)`.** -/
lemma P_eval (f : CPoly F) (e : F) {d : ℕ} (hfd : (toPoly f).natDegree = d) (hd : 1 ≤ d)
    (he : (toPoly f).eval e = 0) {β : L} (hβ : β ≠ 0) :
    ((toPoly ((trim (shiftPoly f e)).drop 1).reverse).map ι).eval β =
      β ^ d * ((toPoly f).map ι).eval (β⁻¹ + ι e) := by
  rw [eval_reverse ι _ hβ, length_R f e hfd hd he]
  have h1 := congrArg (fun q ↦ (q.map ι).eval β⁻¹) (toPoly_shift_eq_X_mul f e hfd hd he)
  simp only [Polynomial.map_comp, eval_comp, Polynomial.map_mul, eval_mul, Polynomial.map_X,
    eval_X, Polynomial.map_add, eval_add, map_C, eval_C] at h1
  have hR : ((toPoly ((trim (shiftPoly f e)).drop 1)).map ι).eval β⁻¹ =
      β * ((toPoly f).map ι).eval (β⁻¹ + ι e) := by
    rw [h1]; field_simp
  rw [hR, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hd]

/-- The new denominator: `D̃(β) = β^δ D(e + 1/β) βᴺ` for `β ≠ 0`. -/
lemma D'_eval (D : CPoly F) (e : F) (N : ℕ) {β : L} (hβ : β ≠ 0) :
    ((toPoly (mul (trim (shiftPoly D e)).reverse (monomial N 1))).map ι).eval β =
      β ^ ((trim (shiftPoly D e)).length - 1) * ((toPoly D).map ι).eval (β⁻¹ + ι e) * β ^ N := by
  rw [toPoly_mul, Polynomial.map_mul, eval_mul, eval_reverse ι _ hβ, eval_shift_map,
    toPoly_monomial]
  simp

end Ident

section Split

variable {K : Type*} [Field K]

/-- A root in an extension of a split polynomial comes from `K`. -/
lemma root_mem_map' {L : Type*} [Field L] (φ : K →+* L) {Q : K[X]} (hQ0 : Q ≠ 0) {l : List K}
    (hl : l.Nodup) (hlen : Q.natDegree ≤ l.length) (hr : ∀ a ∈ l, Q.eval a = 0) {β : L}
    (hβ : (Q.map φ).eval β = 0) : β ∈ l.map φ := by
  classical
  by_contra hβl
  have hl' : (l.map φ).Nodup := hl.map φ.injective
  have hlen' := length_le_natDegree ((Polynomial.map_ne_zero_iff φ.injective).mpr hQ0)
    (l := β :: l.map φ) (List.nodup_cons.mpr ⟨hβl, hl'⟩) (fun a ha ↦ by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hβ
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        rw [eval_map, eval₂_at_apply, hr b hb, map_zero])
  rw [natDegree_map_eq_of_injective φ.injective] at hlen'
  simp at hlen'
  omega

/-- **Splitting from roots**: a squarefree `Q` all of whose roots in `K̄` come from `K` is
`lc · ∏ (X − aᵢ)` over its roots `aᵢ ∈ K`. -/
lemma prod_of_roots_mem [CharZero K] (Q : K[X]) (hQ0 : Q ≠ 0) (hsq : Squarefree Q) (as : List K)
    (hnd : as.Nodup) (has : ∀ a, Q.eval a = 0 ↔ a ∈ as)
    (himg : ∀ β, (Q.map (algebraMap K (AlgebraicClosure K))).eval β = 0 →
      ∃ a, algebraMap K (AlgebraicClosure K) a = β) :
    ∃ lc : K, lc ≠ 0 ∧ Q = C lc * ∏ i : Fin as.length, (X - C (as.get i)) := by
  classical
  let φ := algebraMap K (AlgebraicClosure K)
  have hPL0 : Q.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).mpr hQ0
  have hsplitL : Splits (Q.map φ) := IsAlgClosed.splits _
  have hsepL : (Q.map φ).Separable := ((PerfectField.separable_iff_squarefree).mpr hsq).map
  have hnodupL := nodup_roots hsepL
  have hsubL : ∀ β ∈ (Q.map φ).roots, β ∈ as.map φ := by
    intro β hβ
    have hβr : (Q.map φ).eval β = 0 := (mem_roots hPL0).mp hβ
    obtain ⟨a, rfl⟩ := himg β hβr
    refine List.mem_map.mpr ⟨a, (has a).mp ?_, rfl⟩
    rw [eval_map, eval₂_at_apply] at hβr
    exact φ.injective (by rw [hβr, map_zero])
  have hcardL : Q.natDegree ≤ as.length := by
    rw [← natDegree_map_eq_of_injective φ.injective, hsplitL.natDegree_eq_card_roots]
    have hle : (Q.map φ).roots ≤ ((as.map φ : List _) : Multiset _) :=
      (Multiset.le_iff_subset hnodupL).mpr fun β hβ ↦ by simpa using hsubL β hβ
    simpa using Multiset.card_le_card hle
  have hasle : (as : Multiset K) ≤ Q.roots :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)).mpr fun a ha ↦
      (mem_roots hQ0).mpr ((has a).mpr ha)
  have hrootsEq : Q.roots = (as : Multiset K) := by
    refine (Multiset.eq_of_le_of_card_le hasle ?_).symm
    simp only [Multiset.coe_card]; exact (card_roots' Q).trans hcardL
  have hsplit : Splits Q := by
    rw [splits_iff_card_roots, hrootsEq, Multiset.coe_card]
    have := card_roots' Q
    rw [hrootsEq, Multiset.coe_card] at this
    omega
  refine ⟨Q.leadingCoeff, leadingCoeff_ne_zero.mpr hQ0, ?_⟩
  conv_lhs => rw [hsplit.eq_prod_roots, hrootsEq]
  rw [Multiset.map_coe, Multiset.prod_coe]
  congr 1
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

end Split

section Main

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

set_option maxHeartbeats 3200000 in
/-- **The `n ∣ deg f` procedure answers** over a field containing the non-branch roots of `D`,
`n`-th roots of `f` there and an `n`-th root of `lc f`, with complete root finders, whenever the
torsion oracle answers. -/
theorem superFrontMob_ne_none (f : CPoly F) {n : ℕ} (hn2 : 2 ≤ n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hsq : Squarefree (toPoly f)) {d : ℕ}
    (hfd : (toPoly f).natDegree = d) (hnd : n ∣ d) (hd : 1 ≤ d) (e : F)
    (he : (toPoly f).eval e = 0)
    (torsF : CPoly F → List (F × F × ℕ) → Option (Option ℕ))
    (htors : ∀ P : CPoly F, Squarefree (toPoly P) → Nat.Coprime n (P.length - 1) →
      TorsSpecN P n (torsF P))
    (hans : ∀ P : CPoly F, TorsAnswers P n (torsF P))
    (rootsF : CPoly F → List F)
    (hrootsF : ∀ Q : CPoly F, Squarefree (toPoly Q) → ∀ a, (toPoly Q).eval a = 0 ↔ a ∈ rootsF Q)
    (nthF : F → F) (hnthF : ∀ c b : F, c ≠ 0 → b ^ n = c → nthF c ^ n = c)
    (A : List (CPoly F)) (D : CPoly F) (hD : toPoly D ≠ 0)
    (hSsplit : ∃ l : List F, l.Nodup ∧ (toPoly (nbPartK f D)).natDegree ≤ l.length ∧
      ∀ a ∈ l, (toPoly (nbPartK f D)).eval a = 0)
    (hSnth : ∀ a, (toPoly (nbPartK f D)).eval a = 0 → ∃ b, b ^ n = (toPoly f).eval a)
    (hlc : ∃ c, c ^ n = (toPoly f).leadingCoeff) :
    superFrontMob f n ζ torsF rootsF nthF e A D ≠ none := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨m, hm⟩ := hnd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm; omega
    · exact h0
  have hd2 : 2 ≤ d := by rw [hm]; nlinarith
  have hRlen : ((trim (shiftPoly f e)).drop 1).length = d := length_R f e hfd hd he
  have hsD0 : toPoly (trim (shiftPoly D e)) ≠ 0 := by
    rw [toPoly_trimShift]
    intro h0
    rcases comp_eq_zero_iff.mp h0 with h0 | ⟨-, h0⟩
    · exact hD h0
    · have := congrArg natDegree h0
      rw [natDegree_X_add_C, natDegree_C] at this
      exact one_ne_zero this
  have hsDne : trim (shiftPoly D e) ≠ [] := fun h ↦ hsD0 (by rw [h]; rfl)
  have hs0 : (trim (shiftPoly f e)).getD 0 0 = 0 := by
    rw [trimShift_eq_cons f e hfd hd he]; rfl
  have hmdiv : ((trim (shiftPoly f e)).drop 1).length / n = m := by
    rw [hRlen, hm, Nat.mul_div_cancel_left _ hn]
  set R := (trim (shiftPoly f e)).drop 1 with hR
  set sD := trim (shiftPoly D e) with hsD
  set N := mobNeed e A m - (sD.length - 1) with hN
  have hmob : mobData f n e A D =
      some (R.reverse, (List.range n).map (mobNum e A sD m N), mul sD.reverse (monomial N 1)) := by
    unfold mobData
    simp only [← hR, ← hsD, hmdiv]
    rw [if_pos ⟨hs0, by rw [hRlen, hm], hsDne⟩]
  unfold superFrontMob
  rw [hmob]
  simp only
  set P := R.reverse with hP
  set D' := mul sD.reverse (monomial N (1 : F)) with hD'
  have hPlen : P.length = d := by rw [hP, List.length_reverse, hRlen]
  have hPsq : Squarefree (toPoly P) := squarefree_P f e hfd hd he hsq
  have hPlast : P.getD (P.length - 1) 0 ≠ 0 := P_last_ne f e hfd hd he hsq
  have hPdeg : (toPoly P).natDegree = P.length - 1 := natDegree_of_last hPlast
  have hcop : Nat.Coprime n (P.length - 1) := by
    rw [hPlen, hm]
    have h1 : Nat.gcd n (n * m - 1) ∣ n * m := (Nat.gcd_dvd_left _ _).mul_right m
    have h2 : Nat.gcd n (n * m - 1) ∣ n * m - 1 := Nat.gcd_dvd_right _ _
    have h3 := Nat.dvd_sub h1 h2
    rw [show n * m - (n * m - 1) = 1 by omega] at h3
    exact Nat.eq_one_of_dvd_one h3
  have hsDrev0 : toPoly sD.reverse ≠ 0 := by
    rw [toPoly_reverseK]
    intro h0
    rw [reflect_eq_zero_iff] at h0
    exact hsD0 h0
  have hD'0 : toPoly D' ≠ 0 := by
    rw [hD', toPoly_mul, toPoly_monomial, mul_ne_zero_iff]
    exact ⟨hsDrev0, by simp⟩
  set Q := nbPartK P D' with hQ
  have hQsq : Squarefree (toPoly Q) := squarefree_nbPartK P D' hD'0
  have hQ0 : toPoly Q ≠ 0 := nbPartK_ne_zero P D' hD'0
  have hQD : toPoly Q ∣ toPoly D' := by
    obtain ⟨-, -, -, he'⟩ := nbPartK_facts P D' hD'0
    rw [sqfreePart_mul D' hD'0, he', mul_assoc]; exact dvd_mul_right _ _
  have hQP : IsCoprime (toPoly Q) (toPoly P) := isCoprime_nbPartK P D' hD'0
  set as := (rootsF Q).dedup with has
  have hnd : as.Nodup := List.nodup_dedup _
  have hmemQ : ∀ a, (toPoly Q).eval a = 0 ↔ a ∈ as := fun a ↦ by
    rw [has, List.mem_dedup]; exact hrootsF Q hQsq a
  -- roots of the non-branch part of `D` (over `F` and in extensions)
  set S := nbPartK f D with hS
  let φ := algebraMap F (AlgebraicClosure F)
  -- a root `β ≠ 0` of `Q` gives the root `1/β + e` of `S`
  have hback : ∀ β : AlgebraicClosure F, β ≠ 0 →
      ((toPoly Q).map φ).eval β = 0 → ((toPoly S).map φ).eval (β⁻¹ + φ e) = 0 ∧
        ((toPoly P).map φ).eval β ≠ 0 := by
    intro β hβ hQβ
    have hD'β : ((toPoly D').map φ).eval β = 0 := by
      obtain ⟨q, hq⟩ := hQD
      rw [hq, Polynomial.map_mul, eval_mul, hQβ, zero_mul]
    have hPβ : ((toPoly P).map φ).eval β ≠ 0 := by
      intro h0
      obtain ⟨u, v, huv⟩ := hQP
      have := congrArg (fun r ↦ (r.map φ).eval β) huv
      simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hQβ, h0, mul_zero,
        add_zero, Polynomial.map_one, eval_one] at this
      exact zero_ne_one this
    refine ⟨isRoot_nbPartK f D hD φ _ ?_ ?_, hPβ⟩
    · rw [hD', D'_eval φ D e N hβ] at hD'β
      rcases mul_eq_zero.mp hD'β with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd (pow_eq_zero_iff'.mp h).1 hβ
        · exact h
      · exact absurd (pow_eq_zero_iff'.mp h).1 hβ
    · intro h0
      apply hPβ
      rw [hP, P_eval φ f e hfd hd he hβ]
      rw [IsRoot.def] at h0
      rw [h0, mul_zero]
  -- the `n`-th roots at the new points
  have hPeval : ∀ a : F, a ≠ 0 → (toPoly P).eval a = a ^ d * (toPoly f).eval (a⁻¹ + e) :=
    fun a ha ↦ by
      have h := P_eval (RingHom.id F) f e hfd hd he ha
      simp only [Polynomial.map_id, RingHom.id_apply] at h
      exact h
  have hnthP : ∀ a ∈ as, (toPoly P).eval a ≠ 0 ∧ ∃ b, b ^ n = (toPoly P).eval a := by
    intro a ha
    have hQa := (hmemQ a).mpr ha
    by_cases ha0 : a = 0
    · subst ha0
      have hP0 : (toPoly P).eval 0 = (toPoly f).leadingCoeff := by
        rw [← coeff_zero_eq_eval_zero]; exact P_coeff_zero f e hfd hd he
      rw [hP0]
      refine ⟨leadingCoeff_ne_zero.mpr hsq.ne_zero, hlc⟩
    · have hφa : φ a ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr ha0
      obtain ⟨hSa, hPa⟩ := hback (φ a) hφa (by rw [eval_map, eval₂_at_apply, hQa, map_zero])
      rw [← map_inv₀, ← map_add, eval_map, eval₂_at_apply] at hSa
      rw [eval_map, eval₂_at_apply] at hPa
      have hSa' : (toPoly S).eval (a⁻¹ + e) = 0 := φ.injective (by rw [hSa, map_zero])
      have hPa' : (toPoly P).eval a ≠ 0 := fun h0 ↦ hPa (by rw [h0, map_zero])
      refine ⟨hPa', ?_⟩
      obtain ⟨b, hb⟩ := hSnth _ hSa'
      refine ⟨a ^ m * b, ?_⟩
      rw [hPeval a ha0, mul_pow, hb, ← pow_mul, mul_comm m n, ← hm]
  set g : F → F := fun α ↦ nthF (evalC P α) with hg
  have hgb : ∀ α ∈ as, g α ≠ 0 ∧ g α ^ n = evalC P α := by
    intro α hα
    obtain ⟨hP0, b, hb⟩ := hnthP α hα
    rw [← evalC_eq] at hP0 hb
    have := hnthF _ b hP0 hb
    refine ⟨fun h0 ↦ hP0 ?_, this⟩
    rw [← this, show nthF (evalC P α) = g α from rfl, h0, zero_pow hn.ne']
  have hbget : ∀ i : Fin as.length, (as.map g).getD i 0 = g (as.get i) := fun i ↦ by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]; rfl
  have hcond : (squarefreeCheck P && decide (P.getD (P.length - 1) 0 ≠ 0) &&
      decide (0 < P.length - 1) && decide (Nat.Coprime n (P.length - 1)) &&
      (List.finRange as.length).all fun i ↦
        decide ((as.map g).getD i 0 ≠ 0 ∧ (as.map g).getD i 0 ^ n = evalC P (as.get i))) =
      true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies]
    refine ⟨⟨⟨⟨squarefreeCheck_complete hPsq, hPlast⟩, by omega⟩, hcop⟩, fun i ↦ ?_⟩
    rw [hbget]; exact hgb _ (List.get_mem _ _)
  rw [if_pos (by simpa [hg] using hcond)]
  -- `Q` splits over `F`
  obtain ⟨l, hl, hllen, hlr⟩ := hSsplit
  have himg : ∀ β, ((toPoly Q).map (algebraMap F (AlgebraicClosure F))).eval β = 0 →
      ∃ a, algebraMap F (AlgebraicClosure F) a = β := by
    intro β hβ
    by_cases hβ0 : β = 0
    · exact ⟨0, by rw [hβ0, map_zero]⟩
    obtain ⟨hSβ, -⟩ := hback β hβ0 hβ
    obtain ⟨r, -, hr⟩ := List.mem_map.mp (root_mem_map' (algebraMap F (AlgebraicClosure F))
      (nbPartK_ne_zero f D hD) hl hllen hlr hSβ)
    refine ⟨(r - e)⁻¹, ?_⟩
    rw [map_inv₀, map_sub, hr]
    rw [add_sub_cancel_right, inv_inv]
  obtain ⟨lc, hlc0, hQprod⟩ := prod_of_roots_mem (toPoly Q) hQ0 hQsq as hnd hmemQ himg
  have hinj : Function.Injective fun i : Fin as.length ↦ as.get i :=
    fun i j hij ↦ (List.Nodup.get_inj_iff hnd).mp hij
  have hp1 : 1 ≤ (toPoly P).natDegree := by rw [hPdeg, hPlen]; omega
  exact superFront_ne_none P hn hPsq hp1 hζ (torsF P) (htors P hPsq hcop) (hans P) _ D' hD'0
    (fun i ↦ as.get i) (fun i ↦ (as.map g).getD i 0) hinj
    (fun i ↦ by rw [hbget]; exact (hgb _ (List.get_mem _ _)).1)
    (fun i ↦ by rw [hbget, ← evalC_eq]; exact (hgb _ (List.get_mem _ _)).2) lc hlc0 hQprod

set_option maxHeartbeats 3200000 in
/-- **The data of the `n ∣ deg f` procedure**: under the same conditions, `superFrontMob` is
`superFront` on explicit transformed data (independent of the oracle) with all the properties
needed for it to answer. -/
theorem superFrontMob_data (f : CPoly F) {n : ℕ} (hn2 : 2 ≤ n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hsq : Squarefree (toPoly f)) {d : ℕ}
    (hfd : (toPoly f).natDegree = d) (hnd : n ∣ d) (hd : 1 ≤ d) (e : F)
    (he : (toPoly f).eval e = 0)
    (rootsF : CPoly F → List F)
    (hrootsF : ∀ Q : CPoly F, Squarefree (toPoly Q) → ∀ a, (toPoly Q).eval a = 0 ↔ a ∈ rootsF Q)
    (nthF : F → F) (hnthF : ∀ c b : F, c ≠ 0 → b ^ n = c → nthF c ^ n = c)
    (A : List (CPoly F)) (D : CPoly F) (hD : toPoly D ≠ 0)
    (hSsplit : ∃ l : List F, l.Nodup ∧ (toPoly (nbPartK f D)).natDegree ≤ l.length ∧
      ∀ a ∈ l, (toPoly (nbPartK f D)).eval a = 0)
    (hSnth : ∀ a, (toPoly (nbPartK f D)).eval a = 0 → ∃ b, b ^ n = (toPoly f).eval a)
    (hlc : ∃ c, c ^ n = (toPoly f).leadingCoeff) :
    ∃ (P : CPoly F) (A' : List (CPoly F)) (D' : CPoly F) (m : ℕ) (a b : Fin m → F) (lc : F),
      Squarefree (toPoly P) ∧ 1 ≤ (toPoly P).natDegree ∧ Nat.Coprime n (P.length - 1) ∧
      0 < P.length - 1 ∧ P.getD (P.length - 1) 0 ≠ 0 ∧ toPoly D' ≠ 0 ∧ Function.Injective a ∧
      (∀ i, b i ≠ 0) ∧ (∀ i, b i ^ n = (toPoly P).eval (a i)) ∧ lc ≠ 0 ∧
      toPoly (nbPartK P D') = Polynomial.C lc * ∏ i, (X - Polynomial.C (a i)) ∧
      P = ((trim (shiftPoly f e)).drop 1).reverse ∧ m ≤ (toPoly D).natDegree + 1 ∧
      ∀ torsF : CPoly F → List (F × F × ℕ) → Option (Option ℕ),
        superFrontMob f n ζ torsF rootsF nthF e A D = superFront P n ζ (torsF P) A' D' a b := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨m, hm⟩ := hnd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm; omega
    · exact h0
  have hd2 : 2 ≤ d := by rw [hm]; nlinarith
  have hRlen : ((trim (shiftPoly f e)).drop 1).length = d := length_R f e hfd hd he
  have hsD0 : toPoly (trim (shiftPoly D e)) ≠ 0 := by
    rw [toPoly_trimShift]
    intro h0
    rcases comp_eq_zero_iff.mp h0 with h0 | ⟨-, h0⟩
    · exact hD h0
    · have := congrArg natDegree h0
      rw [natDegree_X_add_C, natDegree_C] at this
      exact one_ne_zero this
  have hsDne : trim (shiftPoly D e) ≠ [] := fun h ↦ hsD0 (by rw [h]; rfl)
  have hs0 : (trim (shiftPoly f e)).getD 0 0 = 0 := by
    rw [trimShift_eq_cons f e hfd hd he]; rfl
  have hmdiv : ((trim (shiftPoly f e)).drop 1).length / n = m := by
    rw [hRlen, hm, Nat.mul_div_cancel_left _ hn]
  set R := (trim (shiftPoly f e)).drop 1 with hR
  set sD := trim (shiftPoly D e) with hsD
  set N := mobNeed e A m - (sD.length - 1) with hN
  have hmob : mobData f n e A D =
      some (R.reverse, (List.range n).map (mobNum e A sD m N), mul sD.reverse (monomial N 1)) := by
    unfold mobData
    simp only [← hR, ← hsD, hmdiv]
    rw [if_pos ⟨hs0, by rw [hRlen, hm], hsDne⟩]
  unfold superFrontMob
  rw [hmob]
  simp only
  set P := R.reverse with hP
  set D' := mul sD.reverse (monomial N (1 : F)) with hD'
  have hPlen : P.length = d := by rw [hP, List.length_reverse, hRlen]
  have hPsq : Squarefree (toPoly P) := squarefree_P f e hfd hd he hsq
  have hPlast : P.getD (P.length - 1) 0 ≠ 0 := P_last_ne f e hfd hd he hsq
  have hPdeg : (toPoly P).natDegree = P.length - 1 := natDegree_of_last hPlast
  have hcop : Nat.Coprime n (P.length - 1) := by
    rw [hPlen, hm]
    have h1 : Nat.gcd n (n * m - 1) ∣ n * m := (Nat.gcd_dvd_left _ _).mul_right m
    have h2 : Nat.gcd n (n * m - 1) ∣ n * m - 1 := Nat.gcd_dvd_right _ _
    have h3 := Nat.dvd_sub h1 h2
    rw [show n * m - (n * m - 1) = 1 by omega] at h3
    exact Nat.eq_one_of_dvd_one h3
  have hsDrev0 : toPoly sD.reverse ≠ 0 := by
    rw [toPoly_reverseK]
    intro h0
    rw [reflect_eq_zero_iff] at h0
    exact hsD0 h0
  have hD'0 : toPoly D' ≠ 0 := by
    rw [hD', toPoly_mul, toPoly_monomial, mul_ne_zero_iff]
    exact ⟨hsDrev0, by simp⟩
  set Q := nbPartK P D' with hQ
  have hQsq : Squarefree (toPoly Q) := squarefree_nbPartK P D' hD'0
  have hQ0 : toPoly Q ≠ 0 := nbPartK_ne_zero P D' hD'0
  have hQD : toPoly Q ∣ toPoly D' := by
    obtain ⟨-, -, -, he'⟩ := nbPartK_facts P D' hD'0
    rw [sqfreePart_mul D' hD'0, he', mul_assoc]; exact dvd_mul_right _ _
  have hQP : IsCoprime (toPoly Q) (toPoly P) := isCoprime_nbPartK P D' hD'0
  set as := (rootsF Q).dedup with has
  have hnd : as.Nodup := List.nodup_dedup _
  have hmemQ : ∀ a, (toPoly Q).eval a = 0 ↔ a ∈ as := fun a ↦ by
    rw [has, List.mem_dedup]; exact hrootsF Q hQsq a
  -- roots of the non-branch part of `D` (over `F` and in extensions)
  set S := nbPartK f D with hS
  let φ := algebraMap F (AlgebraicClosure F)
  -- a root `β ≠ 0` of `Q` gives the root `1/β + e` of `S`
  have hback : ∀ β : AlgebraicClosure F, β ≠ 0 →
      ((toPoly Q).map φ).eval β = 0 → ((toPoly S).map φ).eval (β⁻¹ + φ e) = 0 ∧
        ((toPoly P).map φ).eval β ≠ 0 := by
    intro β hβ hQβ
    have hD'β : ((toPoly D').map φ).eval β = 0 := by
      obtain ⟨q, hq⟩ := hQD
      rw [hq, Polynomial.map_mul, eval_mul, hQβ, zero_mul]
    have hPβ : ((toPoly P).map φ).eval β ≠ 0 := by
      intro h0
      obtain ⟨u, v, huv⟩ := hQP
      have := congrArg (fun r ↦ (r.map φ).eval β) huv
      simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hQβ, h0, mul_zero,
        add_zero, Polynomial.map_one, eval_one] at this
      exact zero_ne_one this
    refine ⟨isRoot_nbPartK f D hD φ _ ?_ ?_, hPβ⟩
    · rw [hD', D'_eval φ D e N hβ] at hD'β
      rcases mul_eq_zero.mp hD'β with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd (pow_eq_zero_iff'.mp h).1 hβ
        · exact h
      · exact absurd (pow_eq_zero_iff'.mp h).1 hβ
    · intro h0
      apply hPβ
      rw [hP, P_eval φ f e hfd hd he hβ]
      rw [IsRoot.def] at h0
      rw [h0, mul_zero]
  -- the `n`-th roots at the new points
  have hPeval : ∀ a : F, a ≠ 0 → (toPoly P).eval a = a ^ d * (toPoly f).eval (a⁻¹ + e) :=
    fun a ha ↦ by
      have h := P_eval (RingHom.id F) f e hfd hd he ha
      simp only [Polynomial.map_id, RingHom.id_apply] at h
      exact h
  have hnthP : ∀ a ∈ as, (toPoly P).eval a ≠ 0 ∧ ∃ b, b ^ n = (toPoly P).eval a := by
    intro a ha
    have hQa := (hmemQ a).mpr ha
    by_cases ha0 : a = 0
    · subst ha0
      have hP0 : (toPoly P).eval 0 = (toPoly f).leadingCoeff := by
        rw [← coeff_zero_eq_eval_zero]; exact P_coeff_zero f e hfd hd he
      rw [hP0]
      refine ⟨leadingCoeff_ne_zero.mpr hsq.ne_zero, hlc⟩
    · have hφa : φ a ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr ha0
      obtain ⟨hSa, hPa⟩ := hback (φ a) hφa (by rw [eval_map, eval₂_at_apply, hQa, map_zero])
      rw [← map_inv₀, ← map_add, eval_map, eval₂_at_apply] at hSa
      rw [eval_map, eval₂_at_apply] at hPa
      have hSa' : (toPoly S).eval (a⁻¹ + e) = 0 := φ.injective (by rw [hSa, map_zero])
      have hPa' : (toPoly P).eval a ≠ 0 := fun h0 ↦ hPa (by rw [h0, map_zero])
      refine ⟨hPa', ?_⟩
      obtain ⟨b, hb⟩ := hSnth _ hSa'
      refine ⟨a ^ m * b, ?_⟩
      rw [hPeval a ha0, mul_pow, hb, ← pow_mul, mul_comm m n, ← hm]
  set g : F → F := fun α ↦ nthF (evalC P α) with hg
  have hgb : ∀ α ∈ as, g α ≠ 0 ∧ g α ^ n = evalC P α := by
    intro α hα
    obtain ⟨hP0, b, hb⟩ := hnthP α hα
    rw [← evalC_eq] at hP0 hb
    have := hnthF _ b hP0 hb
    refine ⟨fun h0 ↦ hP0 ?_, this⟩
    rw [← this, show nthF (evalC P α) = g α from rfl, h0, zero_pow hn.ne']
  have hbget : ∀ i : Fin as.length, (as.map g).getD i 0 = g (as.get i) := fun i ↦ by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]; rfl
  have hcond : (squarefreeCheck P && decide (P.getD (P.length - 1) 0 ≠ 0) &&
      decide (0 < P.length - 1) && decide (Nat.Coprime n (P.length - 1)) &&
      (List.finRange as.length).all fun i ↦
        decide ((as.map g).getD i 0 ≠ 0 ∧ (as.map g).getD i 0 ^ n = evalC P (as.get i))) =
      true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies]
    refine ⟨⟨⟨⟨squarefreeCheck_complete hPsq, hPlast⟩, by omega⟩, hcop⟩, fun i ↦ ?_⟩
    rw [hbget]; exact hgb _ (List.get_mem _ _)
  -- `Q` splits over `F`
  obtain ⟨l, hl, hllen, hlr⟩ := hSsplit
  have himg : ∀ β, ((toPoly Q).map (algebraMap F (AlgebraicClosure F))).eval β = 0 →
      ∃ a, algebraMap F (AlgebraicClosure F) a = β := by
    intro β hβ
    by_cases hβ0 : β = 0
    · exact ⟨0, by rw [hβ0, map_zero]⟩
    obtain ⟨hSβ, -⟩ := hback β hβ0 hβ
    obtain ⟨r, -, hr⟩ := List.mem_map.mp (root_mem_map' (algebraMap F (AlgebraicClosure F))
      (nbPartK_ne_zero f D hD) hl hllen hlr hSβ)
    refine ⟨(r - e)⁻¹, ?_⟩
    rw [map_inv₀, map_sub, hr]
    rw [add_sub_cancel_right, inv_inv]
  obtain ⟨lc, hlc0, hQprod⟩ := prod_of_roots_mem (toPoly Q) hQ0 hQsq as hnd hmemQ himg
  have hinj : Function.Injective fun i : Fin as.length ↦ as.get i :=
    fun i j hij ↦ (List.Nodup.get_inj_iff hnd).mp hij
  have hp1 : 1 ≤ (toPoly P).natDegree := by rw [hPdeg, hPlen]; omega
  -- at most one new point over `x = ∞`, the others over roots of `D`
  have hmD : as.length ≤ (toPoly D).natDegree + 1 := by
    have hrev0 : toPoly sD.reverse ≠ 0 := hsDrev0
    have hnz : (as.filter fun a ↦ a ≠ 0).length ≤ (toPoly sD.reverse).natDegree :=
      length_le_natDegree hrev0 (hnd.filter _) fun a ha ↦ by
        obtain ⟨ham, ha0⟩ := List.mem_filter.mp ha
        have hQa : (toPoly Q).eval a = 0 := (hmemQ a).mpr ham
        obtain ⟨q, hq⟩ := hQD
        have hD'a : (toPoly D').eval a = 0 := by rw [hq, eval_mul, hQa, zero_mul]
        rw [hD', toPoly_mul, eval_mul, toPoly_monomial, eval_mul, eval_C, eval_pow, eval_X,
          one_mul] at hD'a
        exact (mul_eq_zero.mp hD'a).resolve_right (pow_ne_zero _ (by simpa using ha0))
    have hdeg : (toPoly sD.reverse).natDegree ≤ (toPoly D).natDegree := by
      rw [toPoly_reverseK]
      refine natDegree_reflect_le.trans ?_
      rw [hsD, length_trimShift e hD, toPoly_trimShift, natDegree_comp_shift]
      simp
    have hz : (as.filter fun a ↦ !decide (a ≠ 0)).length ≤ 1 := by
      have hnd0 := hnd.filter (fun a ↦ !decide (a ≠ 0))
      have hall : ∀ a ∈ as.filter (fun a ↦ !decide (a ≠ 0)), a = 0 := fun a ha ↦ by
        simpa using (List.mem_filter.mp ha).2
      generalize as.filter (fun a ↦ !decide (a ≠ 0)) = L at hnd0 hall
      match L, hnd0, hall with
      | [], _, _ => simp
      | [_], _, _ => simp
      | a :: b :: t, hnd0, hall =>
        exfalso
        have ha := hall a (by simp)
        have hb := hall b (by simp)
        exact (List.nodup_cons.mp hnd0).1 (by rw [ha, ← hb]; simp)
    have htot := List.length_eq_length_filter_add (l := as) (fun a ↦ decide (a ≠ 0))
    omega
  exact ⟨P, _, D', as.length, fun i ↦ as.get i, fun i ↦ (as.map g).getD i 0, lc, hPsq, hp1, hcop,
    by omega, hPlast, hD'0, hinj,
    fun i ↦ by beta_reduce; rw [hbget]; exact (hgb _ (List.get_mem _ _)).1,
    fun i ↦ by beta_reduce; rw [hbget, ← evalC_eq]; exact (hgb _ (List.get_mem _ _)).2, hlc0, hQprod,
    rfl, hmD, fun torsF ↦ by rw [if_pos (by simpa [hg] using hcond)]⟩

end Main

section NF

/-- The semantic facts about the field built for `n ∣ deg f`. -/
def MobField (f S : CPoly ℚ) (n : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) : Prop :=
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  HasRoots M hM (xnMinus n 1) n ∧ HasRoots M hM f (toPoly f).natDegree ∧
    HasRoots M hM S (toPoly S).natDegree ∧
    (∀ a : NF M, aeval a (toPoly S) = 0 → ∃ b : NF M, b ^ n = aeval a (toPoly f)) ∧
    ∃ c : NF M, c ^ n = algebraMap ℚ (NF M) (toPoly f).leadingCoeff

/-- `NthDone` gives `n`-th roots at every root. -/
lemma nth_of_done {f S : CPoly ℚ} {n : ℕ} (hn : 0 < n) (hSsq : Squarefree (toPoly S))
    {M : CPoly ℚ} {hM : Kron.irredQ M = true} (h : NthDone f S n M hM) :
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    ∀ a : NF M, aeval a (toPoly S) = 0 → ∃ b : NF M, b ^ n = aeval a (toPoly f) := by
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  intro a ha
  obtain ⟨rs, hrs, hall⟩ := h
  have hSsqK : Squarefree (toPoly (liftK (K := NF M) S)) := by
    rw [toPoly_liftK]; exact ((PerfectField.separable_iff_squarefree).mpr hSsq).map.squarefree
  obtain ⟨rs', hrs', hcomp⟩ := rootsIn_complete M _ hSsqK
  rw [hrs] at hrs'
  cases hrs'
  have ham : a ∈ rs.dedup := List.mem_dedup.mpr (hcomp a (by rw [toPoly_liftK, eval_map_algebraMap]; exact ha))
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hall a ham)
  cases hl0 : rootsIn M (xnMinus n (evalC (liftK (K := NF M) f) a)) with
  | none => rw [hl0] at hr; simp at hr
  | some l0 =>
    rw [hl0] at hr
    have hroot := rootsIn_sound M _ hl0 r (List.mem_of_mem_head? hr)
    rw [toPoly_xnMinus hn] at hroot
    simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
    exact ⟨r, by rw [hroot, evalC_eq, toPoly_liftK, eval_map_algebraMap]⟩

/-- Roots-with-`n`-th-roots transport along embeddings (the roots of a split `S` are images). -/
lemma nth_map {f S : CPoly ℚ} {n : ℕ} (hS0 : toPoly S ≠ 0) {M M' : CPoly ℚ}
    {hM : Kron.irredQ M = true} {hM' : Kron.irredQ M' = true}
    (hr : HasRoots M hM S (toPoly S).natDegree)
    (hnth : letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ a : NF M, aeval a (toPoly S) = 0 → ∃ b : NF M, b ^ n = aeval a (toPoly f))
    (φ : (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
          letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
          NF M →+* NF M')) :
    letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
    ∀ a : NF M', aeval a (toPoly S) = 0 → ∃ b : NF M', b ^ n = aeval a (toPoly f) := by
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
  intro a ha
  obtain ⟨l, hl, hlen, hlr⟩ := hr
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp (root_mem_map φ hS0 hl hlen hlr ha)
  obtain ⟨b, hb⟩ := hnth a0 (hlr a0 ha0)
  exact ⟨φ b, by rw [← map_pow, hb, aeval_ringHom_rat]⟩

lemma getLastD_eq_lc {f : CPoly ℚ} (hfd : (toPoly f).natDegree = f.length - 1) (hf0 : f ≠ []) :
    f.getLastD 0 = (toPoly f).leadingCoeff := by
  rw [leadingCoeff, hfd, coeff_toPoly, List.getLastD_eq_getLast? , List.getLast?_eq_getElem?]
  rw [List.getD_eq_getElem?_getD]

end NF

section Build

/-- **`buildFieldMob` succeeds** for large fuel, with all the facts `MobField`. -/
theorem buildFieldMob_spec (f S : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hfsq : Squarefree (toPoly f))
    (hfd : (toPoly f).natDegree = f.length - 1) (hd : 1 ≤ (toPoly f).natDegree)
    (hSsq : Squarefree (toPoly S)) (hcop : IsCoprime (toPoly S) (toPoly f)) (fuel : ℕ)
    (hfn : n < fuel) (hff : (toPoly f).natDegree < fuel) (hfS : (toPoly S).natDegree < fuel) :
    ∃ M hM, buildFieldMob f S n fuel = some ⟨M, hM⟩ ∧ MobField f S n M hM := by
  have hX : Squarefree (toPoly (xnMinus n (1 : ℚ))) := sqf_xnMinus hn one_ne_zero
  have hXd : (toPoly (xnMinus n (1 : ℚ))).natDegree = n := natDegree_xnMinus hn 1
  have hf0 : f ≠ [] := by rintro rfl; simp at hd
  have hlc0 : (toPoly f).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfsq.ne_zero
  obtain ⟨M1, hM1, h1, hr1⟩ := splitLoop_spec (xnMinus n 1) hX fuel [0, 1] irredQ_X 0
    (hasRoots_zero _ _ _) (by omega)
  obtain ⟨M2, hM2, h2, hr2⟩ := splitLoop_spec f hfsq fuel M1 hM1 0 (hasRoots_zero _ _ _)
    (by omega)
  obtain ⟨φ12⟩ := splitLoop_emb f hfsq fuel M1 hM1 M2 hM2 h2
  obtain ⟨M3, hM3, h3, hr3⟩ := splitLoop_spec S hSsq fuel M2 hM2 0 (hasRoots_zero _ _ _)
    (by omega)
  obtain ⟨φ23⟩ := splitLoop_emb S hSsq fuel M2 hM2 M3 hM3 h3
  obtain ⟨M4, hM4, h4, hdone4, ⟨φ34⟩⟩ := nthLoop_spec f S n hn hSsq hcop fuel M3 hM3 0
    (goodRoots_zero f S n _ _) (by omega)
  have hXsq : Squarefree (toPoly ([0, 1] : CPoly ℚ)) := by
    rw [show toPoly ([0, 1] : CPoly ℚ) = X by simp [CPoly.toPoly]]; exact irreducible_X.squarefree
  have hXcop : IsCoprime (toPoly ([0, 1] : CPoly ℚ)) (toPoly [f.getLastD 0]) := by
    rw [show toPoly [f.getLastD 0] = C (f.getLastD 0) by simp [CPoly.toPoly],
      getLastD_eq_lc hfd hf0]
    exact ⟨0, C (toPoly f).leadingCoeff⁻¹, by rw [zero_mul, zero_add, ← C_mul,
      inv_mul_cancel₀ hlc0, C_1]⟩
  have hXdeg : (toPoly ([0, 1] : CPoly ℚ)).natDegree = 1 := by simp [CPoly.toPoly]
  obtain ⟨M5, hM5, h5, hdone5, ⟨φ45⟩⟩ := nthLoop_spec [f.getLastD 0] [0, 1] n hn hXsq hXcop fuel
    M4 hM4 0 (goodRoots_zero _ _ n _ _) (by omega)
  refine ⟨M5, hM5, by simp only [buildFieldMob, h1, h2, h3, h4, h5], ?_⟩
  have hS0 : toPoly S ≠ 0 := hSsq.ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hXd] at hr1
    exact HasRoots.mapEmb (hM' := hM5) (HasRoots.mapEmb (hM' := hM4) (HasRoots.mapEmb (hM' := hM3)
      (HasRoots.mapEmb (hM' := hM2) hr1 φ12) φ23) φ34) φ45
  · exact HasRoots.mapEmb (hM' := hM5) (HasRoots.mapEmb (hM' := hM4)
      (HasRoots.mapEmb (hM' := hM3) hr2 φ23) φ34) φ45
  · exact HasRoots.mapEmb (hM' := hM5) (HasRoots.mapEmb (hM' := hM4) hr3 φ34) φ45
  · exact nth_map (hM' := hM5) hS0 (HasRoots.mapEmb (hM' := hM4) hr3 φ34)
      (nth_of_done hn hSsq hdone4) φ45
  · letI : Fact (Irreducible (toPoly M5)) := ⟨Kron.irredQ_sound M5 hM5⟩
    obtain ⟨b, hb⟩ := nth_of_done hn hXsq hdone5 0 (by simp [CPoly.toPoly])
    refine ⟨b, ?_⟩
    rw [hb, show toPoly [f.getLastD 0] = C (f.getLastD 0) by simp [CPoly.toPoly], aeval_C,
      getLastD_eq_lc hfd hf0]

end Build

section Answer

set_option maxHeartbeats 3200000 in
/-- **`superDecideMobM` answers** over a field with the facts `MobField`, whenever the torsion
oracle answers. -/
theorem superDecideMobM_ne_none (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]
    (hM : Kron.irredQ M = true) (f : CPoly ℚ) {n : ℕ} (hn2 : 2 ≤ n) (hsq : Squarefree (toPoly f))
    (hd1 : 1 ≤ (toPoly f).natDegree) (hnd : n ∣ (toPoly f).natDegree) (A : List (CPoly ℚ))
    (D : CPoly ℚ) (hD : toPoly D ≠ 0) (B : ℕ) (hMF : MobField f (nbPartK f D) n M hM)
    (hans : ∀ P : CPoly (NF M), TorsAnswers P n
      (torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B P n)) :
    superDecideMobM M f n A D B ≠ none := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨hU, hF, hSr, hSn, hLc⟩ := hMF
  set S := nbPartK f D with hSdef
  have hX : Squarefree (toPoly (liftK (K := NF M) (xnMinus n (1 : ℚ)))) := by
    rw [toPoly_liftK]
    exact ((PerfectField.separable_iff_squarefree).mpr (sqf_xnMinus hn one_ne_zero)).map.squarefree
  obtain ⟨rz, hrz, hallz⟩ := rootsIn_complete M _ hX
  have hsqK : Squarefree (toPoly (liftK (K := NF M) f)) := by
    rw [toPoly_liftK]; exact ((PerfectField.separable_iff_squarefree).mpr hsq).map.squarefree
  obtain ⟨rf, hrf, hallf⟩ := rootsIn_complete M _ hsqK
  -- `f` has a root, so the list is non-empty
  obtain ⟨lf, hlf, hlflen, hlfr⟩ := hF
  obtain ⟨r0, hr0⟩ := List.exists_mem_of_length_pos (by omega : 0 < lf.length)
  have hr0f : r0 ∈ rf := hallf r0 (by rw [toPoly_liftK, eval_map_algebraMap]; exact hlfr r0 hr0)
  obtain ⟨e, rest, hrfe⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hr0f)
  have he : (toPoly (liftK (K := NF M) f)).eval e = 0 :=
    rootsIn_sound M _ hrf e (by rw [hrfe]; exact List.mem_cons_self)
  -- a primitive root of unity
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ : NF M, IsPrimitiveRoot ζ n := by
    obtain ⟨l, hl, hlen, hr⟩ := hU
    refine exists_primRoot_of_roots hn hl hlen fun a ha ↦ ?_
    have := hr a ha
    rw [toPoly_xnMinus hn] at this
    simpa [sub_eq_zero] using this
  have hζ0mem : ζ0 ∈ rz := hallz ζ0 (by
    rw [toPoly_liftK, eval_map_algebraMap, toPoly_xnMinus hn]; simp [hζ0.pow_eq_one])
  have hprim : isPrimRoot M n ζ0 = true := by
    simp only [isPrimRoot, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, beq_iff_eq]
    exact ⟨hζ0.pow_eq_one, fun l hl ↦ by
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by simpa using hζ0.pow_ne_one_of_pos_of_lt hpos.ne' hl)⟩
  obtain ⟨ζ, hfind⟩ : ∃ ζ, rz.find? (isPrimRoot M n) = some ζ :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨ζ0, hζ0mem, hprim⟩)
  have hζp : isPrimRoot M n ζ = true := List.find?_some hfind
  have hζ : IsPrimitiveRoot ζ n := isPrimRoot_spec hn hζp
  -- the non-branch part over `K` splits over the roots of `S`
  have hSsqK : Squarefree (toPoly (liftK (K := NF M) S)) := by
    rw [toPoly_liftK]
    exact ((PerfectField.separable_iff_squarefree).mpr (squarefree_nbPartK f D hD)).map.squarefree
  obtain ⟨rs, hrs, hallS⟩ := rootsIn_complete M _ hSsqK
  set as := rs.dedup with has
  have hasnd : as.Nodup := List.nodup_dedup _
  have hrootS : ∀ α ∈ as, aeval α (toPoly S) = 0 := fun α hα ↦ by
    have := rootsIn_sound M _ hrs α (List.mem_dedup.mp hα)
    rwa [toPoly_liftK, eval_map_algebraMap] at this
  have hcount : (toPoly S).natDegree ≤ as.length := by
    obtain ⟨l, hl, hlen', hr⟩ := hSr
    have hsub : l ⊆ as := fun a ha ↦ List.mem_dedup.mpr (hallS a (by
      rw [toPoly_liftK, eval_map_algebraMap]; exact hr a ha))
    exact hlen'.trans (hl.subperm hsub).length_le
  obtain ⟨lc, hlc, hSK⟩ := nbPart_split f D hD as hasnd hrootS hcount
  have hSKroot : ∀ a, (toPoly (nbPartK (liftK (K := NF M) f) (liftK (K := NF M) D))).eval a = 0 →
      a ∈ as := by
    intro a ha
    rw [hSK, eval_mul, eval_C, eval_prod] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact absurd h hlc
    · obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
      rw [hi]; exact List.get_mem _ _
  have hDK : toPoly (liftK (K := NF M) D) ≠ 0 := by
    rw [toPoly_liftK]; exact (Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr hD
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M (int_of_irredQ hM)).symm
  unfold superDecideMobM
  rw [hrz, hrf, hrfe]
  simp only [hfind, hζp, if_true]
  refine superFrontMob_ne_none (liftK f) hn2 hζ hsqK
    (by rw [toPoly_liftK, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective])
    hnd hd1 e he _
    (fun P hP hc ↦ torsOracle_spec (nfRedAt (M := M) (M.map Rat.num))
      (fun p _ R hR ↦ nfRedAt_valid _ hmZ p R hR) (primesBelow B) B hP hc) hans _
    (fun Q hQ a ↦ by
      obtain ⟨l, hl, hc⟩ := rootsIn_complete M Q hQ
      rw [hl, Option.getD_some]
      exact ⟨hc a, rootsIn_sound M Q hl a⟩) _
    (fun c b hc hb ↦ by
      have hxsq := sqf_xnMinus (K := NF M) hn hc
      obtain ⟨l, hl, hcl⟩ := rootsIn_complete M _ hxsq
      have hbl : b ∈ l := hcl b (by rw [toPoly_xnMinus hn]; simp [hb])
      obtain ⟨r, rest', hlr⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hbl)
      have hroot := rootsIn_sound M _ hl r (by rw [hlr]; exact List.mem_cons_self)
      rw [toPoly_xnMinus hn] at hroot
      simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
      rw [hl, hlr]
      simpa using hroot)
    _ _ hDK ⟨as, hasnd, ?_, ?_⟩ ?_ ?_
  · rw [hSK]
    refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun i _ ↦ natDegree_X_sub_C_le _).trans ?_
    simp
  · intro a ha
    rw [hSK, eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_univ ⟨as.idxOf a,
      List.idxOf_lt_length_of_mem ha⟩) (by simp), mul_zero]
  · intro a ha
    have ham := hSKroot a ha
    obtain ⟨b, hb⟩ := hSn a (hrootS a ham)
    exact ⟨b, by rw [hb, toPoly_liftK, eval_map_algebraMap]⟩
  · obtain ⟨c, hc⟩ := hLc
    exact ⟨c, by rw [hc, toPoly_liftK, leadingCoeff_map_of_injective
      (algebraMap ℚ (NF M)).injective]⟩

/-- **`superDecideMobQ` answers** for large fuel whenever the torsion oracle answers. -/
theorem superDecideMobQ_ne_none_of (f : CPoly ℚ) {n : ℕ} (hn2 : 2 ≤ n)
    (hsq : Squarefree (toPoly f)) (hfd : (toPoly f).natDegree = f.length - 1)
    (hd1 : 1 ≤ (toPoly f).natDegree) (hnd : n ∣ (toPoly f).natDegree) (A : List (CPoly ℚ))
    (D : CPoly ℚ) (hD : toPoly D ≠ 0) (B fuel : ℕ) (hfn : n < fuel)
    (hff : (toPoly f).natDegree < fuel) (hfS : (toPoly (nbPartK f D)).natDegree < fuel)
    (hans : ∀ (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (P : CPoly (NF M)), TorsAnswers P n
      (torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B P n)) :
    superDecideMobQ f n A D B fuel ≠ none := by
  obtain ⟨M, hM, hbuild, hMF⟩ := buildFieldMob_spec f (nbPartK f D) (by omega) hsq hfd hd1
    (squarefree_nbPartK f D hD) (isCoprime_nbPartK f D hD) fuel hfn hff hfS
  unfold superDecideMobQ
  rw [hbuild]
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  exact superDecideMobM_ne_none M hM f hn2 hsq hd1 hnd A D hD B hMF (hans M)

end Answer

end Sup
