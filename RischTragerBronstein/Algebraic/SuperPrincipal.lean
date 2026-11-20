import RischTragerBronstein.Algebraic.SuperJets
import RischTragerBronstein.Algebraic.NullSearch

/-!
# A computable principality test on superelliptic curves

For `yⁿ = f(x)` over a computable field `F`, an effective divisor `Γ` (points `(α, β)` with
`n βⁿ⁻¹ ≠ 0`, multiplicities `m`) and a pole bound `M`, `supPrincipalC` looks for a non-zero
`W = ∑ Wᵢ(x) yⁱ` built from the monomials `xᵃ yⁱ` with `n a + d i ≤ M` (`d = deg f`) that
vanishes on `Γ`: the truncated jets of the monomials (branch jets by Newton's iteration) are the
columns of a linear system (`nullSearch`).

* `supPrincipalC_sound`: an answer is such a `W`;
* `supPrincipalC_complete`: if such a `W` exists over an extension field, the test answers.
-/

open Polynomial CPoly

namespace Sup

section Sem

variable {L : Type*} [Field L]

/-- The semantics of a column: truncated jets, one block per point. -/
noncomputable def colSemN : List (L × L × ℕ) → List L[X] → L[X][X] → L[X]
  | q :: Γ, V :: Vs, W => Jac.truncX q.2.2 (jetN W q.1 V) + X ^ q.2.2 * colSemN Γ Vs W
  | _, _, _ => 0

lemma colSemN_add : ∀ (Γ : List (L × L × ℕ)) (Vs : List L[X]) (W W' : L[X][X]),
    colSemN Γ Vs (W + W') = colSemN Γ Vs W + colSemN Γ Vs W'
  | [], _, _, _ => by simp [colSemN]
  | _ :: _, [], _, _ => by simp [colSemN]
  | q :: Γ, V :: Vs, W, W' => by
    simp only [colSemN, jetN_add, Jac.truncX_add, colSemN_add Γ Vs]; ring

lemma colSemN_C_mul : ∀ (Γ : List (L × L × ℕ)) (Vs : List L[X]) (c : L) (W : L[X][X]),
    colSemN Γ Vs (Polynomial.C (Polynomial.C c) * W) = Polynomial.C c * colSemN Γ Vs W
  | [], _, _, _ => by simp [colSemN]
  | _ :: _, [], _, _ => by simp [colSemN]
  | q :: Γ, V :: Vs, c, W => by
    simp only [colSemN, jetN_C_mul, Jac.truncX_C_mul, colSemN_C_mul Γ Vs]; ring

lemma colSemN_zero : ∀ (Γ : List (L × L × ℕ)) (Vs : List L[X]), colSemN Γ Vs 0 = 0
  | [], _ => by simp [colSemN]
  | _ :: _, [] => by simp [colSemN]
  | q :: Γ, V :: Vs => by simp [colSemN, jetN, Jac.truncX, colSemN_zero Γ Vs]

lemma colSemN_sum {ι : Type*} (s : Finset ι) (Γ : List (L × L × ℕ)) (Vs : List L[X])
    (c : ι → L) (W : ι → L[X][X]) :
    colSemN Γ Vs (∑ k ∈ s, Polynomial.C (Polynomial.C (c k)) * W k) =
      ∑ k ∈ s, Polynomial.C (c k) * colSemN Γ Vs (W k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [colSemN_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, colSemN_add, ih,
      colSemN_C_mul]

lemma colSemN_zero_iff : ∀ (Γ : List (L × L × ℕ)) (Vs : List L[X]) (W : L[X][X]),
    Vs.length = Γ.length →
    (colSemN Γ Vs W = 0 ↔ ∀ i : Fin Γ.length, X ^ Γ[i].2.2 ∣ jetN W Γ[i].1 Vs[i]!)
  | [], _, _, _ => by simp [colSemN]
  | q :: Γ, [], _, h => by simp at h
  | q :: Γ, V :: Vs, W, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := colSemN_zero_iff Γ Vs W h
    simp only [colSemN]
    constructor
    · intro h0 i
      have h1 : Jac.truncX q.2.2 (jetN W q.1 V) = 0 := by
        ext t
        have := congrArg (coeff · t) h0
        simp only [coeff_add, coeff_zero] at this ⊢
        rw [Jac.coeff_truncX] at this ⊢
        split_ifs with ht
        · rwa [if_pos ht, coeff_X_pow_mul', if_neg (by omega), add_zero] at this
        · rfl
      have h2 : colSemN Γ Vs W = 0 := by
        rw [h1, zero_add] at h0
        exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ X_ne_zero)
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => exact (Jac.truncX_eq_zero_iff _ _).mp h1
      | succ i =>
        have := (ih.mp h2) ⟨i, by simpa using hi⟩
        simpa using this
    · intro hall
      have h1 := (Jac.truncX_eq_zero_iff _ _).mpr (by simpa using hall ⟨0, by simp⟩)
      have h2 := ih.mpr fun i ↦ by simpa using hall ⟨i.1 + 1, by simp⟩
      rw [h1, h2]; simp

end Sem

section Comp

variable {F : Type*} [Field F] [DecidableEq F]

/-- The monomials `xᵃ yⁱ` with `n a + d i ≤ M`. -/
def basisN (n d M : ℕ) : List (ℕ × ℕ) :=
  ((List.range (M + 1)).flatMap fun a ↦ (List.range n).map fun i ↦ (a, i)).filter
    fun ai ↦ n * ai.1 + d * ai.2 ≤ M

lemma mem_basisN (n d M a i : ℕ) (hn : 0 < n) :
    (a, i) ∈ basisN n d M ↔ i < n ∧ n * a + d * i ≤ M := by
  simp only [basisN, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a', ha', i', hi', rfl, rfl⟩, h⟩
    exact ⟨hi', h⟩
  · rintro ⟨hi, h⟩
    refine ⟨⟨a, ?_, i, hi, rfl, rfl⟩, h⟩
    have : a ≤ n * a := Nat.le_mul_of_pos_left a hn
    omega

lemma nodup_basisN (n d M : ℕ) : (basisN n d M).Nodup := by
  refine List.Nodup.filter _ ?_
  refine List.nodup_flatMap.mpr ⟨fun a _ ↦ (List.nodup_range).map (fun i j h ↦ by
    simpa using h), ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab ↦ ?_
  intro x hx hy
  simp only [List.mem_map] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨i', -, h⟩ := hy
  exact hab (congrArg Prod.fst h).symm

/-- The column of the monomial `xᵃ yⁱ`, with precomputed branches. -/
def colN (Γ : List (F × F × ℕ)) (Vs : List (CPoly F)) (ai : ℕ × ℕ) : CPoly F :=
  (List.zipWith (fun q V ↦ Jac.truncC q.2.2
    (mul (Jac.taylorC q.1 (CPoly.monomial ai.1 1)) (powC V ai.2))) Γ Vs).flatten

/-- The branches used by the columns. -/
def branchesN (f : CPoly F) (n : ℕ) (Γ : List (F × F × ℕ)) : List (CPoly F) :=
  Γ.map fun q ↦ branchCN f n q.1 q.2.1 q.2.2

/-- The columns. -/
def colsN (f : CPoly F) (n d : ℕ) (Γ : List (F × F × ℕ)) (M : ℕ) : List (CPoly F) :=
  (basisN n d M).map (colN Γ (branchesN f n Γ))

/-- **The principality test.** -/
def supPrincipalC (f : CPoly F) (n d : ℕ) (Γ : List (F × F × ℕ)) (M : ℕ) : Option (ℕ × List F) :=
  nullSearch (colsN f n d Γ M)

lemma toPoly_monomial_taylor (α : F) (a : ℕ) :
    toPoly (Jac.taylorC α (CPoly.monomial a 1)) = (X + C α) ^ a := by
  rw [Jac.toPoly_taylorC, toPoly_monomial, map_one, one_mul, X_pow_comp]

lemma toPoly_colN : ∀ (Γ : List (F × F × ℕ)) (Vs : List (CPoly F)) (ai : ℕ × ℕ),
    toPoly (colN Γ Vs ai) = colSemN Γ (Vs.map toPoly) (Polynomial.monomial ai.2 (X ^ ai.1))
  | [], _, ai => by simp [colN, colSemN]
  | _ :: _, [], ai => by simp [colN, colSemN]
  | q :: Γ, V :: Vs, ai => by
    rw [colN, List.zipWith_cons_cons, List.flatten_cons, toPoly_append,
      show (List.zipWith (fun q V ↦ Jac.truncC q.2.2
        (mul (Jac.taylorC q.1 (CPoly.monomial ai.1 1)) (powC V ai.2))) Γ Vs).flatten =
          colN Γ Vs ai from rfl, toPoly_colN Γ Vs ai]
    simp only [List.map_cons, colSemN]
    congr 1
    · rw [Jac.toPoly_truncC, toPoly_mul, toPoly_monomial_taylor, toPoly_powC, jetN_monomial]
    · simp [Jac.length_truncC]

end Comp

section Lin

variable {F : Type*} [Field F] [DecidableEq F] {S : Type*} [Field S] (φ : F →+* S)

lemma IsBranchN.map {f : F[X]} {n : ℕ} {α β : F} {ℓ : ℕ} {V : F[X]}
    (h : IsBranchN f n α β ℓ V) : IsBranchN (f.map φ) n (φ α) (φ β) ℓ (V.map φ) := by
  refine ⟨by rw [coeff_map, h.1], ?_⟩
  obtain ⟨G, hG⟩ := h.2
  refine ⟨G.map φ, ?_⟩
  have := congrArg (Polynomial.map φ) hG
  simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_comp] using this

lemma IsBranchN.mono {R : Type*} [CommRing R] {f : R[X]} {n : ℕ} {α β : R} {ℓ ℓ' : ℕ}
    {V : R[X]} (h : IsBranchN f n α β ℓ V) (hl : ℓ' ≤ ℓ) : IsBranchN f n α β ℓ' V :=
  ⟨h.1, (pow_dvd_pow X hl).trans h.2⟩

/-- `∑ₖ cₖ xᵃᵏ yⁱᵏ`. -/
noncomputable def lsumW (cs : List S) (B : List (ℕ × ℕ)) : S[X][X] :=
  ∑ k ∈ Finset.range B.length, Polynomial.C (Polynomial.C (cs.getD k 0)) *
    Polynomial.monomial (B.getD k (0, 0)).2 (X ^ (B.getD k (0, 0)).1)

lemma lcombS_eq_sum : ∀ (cs : List S) (vs : List (CPoly F)), cs.length = vs.length →
    lcombS φ cs vs = ∑ k ∈ Finset.range vs.length, Polynomial.C (cs.getD k 0) *
      (toPoly (vs.getD k [])).map φ
  | [], [], _ => by simp [lcombS]
  | c :: cs, v :: vs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← lcombS_eq_sum cs vs h]
    simp [lcombS, add_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

lemma colSemN_map : ∀ (Γ : List (F × F × ℕ)) (Vs : List F[X]) (W : F[X][X]),
    (colSemN Γ Vs W).map φ = colSemN (Γ.map fun q ↦ (φ q.1, φ q.2.1, q.2.2))
      (Vs.map (Polynomial.map φ)) (W.map (mapRingHom φ))
  | [], _, _ => by simp [colSemN]
  | _ :: _, [], _ => by simp [colSemN]
  | q :: Γ, V :: Vs, W => by
    simp only [colSemN, List.map_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, colSemN_map Γ Vs W, jetN_map]
    congr 1
    simp only [Jac.truncX, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow,
      Polynomial.map_X, coeff_map, ← jetN_map]

lemma lcombS_colsN (f : CPoly F) (n d : ℕ) (Γ : List (F × F × ℕ)) (M : ℕ) (cL : List S)
    (hcL : cL.length = (basisN n d M).length) :
    lcombS φ cL (colsN f n d Γ M) = colSemN (Γ.map fun q ↦ (φ q.1, φ q.2.1, q.2.2))
      (((branchesN f n Γ).map toPoly).map (Polynomial.map φ)) (lsumW cL (basisN n d M)) := by
  rw [lcombS_eq_sum φ _ _ (by simp [colsN, hcL]), lsumW, colSemN_sum]
  simp only [colsN, List.length_map]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < (basisN n d M).length := Finset.mem_range.mp hk
  have hcol : ((basisN n d M).map (colN Γ (branchesN f n Γ))).getD k [] =
      colN Γ (branchesN f n Γ) ((basisN n d M).getD k (0, 0)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk',
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    rfl
  rw [hcol, toPoly_colN, colSemN_map]
  congr 2
  simp [Polynomial.map_monomial]

lemma coeff_lsumW (cs : List S) (B : List (ℕ × ℕ)) (hnd : B.Nodup) (a i : ℕ) :
    ((lsumW cs B).coeff i).coeff a =
      if (a, i) ∈ B then cs.getD (B.idxOf (a, i)) 0 else 0 := by
  classical
  simp only [lsumW, finsetSum_coeff, coeff_C_mul, coeff_monomial]
  have hterm : ∀ k ∈ Finset.range B.length,
      cs.getD k 0 * (if (B.getD k (0, 0)).2 = i then
        X ^ (B.getD k (0, 0)).1 else 0).coeff a =
        if B.getD k (0, 0) = (a, i) then cs.getD k 0 else 0 := by
    intro k _
    split_ifs with h1 h2 h2
    · rw [coeff_X_pow, if_pos (congrArg Prod.fst h2).symm, mul_one]
    · rw [coeff_X_pow, if_neg (fun h ↦ h2 (Prod.ext h.symm h1)), mul_zero]
    · exact absurd (congrArg Prod.snd h2) h1
    · simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hmem
  · have hidx : B.idxOf (a, i) < B.length := List.idxOf_lt_length_iff.mpr hmem
    rw [Finset.sum_eq_single (B.idxOf (a, i))]
    · rw [if_pos]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some,
        List.getElem_idxOf]
    · intro k hk hne
      rw [if_neg]
      intro h
      apply hne
      have hk' := Finset.mem_range.mp hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at h
      rw [← h]
      exact (show List.idxOf B[k] B = k by simp [hnd]).symm
    · intro h; exact absurd (Finset.mem_range.mpr hidx) h
  · refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [if_neg]
    intro h
    have hk' := Finset.mem_range.mp hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at h
    exact hmem (h ▸ List.getElem_mem _)

end Lin

section Main

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Soundness of the principality test.** -/
theorem supPrincipalC_sound (f : CPoly F) (n : ℕ) (hn : 0 < n) (d : ℕ) (Γ : List (F × F × ℕ))
    (M : ℕ) (hΓ : ∀ q ∈ Γ, (n : F) * q.2.1 ^ (n - 1) ≠ 0 ∧ q.2.1 ^ n = (toPoly f).eval q.1)
    {j : ℕ} {cs : List F} (h : supPrincipalC f n d Γ M = some (j, cs)) :
    ∃ W : F[X][X], W ≠ 0 ∧ (∀ i a, (W.coeff i).coeff a ≠ 0 → i < n ∧ n * a + d * i ≤ M) ∧
      ∀ q ∈ Γ, VanishAtN (toPoly f) n W q.1 q.2.1 q.2.2 := by
  classical
  obtain ⟨hj, hlen, hfj, h0⟩ := nullSearch_sound _ h
  set full := cs.set j 1
  set B := basisN n d M
  have hlenB : full.length = B.length := by rw [hlen]; simp [colsN, B]
  rw [lcombS_colsN (RingHom.id F) f n d Γ M full hlenB] at h0
  simp only [Polynomial.map_id, List.map_id', RingHom.id_apply] at h0
  have hmapid : (Polynomial.map (RingHom.id F) : F[X] → F[X]) = id :=
    funext fun P ↦ Polynomial.map_id
  rw [hmapid, List.map_id] at h0
  set W := lsumW full B
  have hjB : j < B.length := by simpa [colsN, B] using hj
  refine ⟨W, ?_, ?_, ?_⟩
  · intro hW
    have hmem : B[j] ∈ B := List.getElem_mem hjB
    have := coeff_lsumW full B (nodup_basisN n d M) B[j].1 B[j].2
    rw [if_pos (by simpa using hmem), show ((B[j].1, B[j].2) : ℕ × ℕ) = B[j] from rfl,
      show List.idxOf B[j] B = j by simp [nodup_basisN, B], hfj] at this
    have hW' : lsumW full B = 0 := hW
    rw [hW'] at this
    simp at this
  · intro i a hia
    have := coeff_lsumW full B (nodup_basisN n d M) a i
    split_ifs at this with hmem
    · exact (mem_basisN n d M a i hn).mp hmem
    · exact absurd this hia
  · intro q hq
    obtain ⟨k, rfl⟩ := List.get_of_mem hq
    have hz := (colSemN_zero_iff Γ ((branchesN f n Γ).map toPoly) W
      (by simp [branchesN])).mp h0 ⟨k, by simpa using k.2⟩
    obtain ⟨hu, hy⟩ := hΓ _ (List.get_mem _ _)
    refine ⟨_, (branchCN_spec f n hn _ _ hu hy _).mono (Nat.le_succ _), ?_⟩
    simpa [branchesN] using hz

/-- **Completeness of the principality test over extension fields.** -/
theorem supPrincipalC_complete {S : Type*} [Field S] (φ : F →+* S) (f : CPoly F) (n : ℕ)
    (hn : 0 < n) (d : ℕ) (Γ : List (F × F × ℕ)) (M : ℕ)
    (hΓ : ∀ q ∈ Γ, (n : F) * q.2.1 ^ (n - 1) ≠ 0 ∧ q.2.1 ^ n = (toPoly f).eval q.1)
    (W : S[X][X]) (hW0 : W ≠ 0) (hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < n ∧ n * a + d * i ≤ M)
    (hv : ∀ q ∈ Γ, VanishAtN ((toPoly f).map φ) n W (φ q.1) (φ q.2.1) q.2.2) :
    supPrincipalC f n d Γ M ≠ none := by
  classical
  set B := basisN n d M
  set cL : List S := B.map fun ai ↦ (W.coeff ai.2).coeff ai.1
  have hcL : cL.length = B.length := by simp [cL]
  have hW : lsumW cL B = W := by
    ext i a
    rw [coeff_lsumW cL B (nodup_basisN n d M)]
    split_ifs with hmem
    · have hidx : B.idxOf (a, i) < B.length := List.idxOf_lt_length_iff.mpr hmem
      simp [cL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx]
    · by_contra hne
      exact hmem ((mem_basisN n d M a i hn).mpr (hsupp i a (Ne.symm hne)))
  refine nullSearch_complete φ _ cL (by simp [colsN, hcL, B]) ?_ ?_
  · -- a non-zero coordinate
    by_contra hall
    push_neg at hall
    apply hW0
    rw [← hW]
    ext i a
    rw [coeff_lsumW cL B (nodup_basisN n d M)]
    split_ifs with hmem
    · have hidx : B.idxOf (a, i) < B.length := List.idxOf_lt_length_iff.mpr hmem
      rw [hall _ (by simpa [colsN, B] using hidx)]
      simp
    · simp
  · rw [lcombS_colsN φ f n d Γ M cL hcL, hW]
    refine (colSemN_zero_iff _ _ _ (by simp [branchesN])).mpr fun i ↦ ?_
    simp only [List.getElem_map, List.getElem!_eq_getElem?_getD, List.getElem?_map, branchesN]
    have hi : i.1 < Γ.length := by simpa using i.2
    obtain ⟨hu, hy⟩ := hΓ _ (List.getElem_mem hi)
    have hbr := (branchCN_spec f n hn _ _ hu hy (Γ[i.1]'hi).2.2).map φ
    obtain ⟨V', hV', hdv⟩ := hv _ (List.getElem_mem hi)
    have huS : IsUnit ((n : S) * φ (Γ[i.1]'hi).2.1 ^ (n - 1)) := by
      refine IsUnit.mk0 _ ?_
      rw [← map_natCast φ, ← map_pow, ← map_mul]; exact (map_ne_zero_iff φ φ.injective).mpr hu
    have hcong := branchN_unique hn huS (hbr.mono (Nat.le_succ _)) hV'
    have := dvd_sub (jetN_congr W (φ (Γ[i.1]'hi).1) hcong) (dvd_neg.mpr hdv)
    rw [sub_neg_eq_add, sub_add_cancel] at this
    simpa [List.getElem?_eq_getElem hi] using this

end Main

end Sup
