import RischTragerBronstein.Algebraic.SupLogAlgo

/-!
# Semantics of the superelliptic logarithmic-part procedure
-/

open Polynomial CPoly

namespace Sup

section Comp

variable {F : Type*} [Field F] [DecidableEq F]

lemma evalB_eq : ∀ (W : BPoly F) (a b : F), evalB W a b = evalW (toB W) a b
  | [], a, b => by simp [evalB, evalW]
  | c :: W, a, b => by
    have := evalB_eq W a b
    simp only [evalB, List.foldr_cons] at this ⊢
    rw [this, Kron.evalC_eq]
    simp [evalW]

lemma toB_lsumB_cons (c : F) (cs : List F) (al : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    toB (lsumB (c :: cs) (al :: B)) =
      Polynomial.C (Polynomial.C c) * Polynomial.monomial al.2 (X ^ al.1) + toB (lsumB cs B) := by
  have e1 : toPoly ([c] : CPoly F) = Polynomial.C c := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]
  rw [lsumB, toB_addB, toB_smulB, toB_monoB, e1, ← Polynomial.C_mul_X_pow_eq_monomial]

lemma lsumW_cons (c : F) (cs : List F) (al : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    lsumW (c :: cs) (al :: B) =
      Polynomial.C (Polynomial.C c) * Polynomial.monomial al.2 (X ^ al.1) + lsumW cs B := by
  unfold lsumW
  rw [List.length_cons, Finset.sum_range_succ', add_comm]
  rfl

lemma toB_lsumB (cs : List F) (B : List (ℕ × ℕ)) (h : cs.length = B.length) :
    toB (lsumB cs B) = lsumW cs B := by
  induction cs generalizing B with
  | nil =>
    cases B with
    | nil => simp [lsumB, lsumW]
    | cons _ _ => simp at h
  | cons c cs ih =>
    cases B with
    | nil => simp at h
    | cons al B =>
      rw [toB_lsumB_cons, lsumW_cons, ih B (by simpa using h)]

/-- **Soundness of `supPrincipalC`, with the explicit witness.** -/
theorem supPrincipalC_sound_W (f : CPoly F) (n : ℕ) (hn : 0 < n) (d : ℕ) (Γ : List (F × F × ℕ))
    (M : ℕ) (hΓ : ∀ q ∈ Γ, (n : F) * q.2.1 ^ (n - 1) ≠ 0 ∧ q.2.1 ^ n = (toPoly f).eval q.1)
    {j : ℕ} {cs : List F} (h : supPrincipalC f n d Γ M = some (j, cs)) :
    (cs.set j 1).length = (basisN n d M).length ∧
    lsumW (cs.set j 1) (basisN n d M) ≠ 0 ∧
      (∀ i a, ((lsumW (cs.set j 1) (basisN n d M)).coeff i).coeff a ≠ 0 →
        i < n ∧ n * a + d * i ≤ M) ∧
      ∀ q ∈ Γ, VanishAtN (toPoly f) n (lsumW (cs.set j 1) (basisN n d M)) q.1 q.2.1 q.2.2 := by
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
  refine ⟨hlenB, ?_, ?_, ?_⟩
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

lemma mem_gammaL {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (s : ℕ) (q : F × F × ℕ) :
    q ∈ gammaL α β mq s ↔ ∃ i, (α i, β i, s * mq i) = q := by
  simp [gammaL, List.mem_ofFn]

/-- **The extracted witness.** -/
theorem witW_spec (f : CPoly F) (n : ℕ) (hn : 0 < n) (d : ℕ) {r : ℕ} (α β : Fin r → F)
    (mq : Fin r → ℕ) (N : ℕ) (hΓ : ∀ q, (n : F) * β q ^ (n - 1) ≠ 0 ∧ β q ^ n = (toPoly f).eval (α q))
    {Wb : BPoly F} (h : witW f n d α β mq N = some Wb) :
    toB Wb ≠ 0 ∧ (∀ i a, ((toB Wb).coeff i).coeff a ≠ 0 → i < n ∧ n * a + d * i ≤ N * ∑ q, mq q) ∧
      ∀ q, VanishAtN (toPoly f) n (toB Wb) (α q) (β q) (N * mq q) := by
  unfold witW at h
  split at h
  swap
  · cases h
  rename_i jj cs hs
  simp only [Option.some.injEq] at h
  subst h
  have hΓ' : ∀ q ∈ gammaL α β mq N, (n : F) * q.2.1 ^ (n - 1) ≠ 0 ∧
      q.2.1 ^ n = (toPoly f).eval q.1 := by
    intro q hq
    obtain ⟨i, rfl⟩ := (mem_gammaL α β mq N q).mp hq
    exact hΓ i
  obtain ⟨hlen, h0, hs', hv⟩ := supPrincipalC_sound_W f n hn d _ _ hΓ' hs
  rw [toB_lsumB _ _ hlen]
  exact ⟨h0, hs', fun q ↦ hv _ ((mem_gammaL α β mq N _).mpr ⟨q, rfl⟩)⟩

/-- **The witness is found** when `N Γ` is principal. -/
theorem witW_ne_none (f : CPoly F) (n : ℕ) (hn : 0 < n) (d : ℕ) {r : ℕ} (α β : Fin r → F)
    (mq : Fin r → ℕ) (N : ℕ) (hΓ : ∀ q, (n : F) * β q ^ (n - 1) ≠ 0 ∧ β q ^ n = (toPoly f).eval (α q))
    (hP : PrincipalMulN (toPoly f) n d α β mq N) : witW f n d α β mq N ≠ none := by
  obtain ⟨W, hW0, hWs, hWv⟩ := hP
  have hΓ' : ∀ q ∈ gammaL α β mq N, (n : F) * q.2.1 ^ (n - 1) ≠ 0 ∧
      q.2.1 ^ n = (toPoly f).eval q.1 := by
    intro q hq
    obtain ⟨i, rfl⟩ := (mem_gammaL α β mq N q).mp hq
    exact hΓ i
  have hne := supPrincipalC_complete (RingHom.id F) f n hn d _ _ hΓ' W hW0 hWs (by
    intro q hq
    obtain ⟨i, rfl⟩ := (mem_gammaL α β mq N q).mp hq
    simpa using hWv i)
  unfold witW
  obtain ⟨⟨jj, cs⟩, hjc⟩ := Option.ne_none_iff_exists'.mp hne
  rw [hjc]
  simp

lemma toPoly_prodC : ∀ l : List (CPoly F), toPoly (prodC l) = (l.map toPoly).prod
  | [] => by simp [prodC, CPoly.toPoly]
  | c :: l => by
    have := toPoly_prodC l
    simp only [prodC, List.foldr_cons, List.map_cons, List.prod_cons, toPoly_mul] at this ⊢
    rw [this]

lemma toB_prodB : ∀ l : List (BPoly F), toB (prodB l) = (l.map toB).prod
  | [] => by simp [prodB, CPoly.toPoly]
  | c :: l => by
    have := toB_prodB l
    simp only [prodB, List.foldr_cons, List.map_cons, List.prod_cons, toB_mulB] at this ⊢
    rw [this]

lemma toB_sumB : ∀ l : List (BPoly F), toB (sumB l) = (l.map toB).sum
  | [] => by simp [sumB]
  | c :: l => by
    have := toB_sumB l
    simp only [sumB, List.foldr_cons, List.map_cons, List.sum_cons, toB_addB] at this ⊢
    rw [this]

lemma toPoly_linC (a : F) : toPoly (linC a) = X - Polynomial.C a := by
  simp [linC, CPoly.toPoly]; ring

lemma toPoly_prodP {m : ℕ} (a : Fin m → F) :
    toPoly (prodC ((List.finRange m).map fun i ↦ linC (a i))) = ∏ i, (X - Polynomial.C (a i)) := by
  rw [toPoly_prodC, List.map_map, Fin.prod_univ_def]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp [toPoly_linC]

lemma toPoly_prodExc {m : ℕ} (a : Fin m → F) (i : Fin m) :
    toPoly (prodExc a i) = ∏ i' ∈ Finset.univ.erase i, (X - Polynomial.C (a i')) := by
  rw [prodExc, toPoly_prodC, List.map_map, ← Fin.prod_univ_def]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.comp_apply, if_true]
  rw [show toPoly ([1] : CPoly F) = 1 by simp [CPoly.toPoly], one_mul]
  refine Finset.prod_congr rfl fun i' hi' ↦ ?_
  rw [if_neg (Finset.ne_of_mem_erase hi'), toPoly_linC]

lemma prodP_eq {m : ℕ} (a : Fin m → F) (i : Fin m) :
    ∏ i', (X - Polynomial.C (a i')) = (X - Polynomial.C (a i)) * toPoly (prodExc a i) := by
  rw [toPoly_prodExc, Finset.mul_prod_erase _ (fun i' ↦ X - Polynomial.C (a i')) (Finset.mem_univ i)]

end Comp

end Sup
