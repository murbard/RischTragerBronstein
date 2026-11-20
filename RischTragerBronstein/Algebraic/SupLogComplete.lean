import RischTragerBronstein.Algebraic.SupLogAbelPart

/-!
# Completeness of the superelliptic logarithmic-part procedure
-/

open Polynomial CPoly Differential IntermediateField

namespace Sup

section Helpers

variable {F : Type*} [Field F]

lemma bound_of_coeff (n d : ℕ) (W : BPoly F) (i c : ℕ) (h : ((toB W).coeff i).coeff c ≠ 0) :
    i < W.length ∧ n * c + d * i ≤ boundB n d W := by
  rw [coeff_toB, CPoly.coeff_toPoly] at h
  have hi : i < W.length := by
    by_contra hi; push_neg at hi
    rw [List.getD_eq_default _ _ hi] at h; exact h (by simp)
  have hc : c < (W.getD i []).length := by
    by_contra hc; push_neg at hc; exact h (List.getD_eq_default _ _ hc)
  have := length_le_maxLenB W i
  refine ⟨hi, ?_⟩
  unfold boundB
  have h1 : n * c ≤ n * maxLenB W := Nat.mul_le_mul_left _ (by omega)
  have h2 : d * i ≤ d * W.length := Nat.mul_le_mul_left _ hi.le
  omega

/-- The support of `V` in the basis gives `V = lsumW`. -/
lemma lsumW_of_support {C : Type*} [Field C] (n d M : ℕ) (hn : 0 < n) (V : C[X][X])
    (hsupp : ∀ i a, (V.coeff i).coeff a ≠ 0 → i < n ∧ n * a + d * i ≤ M) :
    lsumW ((basisN n d M).map fun ai ↦ (V.coeff ai.2).coeff ai.1) (basisN n d M) = V := by
  classical
  set B := basisN n d M
  set cL : List C := B.map fun ai ↦ (V.coeff ai.2).coeff ai.1
  ext i a
  rw [coeff_lsumW cL B (nodup_basisN n d M)]
  split_ifs with hmem
  · have hidx : B.idxOf (a, i) < B.length := List.idxOf_lt_length_iff.mpr hmem
    simp [cL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx]
  · by_contra hne
    exact hmem ((mem_basisN n d M a i hn).mpr (hsupp i a (Ne.symm hne)))

end Helpers

section Eval

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L : Type*} [Field C] [Field L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero L]

lemma evalE_map_id (ψ : F →+* C) (x y : L) (W : F[X][X]) :
    evalE (RingHom.id C) x y (W.map (mapRingHom ψ)) = evalE ψ x y W := by
  simp only [evalE, coe_eval₂RingHom, eval₂_map]
  congr 1
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_ <;> simp

lemma lsumW_cons' (c : C) (cs : List C) (al : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    lsumW (c :: cs) (al :: B) =
      Polynomial.C (Polynomial.C c) * Polynomial.monomial al.2 (X ^ al.1) + lsumW cs B := by
  unfold lsumW
  rw [List.length_cons, Finset.sum_range_succ', add_comm]
  rfl

lemma evalE_lsumW (x y : L) : ∀ (cs : List C) (B : List (ℕ × ℕ)), cs.length = B.length →
    evalE (RingHom.id C) x y (lsumW cs B) =
      (List.zipWith (fun c al ↦ algebraMap C L c * (x ^ al.1 * y ^ al.2)) cs B).sum
  | [], [], _ => by simp [lsumW]
  | c :: cs, al :: B, h => by
    rw [lsumW_cons', map_add, evalE_lsumW x y cs B (by simpa using h), List.zipWith_cons_cons,
      List.sum_cons, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, evalE_C, map_pow, evalE_X, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, aeval_C, aeval_X, RingHom.id_apply]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

lemma evalE_combBS (hC : ∀ c : C, c′ = 0) (ψ : F →+* C) (x y : L) (hx : x′ = 1) (f : CPoly F)
    {n : ℕ} (hn : 0 < n) (hy0 : y ≠ 0) (hy : y ^ n = aeval x ((toPoly f).map ψ)) (Mm : BPoly F) :
    ∀ (cs : List C) (basis : List (ℕ × ℕ)), cs.length = basis.length →
    evalE (RingHom.id C) x y (combBS ψ cs (exactCols f n hn Mm basis)) =
      evalE ψ x y (toB Mm) * (aeval x ((toPoly f).map ψ) *
        ((List.zipWith (fun c al ↦ algebraMap C L c * (x ^ al.1 * y ^ al.2)) cs basis).sum)′)
  | [], [], _ => by simp [combBS, exactCols]
  | c :: cs, al :: B, h => by
    have ih := evalE_combBS hC ψ x y hx f hn hy0 hy Mm cs B (by simpa using h)
    simp only [exactCols, List.map_cons] at ih ⊢
    simp only [combBS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [map_add, ih, map_mul, evalE_C, evalE_map_id, evalE_reduceB ψ x y f hn hy,
      toB_mulB, map_mul, evalE_derivB (Kc := C) (E := L) hC x y hx ψ f hn hy0 hy, evalE_monoB]
    have hc : (algebraMap C L c)′ = 0 := by rw [deriv_algebraMap, hC, map_zero]
    simp only [Polynomial.map_C, RingHom.id_apply, aeval_C, map_add, Derivation.leibniz, hc,
      smul_zero, add_zero, smul_eq_mul]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end Eval

section Complete

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]

open EllQuad.QCoords Differential.SuperData

lemma mqJ_sub_negJ {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (j : Fin (dim F)) (q : Fin (m * n)) :
    ((mqJ n ζ a b G j q : ℕ) : ℤ) - negJ n ζ a b G j (fibI q) = zJ n ζ a b G j (fibI q) (fibK q) := by
  have hle : (-(zJ n ζ a b G j (fibI q) (fibK q))).toNat ≤ negJ n ζ a b G j (fibI q) :=
    Finset.single_le_sum (f := fun k : Fin n ↦ (-(zJ n ζ a b G j (fibI q) k)).toNat)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (fibK q))
  have h1 : 0 ≤ zJ n ζ a b G j (fibI q) (fibK q) + negJ n ζ a b G j (fibI q) := by
    have := Int.self_le_toNat (-(zJ n ζ a b G j (fibI q) (fibK q)))
    omega
  rw [mqJ, Int.toNat_of_nonneg h1]
  ring

lemma combBS_coeff_ge {K' : Type*} [Field K'] (φ : F →+* K') {n : ℕ} :
    ∀ (cs : List K') (cols : List (BPoly F)), (∀ W ∈ cols, W.length ≤ n) →
      ∀ i, n ≤ i → (combBS φ cs cols).coeff i = 0
  | [], _, _, i, _ => by simp [combBS]
  | _ :: _, [], _, i, _ => by simp [combBS]
  | c :: cs, W :: cols, h, i, hi => by
    have ih := combBS_coeff_ge φ cs cols (fun W' hW' ↦ h W' (List.mem_cons_of_mem _ hW')) i hi
    simp only [combBS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [coeff_add, ih, coeff_C_mul, coeff_map, toB_coeff_ge W (h W List.mem_cons_self) i hi]
    simp

/-- The residue is recovered from its components. -/
lemma resK_repr {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (N : Fin (dim F) → ℕ) (hN : ∀ j, N j ≠ 0) (i : Fin m) (k : Fin n) :
    resK ζ a b G i k = ∑ j, cJ n ζ a b G j (N j) * ((N j : F) * (zJ n ζ a b G j i k : F)) := by
  conv_lhs => rw [EllQuad.QCoords.repr (resK ζ a b G i k)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hD : (denJ n ζ a b G j : F) ≠ 0 := Nat.cast_ne_zero.mpr (EllQuad.denL_ne_zero _)
  have hNj : (N j : F) ≠ 0 := Nat.cast_ne_zero.mpr (hN j)
  have hc := coord_resK_eq n ζ a b G j i k
  have hcF : ((coord j (resK ζ a b G i k) : ℚ) : F) =
      (zJ n ζ a b G j i k : F) / (denJ n ζ a b G j : F) := by
    rw [← hc]; push_cast; rfl
  rw [hcF, cJ]
  field_simp

lemma le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

set_option maxHeartbeats 4000000 in
/-- **Completeness**: if the concrete integrand is a Liouville form and the logarithms `Wⱼ` of all
components are known, the exactness test succeeds. -/
theorem exact_complete (S : SuperData C L) (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (ψ : F →+* C) (f : CPoly F) {n : ℕ} (hn : 0 < n) (hSn : S.n = n)
    (hSp : S.p = (toPoly f).map ψ) (hdeg : (toPoly f).natDegree = f.length - 1)
    (hcop : Nat.Coprime n (f.length - 1)) {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (a b : Fin m → F) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i)) (B B₁ : BPoly F) (G : Fin m → BPoly F)
    (hBn : B.length ≤ n) (hB₁n : B₁.length ≤ n) (hB₁0 : (toB B₁).coeff 0 = 0)
    (hGn : ∀ i, (G i).length ≤ n) (NW : Fin (dim F) → ℕ × BPoly F)
    (hNW : ∀ j, 1 ≤ (NW j).1 ∧ toB (NW j).2 ≠ 0 ∧
      (∀ i c, ((toB (NW j).2).coeff i).coeff c ≠ 0 →
        i < n ∧ n * c + (f.length - 1) * i ≤ (NW j).1 * ∑ q, mqJ n ζ a b G j q) ∧
      ∀ q, VanishAtN (toPoly f) n (toB (NW j).2) (ptA n a q) (ptB n ζ b q)
        ((NW j).1 * mqJ n ζ a b G j q))
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ιI : Type} (sI : Finset ιI) (d w : ιI → L)
    (hd : ∀ i ∈ sI, (d i)′ = 0) (hw : ∀ i ∈ sI, w i ≠ 0 ∧ w i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : ((S.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i) :
      C⟮S.x⟯⟮S.y⟯) : L) = v′ + ∑ i ∈ sI, d i * logDeriv (w i)) :
    exactTest f n hn (logMT f n ζ a b G B B₁ NW).1 (logMT f n ζ a b G B B₁ NW).2
      (basisN n (f.length - 1) (boundH f n B B₁ G + n)) ≠ none := by
  classical
  set K := AlgebraicClosure C
  set ψ' : F →+* K := (algebraMap C K).comp ψ with hψ'
  have hψi : Function.Injective ψ' := ψ'.injective
  have hSd : S.p.natDegree = f.length - 1 := by
    rw [hSp, natDegree_map_eq_of_injective ψ.injective, hdeg]
  have hcopS : Nat.Coprime S.n S.p.natDegree := by rw [hSn, hSd]; exact hcop
  set P : Fin (m * n) → K × K := fun q ↦ (ψ' (ptA n a q), ψ' (ptB n ζ b q)) with hP_def
  have hPinj : Function.Injective P := by
    intro q q' h
    simp only [hP_def, Prod.mk.injEq] at h
    exact pt_injective hζ a b ha hb (Prod.ext (hψi h.1) (hψi h.2))
  have hpK : S.p.map (algebraMap C K) = (toPoly f).map ψ' := by rw [hSp, Polynomial.map_map]
  have hP0 : ∀ q, (P q).2 ≠ 0 := fun q ↦ (map_ne_zero_iff _ hψi).mpr (pt_ne_zero hn hζ b hb q)
  set d0 := f.length - 1 with hd0
  set H := boundH f n B B₁ G with hH
  set Wc : Fin (dim F) → C[X][X] := fun j ↦ mapB ψ (NW j).2 with hWc
  -- the divisors of the `Wⱼ`
  have hdiv : ∀ j, S.elemW (Wc j) ≠ 0 ∧ S.IsIntegralS K (S.elemW (Wc j)) ∧
      (∀ q, S.ordAt K (S.elemW (Wc j)) (algebraMap C K (ψ (ptA n a q)))
        (algebraMap C K (ψ (ptB n ζ b q))) = ((NW j).1 * mqJ n ζ a b G j q : ℕ)) ∧
      (∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α →
        (∀ q, (α, β) ≠ (algebraMap C K (ψ (ptA n a q)), algebraMap C K (ψ (ptB n ζ b q)))) →
        S.ordAt K (S.elemW (Wc j)) α β = 0) ∧
      S.ordInf K (S.elemW (Wc j)) = -((∑ q, (NW j).1 * mqJ n ζ a b G j q : ℕ) : ℤ) := by
    intro j
    obtain ⟨hN1, hW0, hWs, hWv⟩ := hNW j
    refine S.divisor_of_vanish (K := K) hcopS (fun q ↦ ψ (ptA n a q)) (fun q ↦ ψ (ptB n ζ b q))
      (fun q ↦ (NW j).1 * mqJ n ζ a b G j q) ?_ ?_ ?_ (Wc j) ?_ ?_ ?_
    · intro q q' h
      simp only [Prod.mk.injEq] at h
      exact pt_injective hζ a b ha hb (Prod.ext (ψ.injective h.1) (ψ.injective h.2))
    · exact fun q ↦ (map_ne_zero_iff _ ψ.injective).mpr (pt_ne_zero hn hζ b hb q)
    · intro q
      rw [hSn, hSp, eval_map, eval₂_hom, ← map_pow, pt_valid _ hζ a b hbf q]
    · exact fun h0 ↦ hW0 ((Polynomial.map_eq_zero_iff (f := mapRingHom ψ)
        (Polynomial.map_injective ψ ψ.injective)).mp h0)
    · intro i c hc
      have hc' : ((toB (NW j).2).coeff i).coeff c ≠ 0 := by
        intro h0; apply hc; simp [hWc, mapB, coeff_map, h0]
      obtain ⟨h1, h2⟩ := hWs i c hc'
      refine ⟨hSn ▸ h1, ?_⟩
      rw [hSn, hSd, ← Finset.mul_sum]; exact h2
    · intro q
      have := (hWv q).mapR ψ
      rw [hSp, hSn]; exact this
  set μ : Fin (dim F) → K → K → ℤ := fun j α β ↦
    ∑ q, if (α, β) = P q then (((NW j).1 * mqJ n ζ a b G j q : ℕ) : ℤ) else 0 with hμ_def
  have hμ : ∀ j (α β : K), β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (S.elemW (Wc j)) α β = μ j α β := by
    intro j α β _ hv
    by_cases hex : ∃ q, (α, β) = P q
    · obtain ⟨q0, hq0⟩ := hex
      simp only [hμ_def]
      rw [Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hPinj (hq0.symm.trans h)).symm)
        (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos hq0]
      have hα : α = ψ' (ptA n a q0) := congrArg Prod.fst hq0
      have hβ' : β = ψ' (ptB n ζ b q0) := congrArg Prod.snd hq0
      rw [hα, hβ']
      exact (hdiv j).2.2.1 q0
    · push_neg at hex
      rw [(hdiv j).2.2.2.1 α β hv fun q h ↦ hex q h]
      exact (Finset.sum_eq_zero fun q _ ↦ if_neg (hex q)).symm
  have hμbr : ∀ j (e : K), (S.p.map (algebraMap C K)).eval e = 0 →
      S.ordAt K (S.elemW (Wc j)) e 0 = 0 := by
    intro j e he
    refine (hdiv j).2.2.2.1 e 0 (by rw [he, zero_pow S.hn.ne']) fun q h ↦ hP0 q ?_
    exact ((Prod.ext_iff.mp h).2).symm
  -- matching the residues
  have hGd : ∀ i j, S.n ≤ j → (mapB ψ (G i)).coeff j = 0 := fun i j hj ↦ by
    rw [mapB, coeff_map, toB_coeff_ge (G i) (hGn i) j (hSn ▸ hj), map_zero]
  have hmatch : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (∑ i, if α = algebraMap C K (ψ (a i)) then
        evalW ((mapB ψ (G i)).map (mapRingHom (algebraMap C K))) α β else 0) =
      ∑ j, algebraMap C K (ψ (cJ n ζ a b G j (NW j).1)) *
        (((μ j α β - ∑ i, if α = algebraMap C K (ψ (a i)) then
          (((NW j).1 * negJ n ζ a b G j i : ℕ) : ℤ) else 0 : ℤ)) : K) := by
    intro α β hβ hv
    have hres := (S.res_hInt_nb (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) (fun i ↦ mapB ψ (G i))
      hGd α β hβ hv).symm.trans
      (res_integrand S ψ f hSn hSp hζ a b ha hb hbf B B₁ G hGn α β hβ hv)
    rw [hres]
    by_cases hex : ∃ q, (α, β) = P q
    · obtain ⟨q0, hq0⟩ := hex
      rw [Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hPinj (hq0.symm.trans h)).symm)
        (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos hq0]
      have hα : α = ψ' (ptA n a q0) := (Prod.ext_iff.mp hq0).1
      have hei : ∀ j, (∑ i, if α = algebraMap C K (ψ (a i)) then
          (((NW j).1 * negJ n ζ a b G j i : ℕ) : ℤ) else 0) =
          (((NW j).1 * negJ n ζ a b G j (fibI q0) : ℕ) : ℤ) := by
        intro j
        rw [Finset.sum_eq_single (fibI q0)]
        · rw [if_pos (by rw [hα]; rfl)]
        · intro i _ hi
          rw [if_neg]
          intro h
          apply hi
          exact ha (hψi (h.symm.trans hα))
        · intro h; exact absurd (Finset.mem_univ _) h
      have hμq : ∀ j, μ j α β = (((NW j).1 * mqJ n ζ a b G j q0 : ℕ) : ℤ) := by
        intro j
        simp only [hμ_def]
        rw [Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hPinj (hq0.symm.trans h)).symm)
          (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos hq0]
      simp only [hei, hμq]
      rw [resK_repr n ζ a b G (fun j ↦ (NW j).1) (fun j ↦ by have := (hNW j).1; omega),
        map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hz := mqJ_sub_negJ n ζ a b G j q0
      rw [map_mul, show ψ' (cJ n ζ a b G j (NW j).1) = algebraMap C K (ψ (cJ n ζ a b G j (NW j).1))
        from rfl]
      congr 1
      rw [show (((NW j).1 * mqJ n ζ a b G j q0 : ℕ) : ℤ) - (((NW j).1 * negJ n ζ a b G j (fibI q0) : ℕ) : ℤ)
          = (NW j).1 * zJ n ζ a b G j (fibI q0) (fibK q0) by push_cast; rw [← hz]; ring]
      simp only [RingHom.coe_comp, Function.comp_apply, map_mul, map_natCast, map_intCast]
      rw [Int.cast_mul, Int.cast_natCast]
    · push_neg at hex
      rw [Finset.sum_eq_zero fun q _ ↦ if_neg (hex q)]
      have hnone : ∀ i, α ≠ algebraMap C K (ψ (a i)) := by
        intro i hi
        have hβn : β ^ n = ψ' (b i) ^ n := by
          calc β ^ n = β ^ S.n := by rw [hSn]
            _ = ((toPoly f).map ψ').eval α := by rw [hv, hpK]
            _ = ψ' (b i) ^ n := by
              rw [hi, show algebraMap C K (ψ (a i)) = ψ' (a i) from rfl, eval_map, eval₂_hom,
                ← hbf, map_pow]
        obtain ⟨k, hk, hke⟩ := exists_fibre hn (hζ.map_of_injective hψi) _ _
          ((map_ne_zero_iff _ hψi).mpr (hb i)) hβn
        apply hex (finProdFinEquiv (i, ⟨k, hk⟩))
        simp only [hP_def, ptA, ptB, fibI_equiv, fibK_equiv]
        refine Prod.ext hi ?_
        rw [hke]; simp [ψ']
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp only [hμ_def, Finset.sum_eq_zero fun q _ ↦ if_neg (hex q),
        Finset.sum_eq_zero fun i _ ↦ if_neg (hnone i)]
      simp
  -- the logarithmic part
  have ha' : ∀ i, S.p.eval (ψ (a i)) ≠ 0 := by
    intro i h0
    rw [hSp, eval_map, eval₂_hom, ← hbf, map_pow] at h0
    exact hb i (pow_eq_zero_iff hn.ne' |>.mp ((map_eq_zero_iff ψ ψ.injective).mp
      (by rw [map_pow]; exact h0)))
  have hHB : boundB n d0 B ≤ H := (le_max_left _ _).trans (le_max_left _ _)
  have hHB₁ : boundB n d0 B₁ ≤ H := (le_max_right _ _).trans (le_max_left _ _)
  have hHG : ∀ i, boundB n d0 (G i) ≤ H := fun i ↦
    (le_foldr_max (l := (List.finRange m).map fun i ↦ boundB n d0 (G i)) (List.mem_map.mpr
      ⟨i, List.mem_finRange i, rfl⟩)).trans (le_max_right _ _)
  have hcoeffB : ∀ (W : BPoly F) (i c : ℕ), ((mapB ψ W).coeff i).coeff c ≠ 0 →
      ((toB W).coeff i).coeff c ≠ 0 := fun W i c h h0 ↦ h (by simp [mapB, coeff_map, h0])
  have hBb : ∀ i c, ((mapB ψ B).coeff i).coeff c ≠ 0 →
      i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H := by
    intro i c h
    obtain ⟨h1, h2⟩ := bound_of_coeff n d0 B i c (hcoeffB B i c h)
    exact ⟨by omega, by rw [hSn, hSd]; exact h2.trans hHB⟩
  have hB₁b : ∀ i c, ((mapB ψ B₁).coeff i).coeff c ≠ 0 →
      i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H + S.n * S.p.natDegree := by
    intro i c h
    obtain ⟨h1, h2⟩ := bound_of_coeff n d0 B₁ i c (hcoeffB B₁ i c h)
    exact ⟨by omega, by rw [hSn, hSd]; exact h2.trans (hHB₁.trans (Nat.le_add_right _ _))⟩
  have hGb : ∀ k i c, ((mapB ψ (G k)).coeff i).coeff c ≠ 0 →
      i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H + S.n := by
    intro k i c h
    obtain ⟨h1, h2⟩ := bound_of_coeff n d0 (G k) i c (hcoeffB (G k) i c h)
    have := hGn k
    exact ⟨by omega, by rw [hSn, hSd]; exact h2.trans ((hHG k).trans (Nat.le_add_right _ _))⟩
  have hB₁0' : (mapB ψ B₁).coeff 0 = 0 := by rw [mapB, coeff_map, hB₁0, map_zero]
  obtain ⟨V, hVs, hV⟩ := S.log_concrete (K := K) hC hx hconst hcopS (mapB ψ B) (mapB ψ B₁)
    (fun i ↦ ψ (a i)) (fun i ↦ mapB ψ (G i)) ha' H hBb hB₁0' hB₁b hGb
    (fun j ↦ ψ (cJ n ζ a b G j (NW j).1)) Wc (fun j ↦ (hdiv j).1)
    (fun j i ↦ (NW j).1 * negJ n ζ a b G j i) μ hμ hμbr hmatch v hv sI d w hd hw heq
  -- the identity in `L`
  have hyS : S.y ^ n = aeval S.x ((toPoly f).map ψ) := by rw [← hSn, S.hy, hSp]
  have hfx : exC ψ S.x f ≠ 0 := by
    intro h0
    exact S.htr ⟨S.p, S.hsq.ne_zero, by rw [hSp]; exact h0⟩
  have hy0 : S.y ≠ 0 := by
    intro h0; apply hfx
    rw [exC, ← hyS, h0, zero_pow hn.ne']
  have hu : ∀ j, evalE ψ S.x S.y (toB (NW j).2) ≠ 0 := by
    intro j
    refine evalE_ne_zero S ψ _ (hNW j).2.1 fun i hi ↦ ?_
    by_contra h0
    obtain ⟨c, hc⟩ : ∃ c, ((toB (NW j).2).coeff i).coeff c ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := ((hNW j).2.2.1 i c hc).1
    omega
  have hxa : ∀ i, S.x - algebraMap C L (ψ (a i)) ≠ 0 := fun i h0 ↦ by
    have := congrArg (fun t : L ↦ t′) h0
    simp only [map_sub, hx, deriv_algebraMap, hC, map_zero, sub_zero] at this
    exact one_ne_zero this
  have hLM := logMT_eval hC ψ S.x S.y hx f hn hy0 hyS ζ a b G B B₁ NW hu hxa hfx
  have hdegB : ∀ (W : BPoly F), W.length ≤ n → ∀ i, S.n ≤ i → (toB W).coeff i = 0 :=
    fun W hW i hi ↦ toB_coeff_ge W hW i (hSn ▸ hi)
  have hIntL : ((S.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i) :
      C⟮S.x⟯⟮S.y⟯) : L) = evalE ψ S.x S.y (toB B) + evalE ψ S.x S.y (toB B₁) / exC ψ S.x f +
        ∑ i, evalE ψ S.x S.y (toB (G i)) / (S.x - algebraMap C L (ψ (a i))) := by
    simp only [hInt, IntermediateField.coe_add, IntermediateField.coe_mul,
      IntermediateField.coe_inv, IntermediateField.coe_sum, S.polyX_coe,
      elemW_map_coe S ψ _ (hdegB B hBn), elemW_map_coe S ψ _ (hdegB B₁ hB₁n),
      fun i ↦ elemW_map_coe S ψ _ (hdegB (G i) (hGn i)), div_eq_mul_inv]
    rw [hSp]
    simp [exC, aeval_C]
  have hlogL : ∀ j, ((S.logW (Wc j) (denX (fun i ↦ ψ (a i)) fun i ↦ (NW j).1 * negJ n ζ a b G j i) :
      C⟮S.x⟯⟮S.y⟯) : L) = evalE ψ S.x S.y (toB (NW j).2) /
        ∏ i, (S.x - algebraMap C L (ψ (a i))) ^ ((NW j).1 * negJ n ζ a b G j i) := by
    intro j
    have hWd : ∀ i, S.n ≤ i → (toB (NW j).2).coeff i = 0 := by
      intro i hi
      by_contra h0
      obtain ⟨c, hc⟩ : ∃ c, ((toB (NW j).2).coeff i).coeff c ≠ 0 := by
        by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
      have := ((hNW j).2.2.1 i c hc).1
      omega
    simp only [Differential.SuperData.logW, IntermediateField.coe_mul, IntermediateField.coe_inv, S.polyX_coe,
      div_eq_mul_inv, denX, map_prod, map_pow, map_sub, aeval_X, aeval_C]
    congr 1
    exact elemW_map_coe S ψ _ hWd
  have hTL : evalE ψ S.x S.y (toB (logMT f n ζ a b G B B₁ NW).2) =
      evalE ψ S.x S.y (toB (logMT f n ζ a b G B B₁ NW).1) * exC ψ S.x f *
        ((S.elemW V : C⟮S.x⟯⟮S.y⟯) : L)′ := by
    rw [hLM, ← hV, hIntL]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hlogL j]
  -- the polynomial identity
  set basis := basisN n d0 (H + n) with hbasis
  set cs : List C := basis.map fun al ↦ (V.coeff al.2).coeff al.1 with hcs
  have hlen : cs.length = basis.length := by simp [cs]
  have hVs' : ∀ i c, (V.coeff i).coeff c ≠ 0 → i < n ∧ n * c + d0 * i ≤ H + n := by
    intro i c h
    obtain ⟨h1, h2⟩ := hVs i c h
    rw [hSn] at h1
    rw [hSn, hSd] at h2
    exact ⟨h1, h2⟩
  have hVl : lsumW cs basis = V := lsumW_of_support n d0 (H + n) hn V hVs'
  have hVdeg : ∀ i, S.n ≤ i → V.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨c, hc⟩ : ∃ c, (V.coeff i).coeff c ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hVs' i c hc).1
    omega
  have hEV : evalE (RingHom.id C) S.x S.y V = ((S.elemW V : C⟮S.x⟯⟮S.y⟯) : L) := by
    have := elemW_map_coe S (RingHom.id C) V hVdeg
    rw [Polynomial.mapRingHom_id, Polynomial.map_id] at this
    exact this.symm
  set MT := logMT f n ζ a b G B B₁ NW with hMT
  have hcomb := evalE_combBS hC ψ S.x S.y hx f hn hy0 hyS MT.1 cs basis hlen
  rw [← evalE_lsumW S.x S.y cs basis hlen, hVl, hEV] at hcomb
  have hRHS : evalE (RingHom.id C) S.x S.y ((toB (reduceB f n hn MT.2)).map (mapRingHom ψ)) =
      evalE ψ S.x S.y (toB MT.2) := by
    rw [evalE_map_id, evalE_reduceB ψ S.x S.y f hn hyS]
  set Dd := combBS ψ cs (exactCols f n hn MT.1 basis) -
    (toB (reduceB f n hn MT.2)).map (mapRingHom ψ) with hDd
  have hDdeg : ∀ i, S.n ≤ i → Dd.coeff i = 0 := by
    intro i hi
    rw [hDd, coeff_sub, combBS_coeff_ge ψ cs _ (fun W hW ↦ by
      obtain ⟨al, -, rfl⟩ := List.mem_map.mp hW
      exact length_reduceB f n hn _) i (hSn ▸ hi), coeff_map,
      toB_coeff_ge _ (length_reduceB f n hn _) i (hSn ▸ hi), map_zero, sub_zero]
  have hDd0 : Dd = 0 := by
    by_contra hne
    apply evalE_ne_zero S (RingHom.id C) Dd hne hDdeg
    rw [hDd, map_sub, hcomb, hRHS, hTL]
    show _ - _ = (0 : L)
    rw [exC]; ring
  exact exactTest_complete ψ f n hn MT.1 MT.2 basis cs hlen (sub_eq_zero.mp hDd0)

end Complete


end Sup
