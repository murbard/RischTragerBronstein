import RischTragerBronstein.Jacobian.HypDecideNF
import RischTragerBronstein.Jacobian.HypDecideNFComplete

/-!
# Completeness of the genus-`g` procedure over `ℚ`

`hypDecideQ_eventually`: for `f` squarefree of degree `2g + 1` and any `A/D`, `hypDecideQ` answers
for every large search bound.

`hermite_solve_ne_none`: the Hermite system of `hypDecideGenQ` / `hypDecideQ` is always solvable
(the Hermite decomposition exists over `ℚ̄`, `hermite_polyK`, with bounded degrees,
`hermite_deg_boundK`).
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad

namespace Jac

theorem hermite_solve_ne_none (p A D : CPoly ℚ) (hsq : Squarefree (toPoly p))
    (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) (e : ℕ) (he : p.length ≤ e) :
    linSolve (colsG p D (nbPart p D) (A.length + D.length)
      (A.length + 2 * D.length + (nbPart p D).length + e + 3))
      (mul [2] (mul (mul A D) (nbPart p D))) ≠ none := by
  classical
  set M := nbPart p D
  set dW := A.length + D.length
  set nT := A.length + 2 * D.length + M.length + e + 3
  set ι := algebraMap ℚ (AlgebraicClosure ℚ)
  have hinj : Function.Injective ι := ι.injective
  have hsqQ : Squarefree ((toPoly p).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree
  have hp1' : 1 ≤ ((toPoly p).map ι).natDegree := by
    rw [natDegree_map_eq_of_injective hinj]; exact hp1
  have hDq : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hD
  obtain ⟨W, B₀, T, cf, hT, hB, hid⟩ := hermite_polyK ((toPoly p).map ι) hsqQ hp1'
    ((toPoly A).map ι) ((toPoly D).map ι) hDq (IsAlgClosed.splits _)
  have hWd := hermite_deg_boundK _ hp1' _ _ W B₀ T cf hDq hB hid
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at hWd
  have hdvd : ∏ α ∈ T, (X - C α) ∣ (toPoly M).map ι := by
    refine Finset.prod_dvd_of_coprime
      ((pairwise_coprime_X_sub_C (s := fun α : AlgebraicClosure ℚ ↦ α)
        Function.injective_id).set_pairwise _)
      fun α hα ↦ dvd_iff_isRoot.mpr (isRoot_nbPart p D hD ι α (hT α hα).1 (hT α hα).2)
  obtain ⟨Q, hQ⟩ := hdvd
  set TQ := Q * ((∏ α ∈ T, (X - C α)) * B₀ + ∑ α ∈ T, C (cf α) * ∏ β ∈ T.erase α, (X - C β))
  have hidQ : 2 * (toPoly A).map ι * (toPoly D).map ι * (toPoly M).map ι =
      (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W +
        2 * ((toPoly D).map ι) ^ 2 * TQ := by
    rw [hQ]; simp only [TQ]; linear_combination Q * hid
  have hAl := CPoly.natDegree_toPoly_le_length A
  have hDl' := CPoly.natDegree_toPoly_le_length D
  have hMl := CPoly.natDegree_toPoly_le_length M
  have hpl := CPoly.natDegree_toPoly_le_length p
  have hD1 : 1 ≤ D.length := by
    rcases D with _ | ⟨d, D⟩
    · exact absurd (by simp) hD
    · simp
  have hW : W = 0 ∨ W.natDegree < dW := Or.inr (by
    rcases le_total (toPoly A).natDegree (toPoly D).natDegree with h | h
    · rw [max_eq_right h] at hWd; omega
    · rw [max_eq_left h] at hWd; omega)
  have hTQ : TQ = 0 ∨ TQ.natDegree < nT := by
    rcases eq_or_ne TQ 0 with h0 | h0
    · exact Or.inl h0
    right
    have e' : 2 * ((toPoly D).map ι) ^ 2 * TQ = 2 * (toPoly A).map ι * (toPoly D).map ι *
        (toPoly M).map ι - (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W := by
      rw [hidQ]; ring
    have hprod : (2 * ((toPoly D).map ι) ^ 2 * TQ).natDegree =
        2 * (toPoly D).natDegree + TQ.natDegree := by
      rw [natDegree_mul (mul_ne_zero two_ne_zero (pow_ne_zero _ hDq)) h0,
        natDegree_mul two_ne_zero (pow_ne_zero _ hDq), natDegree_pow,
        natDegree_map_eq_of_injective hinj]
      simp
    rw [e'] at hprod
    have hc0 : (2 : (AlgebraicClosure ℚ)[X]).natDegree ≤ 0 := by simp
    have h1 := nd_mulK (nd_mulK (nd_mulK hc0 (natDegree_map_le (f := ι) (p := toPoly A)))
      (natDegree_map_le (f := ι) (p := toPoly D))) (natDegree_map_le (f := ι) (p := toPoly M))
    have h3 := nd_mulK (natDegree_map_le (f := ι) (p := toPoly M))
      (natDegree_LD_leK ((toPoly p).map ι) ((toPoly D).map ι) W hp1')
    simp only [natDegree_map_eq_of_injective hinj] at h1 h3
    have h5 := natDegree_sub_le (2 * (toPoly A).map ι * (toPoly D).map ι * (toPoly M).map ι)
      ((toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W)
    rw [hprod] at h5
    simp only [nT]
    rcases le_total (toPoly A).natDegree (toPoly D).natDegree with h | h
    · rw [max_eq_right h] at hWd
      have h6 : 2 * (toPoly D).natDegree + TQ.natDegree ≤
          (toPoly M).natDegree + ((toPoly D).natDegree + (toPoly D).natDegree +
            (toPoly p).natDegree) := by
        refine h5.trans (max_le (h1.trans (by omega)) (h3.trans (by omega)))
      omega
    · rw [max_eq_left h] at hWd
      have h6 : 2 * (toPoly D).natDegree + TQ.natDegree ≤
          (toPoly M).natDegree + ((toPoly A).natDegree + (toPoly D).natDegree +
            (toPoly p).natDegree) := by
        refine h5.trans (max_le (h1.trans (by omega)) (h3.trans (by omega)))
      omega
  refine linSolve_complete_map ι _ _ ((List.range dW).map W.coeff ++ (List.range nT).map TQ.coeff)
    (by simp [colsG]) ?_
  rw [lcombS_colsG, List.take_left' (by simp), List.drop_left' (by simp),
    List.take_of_length_le (by simp), toPoly_range_coeff W dW hW, toPoly_range_coeff TQ nT hTQ]
  simp only [toPoly_mul, toPoly_two, Polynomial.map_mul, Polynomial.map_ofNat]
  rw [← hidQ]; ring

/-! ### Base points -/

lemma length_le_natDegree_of_roots {K : Type*} [Field K] {P : K[X]} (hP : P ≠ 0) {l : List K}
    (hl : l.Nodup) (hr : ∀ a ∈ l, P.eval a = 0) : l.length ≤ P.natDegree := by
  have hle : (l : Multiset K) ≤ P.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hl)]
    intro a ha; exact (mem_roots hP).mpr (hr a ha)
  simpa using (Multiset.card_le_card hle).trans (card_roots' P)

lemma isCoprime_prodX {K : Type*} [Field K] (Q : K[X]) : ∀ l : List K, (∀ a ∈ l, Q.eval a ≠ 0) →
    IsCoprime (l.map fun r ↦ X - C r).prod Q
  | [], _ => by simp [isCoprime_one_left]
  | a :: t, h => by
    rw [List.map_cons, List.prod_cons]
    refine IsCoprime.mul_left ?_ (isCoprime_prodX Q t fun b hb ↦ h b (List.mem_cons_of_mem _ hb))
    exact (irreducible_X_sub_C a).coprime_iff_not_dvd.mpr fun hd ↦
      h a List.mem_cons_self (dvd_iff_isRoot.mp hd)

lemma squarefree_prodX {K : Type*} [Field K] : ∀ l : List K, l.Nodup →
    Squarefree (l.map fun r ↦ X - C r).prod
  | [], _ => by simp
  | a :: t, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.prod_cons, squarefree_mul_iff]
    refine ⟨(isCoprime_prodX (X - C a) t fun b hb ↦ ?_).symm.isRelPrime,
      (irreducible_X_sub_C a).squarefree, squarefree_prodX t h.2⟩
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl; exact h.1 hb

lemma natDegree_prodX {K : Type*} [Field K] (l : List K) :
    (l.map fun r ↦ X - C r).prod.natDegree = l.length := by
  have := natDegree_multiset_prod_X_sub_C_eq_card (l : Multiset K)
  rwa [Multiset.map_coe, Multiset.prod_coe, Multiset.coe_card] at this

lemma baseAs_spec (p S : CPoly ℚ) (g : ℕ) : (baseAs p S g).Nodup ∧
    ∀ a ∈ baseAs p S g, (toPoly S).eval (a : ℚ) ≠ 0 ∧ (toPoly p).eval (a : ℚ) ≠ 0 := by
  refine ⟨(List.nodup_range.filter _).sublist (List.take_sublist _ _), fun a ha ↦ ?_⟩
  have := (List.mem_filter.mp (List.mem_of_mem_take ha)).2
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, evalC_eq] at this
  exact this

lemma baseAs_length (p S : CPoly ℚ) (g : ℕ) (hS : toPoly S ≠ 0) (hp : toPoly p ≠ 0) :
    (baseAs p S g).length = g := by
  classical
  set N := g + p.length + S.length
  set good : ℕ → Bool := fun a ↦ evalC S (a : ℚ) != 0 && evalC p (a : ℚ) != 0
  have hsplit := List.length_eq_length_filter_add (l := List.range N) good
  set bad := (List.range N).filter fun a ↦ !good a
  have hbad : bad.length ≤ (toPoly S * toPoly p).natDegree := by
    have := length_le_natDegree_of_roots (mul_ne_zero hS hp) (l := bad.map fun a : ℕ ↦ (a : ℚ))
      ((List.nodup_range.filter _).map Nat.cast_injective) fun x hx ↦ by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        have := (List.mem_filter.mp ha).2
        simp only [good, Bool.not_and, Bool.or_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq,
          evalC_eq] at this
        rw [eval_mul]
        rcases this with h | h <;> simp [h]
    simpa using this
  rw [natDegree_mul hS hp] at hbad
  have h1 := CPoly.natDegree_toPoly_le_length S
  have h2 := CPoly.natDegree_toPoly_le_length p
  rw [List.length_range] at hsplit
  have hg : g ≤ ((List.range N).filter good).length := by omega
  unfold baseAs
  rw [List.length_take]
  exact min_eq_left hg

/-! ### Completeness -/

set_option maxHeartbeats 3200000 in
/-- **Completeness of `hypDecideQ`**: for `f` squarefree of degree `2g + 1` (given with its
leading coefficient last), every `∫ A/(D y)` is decided for all large search bounds. -/
theorem hypDecideQ_eventually {f : List ℤ} {g : ℕ}
    (hlen : f.length = 2 * g + 2) (hlcf : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → hypDecideQ f g A D B ≠ none := by
  classical
  set p : CPoly ℚ := f.map (Int.castRingHom ℚ) with hpdef
  have hpf : toPoly p = (toPoly f).map (Int.castRingHom ℚ) := toPoly_map_list _ _
  have hp0 : toPoly p ≠ 0 := hpf ▸ hsq.ne_zero
  set S := nbPart p D
  have hS0 := nbPart_ne_zero p D hD
  have hSsq := squarefree_nbPart p D hD
  have hScop := isCoprime_nbPart p D hD
  obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp (hermite_solve_ne_none p A D (hpf ▸ hsq)
    (by rw [hpf, hdeg]; omega) hD f.length (by simp [p]))
  -- base abscissae
  set as := baseAs p S g
  have hasnd : as.Nodup := (baseAs_spec p S g).1
  have hasg : ∀ a ∈ as, (toPoly S).eval (a : ℚ) ≠ 0 ∧ (toPoly p).eval (a : ℚ) ≠ 0 :=
    (baseAs_spec p S g).2
  have hasl : as.length = g := baseAs_length p S g hS0 hp0
  set asQ : List ℚ := as.map fun a : ℕ ↦ (a : ℚ)
  have hasQnd : asQ.Nodup := hasnd.map Nat.cast_injective
  have hS' : toPoly (baseS p S g) = toPoly S * (asQ.map fun r ↦ X - C r).prod := by
    rw [baseS, toPoly_mul, toPoly_prodLin]
  have hPS : IsCoprime (asQ.map fun r ↦ X - C r).prod (toPoly S) :=
    isCoprime_prodX _ _ fun a ha ↦ by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha; exact (hasg n hn).1
  have hPp : IsCoprime (asQ.map fun r ↦ X - C r).prod (toPoly p) :=
    isCoprime_prodX _ _ fun a ha ↦ by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha; exact (hasg n hn).2
  have hS'sq : Squarefree (toPoly (baseS p S g)) := by
    rw [hS', squarefree_mul_iff]
    exact ⟨hPS.symm.isRelPrime, hSsq, squarefree_prodX _ hasQnd⟩
  have hS'cop : IsCoprime (toPoly (baseS p S g)) (toPoly p) := by
    rw [hS']; exact hScop.mul_left hPp
  obtain ⟨M, hM, hsf, hroots, hpt⟩ := NFC.splitFieldG_spec p (baseS p S g) hS'sq hS'cop
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  -- values of `f`
  have hcurve : ∀ α : NFC.NF M, evalC (curveK f) α = NFC.pValG p α := by
    intro α
    rw [evalC_eq, toPoly_curveK, eval_map_algebraMap, NFC.pValG, hpf]
  have hS'root : ∀ α : NFC.NF M, aeval α (toPoly (baseS p S g)) =
      aeval α (toPoly S) * aeval α (asQ.map fun r ↦ X - C r).prod := by
    intro α; rw [hS', map_mul]
  -- the splitting of `S`
  obtain ⟨l, hl, hlen', hr⟩ := hroots
  have hSK0 : (toPoly S).map (algebraMap ℚ (NFC.NF M)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ (NFC.NF M)).injective).mpr hS0
  set lS := l.filter fun α ↦ decide (aeval α (toPoly S) = 0)
  have hlS : (toPoly S).natDegree ≤ lS.length := by
    set lN := l.filter fun α ↦ !decide (aeval α (toPoly S) = 0)
    have hsum : l.length = lS.length + lN.length :=
      List.length_eq_length_filter_add (l := l) fun α ↦ decide (aeval α (toPoly S) = 0)
    have hN : lN.length ≤ g := by
      have hsub : lN ⊆ asQ.map (algebraMap ℚ (NFC.NF M)) := by
        intro α hα
        obtain ⟨hαl, hαS⟩ := List.mem_filter.mp hα
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hαS
        have h0 := hr α hαl
        rw [hS'root, mul_eq_zero] at h0
        rcases h0 with h0 | h0
        · exact absurd h0 hαS
        rw [map_list_prod, List.prod_eq_zero_iff, List.map_map] at h0
        obtain ⟨r, hr', hr0⟩ := List.mem_map.mp h0
        simp only [Function.comp_apply, map_sub, aeval_X, aeval_C, sub_eq_zero] at hr0
        rw [hr0]
        exact List.mem_map_of_mem hr'
      have := (List.subperm_of_subset (hl.filter _) hsub).length_le
      simpa [asQ, hasl] using this
    have hdS' : (toPoly (baseS p S g)).natDegree = (toPoly S).natDegree + g := by
      have hP0 : (asQ.map fun r ↦ X - C r).prod ≠ 0 := List.prod_ne_zero fun h0 ↦ by
        obtain ⟨r, -, hr0⟩ := List.mem_map.mp h0; exact X_sub_C_ne_zero r hr0
      rw [hS', natDegree_mul hS0 hP0, natDegree_prodX]
      simp [asQ, hasl, S]
    omega
  have hsplitK := EllQuad.split_of_hasRoots hSK0 (hl.filter _)
    (by rw [natDegree_map_eq_of_injective (algebraMap ℚ (NFC.NF M)).injective]; exact hlS)
    (fun a ha ↦ by
      rw [eval_map_algebraMap]; exact of_decide_eq_true (List.mem_filter.mp ha).2)
  -- non-zero square values of `f` at the roots of `S` and at the base abscissae
  have hptS : ∀ α : NFC.NF M, aeval α (toPoly S) = 0 →
      ∃ β : NFC.NF M, β ≠ 0 ∧ β * β = evalC (curveK f) α := by
    intro α hα
    obtain ⟨β, hβ0, hβ⟩ := hpt α (by rw [hS'root, hα, zero_mul])
    exact ⟨β, hβ0, by rw [hcurve]; exact hβ⟩
  have hbase : ∀ a : ℕ, a ∈ as → ∃ β : NFC.NF M, β ≠ 0 ∧
      β * β = ((evalC f (a : ℤ) : ℤ) : NFC.NF M) := by
    intro a ha
    obtain ⟨β, hβ0, hβ⟩ := hpt (algebraMap ℚ (NFC.NF M) (a : ℚ)) (by
      rw [hS'root, map_list_prod]
      refine mul_eq_zero_of_right _ (List.prod_eq_zero_iff.mpr <| List.mem_map.mpr ⟨X - C (a : ℚ), List.mem_map_of_mem
        (List.mem_map_of_mem ha), by simp⟩))
    refine ⟨β, hβ0, ?_⟩
    rw [hβ, NFC.pValG, aeval_algebraMap_apply, coe_aeval_eq_eval, hpf, evalC_eq,
      show ((a : ℚ)) = (((a : ℤ)) : ℚ) by simp, eval_intCast_map]
    simp
  choose! bf hbf using hbase
  obtain ⟨B0, hB0⟩ := hypDecideNF_eventually M (EllQuad.int_of_irredQ hM) hlen hlcf hsq hdeg
    (cs.drop (A.length + D.length)) S hSsq _ lS hsplitK hptS (as.map fun a : ℕ ↦ (a : ℤ))
    (as.map bf) (by simp [hasl]) (by simp [hasl])
    (fun i hi ↦ by
      simp only [List.getElem_map]
      exact ⟨(hbf _ (List.getElem_mem _)).2, (hbf _ (List.getElem_mem _)).1⟩)
    (hasnd.map Nat.cast_injective)
    (fun a ha ↦ by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
      simpa using (hasg n hn).1)
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold hypDecideQ
  rw [if_neg (fun h ↦ hD ((isZero_iff D).mp h))]
  simp only
  rw [hcs]
  simp only
  rw [hsf]
  exact hB0 B hB

section Decides

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The genus-`g` decision over `ℚ`**: for `y² = f(x)`, `f ∈ ℤ[x]` squarefree of degree `2g + 1`,
and any `A, D ∈ ℚ[x]` with `D ≠ 0`, for every large search bound `hypDecideQ` returns an answer,
and the answer is `true` exactly when `∫ A/(D y) dx` is elementary. -/
theorem hypDecideQ_decides [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} (hlen : f.length = 2 * g + 2) (hlcf : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → ∃ ans, hypDecideQ f g A D B = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨B0, hB0⟩ := hypDecideQ_eventually hlen hlcf hsq hdeg A D hD
  refine ⟨B0, fun B hB ↦ ?_⟩
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (hB0 B hB)
  exact ⟨ans, h, hypDecideQ_spec hC hCall x y hx hsq hdeg hy hgen A D B ans h⟩

end Decides

end Jac
