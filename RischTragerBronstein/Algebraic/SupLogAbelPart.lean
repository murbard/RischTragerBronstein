import RischTragerBronstein.Algebraic.SupLogRes

/-!
# The Abel direction of the superelliptic logarithmic-part procedure

If the integrand is elementary, then every residue component `Γⱼ⁺` is torsion
(`abel_component`), by `super_abel`, `principalMulN_of_isPrincipalS` and descent.
-/

open Polynomial CPoly Differential IntermediateField

namespace Sup

section Comb

lemma toNat_natCast_mul (M : ℕ) (x : ℤ) : ((M : ℤ) * x).toNat = M * x.toNat := by
  rcases le_or_gt 0 x with hx | hx
  · lift x to ℕ using hx
    rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  · rw [Int.toNat_of_nonpos (by nlinarith), Int.toNat_of_nonpos hx.le, mul_zero]

/-- Sums over a fibre of `Fin (m * n) ≃ Fin m × Fin n`. -/
lemma sum_fibre {M : Type*} [AddCommMonoid M] {m n : ℕ} (i : Fin m) (g : Fin (m * n) → M) :
    ∑ q ∈ Finset.univ.filter (fun q ↦ fibI q = i), g q = ∑ k : Fin n, g (finProdFinEquiv (i, k)) := by
  rw [Finset.sum_filter, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [fibI_equiv, if_pos rfl]
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun k _ ↦ by rw [fibI_equiv, if_neg hi']
  · intro h; exact absurd (Finset.mem_univ i) h

open Classical in
/-- **The divisor of `super_abel`** in terms of the component multiplicities. -/
lemma gammaAbel {K : Type*} [Field K] {m n : ℕ} (P : Fin (m * n) → K × K)
    (hP : Function.Injective P) (A : Fin m → K) (hA : ∀ q, (P q).1 = A (fibI q))
    (hAi : Function.Injective A) (zq : Fin (m * n) → ℤ) (M : ℕ) (Q : K × K)
    (hfib : ∀ i, Q.1 = A i → Q ∈ Finset.univ.image P) :
    ((if Q ∈ Finset.univ.image P then (M : ℤ) * (fun Q ↦ ∑ q, if Q = P q then zq q else 0) Q
        else 0) +
      ∑ Q' ∈ (Finset.univ.image P).filter
          (fun Q ↦ (fun Q ↦ ∑ q, if Q = P q then zq q else 0) Q < 0) with Q'.1 = Q.1,
        |if Q' ∈ Finset.univ.image P then
          (M : ℤ) * (fun Q ↦ ∑ q, if Q = P q then zq q else 0) Q' else 0|).toNat =
    ∑ q, if Q = P q then M * (zq q + ∑ q' ∈ Finset.univ.filter (fun q' ↦ fibI q' = fibI q),
      ((-(zq q')).toNat : ℤ)).toNat else 0 := by
  have hz : ∀ q, (∑ q', if P q = P q' then zq q' else 0) = zq q := fun q ↦ by
    rw [Finset.sum_eq_single q (fun q' _ hq' ↦ if_neg fun h ↦ hq' (hP h).symm)
      (fun h ↦ absurd (Finset.mem_univ q) h), if_pos rfl]
  by_cases hQ : Q ∈ Finset.univ.image P
  · obtain ⟨q0, -, rfl⟩ := Finset.mem_image.mp hQ
    rw [if_pos hQ]
    simp only [hz]
    have hfilt : ((Finset.univ.image P).filter (fun Q ↦ (∑ q, if Q = P q then zq q else 0) < 0)).filter
        (fun Q' ↦ Q'.1 = (P q0).1) =
        (Finset.univ.filter (fun q ↦ zq q < 0 ∧ fibI q = fibI q0)).image P := by
      ext Q'
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨q, rfl⟩, hzq⟩, h1⟩
        rw [hz] at hzq
        rw [hA, hA] at h1
        exact ⟨q, ⟨hzq, hAi h1⟩, rfl⟩
      · rintro ⟨q, ⟨hzq, hq⟩, rfl⟩
        refine ⟨⟨⟨q, rfl⟩, by rw [hz]; exact hzq⟩, by rw [hA, hA, hq]⟩
    rw [Finset.sum_filter] at *
    rw [← Finset.sum_filter, hfilt, Finset.sum_image fun q _ q' _ h ↦ hP h]
    have hfilt2 : ∑ x ∈ Finset.univ.filter (fun q ↦ zq q < 0 ∧ fibI q = fibI q0),
        |if P x ∈ Finset.univ.image P then (M : ℤ) * ∑ q, (if P x = P q then zq q else 0) else 0| =
        M * ∑ q' ∈ Finset.univ.filter (fun q' ↦ fibI q' = fibI q0), ((-(zq q')).toNat : ℤ) := by
      rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [if_pos (Finset.mem_image_of_mem P (Finset.mem_univ q)), hz]
      by_cases hq : zq q < 0 ∧ fibI q = fibI q0
      · rw [if_pos hq, if_pos hq.2, abs_mul, Nat.abs_cast, abs_of_neg hq.1,
          Int.toNat_of_nonneg (by linarith [hq.1])]
      · rw [if_neg hq]
        by_cases h2 : fibI q = fibI q0
        · rw [if_pos h2]
          have : 0 ≤ zq q := by
            by_contra h3; exact hq ⟨by linarith, h2⟩
          rw [Int.toNat_of_nonpos (by linarith)]; simp
        · rw [if_neg h2]
    rw [hfilt2, ← mul_add, toNat_natCast_mul]
    rw [Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hP h).symm)
      (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos rfl]
  · rw [if_neg hQ, zero_add]
    rw [Finset.sum_eq_zero (s := Finset.univ) fun q _ ↦ if_neg fun h ↦ hQ (by
      rw [h]; exact Finset.mem_image_of_mem P (Finset.mem_univ q))]
    rw [Finset.sum_eq_zero, Int.toNat_zero]
    intro Q' hQ'
    exfalso
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hQ'
    obtain ⟨⟨⟨q, rfl⟩, -⟩, h1⟩ := hQ'
    rw [hA] at h1
    exact hQ (hfib _ h1.symm)

end Comb

section AbelMain

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]

open EllQuad.QCoords Differential.SuperData

lemma coord_resK_eq {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (j : Fin (dim F)) (i : Fin m) (k : Fin n) :
    ((zJ n ζ a b G j i k : ℤ) : ℚ) / (denJ n ζ a b G j : ℚ) = coord j (resK ζ a b G i k) := by
  refine EllQuad.intPt_valQ _ _ (EllQuad.den_dvd_denL ?_) (EllQuad.denL_ne_zero _)
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_map, List.mem_range, true_and]
  exact ⟨i, k, k.2, rfl⟩

lemma negJ_cast {m : ℕ} (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (j : Fin (dim F)) (q : Fin (m * n)) :
    ∑ q' ∈ Finset.univ.filter (fun q' : Fin (m * n) ↦ fibI q' = fibI q),
      ((-(zJ n ζ a b G j (fibI q') (fibK q'))).toNat : ℤ) = (negJ n ζ a b G j (fibI q) : ℤ) := by
  rw [sum_fibre, negJ, Nat.cast_sum]
  simp

set_option maxHeartbeats 1600000 in
/-- **Abel's direction**: if the concrete integrand is a Liouville form, every residue component
is torsion. -/
theorem abel_component (S : SuperData C L) (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (ψ : F →+* C) (f : CPoly F) {n : ℕ} (hSn : S.n = n) (hSp : S.p = (toPoly f).map ψ)
    (hdeg : (toPoly f).natDegree = f.length - 1) (hcop : Nat.Coprime n (f.length - 1)) {m : ℕ}
    {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (a b : Fin m → F) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i)) (B B₁ : BPoly F) (G : Fin m → BPoly F)
    (hGn : ∀ i, (G i).length ≤ n) {ιI : Type*} (s : Finset ιI) (c : ιI → C) (u : ιI → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : ((S.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i) :
      C⟮S.x⟯⟮S.y⟯) : L) = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i))
    (j : Fin (dim F)) :
    ∃ N, 1 ≤ N ∧ PrincipalMulN (toPoly f) n (f.length - 1) (ptA n a) (ptB n ζ b)
      (mqJ n ζ a b G j) N := by
  classical
  set K := AlgebraicClosure C
  set ψ' : F →+* K := (algebraMap C K).comp ψ with hψ'
  have hψi : Function.Injective ψ' := ψ'.injective
  have hn : 0 < n := hSn ▸ S.hn
  have hζ' : IsPrimitiveRoot (ψ' ζ) n := hζ.map_of_injective hψi
  set P : Fin (m * n) → K × K := fun q ↦ (ψ' (ptA n a q), ψ' (ptB n ζ b q)) with hP_def
  have hPinj : Function.Injective P := by
    intro q q' h
    simp only [hP_def, Prod.mk.injEq] at h
    exact pt_injective hζ a b ha hb (Prod.ext (hψi h.1) (hψi h.2))
  have hpK : S.p.map (algebraMap C K) = (toPoly f).map ψ' := by
    rw [hSp, Polynomial.map_map]
  have hval : ∀ q, (P q).2 ^ S.n = (S.p.map (algebraMap C K)).eval (P q).1 := by
    intro q
    rw [hpK, eval_map, eval₂_hom, hSn, ← map_pow, pt_valid _ hζ a b hbf q]
  have hP0 : ∀ q, (P q).2 ≠ 0 := fun q ↦
    (map_ne_zero_iff _ hψi).mpr (pt_ne_zero hn hζ b hb q)
  set Pts := Finset.univ.image P with hPts_def
  have hPts : ∀ Q ∈ Pts, Q.2 ≠ 0 ∧ Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := by
    intro Q hQ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨hP0 q, hval q⟩
  set r : K × K → K := fun Q ↦ ∑ q, if Q = P q then ψ' (resK ζ a b G (fibI q) (fibK q)) else 0
    with hr_def
  set hT := S.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i)
  have hres : ∀ (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α),
      LaurentSeries.res (S.embXY α β hβ hβp ⟨(hT : L), hT.2⟩) =
        if (α, β) ∈ Pts then r (α, β) else 0 := by
    intro α β hβ hβp
    rw [show (⟨(hT : L), hT.2⟩ : C⟮S.x⟯⟮S.y⟯) = hT from rfl,
      res_integrand S ψ f hSn hSp hζ a b ha hb hbf B B₁ G hGn α β hβ hβp]
    split_ifs with hmem
    · rfl
    · refine Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hmem ?_
      rw [h]; exact Finset.mem_image_of_mem P (Finset.mem_univ q)
  obtain ⟨Λ, hΛ⟩ := Jac.exists_extend_functional ψ' (coord j)
  set D := denJ n ζ a b G j with hD_def
  have hD : D ≠ 0 := EllQuad.denL_ne_zero _
  set zq : Fin (m * n) → ℤ := fun q ↦ zJ n ζ a b G j (fibI q) (fibK q) with hzq
  set z : K × K → ℤ := fun Q ↦ ∑ q, if Q = P q then zq q else 0 with hz_def
  have hΛz : ∀ Q ∈ Pts, Λ (r Q) = z Q / D := by
    intro Q hQ
    obtain ⟨q0, -, rfl⟩ := Finset.mem_image.mp hQ
    simp only [hr_def, hz_def]
    rw [Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hPinj h).symm)
      (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos rfl]
    rw [Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hPinj h).symm)
      (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos rfl]
    rw [hΛ, ← coord_resK_eq]
  obtain ⟨M, hM1, hprin⟩ := S.super_abel hC hx s c u hu hu0 v _ hv hT.2 heq Pts hPts r hres Λ z D
    hD hΛz
  -- in `ψ`-form over the algebraic closure
  have hcopB : Nat.Coprime (S.base K).n (S.base K).p.natDegree := by
    rw [base_n, base_p, hpK, natDegree_map_eq_of_injective hψi, hdeg, hSn]; exact hcop
  have hkey := (S.base K).principalMulN_of_isPrincipalS (K := K) hcopB (fun q ↦ (P q).1)
    (fun q ↦ (P q).2) (fun q ↦ M * mqJ n ζ a b G j q) hPinj hP0
    (fun q ↦ by rw [base_n, base_p, hval q]) _ ?_ S.n hprin
  swap
  · intro Q hQv
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Prod.mk.eta]
    by_cases hQ2 : Q.2 = 0
    · rw [if_pos hQ2]
      refine (Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hP0 q ?_).symm
      rw [← h]; exact hQ2
    rw [if_neg hQ2]
    have hfib : ∀ i, Q.1 = ψ' (a i) → Q ∈ Pts := by
      intro i hi
      have hβn : Q.2 ^ n = ψ' (b i) ^ n := by
        rw [base_n, base_p, Polynomial.map_map, Algebra.algebraMap_self, RingHom.id_comp] at hQv
        calc Q.2 ^ n = Q.2 ^ S.n := by rw [hSn]
          _ = ((toPoly f).map ψ').eval Q.1 := by rw [hQv, hpK]
          _ = ψ' (b i) ^ n := by rw [hi, eval_map, eval₂_hom, ← hbf, map_pow]
      obtain ⟨k, hk, hke⟩ := exists_fibre hn hζ' _ _ ((map_ne_zero_iff _ hψi).mpr (hb i)) hβn
      refine Finset.mem_image.mpr ⟨finProdFinEquiv (i, ⟨k, hk⟩), Finset.mem_univ _, ?_⟩
      simp only [hP_def, ptA, ptB, fibI_equiv, fibK_equiv]
      refine Prod.ext hi.symm ?_
      rw [hke]; simp
    have hg := gammaAbel P hPinj (fun i ↦ ψ' (a i)) (fun q ↦ rfl) (fun i i' h ↦ ha (hψi h)) zq M Q
      hfib
    refine hg.trans (Finset.sum_congr rfl fun q _ ↦ ?_)
    split_ifs
    · rw [negJ_cast]; rfl
    · rfl
  -- descend to `F`
  have hkey' : PrincipalMulN ((toPoly f).map ψ') n (f.length - 1) (fun q ↦ ψ' (ptA n a q))
      (fun q ↦ ψ' (ptB n ζ b q)) (fun q ↦ M * mqJ n ζ a b G j q) n := by
    have e1 : (S.base K).p = (toPoly f).map ψ' := by rw [base_p, hpK]
    have e2 : (S.base K).p.natDegree = f.length - 1 := by
      rw [e1, natDegree_map_eq_of_injective hψi, hdeg]
    rw [e2, e1, base_n, hSn] at hkey
    exact hkey
  have hΓF : ∀ q, (n : F) * ptB n ζ b q ^ (n - 1) ≠ 0 ∧ ptB n ζ b q ^ n = (toPoly f).eval (ptA n a q) :=
    fun q ↦ ⟨mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ (pt_ne_zero hn hζ b hb q)),
      pt_valid _ hζ a b hbf q⟩
  obtain ⟨W, hW0, hWs, hWv⟩ := principalMulN_descend ψ' (toPoly f) hn (f.length - 1) (ptA n a)
    (ptB n ζ b) (fun q ↦ M * mqJ n ζ a b G j q) hΓF n hkey'
  refine ⟨n * M, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne' (by omega)), W, hW0, ?_, ?_⟩
  · intro i a' h
    have := hWs i a' h
    rw [← Finset.mul_sum, ← mul_assoc] at this
    exact this
  · intro q
    have := hWv q
    rwa [← mul_assoc] at this

end AbelMain

end Sup
