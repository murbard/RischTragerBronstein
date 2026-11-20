import RischTragerBronstein.Curves.CertBranch
import RischTragerBronstein.Curves.AutoPuiseux
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Irreducibility from the roots at a split point

Let `F ∈ k[x][Y]` be monic of degree `n`, with `x`-degrees at most `d`, and let
`F(a + T, Y) = ∏ⱼ (Y − yⱼ)` with distinct `yⱼ ∈ k⟦T⟧`. A monic factor `G` of `F` has `x`-degrees at
most `d` (the `x`-degree is additive, `natDegree_coeff_le_of_mul`), and `G(a + T, Y)` is the
product of `Y − yⱼ` over a subset `S` (`eq_prod_subset_of_dvd`). So if no subset with
`0 < |S| ≤ n/2` has a product whose coefficients are polynomials of degree `≤ d` in `T`, then `F`
is irreducible (**`irreducible_of_subsets`**).

Unlike an irreducible specialization or an Eisenstein point, this certificate exists for every
irreducible `F` at every split point (over a field where the product coefficients are computed
exactly), whatever the monodromy group.
-/

open Polynomial

namespace Curves

open Differential

section Swap

variable {R : Type*} [CommRing R]

lemma coeff_coeff_swap (p : R[X][X]) (i j : ℕ) :
    ((Bivariate.swap p).coeff j).coeff i = (p.coeff i).coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial n f =>
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
      simp only [(monomial n).map_add, map_add, coeff_add, hf, hg]
    | monomial m r =>
      rw [Bivariate.swap_monomial_monomial]
      simp only [coeff_monomial]
      rcases eq_or_ne m j with rfl | h1 <;> rcases eq_or_ne n i with rfl | h2 <;>
        simp [coeff_monomial, *]

lemma natDegree_coeff_le_swap (p : R[X][X]) (i : ℕ) :
    (p.coeff i).natDegree ≤ (Bivariate.swap p).natDegree := by
  by_cases h : p.coeff i = 0
  · rw [h, natDegree_zero]; exact Nat.zero_le _
  · refine le_natDegree_of_ne_zero fun h0 ↦ ?_
    have := coeff_coeff_swap p i (p.coeff i).natDegree
    rw [h0, coeff_zero] at this
    exact h (leadingCoeff_eq_zero.mp this.symm)

lemma natDegree_swap_le (p : R[X][X]) (d : ℕ) (hd : ∀ i, (p.coeff i).natDegree ≤ d) :
    (Bivariate.swap p).natDegree ≤ d := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_
  ext i
  rw [coeff_coeff_swap, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd i) (by exact_mod_cast hj))

/-- **`x`-degrees of a factor** are bounded by those of the product. -/
lemma natDegree_coeff_le_of_mul [IsDomain R] (G H : R[X][X]) (hH : H ≠ 0) (d : ℕ)
    (hd : ∀ i, ((G * H).coeff i).natDegree ≤ d) (i : ℕ) : (G.coeff i).natDegree ≤ d := by
  by_cases hG : G = 0
  · rw [hG, coeff_zero, natDegree_zero]; exact Nat.zero_le _
  have h1 := natDegree_swap_le _ d hd
  rw [map_mul, natDegree_mul ((map_ne_zero_iff _ Bivariate.swap.injective).mpr hG)
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr hH)] at h1
  exact (natDegree_coeff_le_swap G i).trans (by omega)

end Swap

section Subset

variable {L : Type*} [Field L]

/-- **A monic divisor of a product of distinct linear factors** is the product over a subset. -/
lemma eq_prod_subset_of_dvd {n : ℕ} (r : Fin n → L) (hr : Function.Injective r) (g : L[X])
    (hg : g.Monic) (hdvd : g ∣ ∏ j, (X - C (r j))) :
    ∃ S : Finset (Fin n), g = ∏ j ∈ S, (X - C (r j)) := by
  classical
  have hP : ∏ j, (X - C (r j)) = ∏ a ∈ Finset.univ.image r, (X - C a) := by
    rw [Finset.prod_image fun j _ l _ h ↦ hr h]
  have hP0 : ∏ j, (X - C (r j)) ≠ 0 := (monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _).ne_zero
  have hsp : Splits g := Splits.of_dvd (Splits.prod fun j _ ↦ Splits.X_sub_C _) hP0 hdvd
  have hle : g.roots ≤ (Finset.univ.image r).val := by
    rw [← roots_prod_X_sub_C, ← hP]; exact roots.le_of_dvd hP0 hdvd
  have hnd : g.roots.Nodup := Multiset.nodup_of_le hle (Finset.univ.image r).nodup
  have hT : g.roots = g.roots.toFinset.val := by rw [Multiset.toFinset_val, hnd.dedup]
  have hgT : g = ∏ a ∈ g.roots.toFinset, (X - C a) := by
    have := hsp.eq_prod_roots_of_monic hg
    rwa [hT, ← Finset.prod_eq_multiset_prod] at this
  refine ⟨Finset.univ.filter fun j ↦ r j ∈ g.roots, ?_⟩
  conv_lhs => rw [hgT]
  rw [← Finset.prod_image (s := Finset.univ.filter fun j ↦ r j ∈ g.roots)
    (f := fun a ↦ X - C a) fun j _ l _ h ↦ hr h]
  congr 1
  ext a
  simp only [Multiset.mem_toFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Multiset.mem_of_le hle ha)
    exact ⟨j, ha, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact hj

end Subset

section Irr

variable {k : Type*} [Field k]

lemma coeff_branchSub_one (a : k) (P : k[X]) (d : ℕ) (hP : P.natDegree ≤ d) (t : ℕ) (ht : d < t) :
    (branchSub (C := k) (K := k) 1 a P).coeff (t : ℤ) = 0 := by
  rw [branchSub_apply, HahnSeries.ofPowerSeries_apply_coeff, Polynomial.coeff_coe]
  refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ ht)
  refine (natDegree_comp_le).trans ?_
  rw [natDegree_map, pow_one]
  have : (Polynomial.C a + X : k[X]).natDegree ≤ 1 := by
    rw [add_comm]; exact (natDegree_X_add_C a).le
  calc P.natDegree * (Polynomial.C a + X : k[X]).natDegree ≤ P.natDegree * 1 :=
        Nat.mul_le_mul_left _ this
    _ = P.natDegree := mul_one _
    _ ≤ d := hP

/-- **Irreducibility from the roots at a split point.** -/
theorem irreducible_of_subsets (Fk : k[X][X]) (hmon : Fk.Monic) (hn : 0 < Fk.natDegree) (a : k)
    (d : ℕ) (hd : ∀ i, (Fk.coeff i).natDegree ≤ d) (y : Fin Fk.natDegree → PowerSeries k)
    (hinj : Function.Injective y)
    (hsplit : Fk.map (branchSub (C := k) (K := k) 1 a) =
      ∏ j, (X - C (HahnSeries.ofPowerSeries ℤ k (y j))))
    (hS : ∀ S : Finset (Fin Fk.natDegree), 0 < S.card → 2 * S.card ≤ Fk.natDegree →
      ∃ i t, d < t ∧ PowerSeries.coeff t ((∏ j ∈ S, (X - C (y j))).coeff i) ≠ 0) :
    Irreducible Fk := by
  classical
  rw [hmon.irreducible_iff_natDegree']
  refine ⟨fun h ↦ by rw [h, natDegree_one] at hn; exact lt_irrefl 0 hn, fun f g hf hg hfg hdeg ↦ ?_⟩
  obtain ⟨hg0, hgn⟩ := Finset.mem_Ioc.mp hdeg
  -- the factor over `k⟦T⟧`
  have hinj' : Function.Injective fun j ↦ HahnSeries.ofPowerSeries ℤ k (y j) :=
    fun j l h ↦ hinj (HahnSeries.ofPowerSeries_injective h)
  obtain ⟨S, hS'⟩ := eq_prod_subset_of_dvd _ hinj' (g.map (branchSub (C := k) (K := k) 1 a))
    (hg.map _) (by rw [← hsplit, ← hfg, Polynomial.map_mul]; exact dvd_mul_left _ _)
  have hcard : S.card = g.natDegree := by
    have := congrArg natDegree hS'
    rw [hg.natDegree_map, natDegree_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _] at this
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one] at this
    exact this.symm
  obtain ⟨i, t, hdt, hne⟩ := hS S (by omega) (by
    have := Nat.mul_le_mul_left 2 hgn
    have h2 := Nat.mul_div_le Fk.natDegree 2
    rw [hcard]; linarith)
  apply hne
  -- the degree bound on the factor
  have hgd : (g.coeff i).natDegree ≤ d :=
    natDegree_coeff_le_of_mul g f hf.ne_zero d (by rw [mul_comm, hfg]; exact hd) i
  have h1 := coeff_branchSub_one a (g.coeff i) d hgd t hdt
  rw [← coeff_map, hS'] at h1
  have e : (∏ j ∈ S, (X - C (HahnSeries.ofPowerSeries ℤ k (y j)))) =
      (∏ j ∈ S, (X - C (y j))).map (HahnSeries.ofPowerSeries ℤ k) := by
    rw [Polynomial.map_prod]
    simp [Polynomial.map_sub, map_X, map_C]
  rw [e, coeff_map, HahnSeries.ofPowerSeries_apply_coeff] at h1
  exact h1

end Irr

section Check

variable {F : Type*} [Field F] [DecidableEq F]

open CPoly Sup

/-- The subsets of `{0, …, n − 1}`, as lists. -/
def subsetsL : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => subsetsL n ++ (subsetsL n).map (n :: ·)

/-- `∏_{j ∈ L} (Y − ỹⱼ)`. -/
def prodSubB (ys : List (CPoly F)) (L : List ℕ) : BPoly F :=
  L.foldr (fun j acc ↦ mulB [neg (ys.getD j []), [1]] acc) [[1]]

/-- **The subset certificate** at `x = a` (branch certificate `c` with `N = 1`): the `x`-degrees
of `F` are at most `d`, and for every `L` with `0 < |L| ≤ n/2` some coefficient of
`∏_{j ∈ L} (Y − ỹⱼ)` has a non-zero `Tᵗ` term with `d < t < prec`. -/
def irrSubsetCheck (Fc : BPoly F) (n d : ℕ) (a : F) (c : BranchCert F) : Bool :=
  certCheck Fc n a c && decide (c.N = 1) && Fc.all (fun q ↦ decide (q.length ≤ d + 1)) &&
  (subsetsL n).all fun L ↦ !(decide (0 < L.length) && decide (2 * L.length ≤ n)) ||
    (List.range (L.length + 1)).any fun i ↦ (List.range c.prec).any fun t ↦
      decide (d < t) && decide (((prodSubB c.ys L).getD i []).getD t 0 ≠ 0)

lemma exists_subsetsL : ∀ (n : ℕ) (S : Finset ℕ), (∀ j ∈ S, j < n) →
    ∃ L ∈ subsetsL n, L.Nodup ∧ ∀ j, j ∈ L ↔ j ∈ S
  | 0, S, hS => ⟨[], by simp [subsetsL], List.nodup_nil, fun j ↦ by
      simp only [List.not_mem_nil, false_iff]; exact fun h ↦ absurd (hS j h) (Nat.not_lt_zero _)⟩
  | n + 1, S, hS => by
    classical
    by_cases hn : n ∈ S
    · obtain ⟨L, hL, hnd, hmem⟩ := exists_subsetsL n (S.erase n) fun j hj ↦ by
        have := hS j (Finset.mem_of_mem_erase hj)
        have := Finset.ne_of_mem_erase hj
        omega
      refine ⟨n :: L, List.mem_append_right _ (List.mem_map.mpr ⟨L, hL, rfl⟩),
        List.nodup_cons.mpr ⟨fun h ↦ ?_, hnd⟩, fun j ↦ ?_⟩
      · exact Finset.ne_of_mem_erase ((hmem n).mp h) rfl
      · rw [List.mem_cons, hmem, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨-, h⟩)
          · exact hn
          · exact h
        · intro h
          by_cases hj : j = n
          · exact Or.inl hj
          · exact Or.inr ⟨hj, h⟩
    · obtain ⟨L, hL, hnd, hmem⟩ := exists_subsetsL n S fun j hj ↦ by
        have := hS j hj
        have : j ≠ n := fun h ↦ hn (h ▸ hj)
        omega
      exact ⟨L, List.mem_append_left _ hL, hnd, hmem⟩

lemma length_of_mem_iff {L : List ℕ} (hnd : L.Nodup) {S : Finset ℕ} (h : ∀ j, j ∈ L ↔ j ∈ S) :
    L.length = S.card := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext j
  rw [List.mem_toFinset, h]

lemma toB_prodSubB (ys : List (CPoly F)) : ∀ L : List ℕ,
    toB (prodSubB ys L) = (L.map fun j ↦ X - C (toPoly (ys.getD j []))).prod
  | [] => by simp [prodSubB, toPoly]
  | j :: L => by
    have ih := toB_prodSubB ys L
    simp only [prodSubB, List.foldr_cons] at ih ⊢
    have h1 : toPoly ([1] : CPoly F) = 1 := by simp [toPoly]
    rw [toB_mulB, ih, List.map_cons, List.prod_cons]
    congr 1
    simp only [toB_cons, toB_nil, toPoly_neg, h1, mul_zero, add_zero, map_neg, map_one, mul_one]
    ring

/-- Congruent factors give congruent products. -/
lemma prod_sub_dvd {k : Type*} [Field k] (P : ℕ) (L : List ℕ) (u v : ℕ → PowerSeries k)
    (h : ∀ j ∈ L, (PowerSeries.X : PowerSeries k) ^ P ∣ u j - v j) (i : ℕ) :
    (PowerSeries.X : PowerSeries k) ^ P ∣
      ((L.map fun j ↦ X - C (u j)).prod - (L.map fun j ↦ X - C (v j)).prod).coeff i := by
  set I := Ideal.span {(PowerSeries.X : PowerSeries k) ^ P}
  have e : ((L.map fun j ↦ X - C (u j)).prod).map (Ideal.Quotient.mk I) =
      ((L.map fun j ↦ X - C (v j)).prod).map (Ideal.Quotient.mk I) := by
    rw [Polynomial.map_list_prod, Polynomial.map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun j hj ↦ ?_
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
    congr 2
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h j hj))
  have := congrArg (·.coeff i) e
  simp only [coeff_map] at this
  rw [coeff_sub]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp this)

/-- **The subset certificate proves irreducibility** over every field `k ⊇ F`. -/
theorem irrSubsetCheck_spec (Fc : BPoly F) (n d : ℕ) (a : F) (c : BranchCert F)
    (h : irrSubsetCheck Fc n d a c = true) (hmon : (toB Fc).Monic) (hn : (toB Fc).natDegree = n)
    (hn0 : 0 < n) {k : Type*} [Field k] (ψ : F →+* k) :
    Irreducible ((toB Fc).map (mapRingHom ψ)) := by
  classical
  simp only [irrSubsetCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hc, hN⟩, hlen⟩, hsub⟩ := h
  obtain ⟨y, hy, hinj, hsplit⟩ := certCheck_spec (C := k) (K := k) Fc n hmon hn a c hc ψ
  have hmon' : ((toB Fc).map (mapRingHom ψ)).Monic := hmon.map _
  have hn' : ((toB Fc).map (mapRingHom ψ)).natDegree = n := by rw [hmon.natDegree_map, hn]
  have hψ : (algebraMap k k).comp ψ = ψ := by ext; rfl
  rw [hψ] at hy
  rw [hN] at hsplit
  have e2 : algebraMap k k (ψ a) = ψ a := rfl
  rw [e2] at hsplit
  -- reindex by the degree
  obtain ⟨m, hm⟩ : ∃ m, m = ((toB Fc).map (mapRingHom ψ)).natDegree := ⟨_, rfl⟩
  refine irreducible_of_subsets _ hmon' (by rw [hn']; exact hn0) (ψ a) d (fun i ↦ ?_)
    (fun j ↦ y (Fin.cast hn' j)) (hinj.comp (Fin.cast_injective hn')) ?_ ?_
  · rw [coeff_map, coe_mapRingHom]
    refine (natDegree_map_le).trans ?_
    rw [coeff_toB]
    refine (natDegree_le_iff_coeff_eq_zero.mpr fun t ht ↦ ?_)
    rw [coeff_toPoly]
    have hdt : d < t := by exact_mod_cast ht
    by_cases hi : i < Fc.length
    · have := hlen (Fc.getD i []) (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
      rw [List.getD_eq_default _ _ (by omega)]
    · rw [List.getD_eq_default Fc [] (by omega)]; rfl
  · rw [hsplit]
    exact (Fintype.prod_equiv (finCongr hn'.symm) _ _ fun j ↦ rfl)
  · intro S hS0 hS2
    -- the list of the subset
    obtain ⟨L, hL, hnd, hmem⟩ := exists_subsetsL n (S.map Fin.valEmbedding) fun j hj ↦ by
      obtain ⟨j', -, rfl⟩ := Finset.mem_map.mp hj
      exact hn' ▸ j'.2
    have hcard : L.length = S.card := by rw [length_of_mem_iff hnd hmem, Finset.card_map]
    rcases hsub L hL with h1 | ⟨i, hi, t, ht, hdt, hne⟩
    · exfalso
      rcases h1 with h1 | h1
      · rw [hcard] at h1; exact h1 hS0
      · rw [hcard, ← hn'] at h1; exact h1 hS2
    refine ⟨i, t, hdt, fun h0 ↦ hne ?_⟩
    -- the true product and the computed one
    set u : ℕ → PowerSeries k := fun j ↦ if hj : j < n then y ⟨j, hj⟩ else 0 with hu
    set v : ℕ → PowerSeries k := fun j ↦ thetaT ψ (toPoly (c.ys.getD j [])) with hv
    have hprodS : ∏ j ∈ S, (X - C (y (Fin.cast hn' j))) = (L.map fun j ↦ X - C (u j)).prod := by
      rw [← List.prod_toFinset _ hnd]
      have e : L.toFinset = S.map Fin.valEmbedding := by
        ext j
        rw [List.mem_toFinset, hmem]
      rw [e, Finset.prod_map]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp only [hu, Fin.valEmbedding_apply]
      rw [dite_cond_eq_true (eq_true (by have := j.2; omega))]
      rfl
    have hcomp : (L.map fun j ↦ X - C (v j)).prod = (toB (prodSubB c.ys L)).map (thetaT ψ) := by
      rw [toB_prodSubB, Polynomial.map_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ ↦ ?_
      simp [hv, Polynomial.map_sub, map_X, map_C]
    have hdvd := prod_sub_dvd c.prec L u v (fun j hj ↦ by
      have hj' : j < n := by
        have := (hmem j).mp hj
        obtain ⟨j', -, rfl⟩ := Finset.mem_map.mp this
        exact hn' ▸ j'.2
      simp only [hu, hv, dite_cond_eq_true (eq_true hj')]
      exact hy ⟨j, hj'⟩) i
    rw [hprodS] at h0
    rw [hcomp, coeff_sub, coeff_map] at hdvd
    have ht' := (PowerSeries.X_pow_dvd_iff.mp hdvd) t ht
    rw [map_sub, h0, zero_sub, neg_eq_zero, coeff_toB, thetaT_apply, Polynomial.coeff_coe,
      coeff_map, coeff_toPoly] at ht'
    exact (map_eq_zero_iff ψ ψ.injective).mp ht'

/-- Newton lifts of the simple roots `ys0` of `F(a, Y)` to precision `prec`. -/
def liftRootsAt (Fc : BPoly F) (a : F) (ys0 : List F) (prec : ℕ) : BranchCert F :=
  let H := Fc.map fun q ↦ compC q (shiftC a 1)
  ⟨1, ys0.map fun y0 ↦ newtonT H prec (Nat.log2 prec + 3) [y0], prec⟩

/-- **The subset certificate at a split point** `a` with simple roots `ys0`. -/
def irrAt (Fc : BPoly F) (n d : ℕ) (a : F) (ys0 : List F) (prec : ℕ) : Bool :=
  irrSubsetCheck Fc n d a (liftRootsAt Fc a ys0 prec)

end Check

section Gauss

open Polynomial

/-- **Irreducibility over `Q(x)` from irreducibility over `O[x]`** (`O` integrally closed with
fraction field `Q`, the polynomial monic). -/
theorem irreducible_ratFunc_of_irreducible {O Q : Type*} [CommRing O] [IsDomain O] [Field Q]
    [Algebra O Q] [IsFractionRing O Q] [IsIntegrallyClosed O[X]] (Φ : O[X][X]) (hm : Φ.Monic)
    (hi : Irreducible Φ) :
    Irreducible ((Φ.map (mapRingHom (algebraMap O Q))).map (algebraMap Q[X] (RatFunc Q))) := by
  classical
  letI : Algebra O[X] (RatFunc Q) :=
    ((algebraMap Q[X] (RatFunc Q)).comp (mapRingHom (algebraMap O Q))).toAlgebra
  have hinj : Function.Injective (algebraMap O[X] (RatFunc Q)) :=
    (IsFractionRing.injective Q[X] (RatFunc Q)).comp
      (Polynomial.map_injective _ (IsFractionRing.injective O Q))
  haveI : FaithfulSMul O[X] (RatFunc Q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsFractionRing O[X] (RatFunc Q) := IsFractionRing.of_field _ _ fun z ↦ by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Q[X]) z
    obtain ⟨c, hc, hca⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) a
    obtain ⟨c', hc', hcb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) b
    refine ⟨Polynomial.C c' * IsLocalization.integerNormalization (nonZeroDivisors O) a,
      Polynomial.C c * IsLocalization.integerNormalization (nonZeroDivisors O) b, ?_⟩
    have e : ∀ w : O[X], algebraMap O[X] (RatFunc Q) w =
        algebraMap Q[X] (RatFunc Q) (w.map (algebraMap O Q)) := fun w ↦ rfl
    rw [e, e, Polynomial.map_mul, Polynomial.map_mul, hca, hcb, Polynomial.map_C,
      Polynomial.map_C, ← algebraMap_smul Q c a, ← algebraMap_smul Q c' b, Polynomial.smul_eq_C_mul,
      Polynomial.smul_eq_C_mul]
    have hc0 : algebraMap O Q c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O Q)).mpr
      (nonZeroDivisors.ne_zero hc)
    have hc0' : algebraMap O Q c' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O Q)).mpr
      (nonZeroDivisors.ne_zero hc')
    have hb0 : algebraMap Q[X] (RatFunc Q) b ≠ 0 := (map_ne_zero_iff _
      (IsFractionRing.injective Q[X] (RatFunc Q))).mpr (nonZeroDivisors.ne_zero hb)
    have hC : ∀ q : Q, q ≠ 0 → algebraMap Q[X] (RatFunc Q) (Polynomial.C q) ≠ 0 := fun q hq ↦
      (map_ne_zero_iff _ (IsFractionRing.injective Q[X] (RatFunc Q))).mpr (C_ne_zero.mpr hq)
    simp only [map_mul]
    have hu := hC _ hc0
    have hv := hC _ hc0'
    generalize algebraMap Q[X] (RatFunc Q) (Polynomial.C (algebraMap O Q c)) = u at hu ⊢
    generalize algebraMap Q[X] (RatFunc Q) (Polynomial.C (algebraMap O Q c')) = v at hv ⊢
    generalize algebraMap Q[X] (RatFunc Q) b = B at hb0 ⊢
    field_simp
  have h := (hm.irreducible_iff_irreducible_map_fraction_map (K := RatFunc Q)).mp hi
  rw [Polynomial.map_map]
  exact h

end Gauss

end Curves
