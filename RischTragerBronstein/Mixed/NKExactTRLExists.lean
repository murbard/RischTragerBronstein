import RischTragerBronstein.Mixed.NKExactTRLSome
import RischTragerBronstein.Mixed.NKExactTREExists

/-!
# Existence of answering parameters for the parametric tests

For a constant curve over a logarithmic (resp. exponential) level the parameters of
`exactTR_exists` (resp. `exactTRE_exists`) make `exactTRL` (resp. `exactTREL`) answer for any
parameter list `gs` (`exactTRL_exists`, `exactTREL_exists`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 3200000 in
/-- **`exactTR` answers for a suitable integral basis of a constant curve.** -/
theorem exactTRL_exists (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hn : F0.natDegree ≠ 0)
    (P : GPoly (LC (m + 1))) (hPlen : P.length = F0.natDegree + 1)
    (hPsem : ∀ i, (T.MPr (m + 1) h1).sem (P.getD i (MOr Fc ks (m + 1)).zero) =
      T.phi m ((F0.coeff i).map (algebraMap ℚ (T.F m))))
    (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    ∃ (A B Ai Bi : ℕ → ℕ → ℚ[X]) (r : ℕ → ℤ),
      (exactTRL Fc ks m η lim r P (matQ Fc ks m A B F0.natDegree)
        (matQ Fc ks m Ai Bi F0.natDegree) f gs).isSome := by
  classical
  set n := F0.natDegree with hn'
  set M1 := T.MPr (m + 1) h1 with hM1
  have hN : P.length - 1 = n := by omega
  have hsemn : M1.sem (P.getD n (MOr Fc ks (m + 1)).zero) = 1 := by
    rw [hPsem, hF0.coeff_natDegree, Polynomial.map_one, map_one]
  have hPc : (MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero)
      ((MOr Fc ks (m + 1)).neg (MOr Fc ks (m + 1)).one)) = true := by
    rw [hN]
    refine (M1.isZero_iff _).mpr ?_
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, hsemn, add_neg_cancel]
  have hPmap := T.toPoly_P_const m h1 F0 P hPsem
  have htrQ : Transcendental ℚ (T.ts m) := Transcendental.of_tower_top ℚ htr
  have hPdeg : (GPoly.toPoly M1 P).natDegree = n := by
    have := congrArg natDegree hPmap
    rw [natDegree_map_eq_of_injective (algebraMap (T.F (m + 1)) L).injective,
      natDegree_map_eq_of_injective (transcendental_iff_injective.mp htrQ)] at this
    exact this
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hsemn]
  have hroot : (F0.map (aeval (T.ts m)).toRingHom).eval θ = 0 := by
    rw [← hPmap, eval_map, ← aeval_def]; exact hP
  have hcop := T.sep_P_const m h1 P hPm n hPdeg θ hP hind
  obtain ⟨dθ, hd⟩ := Option.isSome_iff_exists.mp (dThetaC_isSome M1 P hcop)
  obtain ⟨A, B, Ai, Bi, r, S0, Pm, hB, hBi, hTTi, hTiT, hS0, hsq, hder, hdeg⟩ :=
    T.const_logBasis m h1 hm hk htr hη F0 hF0 θ hroot hind
  set t := T.ts m with ht
  set ηL : L := (((T.MP m h1.of_succ).sem η : T.F m) : L) with hηL
  have hηF0 : (T.MP m h1.of_succ).sem η ≠ 0 := fun h0 ↦ hη 0 (by rw [Derivation.map_zero, h0])
  have hS0t : aeval t S0 ≠ 0 := fun h0 ↦ hS0 (transcendental_iff_injective.mp htrQ (by rw [h0, map_zero]))
  set A' := ext2 n A 0 with hA'
  set B' := ext2 n B 1 with hB'
  set Ai' := ext2 n Ai 0 with hAi'
  set Bi' := ext2 n Bi 1 with hBi'
  set Pm' := ext2 n Pm 0 with hPm'
  set r' := extR n r with hr'
  have eA : ∀ i k (hi : i < n) (hk : k < n), A' i k = A ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n A 0 i k hi hk
  have eB : ∀ i k (hi : i < n) (hk : k < n), B' i k = B ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n B 1 i k hi hk
  have eAi : ∀ i k (hi : i < n) (hk : k < n), Ai' i k = Ai ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Ai 0 i k hi hk
  have eBi : ∀ i k (hi : i < n) (hk : k < n), Bi' i k = Bi ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Bi 1 i k hi hk
  have ePm : ∀ i k (hi : i < n) (hk : k < n), Pm' i k = Pm ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Pm 0 i k hi hk
  have er : ∀ k (hk : k < n), r' k = (r ⟨k, hk⟩ : ℤ) := fun k hk ↦ extR_of_lt n r k hk
  set Tc := matQ Fc ks m A' B' n with hTc
  set Ti := matQ Fc ks m Ai' Bi' n with hTi
  -- the values of the matrices
  have sT : ∀ i (hi : i < n) k (hk : k < n),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval t (A ⟨i, hi⟩ ⟨k, hk⟩) / aeval t (B ⟨i, hi⟩ ⟨k, hk⟩) := fun i hi k hk ↦ by
    rw [hTc, matQ_getD _ _ m _ _ n i k hi hk, T.coe_sem_fracQ m h1, eA i k hi hk, eB i k hi hk]
  have sTi : ∀ i (hi : i < n) k (hk : k < n),
      ((M1.sem ((Ti.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval t (Ai ⟨i, hi⟩ ⟨k, hk⟩) / aeval t (Bi ⟨i, hi⟩ ⟨k, hk⟩) := fun i hi k hk ↦ by
    rw [hTi, matQ_getD _ _ m _ _ n i k hi hk, T.coe_sem_fracQ m h1, eAi i k hi hk, eBi i k hi hk]
  -- range sums as `Fin` sums
  have hfin : ∀ (g : ℕ → L), ∑ k ∈ Finset.range n, g k = ∑ k : Fin n, g k := fun g ↦
    (Fin.sum_univ_eq_sum_range g n).symm
  -- the product checks
  have hok : prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true ∧
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true := by
    rw [hN]
    refine ⟨T.prodIdC_of_sem m h1 n _ _ fun i hi j hj ↦ ?_, T.prodIdC_of_sem m h1 n _ _ fun i hi j hj ↦ ?_⟩
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Ti.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2, sTi k k.2 j hj], hTTi ⟨i, hi⟩ ⟨j, hj⟩]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Fin.ext_iff]
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Ti.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Tc.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sTi i hi k k.2, sT k k.2 j hj], hTiT ⟨i, hi⟩ ⟨j, hj⟩]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Fin.ext_iff]
  -- the derivation matrix
  set ηF : T.F (m + 1) := T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) with hηF
  set S0F : (T.F m)[X] := S0.map (algebraMap ℚ (T.F m)) with hS0F
  set Mval : ℕ → ℕ → T.F (m + 1) := fun i j ↦
    ηF * T.phi m ((Pm' i j).map (algebraMap ℚ (T.F m))) / T.phi m S0F with hMvaldef
  have hηFL : (ηF : L) = ηL := by rw [hηF, coe_phi, aeval_C]; rfl
  have hS0FL : ((T.phi m S0F : T.F (m + 1)) : L) = aeval t S0 := by
    rw [hS0F, coe_phi, aeval_map_algebraMap]
  have hMvalL : ∀ i j (hi : i < n) (hj : j < n), (Mval i j : L) =
      ηL * aeval t (Pm ⟨i, hi⟩ ⟨j, hj⟩) / aeval t S0 := fun i j hi hj ↦ by
    rw [hMvaldef]
    push_cast
    rw [hηFL, hS0FL, coe_phi, aeval_map_algebraMap, ePm i j hi hj]
  -- `w = T θ`
  have hwL : ∀ i (hi : i < n), ∑ k ∈ Finset.range n,
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
      ∑ k : Fin n, aeval t (A ⟨i, hi⟩ k) / aeval t (B ⟨i, hi⟩ k) * θ ^ (k : ℕ) := fun i hi ↦ by
    rw [hfin]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2]
  have hMval : ∀ i < P.length - 1, (∑ k ∈ Finset.range (P.length - 1),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range (P.length - 1), (Mval i j : L) *
        ∑ k ∈ Finset.range (P.length - 1), ((M1.sem ((Tc.getD j []).getD k
          (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k := by
    rw [hN]
    intro i hi
    rw [hwL i hi, ← Fin.sum_univ_eq_sum_range (fun j ↦ (Mval i j : L) * ∑ k ∈ Finset.range n,
      ((M1.sem ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k) n]
    have hR : ∑ j : Fin n, (Mval i j : L) * ∑ k ∈ Finset.range n,
        ((M1.sem ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
        ∑ j : Fin n, ηL * aeval t (Pm ⟨i, hi⟩ j) / aeval t S0 *
          ∑ k : Fin n, aeval t (A j k) / aeval t (B j k) * θ ^ (k : ℕ) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [hwL j j.2, hMvalL i j hi j.2]
    rw [hR]
    have hd := hder ⟨i, hi⟩
    rw [← mul_div_cancel_right₀ ((∑ k : Fin n, aeval t (A ⟨i, hi⟩ k) / aeval t (B ⟨i, hi⟩ k) *
      θ ^ (k : ℕ))′) hS0t, hd, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hsqF : Squarefree S0F :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map (f := algebraMap ℚ (T.F m))).squarefree
  have hsq' : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      Mval i j = T.phi m A / T.phi m S := by
    intro i _ j _
    refine ⟨Polynomial.C ((T.MP m h1.of_succ).sem η) * (Pm' i j).map (algebraMap ℚ (T.F m)), S0F,
      hsqF, ?_⟩
    rw [hMvaldef, map_mul]
  have hτ : T.tau m ≠ 0 := T.tau_ne_zero m htr
  have hφS0 : T.phi m S0F ≠ 0 := fun h0 ↦ hS0t (by rw [← hS0FL, h0]; rfl)
  have hprop' : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.degree < B.degree ∧
      Mval i j * T.tau m ^ (r' j - r' i) - (if i = j then (r' i : T.F (m + 1)) *
        T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) / T.tau m else 0) =
        T.phi m A / T.phi m B := by
    rw [hN]
    intro i hi j hj
    set Q : ℚ[X] := X ^ (r ⟨j, hj⟩ + 1) * Pm ⟨i, hi⟩ ⟨j, hj⟩ -
      (if (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩ then Polynomial.C (r ⟨i, hi⟩ : ℚ) * X ^ r ⟨i, hi⟩ * S0 else 0)
      with hQ
    have hQd := hdeg ⟨i, hi⟩ ⟨j, hj⟩
    set B0 : ℚ[X] := X ^ (r ⟨i, hi⟩ + 1) * S0 with hB0
    have hB0d : B0.natDegree = r ⟨i, hi⟩ + 1 + S0.natDegree := by
      rw [hB0, natDegree_mul (pow_ne_zero _ X_ne_zero) hS0, natDegree_X_pow]
    have hB00 : B0 ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS0
    refine ⟨Polynomial.C ((T.MP m h1.of_succ).sem η) * Q.map (algebraMap ℚ (T.F m)),
      B0.map (algebraMap ℚ (T.F m)), (Polynomial.map_ne_zero_iff (algebraMap ℚ (T.F m)).injective).mpr
        hB00, ?_, ?_⟩
    · refine (degree_le_natDegree).trans_lt ?_
      rw [degree_map_eq_of_injective (algebraMap ℚ (T.F m)).injective, degree_eq_natDegree hB00,
        hB0d, Nat.cast_lt]
      have := (natDegree_C_mul_le ((T.MP m h1.of_succ).sem η) (Q.map (algebraMap ℚ (T.F m)))).trans
        (natDegree_map_le (f := algebraMap ℚ (T.F m)))
      have hQd' : Q.natDegree ≤ r ⟨i, hi⟩ + S0.natDegree := hQd
      exact lt_of_le_of_lt (this.trans hQd') (by omega)
    · simp only [hMvaldef, er i hi, er j hj, ePm i j hi hj]
      simp only [hQ, hB0, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        map_mul, map_sub, map_pow]
      have hX : T.phi m X = T.tau m := rfl
      rw [hX, zpow_sub₀ hτ, zpow_natCast, zpow_natCast]
      by_cases hij : i = j
      · subst hij
        simp only [if_true, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
          Polynomial.map_X, map_mul, map_pow, hX, eq_ratCast, map_natCast]
        have hc : T.phi m (Polynomial.C ((r ⟨i, hi⟩ : ℚ) : T.F m)) = ((r ⟨i, hi⟩ : ℕ) : T.F (m + 1)) := by
          rw [show ((r ⟨i, hi⟩ : ℚ) : T.F m) = ((r ⟨i, hi⟩ : ℕ) : T.F m) by push_cast; rfl,
            Polynomial.C_eq_natCast, map_natCast]
        simp only [Polynomial.map_C, eq_ratCast, hηF]
        have hφS : T.phi m (S0.map (algebraMap ℚ (T.F m))) ≠ 0 := hφS0
        have hrr : r ⟨i, hj⟩ = r ⟨i, hi⟩ := rfl
        rw [hrr]
        simp only [hS0F, Polynomial.map_natCast, map_natCast]
        field_simp
        push_cast
        ring
      · have hij' : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h ↦ hij (Fin.mk.inj_iff.mp h)
        simp only [hij, hij', if_false, sub_zero, Polynomial.map_zero, map_zero, hηF]
        have hφS : T.phi m (S0.map (algebraMap ℚ (T.F m))) ≠ 0 := hφS0
        field_simp
        ring
  refine ⟨A', B', Ai', Bi', r', ?_⟩
  exact T.exactTRL_isSome h1 hm hk htr lim hlim hη r' P θ hP hPc (by omega) (by rw [hN]; exact hind)
    dθ hd Tc Ti hok f gs Mval hMval hsq' hprop'


set_option maxHeartbeats 6400000 in
/-- **`exactTRE` answers for constant curves** for suitable `T`, `T⁻¹`, shifts, `N₀` and `C`. -/
theorem exactTREL_exists (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m}
    (hk : ks m = .exp a) (htr : Transcendental (T.F m) (T.ts m))
    (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hb0 : (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) ≠ 0)
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hn : F0.natDegree ≠ 0)
    (P : GPoly (LC (m + 1))) (hPlen : P.length = F0.natDegree + 1)
    (hPsem : ∀ i, (T.MPr (m + 1) h1).sem (P.getD i (MOr Fc ks (m + 1)).zero) =
      T.phi m ((F0.coeff i).map (algebraMap ℚ (T.F m))))
    (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    ∃ (A B Ai Bi : ℕ → ℕ → ℚ[X]) (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)),
      (exactTREL Fc ks m a rdeD r N0 C Ci P (matQ Fc ks m A B F0.natDegree)
        (matQ Fc ks m Ai Bi F0.natDegree) f gs).isSome := by
  classical
  set n := F0.natDegree with hn'
  set M1 := T.MPr (m + 1) h1 with hM1
  have hN : P.length - 1 = n := by omega
  have hsemn : M1.sem (P.getD n (MOr Fc ks (m + 1)).zero) = 1 := by
    rw [hPsem, hF0.coeff_natDegree, Polynomial.map_one, map_one]
  have hPc : (MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero)
      ((MOr Fc ks (m + 1)).neg (MOr Fc ks (m + 1)).one)) = true := by
    rw [hN]
    refine (M1.isZero_iff _).mpr ?_
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, hsemn, add_neg_cancel]
  have hPmap := T.toPoly_P_const m h1 F0 P hPsem
  have htrQ : Transcendental ℚ (T.ts m) := Transcendental.of_tower_top ℚ htr
  have hPdeg : (GPoly.toPoly M1 P).natDegree = n := by
    have := congrArg natDegree hPmap
    rw [natDegree_map_eq_of_injective (algebraMap (T.F (m + 1)) L).injective,
      natDegree_map_eq_of_injective (transcendental_iff_injective.mp htrQ)] at this
    exact this
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hsemn]
  have hroot : (F0.map (aeval (T.ts m)).toRingHom).eval θ = 0 := by
    rw [← hPmap, eval_map, ← aeval_def]; exact hP
  have hcop := T.sep_P_const m h1 P hPm n hPdeg θ hP hind
  obtain ⟨dθ, hd⟩ := Option.isSome_iff_exists.mp (dThetaC_isSome M1 P hcop)
  obtain ⟨dθ, hd⟩ := Option.isSome_iff_exists.mp (dThetaC_isSome M1 P hcop)
  set t := T.ts m with ht
  set b : T.F m := (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) with hb
  set eL : L := ((b : T.F m) : L) * t with heL
  have ht0 : t ≠ 0 := htrQ.ne_zero
  have hbL : ((b : T.F m) : L) ≠ 0 := fun h0 ↦ hb0 (Subtype.ext (by rw [ZeroMemClass.coe_zero]; exact h0))
  obtain ⟨A, B, Ai, Bi, r, S0, Pm, hB, hBi, hTTi, hTiT, hS0, hsq, hder, hdeg, hz0, hinf⟩ :=
    T.const_logBasisG m htr eL (mul_ne_zero hbL ht0) (T.deriv_ts_L_exp m h1.of_succ hm hk) F0 hF0 θ
      hroot hind
  have hS0t : aeval t S0 ≠ 0 := fun h0 ↦ hS0 (transcendental_iff_injective.mp htrQ (by rw [h0, map_zero]))
  set A' := ext2 n A 0 with hA'
  set B' := ext2 n B 1 with hB'
  set Ai' := ext2 n Ai 0 with hAi'
  set Bi' := ext2 n Bi 1 with hBi'
  set Pm' := ext2 n Pm 0 with hPm'
  set r' := extR n r with hr'
  have eA : ∀ i k (hi : i < n) (hk : k < n), A' i k = A ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n A 0 i k hi hk
  have eB : ∀ i k (hi : i < n) (hk : k < n), B' i k = B ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n B 1 i k hi hk
  have eAi : ∀ i k (hi : i < n) (hk : k < n), Ai' i k = Ai ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Ai 0 i k hi hk
  have eBi : ∀ i k (hi : i < n) (hk : k < n), Bi' i k = Bi ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Bi 1 i k hi hk
  have ePm : ∀ i k (hi : i < n) (hk : k < n), Pm' i k = Pm ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Pm 0 i k hi hk
  have er : ∀ k (hk : k < n), r' k = (r ⟨k, hk⟩ : ℤ) := fun k hk ↦ extR_of_lt n r k hk
  set Tc := matQ Fc ks m A' B' n with hTc
  set Ti := matQ Fc ks m Ai' Bi' n with hTi
  -- the values of the matrices
  have sT : ∀ i (hi : i < n) k (hk : k < n),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval t (A ⟨i, hi⟩ ⟨k, hk⟩) / aeval t (B ⟨i, hi⟩ ⟨k, hk⟩) := fun i hi k hk ↦ by
    rw [hTc, matQ_getD _ _ m _ _ n i k hi hk, T.coe_sem_fracQ m h1, eA i k hi hk, eB i k hi hk]
  have sTi : ∀ i (hi : i < n) k (hk : k < n),
      ((M1.sem ((Ti.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval t (Ai ⟨i, hi⟩ ⟨k, hk⟩) / aeval t (Bi ⟨i, hi⟩ ⟨k, hk⟩) := fun i hi k hk ↦ by
    rw [hTi, matQ_getD _ _ m _ _ n i k hi hk, T.coe_sem_fracQ m h1, eAi i k hi hk, eBi i k hi hk]
  -- range sums as `Fin` sums
  have hfin : ∀ (g : ℕ → L), ∑ k ∈ Finset.range n, g k = ∑ k : Fin n, g k := fun g ↦
    (Fin.sum_univ_eq_sum_range g n).symm
  -- the product checks
  have hok : prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true ∧
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true := by
    rw [hN]
    refine ⟨T.prodIdC_of_sem m h1 n _ _ fun i hi j hj ↦ ?_, T.prodIdC_of_sem m h1 n _ _ fun i hi j hj ↦ ?_⟩
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Ti.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2, sTi k k.2 j hj], hTTi ⟨i, hi⟩ ⟨j, hj⟩]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Fin.ext_iff]
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Ti.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Tc.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sTi i hi k k.2, sT k k.2 j hj], hTiT ⟨i, hi⟩ ⟨j, hj⟩]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Fin.ext_iff]
  -- the derivation matrix
  set bF : T.F (m + 1) := T.phi m (Polynomial.C b) with hbF
  set S0F : (T.F m)[X] := S0.map (algebraMap ℚ (T.F m)) with hS0F
  set Mval : ℕ → ℕ → T.F (m + 1) := fun i j ↦
    bF * T.tau m * T.phi m ((Pm' i j).map (algebraMap ℚ (T.F m))) / T.phi m S0F with hMvaldef
  have hbFL : (bF : L) = (b : L) := by rw [hbF, coe_phi, aeval_C]; rfl
  have hS0FL : ((T.phi m S0F : T.F (m + 1)) : L) = aeval t S0 := by
    rw [hS0F, coe_phi, aeval_map_algebraMap]
  have htauL : ((T.tau m : T.F (m + 1)) : L) = t := by
    show ((T.phi m X : T.F (m + 1)) : L) = t
    rw [coe_phi, aeval_X]
  have hMvalL : ∀ i j (hi : i < n) (hj : j < n), (Mval i j : L) =
      eL * aeval t (Pm ⟨i, hi⟩ ⟨j, hj⟩) / aeval t S0 := fun i j hi hj ↦ by
    rw [hMvaldef]
    push_cast
    rw [hbFL, hS0FL, htauL, coe_phi, aeval_map_algebraMap, ePm i j hi hj, heL]
  -- `w = T θ`
  have hwL : ∀ i (hi : i < n), ∑ k ∈ Finset.range n,
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
      ∑ k : Fin n, aeval t (A ⟨i, hi⟩ k) / aeval t (B ⟨i, hi⟩ k) * θ ^ (k : ℕ) := fun i hi ↦ by
    rw [hfin]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2]
  have hMval : ∀ i < P.length - 1, (∑ k ∈ Finset.range (P.length - 1),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range (P.length - 1), (Mval i j : L) *
        ∑ k ∈ Finset.range (P.length - 1), ((M1.sem ((Tc.getD j []).getD k
          (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k := by
    rw [hN]
    intro i hi
    rw [hwL i hi, ← Fin.sum_univ_eq_sum_range (fun j ↦ (Mval i j : L) * ∑ k ∈ Finset.range n,
      ((M1.sem ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k) n]
    have hR : ∑ j : Fin n, (Mval i j : L) * ∑ k ∈ Finset.range n,
        ((M1.sem ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
        ∑ j : Fin n, eL * aeval t (Pm ⟨i, hi⟩ j) / aeval t S0 *
          ∑ k : Fin n, aeval t (A j k) / aeval t (B j k) * θ ^ (k : ℕ) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [hwL j j.2, hMvalL i j hi j.2]
    rw [hR]
    have hd := hder ⟨i, hi⟩
    rw [← mul_div_cancel_right₀ ((∑ k : Fin n, aeval t (A ⟨i, hi⟩ k) / aeval t (B ⟨i, hi⟩ k) *
      θ ^ (k : ℕ))′) hS0t, hd, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hτ : T.tau m ≠ 0 := T.tau_ne_zero m htr
  have hφS0 : T.phi m S0F ≠ 0 := fun h0 ↦ hS0t (by rw [← hS0FL, h0]; rfl)
  set N0 := F0.natDegree.factorial with hN0def
  have hN0pos : 0 < N0 := Nat.factorial_pos _
  have hsepF : ∀ S : ℚ[X], Squarefree S → Squarefree (S.map (algebraMap ℚ (T.F m))) := fun S hS ↦
    ((PerfectField.separable_iff_squarefree.mpr hS).map (f := algebraMap ℚ (T.F m))).squarefree
  -- the data at `t = 0`
  obtain ⟨lam0, hsq', hP0⟩ : ∃ lam0 : ℕ → ℕ → ℚ,
      (∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
        S.coeff 0 ≠ 0 ∧ A.coeff 0 = b * (lam0 j i : T.F m) * S.coeff 0 ∧
        Mval i j = T.phi m A / T.phi m S) ∧
      aeval (Matrix.of fun i j : Fin (P.length - 1) ↦ lam0 i j)
        (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0 := by
    rw [hN]
    by_cases hX : X ∣ S0
    · obtain ⟨S1, hS1⟩ := hX
      have hs : S1.eval 0 ≠ 0 := by
        intro h0
        have : X * X ∣ S0 := by
          rw [hS1]; exact mul_dvd_mul_left X (X_dvd_iff.mpr (by rw [coeff_zero_eq_eval_zero, h0]))
        exact not_isUnit_X (hsq X this)
      refine ⟨fun i j ↦ if h : i < n ∧ j < n then (Pm ⟨j, h.2⟩ ⟨i, h.1⟩).eval 0 / S1.eval 0 else 0,
        fun i hi j hj ↦ ?_, ?_⟩
      · refine ⟨Polynomial.C b * (Pm' i j).map (algebraMap ℚ (T.F m)),
          S1.map (algebraMap ℚ (T.F m)), hsepF S1 (hS1 ▸ hsq).of_mul_right, ?_, ?_, ?_⟩
        · rw [coeff_map, coeff_zero_eq_eval_zero]
          exact (_root_.map_ne_zero _).mpr hs
        · rw [coeff_C_mul, coeff_map, coeff_map, ePm i j hi hj]
          simp only [hj, hi, and_self, ↓reduceDIte, coeff_zero_eq_eval_zero, eq_ratCast]
          have hs' : ((S1.eval 0 : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hs
          push_cast
          field_simp
        · have hS0F' : S0F = X * S1.map (algebraMap ℚ (T.F m)) := by
            rw [hS0F, hS1, Polynomial.map_mul, Polynomial.map_X]
          have hφS1 : T.phi m (S1.map (algebraMap ℚ (T.F m))) ≠ 0 := by
            intro h0; apply hφS0; rw [hS0F', map_mul, h0, mul_zero]
          rw [hMvaldef]
          simp only
          rw [hS0F', map_mul, map_mul, show T.phi m X = T.tau m from rfl, hbF]
          field_simp
      · have := ann_lam0 (Matrix.of fun i j : Fin n ↦ (Pm i j).eval 0) (S1.eval 0) hs N0 (hz0 S1 hS1)
        convert this using 3
        ext i j
        simp
    · refine ⟨fun _ _ ↦ 0, fun i hi j hj ↦ ?_, ?_⟩
      · refine ⟨Polynomial.C b * X * (Pm' i j).map (algebraMap ℚ (T.F m)), S0F, hsepF S0 hsq, ?_,
          ?_, ?_⟩
        · rw [hS0F, coeff_map, coeff_zero_eq_eval_zero]
          exact (_root_.map_ne_zero _).mpr fun h0 ↦ hX (X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero]))
        · simp [mul_assoc]
        · rw [hMvaldef]
          simp only
          rw [map_mul, map_mul, show T.phi m X = T.tau m from rfl]
      · have h0 : (Matrix.of fun _ _ : Fin n ↦ ((0 : ℚ) : ℚ)) = 0 := by ext; simp
        have hev : (Lagrange.nodal (Finset.range N0) (annNodes N0)).eval 0 = 0 := by
          have := Lagrange.eval_nodal_at_node (s := Finset.range N0) (v := annNodes N0)
            (Finset.mem_range.mpr hN0pos)
          simpa [annNodes] using this
        rw [h0, show (0 : Matrix (Fin n) (Fin n) ℚ) = algebraMap ℚ _ 0 from (map_zero _).symm,
          aeval_algebraMap_apply, coe_aeval_eq_eval, hev, map_zero]
  -- the data at infinity
  obtain ⟨Bm, Bim, d, hBB, hBiB, hdiag⟩ := diag_lamInf (lamInf r Pm S0) N0 hinf
  set Cl := qlist n Bim with hCl
  set Cil := qlist n Bm with hCil
  set lamI : ℕ → ℕ → ℚ := fun i j ↦
    if h : i < n ∧ j < n then (if i = j then d ⟨i, h.1⟩ else 0) else 0 with hlamI
  have hqq : ∀ (X Y : Matrix (Fin n) (Fin n) ℚ), X * Y = 1 → ∀ i < P.length - 1, ∀ j < P.length - 1,
      ∑ k ∈ Finset.range (P.length - 1), qget (qlist n X) i k * qget (qlist n Y) k j =
        if i = j then 1 else 0 := by
    intro X Y hXY
    rw [hN]
    intro i hi j hj
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦ qget (qlist n X) i k * qget (qlist n Y) k j)]
    rw [Finset.sum_congr rfl fun k _ ↦ by rw [qget_qlist n X i k hi k.2, qget_qlist n Y k j k.2 hj]]
    have := congrFun (congrFun hXY ⟨i, hi⟩) ⟨j, hj⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]
    simp [Fin.ext_iff]
  have hC1 := hqq Bim Bm hBiB
  have hC2 := hqq Bm Bim hBB
  have htri : ∀ i < P.length - 1, ∀ j < P.length - 1, j < i → lamI i j = 0 := by
    intro i _ j _ hji
    simp only [hlamI]
    split_ifs with h h'
    · omega
    · rfl
    · rfl
  have hlim : ∀ k < P.length - 1, ∀ l < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree = (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * (lamI l k : T.F m) *
        B.leadingCoeff ∧
      ∑ i ∈ Finset.range (P.length - 1), ∑ j ∈ Finset.range (P.length - 1),
        (qget Cl k i : T.F (m + 1)) * (T.tau m ^ (r' j - r' i) * Mval i j -
          (if i = j then (r' i : T.F (m + 1)) *
            T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a))) else 0)) *
          (qget Cil j l : T.F (m + 1)) = T.phi m A / T.phi m B := by
    rw [hN]
    intro k hk l hl
    set R := Finset.univ.sup r with hR
    have hRi : ∀ i, r i ≤ R := fun i ↦ Finset.le_sup (Finset.mem_univ i)
    set Q : ℚ[X] := X ^ R * S0 with hQ
    have hQ0 : Q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS0
    have hQdeg : Q.natDegree = R + S0.natDegree := by
      rw [hQ, natDegree_mul (pow_ne_zero _ X_ne_zero) hS0, natDegree_X_pow]
    have hQlc : Q.leadingCoeff = S0.leadingCoeff := by
      rw [hQ, leadingCoeff_mul, leadingCoeff_X_pow, one_mul]
    set Aq : ℚ[X] := ∑ i : Fin n, ∑ j : Fin n, Polynomial.C (Bim ⟨k, hk⟩ i * Bm j ⟨l, hl⟩) *
      (X ^ (R - r i) * pqF r Pm S0 i j) with hAq
    have hqdeg : ∀ i, (qF r S0 i).natDegree = r i + S0.natDegree := fun i ↦ by
      rw [qF, natDegree_mul (pow_ne_zero _ X_ne_zero) hS0, natDegree_X_pow]
    have hqlc : ∀ i, (qF r S0 i).leadingCoeff = S0.leadingCoeff := fun i ↦ by
      rw [qF, leadingCoeff_mul, leadingCoeff_X_pow, one_mul]
    have hlc0 : S0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hS0
    have hterm : ∀ i j, (X ^ (R - r i) * pqF r Pm S0 i j).natDegree ≤ R + S0.natDegree := by
      intro i j
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_X_pow]
      have := hdeg i j
      have := hRi i
      have : (pqF r Pm S0 i j).natDegree ≤ r i + S0.natDegree := hdeg i j
      omega
    have hAqdeg : Aq.natDegree ≤ Q.natDegree := by
      rw [hQdeg]
      refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
      exact (natDegree_C_mul_le _ _).trans (hterm i j)
    have hAqc : Aq.coeff Q.natDegree = (lamI l k) * Q.leadingCoeff := by
      have e1 : ∀ i j, (X ^ (R - r i) * pqF r Pm S0 i j).coeff (R + S0.natDegree) =
          lamInf r Pm S0 i j * S0.leadingCoeff := by
        intro i j
        rw [coeff_X_pow_mul', if_pos (by have := hRi i; omega),
          show R + S0.natDegree - (R - r i) = (qF r S0 i).natDegree by rw [hqdeg]; have := hRi i; omega]
        simp only [lamInf, Matrix.of_apply, hqlc]
        field_simp
      rw [hQdeg, hQlc, hAq, finsetSum_coeff]
      simp only [finsetSum_coeff, coeff_C_mul, e1]
      have hd := congrFun (congrFun hdiag ⟨k, hk⟩) ⟨l, hl⟩
      simp only [Matrix.mul_apply, Matrix.diagonal_apply] at hd
      have e2 : ∑ i : Fin n, ∑ j : Fin n, Bim ⟨k, hk⟩ i * Bm j ⟨l, hl⟩ *
          (lamInf r Pm S0 i j * S0.leadingCoeff) =
          (∑ j : Fin n, (∑ i : Fin n, Bim ⟨k, hk⟩ i * lamInf r Pm S0 i j) * Bm j ⟨l, hl⟩) *
            S0.leadingCoeff := by
        rw [Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [e2, hd]
      simp only [hlamI, hk, hl, and_self, ↓reduceDIte]
      by_cases hkl : k = l
      · subst hkl; simp
      · have : (⟨k, hk⟩ : Fin n) ≠ ⟨l, hl⟩ := fun h ↦ hkl (Fin.mk.inj_iff.mp h)
        simp [this, Ne.symm hkl]
    have hrat : ∀ q : ℚ, T.phi m (Polynomial.C (algebraMap ℚ (T.F m) q)) = (q : T.F (m + 1)) :=
      fun q ↦ eq_ratCast ((T.phi m).comp (Polynomial.C.comp (algebraMap ℚ (T.F m)))) q
    have hinjQ := (algebraMap ℚ (T.F m)).injective
    refine ⟨Polynomial.C b * Aq.map (algebraMap ℚ (T.F m)), Q.map (algebraMap ℚ (T.F m)),
      (Polynomial.map_ne_zero_iff hinjQ).mpr hQ0, ?_, ?_, ?_⟩
    · rw [natDegree_map_eq_of_injective hinjQ]
      exact (natDegree_C_mul_le _ _).trans ((natDegree_map_le).trans hAqdeg)
    · rw [natDegree_map_eq_of_injective hinjQ, coeff_C_mul, coeff_map, hAqc,
        leadingCoeff_map_of_injective hinjQ, map_mul, eq_ratCast]
      ring
    · have hφQ : T.phi m (Q.map (algebraMap ℚ (T.F m))) = T.tau m ^ R * T.phi m S0F := by
        rw [hQ, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_mul, map_pow]
      have hpt : ∀ i j : Fin n, T.tau m ^ ((r j : ℤ) - r i) * Mval i j -
          (if (i : ℕ) = j then ((r i : ℤ) : T.F (m + 1)) * bF else 0) =
          bF * T.phi m ((X ^ (R - r i) * pqF r Pm S0 i j).map (algebraMap ℚ (T.F m))) /
            T.phi m (Q.map (algebraMap ℚ (T.F m))) := by
        intro i j
        have hRpow : T.tau m ^ R = T.tau m ^ (R - r i) * T.tau m ^ r i :=
          (pow_sub_mul_pow _ (hRi i)).symm
        rw [hφQ, hRpow]
        simp only [hMvaldef, ePm i j i.2 j.2, pqF, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_sub, map_mul, map_pow, map_sub]
        rw [show T.phi m X = T.tau m from rfl, zpow_sub₀ hτ, zpow_natCast, zpow_natCast]
        by_cases hij : i = j
        · subst hij
          simp only [ite_true, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_mul, map_pow,
            Polynomial.map_C, eq_ratCast, show T.phi m X = T.tau m from rfl]
          have hc : T.phi m (Polynomial.C ((r i : ℚ) : T.F m)) = ((r i : ℕ) : T.F (m + 1)) := by
            rw [show ((r i : ℚ) : T.F m) = ((r i : ℕ) : T.F m) by push_cast; rfl,
              Polynomial.C_eq_natCast, map_natCast]
          simp only [hc]
          push_cast
          field_simp
          ring
        · have hij' : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
          simp only [hij, hij', ite_false, sub_zero, Polynomial.map_zero, map_zero]
          field_simp
          ring
      simp only [Finset.sum_range]
      rw [hAq, Polynomial.map_sum, Finset.mul_sum, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Polynomial.map_sum, Finset.mul_sum, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [qget_qlist n Bim k i hk i.2, qget_qlist n Bm j l j.2 hl, er i i.2, er j j.2]
      have hfin : ∀ x : Fin n, (⟨(x : ℕ), x.2⟩ : Fin n) = x := fun x ↦ rfl
      simp only [hfin]
      have hR' : T.phi m (Polynomial.C b * (Polynomial.C (Bim ⟨k, hk⟩ i * Bm j ⟨l, hl⟩) *
          (X ^ (R - r i) * pqF r Pm S0 i j)).map (algebraMap ℚ (T.F m))) =
          bF * ((Bim ⟨k, hk⟩ i * Bm j ⟨l, hl⟩ : ℚ) : T.F (m + 1)) *
            T.phi m ((X ^ (R - r i) * pqF r Pm S0 i j).map (algebraMap ℚ (T.F m))) := by
        rw [Polynomial.map_mul (algebraMap ℚ (T.F m)) (p := Polynomial.C (Bim ⟨k, hk⟩ i * Bm j ⟨l, hl⟩)),
          Polynomial.map_C, map_mul, map_mul, hrat, ← hbF,
          mul_assoc]
      rw [hpt i j, hR']
      push_cast
      ring
  refine ⟨A', B', Ai', Bi', r', N0, Cl, Cil, ?_⟩
  exact T.exactTREL_isSome h1 hm hk htr rdeD hb0 r' N0 Cl Cil P θ hP hPc (by omega)
    (by rw [hN]; exact hind) dθ hd Tc Ti hok f gs Mval hMval lam0 hsq' hN0pos hP0 hC1 hC2 lamI hlim htri


end MTower

end Curves.MT
