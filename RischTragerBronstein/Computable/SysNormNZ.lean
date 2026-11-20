import RischTragerBronstein.Computable.SysNormUnit
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# The indicial norm is not identically zero

If no irreducible factor of the monic `q` divides `dq`, then modulo each factor `p` the indicial
polynomial `det(A₀ − E dq I)` is `(−dq)ⁿ` times a characteristic polynomial, so it has finitely
many roots; the field being infinite, some `e` avoids them all, `det(A₀ − e dq I)` is then coprime
to `q`, and the norm at `e` is non-zero (`det_multMat_ne_zero`): **`indNorm' q dq A₀ ≠ 0`**
(`indNorm'_ne_zero`).
-/

open Polynomial

namespace Tower.Sys

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The indicial polynomial modulo an irreducible `p ∤ dq` is non-zero. -/
lemma indPoly_map_ne_zero (dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (p : K[X])
    (hp : Irreducible p) (hpd : ¬ p ∣ dq) :
    (indPoly dq A0).map (AdjoinRoot.mk p) ≠ 0 := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  set φ := AdjoinRoot.mk p
  have hd : φ dq ≠ 0 := fun h ↦ hpd (AdjoinRoot.mk_eq_zero.mp h)
  set B : Matrix (Fin n) (Fin n) (AdjoinRoot p) := Matrix.of fun i j ↦ (φ dq)⁻¹ * φ (A0 i j)
  have hM : (Matrix.of fun i j ↦ C (A0 i j) - if i = j then X * C dq else 0 :
      Matrix (Fin n) (Fin n) K[X][X]).map (mapRingHom φ) = (-C (φ dq)) • B.charmatrix := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.charmatrix_apply, B,
      coe_mapRingHom, smul_eq_mul]
    have hc : C (φ dq) * C (φ dq)⁻¹ = (1 : (AdjoinRoot p)[X]) := by
      rw [← C_mul, mul_inv_cancel₀ hd, C_1]
    split_ifs with hij
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_mul,
        Polynomial.map_X, C_mul]
      linear_combination (-1 : (AdjoinRoot p)[X]) * C (φ (A0 i i)) * hc
    · simp only [Matrix.diagonal_apply_ne _ hij, Polynomial.map_sub, Polynomial.map_C,
        Polynomial.map_zero, sub_zero, zero_sub, C_mul]
      linear_combination (-1 : (AdjoinRoot p)[X]) * C (φ (A0 i j)) * hc
  have e : (indPoly dq A0).map φ = (-C (φ dq)) ^ n * B.charpoly := by
    rw [indPoly, ← coe_mapRingHom, RingHom.map_det, RingHom.mapMatrix_apply, hM, Matrix.det_smul,
      Fintype.card_fin, Matrix.charpoly]
  rw [e]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (C_ne_zero.mpr hd))) (Matrix.charpoly_monic B).ne_zero

/-- **The indicial norm is not identically zero.** -/
theorem indNorm'_ne_zero (q dq : K[X]) (hq : q.Monic) (A0 : Matrix (Fin n) (Fin n) K[X])
    (hpd : ∀ p : K[X], Irreducible p → p ∣ q → ¬ p ∣ dq) : indNorm' q dq A0 ≠ 0 := by
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  -- the irreducible factors of `q`
  set fs := (UniqueFactorizationMonoid.normalizedFactors q).toFinset with hfs
  have hq0 : q ≠ 0 := hq.ne_zero
  -- the bad constants
  have hbad : ∀ p ∈ fs, Set.Finite {e : K | p ∣ (Matrix.of fun i j ↦
      A0 i j - if i = j then C e * dq else 0).det} := by
    intro p hp
    have hpi : Irreducible p :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
    have hpq : p ∣ q :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)
    haveI : Fact (Irreducible p) := ⟨hpi⟩
    have hne := indPoly_map_ne_zero dq A0 p hpi (hpd p hpi hpq)
    refine ((indPoly dq A0).map (AdjoinRoot.mk p)).roots.toFinset.finite_toSet.preimage
      (f := fun e : K ↦ AdjoinRoot.of p e) ?_ |>.subset ?_
    · intro a _ b _ h; exact (AdjoinRoot.of p).injective h
    · intro e he
      simp only [Set.mem_setOf_eq] at he
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
      rw [← indPoly_eval] at he
      have := AdjoinRoot.mk_eq_zero.mpr he
      rw [eval_map, ← AdjoinRoot.mk_C, eval₂_at_apply]
      exact this
  have hfin := Set.Finite.biUnion fs.finite_toSet hbad
  obtain ⟨e, he⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at he
  intro h0
  have hev := congrArg (eval e) h0
  rw [eval_zero, indNorm'_eval] at hev
  refine det_multMat_ne_zero q _ hq ?_ hev
  refine isCoprime_of_irreducible_dvd (fun h ↦ hq0 h.2) fun z hz hzx hzq ↦ ?_
  obtain ⟨p, hp, hzp⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hq0 hz hzq
  exact he p (Multiset.mem_toFinset.mpr hp) (hzp.symm.dvd.trans hzx)

end Tower.Sys
