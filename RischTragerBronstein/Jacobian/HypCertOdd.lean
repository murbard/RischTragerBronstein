import RischTragerBronstein.Algebraic.EllCertValid
import RischTragerBronstein.Jacobian.TorsionDecideU

/-!
# Log certificates in any genus

`certCheck_ok_odd`: for `y² = p(x)` with `deg p = 2g + 1`, integrand `B/y + ∑ (zᵢ/D) βᵢ/((x − αᵢ) y)`
and any nonzero `A + B y` with pole order `≤ ∑ n|zᵢ|` vanishing on `∑ n |zᵢ| (αᵢ, sign zᵢ βᵢ)`,
the elliptic certificate check `certCheck` succeeds (generalising `EllAlgo.certCheck_ok_gen`
from cubics to any odd degree).
-/

open Polynomial EllAlgo

namespace Jac

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 1600000 in
theorem certCheck_ok_odd [DecidableEq K] (pC : CPoly K) {g : ℕ}
    (hpd : (CPoly.toPoly pC).natDegree = 2 * g + 1)
    (pts : List (K × K × ℤ))
    (hon : ∀ q ∈ pts, (CPoly.toPoly pC).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (AB : CPoly K × CPoly K)
    (hAB0 : CPoly.toPoly AB.1 ≠ 0 ∨ CPoly.toPoly AB.2 ≠ 0)
    (hpole : PoleLE g (CPoly.toPoly AB.1, CPoly.toPoly AB.2) ((ptsQ pts n).map fun q ↦ q.2.2).sum)
    (hvan : ∀ q ∈ ptsQ pts n,
      X ^ q.2.2 ∣ locVal pC (CPoly.toPoly AB.1) (CPoly.toPoly AB.2) q) (B : CPoly K) :
    certCheck pC AB (fracG B D pts) (1 / ((n : K) * D)) = true := by
  set p := CPoly.toPoly (pC) with hpdef
  set A := CPoly.toPoly AB.1 with hAdef
  set Bp := CPoly.toPoly AB.2 with hBdef
  have hAB : A ≠ 0 ∨ Bp ≠ 0 := hAB0
  set N := A ^ 2 - Bp ^ 2 * p with hNdef
  have hN0 : N ≠ 0 := by
    have := hnorm_ne_zero (f := p) (ψ := (A, Bp)) ⟨g, hpd⟩ (by
      intro h; simp only [Prod.mk.injEq] at h; tauto)
    simpa [hnorm] using this
  have hloc := hvan
  set M₀ := ((ptsQ pts n).map fun q ↦ q.2.2).sum with hM₀
  have hdeg : N.natDegree ≤ M₀ := by
    have h1 : (A ^ 2).natDegree ≤ M₀ := by
      rw [natDegree_pow]; exact hpole.1
    have h2 : (Bp ^ 2 * p).natDegree ≤ M₀ := by
      rcases hpole.2 with h0 | h0
      · simp only at h0; rw [h0]; simp
      · calc (Bp ^ 2 * p).natDegree ≤ (Bp ^ 2).natDegree + p.natDegree := natDegree_mul_le
          _ ≤ M₀ := by rw [natDegree_pow, hpd]; simp only at h0; omega
    exact (natDegree_sub_le _ _).trans (max_le h1 h2)
  -- per-point data
  set L := pts.length
  let α : Fin L → K := fun i ↦ pts[i].1
  let z : Fin L → ℤ := fun i ↦ pts[i].2.2
  let m : Fin L → ℕ := fun i ↦ n * (z i).natAbs
  let y : Fin L → K := fun i ↦ ((z i).sign : K) * pts[i].2.1
  have hqi : ∀ i : Fin L, (α i, y i, m i) ∈ ptsQ pts n := fun i ↦ by
    simp only [ptsQ, List.mem_map]
    exact ⟨pts[i], List.getElem_mem _, rfl⟩
  have hinj : Set.InjOn α (Finset.univ : Finset (Fin L)) := by
    intro i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
      (hj := by rw [List.length_map]; exact j.2)).mp
      (by simp only [List.getElem_map]; exact hij))
  have hres : ∀ i : Fin L, 1 ≤ m i → ∃ N₁ : K[X], N = (X - C (α i)) ^ m i * N₁ ∧
      (X - C (α i)) ^ m i ∣ (2 * p * (A * derivative Bp - derivative A * Bp) +
        A * Bp * derivative p) - C ((m i : K) * y i) * (X - C (α i)) ^ (m i - 1) * N₁ := by
    intro i hm
    have hz : z i ≠ 0 := by
      intro h0; simp only [m, h0, Int.natAbs_zero, mul_zero] at hm; omega
    have hβ := (hon _ (List.getElem_mem i.2)).2
    have hs : ((z i).sign : K) ^ 2 = 1 := by
      rcases lt_trichotomy (z i) 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
      · exact absurd h hz
      · rw [Int.sign_eq_one_of_pos h]; norm_num
    have hy0 : y i ≠ 0 := by
      simp only [y]
      refine mul_ne_zero (fun h0 ↦ ?_) hβ
      rw [h0] at hs; norm_num at hs
    have hpα : p.eval (α i) = y i ^ 2 := by
      have hc := (hon _ (List.getElem_mem i.2)).1
      simp only [y, α, z] at hs ⊢
      rw [mul_pow, hs, one_mul]
      exact hc
    obtain ⟨N₁, h1, h2⟩ := residue_at (pC) A Bp (α i) (y i) (m i) hm hy0 hpα
      (hloc _ (hqi i))
    exact ⟨N₁, h1, h2⟩
  have hdvdN : ∀ i ∈ (Finset.univ : Finset (Fin L)), (X - C (α i)) ^ m i ∣ N := by
    intro i _
    rcases Nat.eq_zero_or_pos (m i) with h0 | h0
    · rw [h0, pow_zero]; exact one_dvd _
    · obtain ⟨N₁, h1, -⟩ := hres i h0
      exact ⟨N₁, h1⟩
  have hM₀' : M₀ = ∑ i : Fin L, m i := by
    rw [hM₀, ptsQ, List.map_map, sum_map_eq_fin]
    rfl
  obtain ⟨lam, hlam, hNeq⟩ := norm_shape' Finset.univ α hinj m N hN0 hdvdN (hM₀' ▸ hdeg)
  -- the denominator of `G`
  have hGd : CPoly.toPoly (fracG B D pts).2 = ∏ i : Fin L, (X - C (α i)) := by
    rw [fracG_den, prod_map_eq_fin]
  have hGd0 : CPoly.toPoly (fracG B D pts).2 ≠ 0 := by
    rw [hGd]; exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _
  -- the global divisibility
  set cc : K := 1 / ((n : K) * D)
  set Mp := 2 * p * (A * derivative Bp - derivative A * Bp) + A * Bp * derivative p
  set Q := CPoly.toPoly (fracG B D pts).1 * N - CPoly.toPoly (fracG B D pts).2 * (C cc * Mp)
  have hcop : ((Finset.univ : Finset (Fin L)) : Set (Fin L)).Pairwise
      (Function.onFun IsCoprime fun i ↦ (X - C (α i)) ^ (m i + 1)) := by
    intro i hi j hj hij
    exact ((isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun h ↦ hij (hinj hi hj h)).isUnit)).pow
  have hpt : ∀ i ∈ (Finset.univ : Finset (Fin L)), (X - C (α i)) ^ (m i + 1) ∣ Q := by
    intro i _
    obtain ⟨Gq, H, hG1, hG2⟩ := fracG_local B D pts pts[i] (List.getElem_mem i.2)
    rcases Nat.eq_zero_or_pos (m i) with h0 | h0
    · have hz : z i = 0 := by
        simp only [m] at h0
        rcases Nat.mul_eq_zero.mp h0 with h | h
        · omega
        · exact Int.natAbs_eq_zero.mp h
      rw [h0, zero_add, pow_one]
      refine ⟨H * N - Gq * (C cc * Mp), ?_⟩
      simp only [Q, hG1, hG2]
      simp only [z] at hz
      rw [hz]; simp only [Int.cast_zero, zero_div, zero_mul, map_zero]
      ring
    · obtain ⟨N₁, h1, T, hT⟩ := hres i h0
      obtain ⟨k, hk⟩ : ∃ k, m i = k + 1 := ⟨m i - 1, by omega⟩
      rw [hk] at h1 hT ⊢
      rw [Nat.add_sub_cancel] at hT
      refine point_dvd _ _ N Mp Gq H N₁ T (α i) cc _ (y i) k hG1 hG2 h1 (by
        linear_combination hT) ?_
      rw [← hk]
      simp only [cc, m, y, z]
      have hDq : (D : K) ≠ 0 := by exact_mod_cast hD
      have hnq : (n : K) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hs : ((pts[i].2.2.sign : ℤ) : K) * (pts[i].2.2.natAbs : K) = (pts[i].2.2 : K) := by
        have h' := congrArg (fun t : ℤ ↦ (t : K)) (Int.sign_mul_natAbs pts[i].2.2)
        simp only [Int.cast_mul, Int.cast_natCast] at h'
        exact h'
      push_cast
      field_simp
      linear_combination pts[i].2.1 * hs
  have hprod := Finset.prod_dvd_of_coprime hcop hpt
  have hGN : CPoly.toPoly (fracG B D pts).2 * N =
      C lam * ∏ i : Fin L, (X - C (α i)) ^ (m i + 1) := by
    rw [hGd, hNeq]
    simp only [pow_succ, Finset.prod_mul_distrib]
    ring
  have hdvdQ : CPoly.toPoly (fracG B D pts).2 * N ∣ Q := by
    rw [hGN]
    exact (C_mul_dvd (by exact hlam)).mpr hprod
  -- the check
  unfold certCheck certR
  have hNpoly : CPoly.toPoly (certN (pC) AB) = N := by
    simp only [certN, CPoly.toPoly_sub, CPoly.toPoly_mul]; ring
  have hMpoly : CPoly.toPoly (certM (pC) AB) = Mp := by
    have h2 : CPoly.toPoly ([2] : CPoly K) = 2 := by
      rw [CPoly.toPoly_cons, CPoly.toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [certM, CPoly.toPoly_add, CPoly.toPoly_sub, CPoly.toPoly_mul, CPoly.toPoly_deriv, h2]
    ring
  have hex := divMod_exact (CPoly.sub (CPoly.mul (fracG B D pts).1
      (certN (pC) AB))
      (CPoly.mul (fracG B D pts).2 (CPoly.smul cc (certM (pC) AB))))
    (CPoly.mul (fracG B D pts).2 (certN (pC) AB))
    (by rw [CPoly.toPoly_mul, hNpoly]; exact mul_ne_zero hGd0 hN0)
    (by
      simp only [CPoly.toPoly_mul, CPoly.toPoly_sub, CPoly.toPoly_smul, hNpoly, hMpoly]
      exact hdvdQ)
  simp only [CPoly.toPoly_mul, CPoly.toPoly_sub, CPoly.toPoly_smul, hNpoly, hMpoly] at hex
  simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, CPoly.isZero_iff, hNpoly]
  refine ⟨⟨hN0, hGd0⟩, (CPoly.beq_iff _ _).mpr ?_⟩
  simp only [CPoly.toPoly_mul, CPoly.toPoly_add, CPoly.toPoly_smul, hNpoly, hMpoly]
  linear_combination hex


end Jac
