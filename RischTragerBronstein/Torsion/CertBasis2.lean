import RischTragerBronstein.Torsion.CertBasis1

/-!
# Integral bases at special points: certificates (any characteristic)

At a special point `a` with a certified branch system (`certCheck`), the basis functions
`wⱼ = Bⱼ(x, y)/D(x)` are expanded along the approximate roots (`serTrunc`, from `phi_repr`):

* `basisCheckAt`: the expansions have no negative powers and the matrix of their first `N`
  coefficients (above each root) has a left inverse `Lm`;
* `basisCheckAt_spec`: then the `wⱼ` are regular along the certified system, hence along every
  system above `a` (`order_transfer`), and locally independent there.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors CPoly Sup

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- The order of `D(a + Tᴺ)`. -/
def muD (Dc : CPoly F) (a : F) (N : ℕ) : ℕ := ordC (compC Dc (shiftC a N))

/-- The first `prec` coefficients of `Tᵘ B(a + Tᴺ, y)/D(a + Tᴺ)`. -/
def serTrunc (B : BPoly F) (Dc : CPoly F) (a : F) (N prec : ℕ) (yt : CPoly F) : CPoly F :=
  divTrunc (bivEval B (shiftC a N) yt) ((compC Dc (shiftC a N)).drop (muD Dc a N)) prec

/-- The coefficient matrix: row `r = k N + t` (`t < N`, above root `k`), column `j`. -/
def matEntry (Bc : List (BPoly F)) (Dc : CPoly F) (a : F) (c : BranchCert F) (r j : ℕ) : F :=
  (serTrunc (Bc.getD j []) Dc a c.N c.prec (c.ys.getD (r / c.N) [])).getD (muD Dc a c.N + r % c.N) 0

/-- `Lm · M = I` for an `R × n` matrix `M`. -/
def leftInvCheck (Lm : List (List F)) (M : ℕ → ℕ → F) (R n : ℕ) : Bool :=
  (List.range n).all fun i ↦ (List.range n).all fun j ↦
    decide ((∑ r ∈ Finset.range R, (Lm.getD i []).getD r 0 * M r j) = if i = j then 1 else 0)

/-- **The basis check at a special point.** -/
def basisCheckAt (n : ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (a : F) (c : BranchCert F)
    (Lm : List (List F)) : Bool :=
  decide (muD Dc a c.N < (compC Dc (shiftC a c.N)).length) &&
    decide (muD Dc a c.N + c.N ≤ c.prec) &&
    ((List.range n).all fun j ↦ (List.range n).all fun k ↦ (List.range (muD Dc a c.N)).all fun t ↦
      decide ((serTrunc (Bc.getD j []) Dc a c.N c.prec (c.ys.getD k [])).getD t 0 = 0)) &&
    leftInvCheck Lm (matEntry Bc Dc a c) (n * c.N) n

end Defs

section Spec

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- **Left inverses give independence** over any field extension. -/
lemma eq_zero_of_leftInvCheck (ψ : F →+* K) {Lm : List (List F)} {M : ℕ → ℕ → F} {R n : ℕ}
    (h : leftInvCheck Lm M R n = true) (c : Fin n → K)
    (hc : ∀ r < R, ∑ j : Fin n, ψ (M r j) * c j = 0) : c = 0 := by
  simp only [leftInvCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  funext i
  have e : c i = ∑ j : Fin n, (if (i : ℕ) = j then 1 else 0) * c j := by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [if_neg (fun h ↦ hj (Fin.ext h.symm)), zero_mul])
      (fun h ↦ absurd (Finset.mem_univ i) h), if_pos rfl, one_mul]
  rw [e, Pi.zero_apply]
  calc ∑ j : Fin n, (if (i : ℕ) = j then (1 : K) else 0) * c j
      = ∑ j : Fin n, ψ (∑ r ∈ Finset.range R, (Lm.getD i []).getD r 0 * M r j) * c j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [h i i.2 j j.2]; split_ifs <;> simp
    _ = ∑ r ∈ Finset.range R, ψ ((Lm.getD i []).getD r 0) * ∑ j : Fin n, ψ (M r j) * c j := by
        simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    _ = 0 := Finset.sum_eq_zero fun r hr ↦ by rw [hc r (Finset.mem_range.mp hr), mul_zero]

namespace CurveData

variable (S : CurveData C L)

/-- The coefficients of `B(x, y)/D(x)` along a certified root. -/
lemma coeff_embG_cert (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (B : BPoly F) (Dc : CPoly F) (hD : toPoly Dc ≠ 0) (a : F) (N : ℕ) (hN : 0 < N)
    (hμ : muD Dc a N < (compC Dc (shiftC a N)).length) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub N (algebraMap C K (ψ₀ a)))).eval (ofPowerSeries ℤ K Y) = 0)
    (yt : CPoly F) (prec : ℕ)
    (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (s : ℤ) (hs : s + muD Dc a N < prec) :
    (S.embG (branchSub N (algebraMap C K (ψ₀ a))) (branchSub_injective N hN _) (ofPowerSeries ℤ K Y)
      hY (S.fnWQ ((toB B).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))).coeff s =
      if 0 ≤ s + muD Dc a N then
        algebraMap C K (ψ₀ ((serTrunc B Dc a N prec yt).getD (s + muD Dc a N).toNat 0)) else 0 := by
  have hD' : (toPoly Dc).map ψ₀ ≠ 0 := (Polynomial.map_ne_zero_iff ψ₀.injective).mpr hD
  obtain ⟨V, hV, hVt⟩ := S.phi_repr Fc ψ₀ hSF a N hN Y hY yt prec hy
    (S.fnWQ ((toB B).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)) B Dc
    (S.fnWQ_mul _ _ hD') hμ
  rw [hV, LaurentSeries.coeff_single_mul, sub_neg_eq_add, coeff_ofPS]
  unfold muD at hs ⊢
  by_cases h0 : 0 ≤ s + (ordC (compC Dc (shiftC a N)) : ℤ)
  · rw [if_pos h0, if_pos h0]
    have := (PowerSeries.X_pow_dvd_iff.mp hVt) (s + (ordC (compC Dc (shiftC a N)) : ℤ)).toNat
      (by omega)
    rw [map_sub, coeff_thetaT, sub_eq_zero] at this
    rw [this]; rfl
  · rw [if_neg h0, if_neg h0]

/-- **The basis at a special point from its certificate.** -/
theorem basisCheckAt_spec (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = S.F.natDegree)
    (Bc : List (BPoly F)) (Dc : CPoly F) (hD : toPoly Dc ≠ 0) (a : F) (c : BranchCert F)
    (hcert : certCheck Fc S.F.natDegree a c = true) (Lm : List (List F))
    (hchk : basisCheckAt S.F.natDegree Bc Dc a c Lm = true) :
    (∀ (j : Fin S.F.natDegree) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N (algebraMap C K (ψ₀ a))) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      0 ≤ (S.embG (branchSub N (algebraMap C K (ψ₀ a))) (branchSub_injective N (Nat.pos_of_ne_zero hN) _)
        r (S.root_of_mem hl hr)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))).order) ∧
    (∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
      ∃ hs : S.F.map (branchSub N (algebraMap C K (ψ₀ a))) = ∏ k, (X - Polynomial.C (r k)),
        S.LocIndep (fun j ↦ S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))
          N hN (algebraMap C K (ψ₀ a)) r hs) := by
  classical
  simp only [basisCheckAt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hchk
  obtain ⟨⟨⟨hμ, hprec⟩, hzero⟩, hinv⟩ := hchk
  have hN : 0 < c.N := by
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hcert
    exact hcert.1.1.1
  obtain ⟨y, hy, -, hsplit⟩ := certCheck_spec (K := K) Fc S.F.natDegree hmon hdeg a c hcert ψ₀
  rw [← hSF] at hsplit
  have hroot : ∀ k, (S.F.map (branchSub c.N (algebraMap C K (ψ₀ a)))).eval
      (ofPowerSeries ℤ K (y k)) = 0 := fun k ↦ by
    rw [hsplit, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  set μ := muD Dc a c.N with hμdef
  have hco := fun (j : Fin S.F.natDegree) (k : Fin S.F.natDegree) (s : ℤ) (hs : s + μ < c.prec) ↦
    S.coeff_embG_cert Fc ψ₀ hSF (Bc.getD j []) Dc hD a c.N hN hμ (y k) (hroot k)
      (c.ys.getD k []) c.prec (hy k) s hs
  -- regularity along the certified roots
  have hreg0 : ∀ j k : Fin S.F.natDegree, LowerBd (S.embG (branchSub c.N (algebraMap C K (ψ₀ a)))
      (branchSub_injective c.N hN _) (ofPowerSeries ℤ K (y k)) (hroot k)
      (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))) 0 := by
    intro j k s hs
    rw [hco j k s (by omega)]
    split_ifs with h0
    · rw [hzero j j.2 k k.2 _ (by omega), map_zero, map_zero]
    · rfl
  have hl0 : S.F.map (branchSub c.N (algebraMap C K (ψ₀ a))) =
      ((List.ofFn fun k ↦ ofPowerSeries ℤ K (y k)).map fun r ↦ X - Polynomial.C r).prod := by
    rw [hsplit, List.map_ofFn, List.prod_ofFn]; rfl
  refine ⟨fun j N' hN' l hl r hr ↦ ?_, c.N, hN, fun k ↦ ofPowerSeries ℤ K (y k), hsplit, ?_⟩
  · obtain ⟨r0, hr0, htr⟩ := S.order_transfer _ c.N N' hN (Nat.pos_of_ne_zero hN') _ l hl0 hl r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr0
    have h1 := htr (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))
    have h2 := order_nonneg_of_lowerBd' _ (hreg0 j k)
    have hNc : (0 : ℤ) < c.N := by exact_mod_cast hN
    have : (0 : ℤ) ≤ c.N * (S.embG (branchSub N' (algebraMap C K (ψ₀ a)))
        (branchSub_injective N' (Nat.pos_of_ne_zero hN') _) r (S.root_of_mem hl hr)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))).order := by
      rw [h1]; exact mul_nonneg (by positivity) h2
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact this) hNc
  · intro cc hcc
    refine eq_zero_of_leftInvCheck ((algebraMap C K).comp ψ₀) hinv cc fun r hr ↦ ?_
    have hk : r / c.N < S.F.natDegree := (Nat.div_lt_iff_lt_mul hN).mpr hr
    have ht : r % c.N < c.N := Nat.mod_lt _ hN
    have h := hcc ⟨r / c.N, hk⟩ ((r % c.N : ℕ) : ℤ) (by exact_mod_cast ht)
    rw [HahnSeries.coeff_sum] at h
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hco j ⟨r / c.N, hk⟩ _ (by push_cast; omega), if_pos (by positivity), mul_comm]
    congr 2
    simp only [matEntry, RingHom.comp_apply]
    rw [show ((r % c.N : ℕ) : ℤ) + (muD Dc a c.N : ℤ) = ((muD Dc a c.N + r % c.N : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]

end CurveData

end Spec

end Curves
