import RischTragerBronstein.Mixed.NKInfRDecide
import RischTragerBronstein.Computable.NCodes

/-!
# Units with algebraic coefficients

A unit `u = ∑ₖ αᵏ Aₖ(θ)` with `α` a root of a monic `μ ∈ ℤ[X]` and `Aₖ` codes over `ℚ`
(`NCodes`): `unitCN` checks `u v ≡ 1` (`v = ∑ αᵏ Bₖ`), `logDerChkN` checks `u′ = (∑ αᵏ gₖ) u`
(with `θ′ = dθ` certified as in `logDerChk`), `ncC` certifies that a coordinate `j ≥ 1` of
`∑ αᵏ gₖ` is invertible (so `u` is not in `Fₘ`). All checks use unnormalized code arithmetic and
hold for every root `α` of `μ` (`unitCN_sound`, `logDerChkN_sound`, `ncC_sound`).
-/

open Polynomial NCodes

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The integer `z` as a code. -/
def intC {α : Type} (O : COps α) (z : ℤ) : α :=
  if 0 ≤ z then O.natCast z.toNat else O.neg (O.natCast z.natAbs)

/-- Ring operations on `θ`-polynomials (unnormalized). -/
def θOps (m : ℕ) : ROps (GPoly (LC (m + 1))) :=
  ⟨GPoly.add (MO Fc ks (m + 1)), GPoly.mul (MO Fc ks (m + 1)), GPoly.neg (MO Fc ks (m + 1)), [],
    fun z ↦ [intC (MO Fc ks (m + 1)) z]⟩

/-- Ring operations on coefficients (unnormalized). -/
def scOps (m : ℕ) : ROps (LC (m + 1)) :=
  ⟨(MO Fc ks (m + 1)).add, (MO Fc ks (m + 1)).mul, (MO Fc ks (m + 1)).neg, (MO Fc ks (m + 1)).zero,
    intC (MO Fc ks (m + 1))⟩

/-- **`u v ≡ 1`** for `u = ∑ αᵏ Aₖ`, `v = ∑ αᵏ Bₖ` modulo `μ(α)` and `P`. -/
def unitCN (m : ℕ) (Pp : List (GPoly (LC m))) (μ : List ℤ) (As Bs : List (List (GPoly (LC m)))) :
    Bool :=
  let R := θOps Fc ks m
  let c := nRed R μ (nConv R (As.map (nkFl Fc ks m)) (Bs.map (nkFl Fc ks m)))
  zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1)) (c.getD 0 []) [(MO Fc ks (m + 1)).one]) &&
  (List.range μ.length).all fun s ↦ s == 0 || zeroModC Fc ks m Pp (c.getD s [])

/-- The derivative code of `A(θ)` given `θ′ = dθ`. -/
def dCode (m : ℕ) (dθ : GPoly (LC (m + 1))) (u : GPoly (LC (m + 1))) : GPoly (LC (m + 1)) :=
  GPoly.add (MO Fc ks (m + 1)) (GPoly.mapD (MO Fc ks (m + 1)) u)
    (GPoly.mul (MO Fc ks (m + 1)) dθ (GPoly.derivX (MO Fc ks (m + 1)) u))

/-- **The logarithmic derivative certificate** `u′ = (∑ αᵏ gₖ) u` (with `θ′ = dθ` certified by
`P_θ dθ + Pᐞ ≡ 0`, `wθ P_θ ≡ 1`). -/
def logDerChkN (m : ℕ) (Pp : List (GPoly (LC m))) (μ : List ℤ) (As : List (List (GPoly (LC m))))
    (gs : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let R := θOps Fc ks m
  let a := As.map (nkFl Fc ks m)
  let c := nRed R μ (nAdd R (a.map (dCode Fc ks m dθ)) (nNeg R (nConv R gs a)))
  zeroModC Fc ks m Pp (GPoly.add O1 (GPoly.mul O1 dθ (GPoly.derivX O1 P)) (GPoly.mapD O1 P)) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 wθ (GPoly.derivX O1 P)) [O1.one]) &&
  (List.range μ.length).all fun s ↦ zeroModC Fc ks m Pp (c.getD s [])

/-- **Non-constancy certificate**: the coordinate `j ≥ 1` of `∑ αᵏ gₖ` has inverse `∑ αˡ hₗ`. -/
def ncC (m : ℕ) (μ : List ℤ) (gs : List (GPoly (LC (m + 1)))) (j : ℕ) (hinv : List (LC (m + 1))) :
    Bool :=
  let S := scOps Fc ks m
  let O1 := MO Fc ks (m + 1)
  let c := nRed S μ (nConv S (gs.map fun g ↦ g.getD j (MOr Fc ks (m + 1)).zero) hinv)
  decide (1 ≤ j) && O1.isZero (O1.add (c.getD 0 O1.zero) (O1.neg O1.one)) &&
  (List.range μ.length).all fun s ↦ s == 0 || O1.isZero (c.getD s O1.zero)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma sem_intC {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)
    (z : ℤ) : M.sem (intC O z) = z := by
  unfold intC
  split_ifs with h
  · rw [M.sem_natCast]
    conv_rhs => rw [← Int.toNat_of_nonneg h]
    rw [Int.cast_natCast]
  · rw [M.sem_neg, M.sem_natCast]
    have e : (z.natAbs : ℤ) = -z := by omega
    rw [show ((z.natAbs : ℕ) : K) = ((z.natAbs : ℤ) : K) from (Int.cast_natCast _).symm, e,
      Int.cast_neg, neg_neg]

lemma evθ_RSem (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) : RSem (θOps Fc ks m) (T.evθ m h1 θ) where
  add a b := by simp only [θOps]; rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_add, map_add]
  mul a b := by simp only [θOps]; rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_mul, map_mul]
  neg a := by simp only [θOps]; rw [evθ_MP, evθ_MP, GPoly.toPoly_neg, map_neg]
  zero := by simp only [θOps]; rw [evθ_MP]; simp [GPoly.toPoly_nil]
  ofInt z := by
    simp only [θOps]
    rw [evθ_MP]
    simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, aeval_C, sem_intC]
    simp

lemma sc_RSem (m : ℕ) (h1 : T.Tr (m + 1)) :
    RSem (scOps Fc ks m) (fun a ↦ (((T.MP (m + 1) h1).sem a : T.F (m + 1)) : L)) where
  add a b := by simp only [scOps]; rw [(T.MP (m + 1) h1).sem_add]; push_cast; rfl
  mul a b := by simp only [scOps]; rw [(T.MP (m + 1) h1).sem_mul]; push_cast; rfl
  neg a := by simp only [scOps]; rw [(T.MP (m + 1) h1).sem_neg]; push_cast; rfl
  zero := by simp only [scOps]; rw [(T.MP (m + 1) h1).sem_zero]; rfl
  ofInt z := by simp only [scOps]; rw [sem_intC]; push_cast; rfl

/-- The value of an `N`-code of `θ`-polynomials at `α`. -/
noncomputable def nθ (m : ℕ) (h1 : T.Tr (m + 1)) (θ α : L) (c : List (GPoly (LC (m + 1)))) : L :=
  nVal (T.evθ m h1 θ) α c

lemma nVal_eq_zero_of (m : ℕ) (h1 : T.Tr (m + 1)) (θ α : L) (c : List (GPoly (LC (m + 1))))
    (N : ℕ) (hN : c.length ≤ N) (h : ∀ s < N, T.evθ m h1 θ (c.getD s []) = 0) :
    nVal (T.evθ m h1 θ) α c = 0 := by
  rw [nVal_eq_sum (T.evθ_RSem m h1 θ) α c N hN]
  exact Finset.sum_eq_zero fun s hs ↦ by
    change α ^ s * T.evθ m h1 θ (c.getD s []) = 0
    rw [h s (Finset.mem_range.mp hs), mul_zero]

/-- **Soundness of `unitCN`**: `u v = 1` at every root `α` of `μ`. -/
lemma unitCN_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (μ : List ℤ) (hd : 0 < μ.length) (α : L)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : L) * α ^ i = 0)
    (As Bs : List (List (GPoly (LC m)))) (h : unitCN Fc ks m Pp μ As Bs = true) :
    nVal (T.evθ m h1 θ) α (As.map (nkFl Fc ks m)) * nVal (T.evθ m h1 θ) α (Bs.map (nkFl Fc ks m)) =
      1 := by
  have hS := T.evθ_RSem m h1 θ
  unfold unitCN at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h0, hs⟩ := h
  set c := nRed (θOps Fc ks m) μ (nConv (θOps Fc ks m) (As.map (nkFl Fc ks m))
    (Bs.map (nkFl Fc ks m))) with hc
  rw [← nVal_nConv hS, ← nVal_nRed hS α μ hd hμ, ← hc,
    nVal_eq_sum hS α c μ.length (length_nRed _ μ hd _)]
  rw [Finset.sum_eq_single 0 (fun s hsr hs0 ↦ by
      have := T.zeroModC_sound m h1 θ Pp _ hP ((hs s (Finset.mem_range.mp hsr)).resolve_left hs0)
      change α ^ s * T.evθ m h1 θ (c.getD s []) = 0
      rw [this, mul_zero]) (fun h ↦ absurd (Finset.mem_range.mpr hd) h)]
  have := T.zeroModC_sound m h1 θ Pp _ hP h0
  rw [evθ_MP, GPoly.toPoly_sub, map_sub, ← evθ_MP, ← evθ_MP, T.evθ_one_MO m h1 θ, sub_eq_zero]
    at this
  change α ^ 0 * T.evθ m h1 θ (c.getD 0 []) = 1
  rw [pow_zero, one_mul, this]

/-- The value of `A(θ)` differentiates to the value of `dCode`. -/
lemma evθ_dCode (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (dθ : GPoly (LC (m + 1)))
    (hθ' : θ′ = T.evθ m h1 θ dθ) (u : GPoly (LC (m + 1))) :
    T.evθ m h1 θ (dCode Fc ks m dθ u) = (T.evθ m h1 θ u)′ := by
  rw [T.deriv_evθ_MO m h1 θ u, dCode, evθ_MP, GPoly.toPoly_add, GPoly.toPoly_mul, map_add, map_mul,
    ← evθ_MP, ← evθ_MP, ← evθ_MP, hθ']
  ring

lemma nVal_deriv (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (α : L) (hα : α′ = 0)
    (dθ : GPoly (LC (m + 1))) (hθ' : θ′ = T.evθ m h1 θ dθ) (a : List (GPoly (LC (m + 1)))) :
    nVal (T.evθ m h1 θ) α (a.map (dCode Fc ks m dθ)) = (nVal (T.evθ m h1 θ) α a)′ := by
  induction a with
  | nil => simp [nVal]
  | cons x a ih =>
    simp only [List.map_cons, nVal, ih, T.evθ_dCode m h1 θ dθ hθ' x, map_add, Derivation.leibniz,
      hα, smul_eq_mul, mul_zero, add_zero]

/-- **Soundness of `logDerChkN`**: `u′ = (∑ αᵏ gₖ) u` at every constant root `α` of `μ`. -/
lemma logDerChkN_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (μ : List ℤ) (hd : 0 < μ.length) (α : L)
    (hα : α′ = 0)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : L) * α ^ i = 0)
    (As : List (List (GPoly (LC m)))) (gs : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1)))
    (h : logDerChkN Fc ks m Pp μ As gs dθ wθ = true) :
    (nVal (T.evθ m h1 θ) α (As.map (nkFl Fc ks m)))′ =
      nVal (T.evθ m h1 θ) α gs * nVal (T.evθ m h1 θ) α (As.map (nkFl Fc ks m)) := by
  have hS := T.evθ_RSem m h1 θ
  unfold logDerChkN at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hd', hw'⟩, hs⟩ := h
  have hθ' := T.deriv_θ_of_chk m h1 θ Pp dθ wθ hP hd' hw'
  set a := As.map (nkFl Fc ks m) with ha
  have h0 := T.nVal_eq_zero_of m h1 θ α _ μ.length (length_nRed _ μ hd _)
    (fun s hs' ↦ T.zeroModC_sound m h1 θ Pp _ hP (hs s hs'))
  rw [nVal_nRed hS α μ hd hμ, nVal_nAdd hS, nVal_nNeg hS, nVal_nConv hS,
    T.nVal_deriv m h1 θ α hα dθ hθ'] at h0
  linear_combination h0

/-- **Soundness of `ncC`**: the coordinate `j ≥ 1` of `∑ αᵏ gₖ` is invertible. -/
lemma ncC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (μ : List ℤ) (hd : 0 < μ.length) (α : L)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : L) * α ^ i = 0)
    (gs : List (GPoly (LC (m + 1)))) (j : ℕ) (hinv : List (LC (m + 1)))
    (h : ncC Fc ks m μ gs j hinv = true) :
    1 ≤ j ∧ nVal (fun a ↦ (((T.MP (m + 1) h1).sem a : T.F (m + 1)) : L)) α
      (gs.map fun g ↦ g.getD j (MOr Fc ks (m + 1)).zero) *
      nVal (fun a ↦ (((T.MP (m + 1) h1).sem a : T.F (m + 1)) : L)) α hinv = 1 := by
  have hS := T.sc_RSem m h1
  unfold ncC at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hj, h0⟩, hs⟩ := h
  refine ⟨hj, ?_⟩
  set M := T.MP (m + 1) h1
  set c := nRed (scOps Fc ks m) μ (nConv (scOps Fc ks m)
    (gs.map fun g ↦ g.getD j (MOr Fc ks (m + 1)).zero) hinv) with hc
  rw [← nVal_nConv hS, ← nVal_nRed hS α μ hd hμ, ← hc,
    nVal_eq_sum hS α c μ.length (length_nRed _ μ hd _)]
  have hz : (scOps Fc ks m).zero = (MO Fc ks (m + 1)).zero := rfl
  rw [Finset.sum_eq_single 0 (fun s hs' hs0 ↦ by
      have := (M.isZero_iff _).mp ((hs s (Finset.mem_range.mp hs')).resolve_left hs0)
      rw [hz, this]; simp) (fun h ↦ absurd (Finset.mem_range.mpr hd) h)]
  have := (M.isZero_iff _).mp h0
  rw [M.sem_add, M.sem_neg, M.sem_one, add_neg_eq_zero] at this
  rw [hz, this]; simp

end MTower

end Curves.MT
