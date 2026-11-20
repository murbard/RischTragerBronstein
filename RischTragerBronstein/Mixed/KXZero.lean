import RischTragerBronstein.Mixed.KXData

/-!
# Square roots over an exponential level with poles: the place `t = 0`

* `kx_hns`: when `kxZ` finds nothing, `A(0)` is not a square in `Fₘ`;
* `kx_zero_twist`: when it finds `z` (`κ = z² A(0)`, `s = √κ` constant), the point
  `P₊ = (0, b₀)`, `b₀ = s/z`, is `Fₘ`-rational, and the twist `Â = (z/s)² A` is the image of the code
  `kxFK0` (with `Â(0) = 1`);
* `gammaQ_single`, `mK_single`: the one-point class `P₊`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential.SuperData

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

open Classical in
lemma gammaQ_single (b₀ : C) (Q : K × K) :
    gammaQ (fun _ : Fin 1 ↦ (0 : C)) (fun _ ↦ b₀) (fun _ ↦ 1) Q = gammaP (algebraMap C K b₀) Q := by
  simp [gammaQ, gammaP]

lemma mK_single : mK (fun _ : Fin 1 ↦ 1) (fun _ : Fin 1 ↦ (0 : Fin 1)) 0 = fun _ ↦ 1 := by
  funext q; simp [mK]

end Differential.SuperData

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma kxZ_some {m : ℕ} {A : GPoly (LC m)} {z : LC m} (h : kxZ Fc ks lv m A = some z) :
    ∃ q, (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = some (q, z) := by
  unfold kxZ at h
  obtain ⟨⟨q, z'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
  subst h2
  exact ⟨q, h1⟩

lemma kxZ_none {m : ℕ} {A : GPoly (LC m)} (h : kxZ Fc ks lv m A = none) :
    (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = none := by
  unfold kxZ at h
  exact Option.map_eq_none_iff.mp h

/-- **No square root of `A(0)` in `Fₘ`** when `kxZ` finds nothing. -/
theorem kx_hns (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (A : GPoly (LC m))
    (hTm : T.Tr m) (ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0)
    (hfind : kxZ Fc ks lv m A = none) (β₀ : AlgebraicClosure (T.F m))
    (hβ₀ : β₀ ^ 2 = algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero))) :
    ∀ c : T.F m, algebraMap (T.F m) (AlgebraicClosure (T.F m)) c ≠ β₀ := by
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set a0 := A.getD 0 (MO Fc ks m).zero with ha0def
  intro cc hcc
  have hc2 : cc ^ 2 = (T.MP m hTm).sem a0 := by
    apply (algebraMap (T.F m) (AlgebraicClosure (T.F m))).injective
    rw [map_pow, hcc, hβ₀]
  have hcc0 : cc ≠ 0 := fun h0 ↦ ha0v (by rw [← hc2, h0, zero_pow two_ne_zero])
  obtain ⟨r, hr, hr0⟩ := T.halfKer_complete (lv := lv) m hTm (halfFr Fc ks m a0)
    (MSm.rde _ (T.halfFr_ok m hTm a0)) cc⁻¹ (inv_ne_zero hcc0) (by
      apply Subtype.ext
      have hsh := T.sem_halfFr m hTm a0
      rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, hsh,
        ← T.sem_MP m hTm a0, ← hc2]
      have hccL : ((cc : T.F m) : L) ≠ 0 := fun h0 ↦ hcc0 (Subtype.ext h0)
      rw [IntermediateField.coe_inv, IntermediateField.coe_pow, logDeriv, Derivation.leibniz_inv,
        Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul, IntermediateField.coe_zero]
      field_simp
      ring)
  have := List.find?_eq_none.mp (kxZ_none hfind) r hr
  simp [hr0] at this

/-- **The twisted curve at `t = 0`**: `b₀ = s/z` with `b₀² = A(0)`, and `μ₀ = z/s` with
`μ₀² A` the image of `kxFK0`, `(μ₀² A)(0) = 1`. -/
theorem kx_zero_twist [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (z : LC m)
    (hfind : kxZ Fc ks lv m A = some z) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (s : L) (hs2 : s ^ 2 = (kxKap Fc ks m A z : L)) (hs' : s′ = 0) :
    ∃ (b₀ μ₀ : T.F m), b₀ ≠ 0 ∧ b₀ ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) ∧
      μ₀ ≠ 0 ∧ μ₀ * b₀ = 1 ∧ ((μ₀ : T.F m) : L) = T.ev m z / s ∧
      Polynomial.C (μ₀ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTr.of_succ) A) =
        (toPoly (kxFK0 Fc ks m A z)).map (T.psiF m hTr.of_succ) ∧
      (toPoly (kxFK0 Fc ks m A z)).natDegree = (kxFK0 Fc ks m A z).length - 1 ∧
      (toPoly (kxFK0 Fc ks m A z)).eval 0 = 1 ∧ Squarefree (toPoly (kxFK0 Fc ks m A z)) ∧
      Nat.Coprime 2 ((kxFK0 Fc ks m A z).length - 1) := by
  have hTm : T.Tr m := hTr.of_succ
  obtain ⟨q, hq⟩ := kxZ_some hfind
  obtain ⟨μ, hμ, hμv, hp0, hpf⟩ := T.ke_S_setup hmon hdeg m hn hc hTr A hsq hdegA hcopA ha0 q z
    hq θ hθ s hs2 hs'
  set S := T.keS m hTr A hsq hdegA θ hθ μ hμ with hS
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ μ hμ hcopA
  obtain ⟨hd, hf0, hsqK, hcop2⟩ := fK_facts (T.psiF m hTm) (kxFK0 Fc ks m A z)
    (CPoly.trim_trim _) S.p hpf hp0 S.hsq hcopS
  have hp : S.p = Polynomial.C (μ ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
  have hp0' : μ ^ 2 * (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) = 1 := by
    rw [← hp0, hp, eval_mul, eval_C, T.toPoly_eval_zero m hTm]
  refine ⟨μ⁻¹, μ, inv_ne_zero hμ, ?_, hμ, mul_inv_cancel₀ hμ, hμv, ?_, hd, hf0, hsqK, hcop2⟩
  · field_simp; rw [← hp0']
  · rw [one_pow, Polynomial.C_1, one_mul, ← hp]; exact hpf

end MTower

end Curves.MT
