import RischTragerBronstein.Mixed.KQDecides
import RischTragerBronstein.Mixed.KEWit

/-!
# Square roots over a logarithm with poles: the antiderivative

`kqDecideCW` mirrors `kqDecideC` (`kqDecideCW_isSome`); with a `true` answer it returns the
solution `r` of the parametric Risch equation and the torsion witness `W₀ + W₁ θ̂` (`θ̂ = √κ θ`,
`θ̂² = Â = κ A`). The antiderivative (`kqDecideCW_valid`): with `N = W₀² − W₁² Â`, `a = y/q₀`,
`C = −(q₁/q₀)/√κ`,

  `∫ f = a θ + C log(W₀ + W₁ θ̂) − (C/2) log N`  (`N ≠ 0`),   `∫ f = a θ`  (`N = 0`),

in any extension with a constant `√κ`.
-/

open Polynomial CPoly Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- **The antiderivative data of `kqDecide`.** -/
structure KQW (m : ℕ) where
  y : LC (m + 1)
  q0 : ℚ
  q1 : ℚ
  W0 : GPoly (LC m)
  W1 : GPoly (LC m)

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- **`kqDecideC` with the antiderivative.** -/
def kqDecideCW (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) :
    Option (Option (KQW m)) :=
  let O := MO Fc ks m
  let rhs : LC (m + 1) := (B, GPoly.mul O (prodLinG Fc ks m cs) (powG O A l))
  let frA := kpFr Fc ks m 1 2 A
  if cs.length = 0 then none
  else if !kqOK Fc ks m A B l cs then none
  else if !kqConst Fc ks m η A B l cs then some none
  else if !kqClass Fc ks m η A B l cs then none
  else
    let fK := kqFK Fc ks m η A B l cs
    match torsOracleC (redAtKF Fc m rs) (cpf fK) ps bound fK 2
      (gammaL (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) 1) with
    | none => none
    | some none => some none
    | some (some N) =>
      match witW fK 2 (fK.length - 1) (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs)
          (kqMq Fc ks m η A B l cs) N with
      | none => none
      | some Wb =>
        let W0 := (Wb.getD 0 []).map (unTr Fc m)
        let W1 := (Wb.getD 1 []).map (unTr Fc m)
        some (((prdeC Fc ks lv (m + 1) frA [rhs, normC Fc (m + 1)
          (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 O.one)]).find?
          fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map fun r ↦ ⟨r.2, r.1.getD 0 0, r.1.getD 1 0, W0, W1⟩)

/-- **`kqDecideCW` answers exactly as `kqDecideC`.** -/
theorem kqDecideCW_isSome (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) :
    (kqDecideCW Fc ks lv m η A B l cs ps bound rs cpf).map Option.isSome =
      kqDecideC Fc ks lv m η A B l cs ps bound rs cpf := by
  unfold kqDecideCW kqDecideC
  dsimp only
  split_ifs
  · rfl
  · rfl
  · rfl
  · rfl
  · split
    · rename_i heq; rw [heq]; rfl
    · rename_i heq; rw [heq]; rfl
    · rename_i N heq
      rw [heq]
      dsimp only
      split
      · rename_i heq3; rw [heq3]; rfl
      · rename_i Wb heq3
        rw [heq3]
        simp only [Option.map_some, Option.isSome_map]
        congr 1
        rw [Bool.eq_iff_iff, List.find?_isSome, List.any_eq_true]

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **A valid KQ antiderivative** (`κ = kqK … 0`, `Â = κ A`). -/
def KQW.Valid (m : ℕ) (η : LC m) (A B : GPoly (LC m))
    (l : ℕ) (cs : List (LC m)) (θ : L) (w : KQW m) : Prop :=
  let κ := kqK Fc ks m η A B l cs 0
  let f := T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
    (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ
  let a := T.ev (m + 1) w.y / (w.q0 : L)
  let N := T.evP m w.W0 ^ 2 - T.evP m w.W1 ^ 2 * T.evP m (kqAhat Fc ks m η A B l cs)
  κ ≠ 0 ∧ (N = 0 → f = (a * θ)′) ∧
  (N ≠ 0 → ∀ (E : Type u) [Field E] [CharZero E] [Differential E] [Algebra L E]
    [DifferentialAlgebra L E] (s : E), s ^ 2 = κ → s′ = 0 →
    let ψ := algebraMap L E
    let Y := s * ψ θ
    let C := ψ (((-w.q1 / w.q0 : ℚ)) : L) / s
    ψ f = (ψ (a * θ))′ + C * logDeriv (ψ (T.evP m w.W0) + ψ (T.evP m w.W1) * Y) +
      (-(C / 2)) * logDeriv (ψ N))

set_option maxHeartbeats 4000000 in
/-- **The KQ antiderivative from a solution of the parametric equation.** -/
theorem kq_param_antiderivative (m : ℕ)
    (hTr : T.Tr (m + 1)) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (η : LC m) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0) (hκ : kqK Fc ks m η A B l cs 0 ≠ 0)
    (W0 W1 : GPoly (LC m))
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (r : List ℚ × LC (m + 1))
    (hr : r ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      [((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) : LC (m + 1)),
        normC Fc (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 (MO Fc ks m).one)])
    (hq0 : r.1.getD 0 0 ≠ 0) :
    KQW.Valid T m η A B l cs θ ⟨r.2, r.1.getD 0 0, r.1.getD 1 0, W0, W1⟩ := by
  refine ⟨hκ, ?_⟩
  dsimp only
  set col := normC Fc (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 (MO Fc ks m).one)
    with hcol
  set rhs : LC (m + 1) := (B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
    (powG (MO Fc ks m) A l)) with hrhs
  have hs := hspec.sound [rhs, col] r hr
  have hsQ : sQ (T.MP (m + 1) hTr) r.1 [rhs, col] =
      ((r.1.getD 0 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem rhs +
        ((r.1.getD 1 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem col := by
    simp [sQ, Finset.sum_range_succ]
  rw [hsQ] at hs
  have hsL := congrArg Subtype.val hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv] at hsL
  rw [T.sem_kpFr m hTr] at hsL
  simp only [T.sem_MP (m + 1) hTr] at hsL
  rw [hcol, T.ev_normC (m + 1) hTr] at hsL
  set av : L := T.ev (m + 1) r.2 with hav
  set q0 : ℚ := r.1.getD 0 0 with hq0d
  set q1 : ℚ := r.1.getD 1 0 with hq1d
  have hq0L : (q0 : L) ≠ 0 := by exact_mod_cast hq0
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (av / q0) 1
  simp only [pow_one] at h1
  have hf : T.ev (m + 1) rhs * θ = ((av / q0) * θ)′ + ((-q1 / q0 : ℚ) : L) *
      (T.ev (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 (MO Fc ks m).one) * θ) := by
    rw [h1]
    have hq0d' : ((q0 : L))′ = 0 := Tower.NestP.deriv_ratCastK (K := L) q0
    have hd : (av / (q0 : L))′ = av′ / q0 := by
      rw [div_eq_mul_inv av, Derivation.leibniz, Derivation.leibniz_inv, hq0d', div_eq_mul_inv]
      simp only [smul_eq_mul, mul_zero, zero_add, neg_zero]
      ring
    rw [hd]
    generalize T.ev (m + 1) rhs = R at hsL ⊢
    push_cast at hsL ⊢
    field_simp
    linear_combination (-2 * θ : L) * hsL
  rw [T.ev_logCol m hTr, T.ev_one_code m hTr.of_succ, mul_one] at hf
  have hPvA : T.evP m (kqAhat Fc ks m η A B l cs) = (kqK Fc ks m η A B l cs 0 : L) * T.evP m A := by
    rw [kqAhat, T.evP_mapMul m hTr.of_succ, ← T.sem_MP m hTr.of_succ, T.sem_mcst]
    push_cast; ring
  set κ := kqK Fc ks m η A B l cs 0 with hκd
  set Pv := T.evP m (kqAhat Fc ks m η A B l cs) with hPvd
  set W0v := T.evP m W0 with hW0v
  set W1v := T.evP m W1 with hW1v
  refine ⟨fun hN ↦ ?_, fun hN E _ _ _ _ _ s hs2 hs' ↦ ?_⟩
  · rw [hf]
    have hN' : W0v * W0v - W1v * W1v * Pv = 0 := by linear_combination hN
    rw [hN', inv_zero, mul_zero, zero_mul, mul_zero, add_zero]
  · set ψ := algebraMap L E with hψ
    have hψd : ∀ w : L, (ψ w)′ = ψ w′ := fun w ↦ deriv_algebraMap w
    have hs0 : s ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow two_ne_zero] at hs2; exact hκ (by exact_mod_cast hs2.symm)
    have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
    set Y := s * ψ θ with hYdef
    have hY0 : Y ≠ 0 := mul_ne_zero hs0 ((map_ne_zero ψ).mpr hθ0)
    have hY2 : Y ^ 2 = ψ Pv := by
      rw [hYdef, mul_pow, hs2, ← map_pow, hθ, hPvA, map_mul, map_ratCast]
    have hNm : ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv ≠ 0 := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_sub]
      exact (map_ne_zero ψ).mpr hN
    have hcolY := colY_logDeriv Y (ψ W0v) (ψ W1v) (ψ Pv) hY2 hY0 hNm
    have hψN : ψ (W0v ^ 2 - W1v ^ 2 * Pv) = ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv := by
      simp only [map_sub, map_mul, map_pow]
    rw [hψN, hf, RingHom.map_add, ← hψd, add_assoc]
    congr 1
    have hθY : ψ θ = Y / s := by rw [hYdef]; field_simp
    have e1 : ψ ((1 / 2 : L)) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    have hexp : ψ (((-q1 / q0 : ℚ)) : L) * ψ ((W0v * (W1v′ + W1v * ((1 / 2 : L) * (Pv′ * Pv⁻¹))) -
        W0v′ * W1v) * (W0v * W0v - W1v * W1v * Pv)⁻¹) * ψ θ =
        ψ (((-q1 / q0 : ℚ)) : L) / s * ((ψ W0v * ((ψ W1v)′ + ψ W1v * ((1 / 2 : E) *
          ((ψ Pv)′ * (ψ Pv)⁻¹))) - (ψ W0v)′ * ψ W1v) / (ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv) * Y) := by
      rw [hθY]
      simp only [RingHom.map_mul, RingHom.map_sub, RingHom.map_add, map_inv₀, e1, hψd]
      rw [show ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv = ψ W0v * ψ W0v - ψ W1v * ψ W1v * ψ Pv by ring]
      field_simp
    rw [RingHom.map_mul, RingHom.map_mul, ← mul_assoc, hexp, hcolY]
    ring

/-- **Every antiderivative returned by `kqDecideCW` is valid.** -/
theorem kqDecideCW_valid (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hdegpos : 0 < degG (MO Fc ks m) A) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (w : KQW m)
    (hdec : kqDecideCW Fc ks lv m η A B l cs ps bound rs cpf = some (some w)) :
    KQW.Valid T m η A B l cs θ w := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  unfold kqDecideCW at hdec
  dsimp only at hdec
  split_ifs at hdec with hr0 hok hcst hcl
  all_goals try (simp at hdec; done)
  · have hok' : kqOK Fc ks m A B l cs = true := by
      revert hok; cases kqOK Fc ks m A B l cs <;> simp
    have hcst' : kqConst Fc ks m η A B l cs = true := by
      revert hcst; cases kqConst Fc ks m η A B l cs <;> simp
    have hκ0 := T.kqK_ne m MS.hyp hk A B l cs hok' hcst' 0 (Nat.pos_of_ne_zero hr0)
    split at hdec
    · exact absurd hdec (by simp)
    · exact absurd hdec (by simp)
    · split at hdec
      · exact absurd hdec (by simp)
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
        have hr0' := List.find?_some hr
        simp only [decide_eq_true_eq] at hr0'
        exact T.kq_param_antiderivative m hTr A B l cs η θ hθ hA0 hκ0 _ _ hspecA r
          (List.mem_of_find?_eq_some hr) hr0'

end MTower

end Curves.MT
