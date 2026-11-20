import RischTragerBronstein.Mixed.KEFull
import RischTragerBronstein.Mixed.KPWit

/-!
# Square roots over an exponential: the antiderivative

`keDecideCW` mirrors `keDecideC` (`keDecideCW_isSome`) and returns, with a `true` answer, the
antiderivative of `f = B/(tᵏ Aˡ) θ` (`θ² = A`):

* `plain y`: `∫ f = y θ` (`ke_plain_antiderivative`);
* `param y q₀ q₁ z κ W₀ W₁`: with `θ̂ = z θ/√κ`, `θ̂² = Â` (`Â = (z²/κ) A`), `N = W₀² − W₁² Â`,
  `∫ f = (y/q₀) θ + C log(W₀ + W₁ θ̂) − (C/2) log N`, `C = −(q₁/q₀) √κ` — in any extension
  with a constant `√κ` (`ke_param_antiderivative`); when `N = 0`, `∫ f = (y/q₀) θ`.
-/

open Polynomial CPoly Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

/-- **The logarithmic column, explicitly**: for `Y² = P`, `Y ≠ 0`, `N = W₀² − W₁² P ≠ 0`,
`(W₀ (W₁′ + W₁ P′/(2P)) − W₀′ W₁)/N · Y = (W₀ + W₁ Y)′/(W₀ + W₁ Y) − ½ N′/N`. -/
theorem colY_logDeriv {F : Type*} [Field F] [Differential F] [CharZero F] (Y W0 W1 P : F)
    (hY2 : Y ^ 2 = P) (hY0 : Y ≠ 0) (hN : W0 ^ 2 - W1 ^ 2 * P ≠ 0) :
    (W0 * (W1′ + W1 * ((1 / 2 : F) * (P′ * P⁻¹))) - W0′ * W1) / (W0 ^ 2 - W1 ^ 2 * P) * Y =
      logDeriv (W0 + W1 * Y) - (1 / 2 : F) * logDeriv (W0 ^ 2 - W1 ^ 2 * P) := by
  subst hY2
  have hP0 : Y ^ 2 ≠ 0 := pow_ne_zero 2 hY0
  set r := (1 / 2 : F) * ((Y ^ 2)′ * (Y ^ 2)⁻¹) with hr
  have hYd : Y′ = r * Y := by
    rw [hr, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul]
    field_simp
    ring
  have hab := logDeriv_ab (y := Y) W0 W1 (Y ^ 2) r rfl hYd hN
  have hNd : logDeriv (W0 ^ 2 - W1 ^ 2 * Y ^ 2) =
      2 * ((W0 * W0′ - W1 * (W1′ + W1 * r) * Y ^ 2) / (W0 ^ 2 - W1 ^ 2 * Y ^ 2)) := by
    unfold logDeriv
    simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, hYd, smul_eq_mul,
      nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [hab, hNd]
  ring

end Differential

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- **The antiderivative data of `keDecide`.** -/
inductive KEW (m : ℕ) where
  | plain (y : LC (m + 1))
  | param (y : LC (m + 1)) (q0 q1 : ℚ) (z : LC m) (κ : ℚ) (W0 W1 : GPoly (LC m))

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- `Â = (z²/κ) A`. -/
def keAhat (m : ℕ) (A : GPoly (LC m)) (z : LC m) (κ : ℚ) : GPoly (LC m) :=
  A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z) (mcst Fc ks m κ⁻¹)))

/-- **`keDecideC` with the antiderivative.** -/
def keDecideCW (m : ℕ) (A B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) : Option (Option (KEW m)) :=
  let O := MO Fc ks m
  let a0 := A.getD 0 O.zero
  let rhs : LC (m + 1) := (B, denC Fc ks m k l A)
  let frA := kpFr Fc ks m 1 2 A
  let plain := (rdeSolFr Fc ks lv (m + 1) frA rhs).map KEW.plain
  match (prdeC Fc ks lv m (halfFr Fc ks m a0) []).find? (fun r ↦ !O.isZero r.2) with
  | none => some plain
  | some (_, z) =>
    let κ := (ratValC Fc ks m (O.mul (O.mul z z) a0)).getD 0
    let c := O.mul (O.mul z z) (mcst Fc ks m κ⁻¹)
    let Ahat : GPoly (LC m) := A.map (O.mul c)
    let fK : CPoly (KF Fc m) := CPoly.trim (Ahat.map (trC Fc m))
    match torsOracleC (redAtKF Fc m rs) (cpf fK) ps bound fK 2 (gammaL ![(0 : KF Fc m)] ![1] ![1] 1) with
    | none => none
    | some none => some plain
    | some (some N) =>
      match witW fK 2 (fK.length - 1) ![(0 : KF Fc m)] ![1] ![1] N with
      | none => none
      | some Wb =>
        let W0 := (Wb.getD 0 []).map (unTr Fc m)
        let W1 := (Wb.getD 1 []).map (unTr Fc m)
        some (((prdeC Fc ks lv (m + 1) frA [rhs, normC Fc (m + 1) (logCol Fc ks m Ahat W0 W1 z)]).find?
          fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map fun r ↦
            KEW.param r.2 (r.1.getD 0 0) (r.1.getD 1 0) z κ W0 W1)

/-- **`keDecideCW` answers exactly as `keDecideC`.** -/
theorem keDecideCW_isSome (m : ℕ) (A B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) :
    (keDecideCW Fc ks lv m A B k l ps bound rs cpf).map Option.isSome =
      keDecideC Fc ks lv m A B k l ps bound rs cpf := by
  unfold keDecideCW keDecideC
  dsimp only
  split
  · rename_i heq
    rw [heq]
    simp only [Option.map_some, Option.isSome_map]
    exact congrArg some (rdeSolFr_isSome _ _ _ _ _ _)
  · rename_i q z heq
    rw [heq]
    dsimp only
    split
    · rename_i heq2; rw [heq2]; rfl
    · rename_i heq2; rw [heq2]
      simp only [Option.map_some, Option.isSome_map]
      exact congrArg some (rdeSolFr_isSome _ _ _ _ _ _)
    · rename_i N heq2
      rw [heq2]
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

/-- **The plain antiderivative**: `(y θ)′ = B/(tᵏ Aˡ) θ`. -/
theorem ke_plain_antiderivative (m : ℕ) (hTr : T.Tr (m + 1)) (A B : GPoly (LC m)) (k l : ℕ)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (y : LC (m + 1))
    (hy : rdeSolFr Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) ((B, denC Fc ks m k l A) : LC (m + 1)) =
      some y) :
    (T.ev (m + 1) y * θ)′ = T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ := by
  have hz := T.rdeSolFr_sound (m + 1) hTr _ hspec _ y hy
  have hzL := congrArg Subtype.val hz
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
    T.sem_frac_code m hTr, T.evP_denC m hTr.of_succ, T.sem_MP] at hzL
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (T.ev (m + 1) y) 1
  simp only [pow_one] at h1
  rw [h1, hzL]

set_option maxHeartbeats 4000000 in
/-- **The antiderivative with a logarithmic part.** With `a = y`, `C = −(q₁/q₀) √κ`: if
`N = W₀² − W₁² Â ≠ 0`, then in every extension with a constant `s`, `s² = κ`,
`f = ((a/q₀) θ)′ + C (W₀ + W₁ θ̂)′/(W₀ + W₁ θ̂) − (C/2) N′/N` (`θ̂ = z θ / s`);
if `N = 0`, `f = ((a/q₀) θ)′`. -/
theorem ke_param_antiderivative (m : ℕ)
    (hTr : T.Tr (m + 1)) (A B : GPoly (LC m)) (k l : ℕ) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hA0 : T.evP m A ≠ 0) (zc : LC m) (hz0 : T.ev m zc ≠ 0) (κ : ℚ) (hκ : κ ≠ 0)
    (W0 W1 : GPoly (LC m))
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (r : List ℚ × LC (m + 1))
    (hr : r ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) [((B, denC Fc ks m k l A) : LC (m + 1)),
      normC Fc (m + 1) (logCol Fc ks m (keAhat Fc ks m A zc κ) W0 W1 zc)])
    (hq0 : r.1.getD 0 0 ≠ 0) :
    let f := T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ
    let a := T.ev (m + 1) r.2 / (r.1.getD 0 0 : L)
    let Pv := T.evP m (keAhat Fc ks m A zc κ)
    let N := T.evP m W0 ^ 2 - T.evP m W1 ^ 2 * Pv
    (N = 0 → f = (a * θ)′) ∧
    (N ≠ 0 → ∀ (E : Type u) [Field E] [CharZero E] [Differential E] [Algebra L E]
      [DifferentialAlgebra L E] (s : E), s ^ 2 = κ → s′ = 0 →
      let ψ := algebraMap L E
      let Y := ψ (T.ev m zc * θ) / s
      let C := ψ (((-(r.1.getD 1 0) / r.1.getD 0 0 : ℚ)) : L) * s
      ψ f = (ψ (a * θ))′ + C * logDeriv (ψ (T.evP m W0) + ψ (T.evP m W1) * Y) +
        (-(C / 2)) * logDeriv (ψ N)) := by
  intro f a Pv N
  simp only [f, a, Pv, N]
  set col := normC Fc (m + 1) (logCol Fc ks m (keAhat Fc ks m A zc κ) W0 W1 zc) with hcol
  set rhs : LC (m + 1) := (B, denC Fc ks m k l A) with hrhs
  have hs := hspec.sound [rhs, col] r hr
  have hsQ : sQ (T.MP (m + 1) hTr) r.1 [rhs, col] =
      ((r.1.getD 0 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem rhs +
        ((r.1.getD 1 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem col := by
    simp [sQ, Finset.sum_range_succ]
  rw [hsQ] at hs
  have hsL := congrArg Subtype.val hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv] at hsL
  rw [T.sem_kpFr m hTr, hrhs, T.sem_frac_code m hTr, T.evP_denC m hTr.of_succ] at hsL
  simp only [T.sem_MP (m + 1) hTr] at hsL
  rw [hcol, T.ev_normC (m + 1) hTr] at hsL
  set av : L := T.ev (m + 1) r.2 with hav
  set q0 : ℚ := r.1.getD 0 0 with hq0d
  set q1 : ℚ := r.1.getD 1 0 with hq1d
  have hq0L : (q0 : L) ≠ 0 := by exact_mod_cast hq0
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (av / q0) 1
  simp only [pow_one] at h1
  have hf : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = ((av / q0) * θ)′ +
      ((-q1 / q0 : ℚ) : L) * (T.ev (m + 1) (logCol Fc ks m (keAhat Fc ks m A zc κ) W0 W1 zc) * θ) := by
    rw [h1]
    have hq0d' : ((q0 : L))′ = 0 := Tower.NestP.deriv_ratCastK (K := L) q0
    have hd : (av / (q0 : L))′ = av′ / q0 := by
      rw [div_eq_mul_inv av, Derivation.leibniz, Derivation.leibniz_inv, hq0d', div_eq_mul_inv]
      simp only [smul_eq_mul, mul_zero, zero_add, neg_zero]
      ring
    rw [hd]
    generalize T.evP m B / (T.ts m ^ k * T.evP m A ^ l) = R at hsL ⊢
    push_cast at hsL ⊢
    field_simp
    linear_combination (-2 * θ : L) * hsL
  rw [T.ev_logCol m hTr] at hf
  have hPvA : T.evP m (keAhat Fc ks m A zc κ) = T.ev m zc ^ 2 / κ * T.evP m A := by
    rw [keAhat, T.evP_mapMul m hTr.of_succ]
    congr 1
    rw [← T.sem_MP m hTr.of_succ, (T.MP m hTr.of_succ).sem_mul, (T.MP m hTr.of_succ).sem_mul,
      T.sem_mcst, IntermediateField.coe_mul, IntermediateField.coe_mul, T.sem_MP m hTr.of_succ]
    push_cast; ring
  set Pv := T.evP m (keAhat Fc ks m A zc κ) with hPvd
  set W0v := T.evP m W0 with hW0v
  set W1v := T.evP m W1 with hW1v
  set zv := T.ev m zc with hzv
  refine ⟨fun hN ↦ ?_, fun hN E _ _ _ _ _ s hs2 hs' ↦ ?_⟩
  · rw [hf]
    have hN' : W0v * W0v - W1v * W1v * Pv = 0 := by linear_combination hN
    rw [hN', inv_zero, mul_zero, zero_mul, zero_mul, mul_zero, add_zero]
  · set ψ := algebraMap L E with hψ
    have hψd : ∀ w : L, (ψ w)′ = ψ w′ := fun w ↦ deriv_algebraMap w
    have hs0 : s ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow two_ne_zero] at hs2; exact hκ (by exact_mod_cast hs2.symm)
    have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
    have hPv0 : Pv ≠ 0 := by
      rw [hPvA]; exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 hz0) (by exact_mod_cast hκ)) hA0
    have hPψ : ψ Pv ≠ 0 := (map_ne_zero ψ).mpr hPv0
    set rv := (1 / 2 : L) * (Pv′ * Pv⁻¹) with hrvdef
    set Y := ψ (zv * θ) / s with hYdef
    have hY0 : Y ≠ 0 := div_ne_zero ((map_ne_zero ψ).mpr (mul_ne_zero hz0 hθ0)) hs0
    have hY2 : Y ^ 2 = ψ Pv := by
      rw [hYdef, div_pow, hs2, ← map_pow, hPvA, mul_pow, hθ]
      simp only [map_mul, map_div₀, map_pow, map_ratCast]
      field_simp
    have hYd : Y′ = ψ rv * Y := by
      have hd := congrArg (fun w ↦ w′) hY2
      simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, hψd] at hd
      have hrv : ψ rv = (1 / 2 : E) * (ψ Pv′ * (ψ Pv)⁻¹) := by
        simp only [rv, map_mul, map_div₀, map_one, map_ofNat, map_inv₀]
      rw [hrv, ← hY2, ← hd]
      field_simp
      ring
    have hNm : ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv ≠ 0 := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_sub]
      exact (map_ne_zero ψ).mpr hN
    have hab := logDeriv_ab (y := Y) (ψ W0v) (ψ W1v) (ψ Pv) (ψ rv) hY2 hYd hNm
    have hP' : (ψ Pv)′ = 2 * ψ rv * ψ Pv := by
      rw [← hY2, Derivation.leibniz_pow, hYd]; simp; ring
    have hNd : logDeriv (ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv) =
        2 * ((ψ W0v * (ψ W0v)′ - ψ W1v * ((ψ W1v)′ + ψ W1v * ψ rv) * ψ Pv) /
          (ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv)) := by
      unfold logDeriv
      rw [map_sub, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, hP']
      simp only [smul_eq_mul, nsmul_eq_mul]
      field_simp
      push_cast
      ring
    have hψN : ψ (W0v ^ 2 - W1v ^ 2 * Pv) = ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv := by
      simp only [map_sub, map_mul, map_pow]
    rw [hψN, hab, hNd, hf, RingHom.map_add, ← hψd, add_assoc]
    congr 1
    have hrvψ : ψ rv = (1 / 2 : E) * ((ψ Pv)′ * (ψ Pv)⁻¹) := by
      simp only [rv, RingHom.map_mul, map_div₀, map_one, map_ofNat, map_inv₀, hψd]
    rw [hrvψ]
    simp only [RingHom.map_mul, map_div₀, map_inv₀, RingHom.map_sub, RingHom.map_add, map_ratCast,
      RingHom.map_pow, ← hψd]
    have e1 : ψ ((1 / 2 : L)) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    have e2 : ψ (Pv′ * Pv⁻¹) = (ψ Pv)′ * (ψ Pv)⁻¹ := by rw [RingHom.map_mul, map_inv₀, hψd]
    have e3 : ψ (zv * θ) = ψ zv * ψ θ := RingHom.map_mul _ _ _
    rw [hYdef]
    simp only [e1, e2, e3, hrvψ]
    field_simp
    ring

/-- **A valid KE antiderivative** for `f = B/(tᵏ Aˡ) θ`. -/
def KEW.Valid (m : ℕ) (A B : GPoly (LC m)) (k l : ℕ)
    (θ : L) : KEW m → Prop
  | .plain y => (T.ev (m + 1) y * θ)′ = T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ
  | .param y q0 q1 z κ W0 W1 =>
    let f := T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ
    let a := T.ev (m + 1) y / (q0 : L)
    let N := T.evP m W0 ^ 2 - T.evP m W1 ^ 2 * T.evP m (keAhat Fc ks m A z κ)
    κ ≠ 0 ∧ (N = 0 → f = (a * θ)′) ∧
    (N ≠ 0 → ∀ (E : Type u) [Field E] [CharZero E] [Differential E] [Algebra L E]
      [DifferentialAlgebra L E] (s : E), s ^ 2 = κ → s′ = 0 →
      let ψ := algebraMap L E
      let Y := ψ (T.ev m z * θ) / s
      let C := ψ (((-q1 / q0 : ℚ)) : L) * s
      ψ f = (ψ (a * θ))′ + C * logDeriv (ψ (T.evP m W0) + ψ (T.evP m W1) * Y) +
        (-(C / 2)) * logDeriv (ψ N))

/-- **Every antiderivative returned by `keDecideCW` is valid.** -/
theorem keDecideCW_valid (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) (A : GPoly (LC m)) (hdegpos : 0 < degG (MO Fc ks m) A)
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (w : KEW m)
    (hdec : keDecideCW Fc ks lv m A B k l ps bound rs cpf = some (some w)) :
    KEW.Valid T m A B k l θ w := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  have hplain : ∀ y, rdeSolFr Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      ((B, denC Fc ks m k l A) : LC (m + 1)) = some y → KEW.Valid T m A B k l θ (.plain y) :=
    fun y hy ↦ T.ke_plain_antiderivative m hTr A B k l θ hθ hA0 hspecA y hy
  unfold keDecideCW at hdec
  dsimp only at hdec
  rcases hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) with _ | ⟨q, z⟩
  · rw [hfind] at hdec
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
    exact hplain y hy
  · rw [hfind] at hdec
    dsimp only at hdec
    obtain ⟨hz0, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q z hfind
    split at hdec
    · exact absurd hdec (by simp)
    · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
      exact hplain y hy
    · split at hdec
      · exact absurd hdec (by simp)
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
        have hr0 := List.find?_some hr
        simp only [decide_eq_true_eq] at hr0
        have key := T.ke_param_antiderivative m hTr A B k l θ hθ hA0 z hz0 _ hκ0 _ _ hspecA r
          (List.mem_of_find?_eq_some hr) hr0
        exact ⟨hκ0, key.1, key.2⟩

end MTower

end Curves.MT
