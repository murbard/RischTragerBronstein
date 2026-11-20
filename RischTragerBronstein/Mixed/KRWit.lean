import RischTragerBronstein.Mixed.KRDecides
import RischTragerBronstein.Mixed.PrdeWit
import RischTragerBronstein.Mixed.KPWit

/-!
# Radicals over an exponential: the antiderivative

`kr_col_logs`: the column of `krCol` explicitly — in any extension with `sⁿ = κ` and a primitive
`n`-th root of unity `ζ`, `col θʲ = ∑_k (sʲ/n) ζ^{(n−j)k} W(ζᵏ Y₀)′/W(ζᵏ Y₀)` (`Y₀ = z θ/s`).
`krDecideCW` mirrors `krDecideC` (`krDecideCW_isSome`) and returns the antiderivative data:
`plain y` (`∫ f = y θʲ`) or a parametric solution with the column (`∫ f = (y/q₀) θʲ − (q₁/q₀) ∫ col θʲ`,
the last integral the logarithms above), `krDecideCW_valid`.
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- **The antiderivative data of `krDecide`.** -/
inductive KRW (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) where
  | plain (y : LC (m + 1))
  | param (r : List ℚ × LC (m + 1)) (z : LC m) (κ : ℚ) (W0 : BPoly (KF Fc m)) (col : LC (m + 1))

section Codes

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- **`krDecideC` with the antiderivative.** -/
def krDecideCW (m n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (A B : GPoly (LC m))
    (kt l : ℕ) (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option (Option (KRW Fc m)) :=
  let O := MO Fc ks m
  let rhs : LC (m + 1) := (B, denC Fc ks m kt l A)
  let frA := kpFr Fc ks m j n A
  let plain := (rdeSolFr Fc ks lv (m + 1) frA rhs).map KRW.plain
  if !(decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) then none
  else if O.isZero (A.getD 0 O.zero) then none
  else
    match krZ Fc ks lv m n A with
    | none => some plain
    | some z =>
      let κ := (ratValC Fc ks m (O.mul (powC O z n) (A.getD 0 O.zero))).getD 0
      if κ = 0 then none
      else
        match krTorsC Fc ks m n A z κ cpf ps bound rs with
        | none => none
        | some none => some plain
        | some (some N) =>
          match krWit Fc ks m n A z κ N with
          | none => none
          | some Wb =>
            match descendNF Fc m n (normNF Fc m n Wb) with
            | none => none
            | some W0 =>
              match krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0 with
              | none => none
              | some col => some ((prdeSolN Fc ks lv m frA rhs [col]).map fun r ↦
                  KRW.param r z κ W0 col)

/-- **`krDecideCW` answers exactly as `krDecideC`.** -/
theorem krDecideCW_isSome (m n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))]
    (A B : GPoly (LC m)) (kt l : ℕ) (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (krDecideCW Fc ks lv m n j A B kt l cpf ps bound rs).map Option.isSome =
      krDecideC Fc ks lv m n j A B kt l cpf ps bound rs := by
  unfold krDecideCW krDecideC
  dsimp only
  have hp : ∀ fr rhs, (Option.map (Option.isSome) (some ((rdeSolFr Fc ks lv (m + 1) fr rhs).map
      (KRW.plain (Fc := Fc))))) = some (rdeOKFr Fc ks lv (m + 1) fr rhs) := fun fr rhs ↦ by
    simp only [Option.map_some, Option.isSome_map, rdeSolFr_isSome]
  split_ifs
  all_goals try rfl
  rcases hz : krZ Fc ks lv m n A with _ | z
  · simp only [hz]; exact hp _ _
  · simp only [hz]
    split_ifs
    · rfl
    · rcases ht : krTorsC Fc ks m n A z _ cpf ps bound rs with _ | _ | N
      · simp only [ht]; rfl
      · simp only [ht]; exact hp _ _
      · simp only [ht]
        rcases hw : krWit Fc ks m n A z _ N with _ | Wb
        · simp only [hw]; rfl
        · simp only [hw]
          rcases hd : descendNF Fc m n (normNF Fc m n Wb) with _ | W0
          · simp only [hd]; rfl
          · simp only [hd]
            rcases hc : krCol Fc ks m n (krAh Fc ks m n A z _) z j W0 with _ | col
            · simp only [hc]; rfl
            · simp only [hc, Option.map_some, Option.isSome_map]
              exact congrArg some (prdeSolN_isSome _ _ _ _ _ _ _)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 4000000 in
/-- **The column of `krCol`, explicitly.** -/
theorem kr_col_logs (m n j : ℕ) (hn : 0 < n) (hj : j < n) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (θ : L) (hθ : θ ^ n = T.evP m A) (hA0 : T.evP m A ≠ 0) (z : LC m) (hz0 : T.ev m z ≠ 0)
    (κ : ℚ) (hκ : κ ≠ 0) (W : BPoly (KF Fc m)) (col : LC (m + 1))
    (h : krCol Fc ks m n (krAh Fc ks m n A z κ) z j W = some col)
    (E : Type u) [Field E] [CharZero E] [Differential E] [Algebra L E] [DifferentialAlgebra L E]
    (s ζ : E) (hsn : s ^ n = κ) (hζ : IsPrimitiveRoot ζ n) :
    let ψ := algebraMap L E
    let φ : T.F (m + 1) →+* E := ψ.comp (algebraMap (T.F (m + 1)) L)
    let Wp := Polynomial.map φ (toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem
      (pcP Fc ks m (c.map (unTr Fc m)))))
    let Y0 := ψ (T.ev m z * θ) / s
    (∀ k, Wp.eval (ζ ^ k * Y0) ≠ 0) ∧
    ψ (T.ev (m + 1) col * θ ^ j) = ∑ k ∈ Finset.range n,
      (s ^ j / n * ζ ^ ((n - j) * k)) * logDeriv (Wp.eval (ζ ^ k * Y0)) := by
  intro ψ' φ' Wp' Y0'
  obtain ⟨Wd, s1, s2, Q, D, g, hg, hWd, hbez, hdiv, hD, hcol⟩ :=
    T.krCol_spec m n hn hTr _ z j W col h
  set ψ := algebraMap L E with hψ
  have hψd : ∀ w : L, (ψ w)′ = ψ w′ := fun w ↦ deriv_algebraMap w
  set φ : T.F (m + 1) →+* E := ψ.comp (algebraMap (T.F (m + 1)) L) with hφdef
  have hφ : ∀ x, φ x′ = (φ x)′ := fun x ↦ by
    simp only [hφdef, RingHom.comp_apply, hψd]
    rfl
  have hφv : ∀ x : T.F (m + 1), φ x = ψ (x : L) := fun x ↦ rfl
  set Av := (T.MP (m + 1) hTr).sem (pcP Fc ks m (krAh Fc ks m n A z κ)) with hAv
  have hAvL : ((Av : T.F (m + 1)) : L) = T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * T.evP m A := by
    rw [hAv, T.sem_MP (m + 1) hTr]
    change T.evP m (krAh Fc ks m n A z κ) / T.evP m [(MO Fc ks m).one] = _
    rw [T.evP_krAh m n hTr.of_succ, T.evP_single, T.ev_one_code m hTr.of_succ, div_one]
  have hκL : (κ : E) ≠ 0 := by exact_mod_cast hκ
  have hs0 : s ≠ 0 := fun h0 ↦ hκL (by rw [← hsn, h0, zero_pow hn.ne'])
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow hn.ne'])
  set Y0 : E := ψ (T.ev m z * θ) / s with hY0
  have hY0n : Y0 ^ n = φ Av := by
    rw [hφv, hAvL, hY0, div_pow, hsn, ← map_pow, mul_pow, hθ]
    simp only [map_mul, map_pow, map_ratCast]
    field_simp
    rw [Rat.cast_div, Rat.cast_one]
    field_simp
  have hAv0 : φ Av ≠ 0 := by
    rw [hφv, hAvL]
    refine (map_ne_zero ψ).mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0) ?_) hA0)
    exact_mod_cast inv_ne_zero hκ
  set r : T.F (m + 1) := ((1 / n : ℚ) : T.F (m + 1)) * (Av′ * Av⁻¹) with hr
  have hφr : φ r = ((1 / n : ℚ) : E) * ((φ Av)′ * (φ Av)⁻¹) := by
    rw [hr, map_mul, map_mul, map_inv₀, hφ, map_ratCast]
  have hkey : ∀ k : ℕ, ((Polynomial.map φ (toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem
      (pcP Fc ks m (c.map (unTr Fc m)))))).eval (ζ ^ k * Y0)) ≠ 0 ∧
      logDeriv ((Polynomial.map φ (toPoly (W.map fun c ↦ (T.MP (m + 1) hTr).sem
        (pcP Fc ks m (c.map (unTr Fc m)))))).eval (ζ ^ k * Y0)) =
        (D.map φ).eval (ζ ^ k * Y0) / φ g := fun k ↦ by
    have hYk : (ζ ^ k * Y0) ^ n = φ Av := by
      rw [mul_pow, ← pow_mul, mul_comm k n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hY0n]
    refine twist_dlog_hom φ hφ n _ Wd s1 s2 Q D Av r g hWd hbez hg hdiv _ hYk ?_
    rw [hφr]
    exact deriv_of_pow_eq n hn _ _ hYk hAv0
  have hDn : ∀ i, n ≤ i → (D.map φ).coeff i = 0 := fun i hi ↦ by rw [coeff_map, hD i hi, map_zero]
  have hsum := twist_sum n ζ hζ (D.map φ) hDn j hj Y0
  -- the value of the column
  have hcolL : ψ (T.ev (m + 1) col * θ ^ j) = s ^ j * φ (D.coeff j) * Y0 ^ j / φ g := by
    have e1 : T.ev (m + 1) col = ((((T.MP (m + 1) hTr).sem col : T.F (m + 1))) : L) :=
      (T.sem_MP (m + 1) hTr col).symm
    rw [e1, hcol]
    have e2 : ((((T.MP (m + 1) hTr).sem (pcP Fc ks m [powC (MO Fc ks m) z j]) : T.F (m + 1))) : L) =
        T.ev m z ^ j := by
      rw [T.sem_MP (m + 1) hTr]
      change T.evP m [powC (MO Fc ks m) z j] / T.evP m [(MO Fc ks m).one] = _
      rw [T.evP_single, T.evP_single, T.ev_one_code m hTr.of_succ, div_one, ← T.sem_MP m hTr.of_succ,
        sem_powC, IntermediateField.coe_pow, T.sem_MP m hTr.of_succ]
    rw [IntermediateField.coe_div, IntermediateField.coe_mul, e2, hY0]
    simp only [map_mul, map_div₀, map_pow, ← hφv]
    field_simp
    rw [div_pow, mul_pow]
    field_simp
  have hgoal : ψ (((1 : ℚ) : L) * (T.ev (m + 1) col * θ ^ j)) = ∑ k ∈ Finset.range n,
      (((1 : ℚ) : E) * s ^ j / n * ζ ^ ((n - j) * k)) * logDeriv ((Polynomial.map φ (toPoly
        (W.map fun c ↦ (T.MP (m + 1) hTr).sem (pcP Fc ks m (c.map (unTr Fc m)))))).eval
          (ζ ^ k * Y0)) := by
    simp_rw [fun k ↦ (hkey k).2]
    rw [map_mul, hcolL, map_ratCast]
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
    have hg' : φ g ≠ 0 := (map_ne_zero φ).mpr hg
    have e3 : ∑ k ∈ Finset.range n, ((1 : ℚ) : E) * s ^ j / n * ζ ^ ((n - j) * k) *
        ((D.map φ).eval (ζ ^ k * Y0) / φ g) = ((1 : ℚ) : E) * s ^ j / n / φ g *
          ∑ k ∈ Finset.range n, ζ ^ ((n - j) * k) * (D.map φ).eval (ζ ^ k * Y0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      field_simp
    rw [e3, hsum, coeff_map]
    field_simp
  refine ⟨fun k ↦ (hkey k).1, ?_⟩
  have := hgoal
  simp only [Rat.cast_one, one_mul] at this
  exact this

/-- **A valid KR antiderivative** for `f = B/(tᵏ Aˡ) θʲ`. -/
def KRW.Valid (lv : (m : ℕ) → LC m) (m n j : ℕ) (A B : GPoly (LC m)) (kt l : ℕ) (θ : L) :
    KRW Fc m → Prop
  | .plain y => (T.ev (m + 1) y * θ ^ j)′ = T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j
  | .param r z κ W0 col =>
    r ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A) [((B, denC Fc ks m kt l A) : LC (m + 1)), col] ∧
    r.1.getD 0 0 ≠ 0 ∧ krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0 = some col ∧
    T.ev m z ≠ 0 ∧ κ ≠ 0 ∧
    T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j =
      ((T.ev (m + 1) r.2 / (r.1.getD 0 0 : L)) * θ ^ j)′ +
        ((-(r.1.getD 1 0) / r.1.getD 0 0 : ℚ) : L) * (T.ev (m + 1) col * θ ^ j)

set_option maxHeartbeats 4000000 in
/-- **Every antiderivative returned by `krDecideCW` is valid** (the column then by `kr_col_logs`). -/
theorem krDecideCW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (n j : ℕ)
    [Fact (Irreducible (toPoly (cycK Fc m n)))] (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A)) (θ : L) (hθ : θ ^ n = T.evP m A)
    (B : GPoly (LC m)) (kt l : ℕ) (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (w : KRW Fc m)
    (hdec : krDecideCW Fc ks lv m n j A B kt l cpf ps bound rs = some (some w)) :
    KRW.Valid T lv m n j A B kt l θ w := by
  obtain ⟨hTr, hsq, hdegA, hcopA, hM, hspecA, hA0⟩ :=
    T.kr_setup (lv := lv) hmon hdeg m hn hc n j A hsqc hdegpos hcop
  have hTm : T.Tr m := hTr.of_succ
  have hrhs : T.ev (m + 1) ((B, denC Fc ks m kt l A) : LC (m + 1)) =
      T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) := T.ev_rhs m hTr A B kt l
  unfold krDecideCW at hdec
  dsimp only at hdec
  by_cases hchk : (decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) = true
  swap
  · simp only [Bool.not_eq_true] at hchk
    simp [hchk] at hdec
  rw [if_neg (by simp only [hchk, Bool.not_true]; decide)] at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hn1, hj0⟩, hjn⟩, hjc⟩ := hchk
  have hn0 : 0 < n := by omega
  by_cases ha0t : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = true
  · rw [if_pos ha0t] at hdec; exact absurd hdec (by simp)
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by simpa using ha0t
  rw [if_neg (by rw [ha0]; decide)] at hdec
  have hplain : ∀ y, rdeSolFr Fc ks lv (m + 1) (kpFr Fc ks m j n A)
      ((B, denC Fc ks m kt l A) : LC (m + 1)) = some y → KRW.Valid T lv m n j A B kt l θ (.plain y) := by
    intro y hy
    have hz := T.rdeSolFr_sound (m + 1) hTr _ hspecA _ y hy
    have hzL := congrArg Subtype.val hz
    have hrhs' : (((T.MP (m + 1) hTr).sem ((B, denC Fc ks m kt l A) : LC (m + 1)) : T.F (m + 1)) :
        L) = T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) := by
      exact (T.sem_MP (m + 1) hTr _).trans hrhs
    rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
      T.sem_MP (m + 1) hTr, hrhs'] at hzL
    show _ = _
    rw [deriv_mul_radical θ (T.evP m A) n hn0 hθ hA0, hzL]
  rcases hz : krZ Fc ks lv m n A with _ | z
  · simp only [hz] at hdec
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
    exact hplain y hy
  · simp only [hz] at hdec
    obtain ⟨-, -, hκ0⟩ := T.kr_z_facts hmon hdeg m n hn0 hn hc A ha0 z hz
    obtain ⟨hz0, -⟩ := T.kr_zsem hmon hdeg m n hn0 hn hc hTm A ha0 z hz
    have hz0L : T.ev m z ≠ 0 := fun h ↦ hz0 (Subtype.ext (by rw [T.sem_MP m hTm]; exact h))
    set κ : ℚ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
      (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκdef
    rw [if_neg hκ0] at hdec
    rcases htors : krTorsC Fc ks m n A z κ cpf ps bound rs with _ | _ | N
    · simp only [htors] at hdec; exact absurd hdec (by simp)
    · simp only [htors] at hdec
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
      exact hplain y hy
    · simp only [htors] at hdec
      rcases hwit : krWit Fc ks m n A z κ N with _ | Wb
      · simp only [hwit] at hdec; exact absurd hdec (by simp)
      simp only [hwit] at hdec
      rcases hdsc : descendNF Fc m n (normNF Fc m n Wb) with _ | W0b
      · simp only [hdsc] at hdec; exact absurd hdec (by simp)
      simp only [hdsc] at hdec
      rcases hcolc : krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0b with _ | col
      · simp only [hcolc] at hdec; exact absurd hdec (by simp)
      simp only [hcolc] at hdec
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
      have hr0 := List.find?_some hr
      simp only [decide_eq_true_eq] at hr0
      have hrm := List.mem_of_find?_eq_some hr
      refine ⟨hrm, hr0, hcolc, hz0L, hκ0, ?_⟩
      have := T.prde_param_eqN m n j hn0 hTr A θ hθ hA0 hspecA _ [col] r hrm hr0
      rw [hrhs] at this
      rw [this]
      simp

end MTower

end Curves.MT
