import RischTragerBronstein.Mixed.ExpCurveMain
import RischTragerBronstein.Mixed.PrimGen

/-!
# One logarithm over a curve: the algorithm

`integrateLogCurve Fc ucode A D N`, for `∫ A(t)/D(t)` with `t = log u` over the function field of
the curve `F(x, y) = 0` (`Fc` over `ℚ`, `u` and the coefficients of `A, D` curve codes),
`η = u′ / u`:

1. Hermite reduction (every irreducible is normal in a primitive extension);
2. the residue test on the simple part;
3. the polynomial part `∑ aⱼ tʲ` (`j ≤ d`) by the chain of limited integration problems, top
   down: `Qⱼ′ + γ η = aⱼ − (j + 1) η Qⱼ₊₁` (`Q_{d+1} = 0`), each solved with `curveRde` (`h = 0`,
   right-hand sides `[aⱼ − (j + 1) η Qⱼ₊₁, η]`, a returned solution with non-zero first
   parameter);
4. the constant term `a₀ − η Q₁` must have an elementary integral on the curve (`decideTotal`).

This file: the algorithm, and the soundness (`primChain_sound`) and completeness
(`primChain_complete`, over any curve whose constants contain those of the ambient field, with `η`
not a constant multiple of a derivative) of the chain.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup NFC

section Alg

variable (Fc : BPoly ℚ)

/-- The code of the rational `q`. -/
def ratCode (q : ℚ) : GPoly (GFrac ℚ) :=
  (curveOps Fc).mul (intCode Fc q.num) ((curveOps Fc).inv ((curveOps Fc).natCast q.den))

/-- `η = u′ / u`. -/
def etaCode (ucode : GPoly (GFrac ℚ)) : GPoly (GFrac ℚ) :=
  (curveOps Fc).mul ((curveOps Fc).deriv ucode) ((curveOps Fc).inv ucode)

/-- `a − (j + 1) η Q`. -/
def chainRHS (ηc a Q : GPoly (GFrac ℚ)) (j : ℕ) : GPoly (GFrac ℚ) :=
  (curveOps Fc).add a ((curveOps Fc).neg
    ((curveOps Fc).mul ((curveOps Fc).mul ((curveOps Fc).natCast (j + 1)) ηc) Q))

/-- One step of the chain: a solution `Q'` of `Q'′ + γ η = a − (j + 1) η Q`. -/
def chainStep (ηc a Q : GPoly (GFrac ℚ)) (j : ℕ) : Option (GPoly (GFrac ℚ)) :=
  ((curveRde Fc (curveOps Fc).zero [chainRHS Fc ηc a Q j, ηc]).find?
    fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map
    fun r ↦ (curveOps Fc).mul (ratCode Fc (r.1.getD 0 0)⁻¹) r.2

/-- The chain from index `j` down to `1`, starting from `Qⱼ₊₁ = Q`; returns `Q₁`. -/
def primChain (ηc : GPoly (GFrac ℚ)) (Λ : GPoly (GPoly (GFrac ℚ))) :
    ℕ → GPoly (GFrac ℚ) → Option (GPoly (GFrac ℚ))
  | 0, Q => some Q
  | j + 1, Q => (chainStep Fc ηc (Λ.getD (j + 1) (curveOps Fc).zero) Q (j + 1)).bind
      (primChain ηc Λ j)

/-- The constant term `a₀ − η Q₁`. -/
def logConst (ηc : GPoly (GFrac ℚ)) (Λ : GPoly (GPoly (GFrac ℚ))) (Q1 : GPoly (GFrac ℚ)) :
    GPoly (GFrac ℚ) :=
  (curveOps Fc).add (Λ.getD 0 (curveOps Fc).zero) ((curveOps Fc).neg ((curveOps Fc).mul ηc Q1))

/-- **One logarithm over a curve**, with search bound `N` for the constant term. -/
def integrateLogCurve (ucode : GPoly (GFrac ℚ)) (A D : GPoly (GPoly (GFrac ℚ))) (N : ℕ) :
    Option Bool :=
  let O := curveOps Fc
  let ηc := etaCode Fc ucode
  let w : GPoly (GPoly (GFrac ℚ)) := [ηc]
  let h := GPoly.hermite O w A D
  let qr := GPoly.divMod O h.b h.s
  if !(GPoly.residueCheck O w qr.2 h.s) then some false
  else match primChain Fc ηc qr.1 qr.1.length O.zero with
    | none => some false
    | some Q1 => decideTotal Fc ((codeW (cvNorm Fc (logConst Fc ηc qr.1 Q1))).map trim)
        (codeQ (cvNorm Fc (logConst Fc ηc qr.1 Q1))) N

end Alg

section Chain

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))
  (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)

lemma sem_ratCode (q : ℚ) : (cM hC S hx Fc hSF).sem (ratCode Fc q) = (q : E) := by
  rw [ratCode, CField.sem_mul, sem_intCode, CField.sem_inv, CField.sem_natCast, Rat.cast_def,
    div_eq_mul_inv]

lemma sem_etaCode (u : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (etaCode Fc u) = logDeriv ((cM hC S hx Fc hSF).sem u) := by
  rw [etaCode, CField.sem_mul, CField.sem_deriv, CField.sem_inv, logDeriv, div_eq_mul_inv]

lemma sem_chainRHS (ηc a Q : GPoly (GFrac ℚ)) (j : ℕ) :
    (cM hC S hx Fc hSF).sem (chainRHS Fc ηc a Q j) = (cM hC S hx Fc hSF).sem a -
      ((j + 1 : ℕ) : E) * (cM hC S hx Fc hSF).sem ηc * (cM hC S hx Fc hSF).sem Q := by
  rw [chainRHS, CField.sem_add, CField.sem_neg, CField.sem_mul, CField.sem_mul,
    CField.sem_natCast, sub_eq_add_neg]

lemma sem_logConst (ηc : GPoly (GFrac ℚ)) (Λ : GPoly (GPoly (GFrac ℚ))) (Q1 : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (logConst Fc ηc Λ Q1) =
      (cM hC S hx Fc hSF).sem (Λ.getD 0 (curveOps Fc).zero) -
        (cM hC S hx Fc hSF).sem ηc * (cM hC S hx Fc hSF).sem Q1 := by
  rw [logConst, CField.sem_add, CField.sem_neg, CField.sem_mul, sub_eq_add_neg]

include hC in
lemma deriv_ratCast' (q : ℚ) : ((q : E))′ = 0 := by
  rw [← map_ratCast (algebraMap Kc E) q, deriv_algebraMap, hC, map_zero]

lemma ratCast_mem (q : ℚ) : (q : E) ∈ Kc⟮S.x⟯⟮S.y⟯ := by
  rw [← map_ratCast (algebraMap Kc E) q]
  exact S.const_mem _

/-- **Soundness of one step.** -/
lemma chainStep_sound (ηc a Q Q' : GPoly (GFrac ℚ)) (j : ℕ)
    (h : chainStep Fc ηc a Q j = some Q') :
    ∃ γ : ℚ, ((cM hC S hx Fc hSF).sem Q')′ + (γ : E) * (cM hC S hx Fc hSF).sem ηc =
      (cM hC S hx Fc hSF).sem (chainRHS Fc ηc a Q j) := by
  set M := cM hC S hx Fc hSF
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  have hr0 := List.find?_some hr
  simp only [decide_eq_true_eq] at hr0
  have hmem := List.mem_of_find?_eq_some hr
  have hs := curveRde_sound hC S hx Fc hSF _ _ r hmem
  simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ] at hs
  rw [M.sem_zero, Derivation.map_zero, zero_mul, add_zero] at hs
  set r0 := r.1.getD 0 0
  set r1 := r.1.getD 1 0
  have hq : (r0 : E) ≠ 0 := by exact_mod_cast hr0
  refine ⟨-(r1 / r0), ?_⟩
  rw [M.sem_mul, sem_ratCode, Derivation.leibniz, deriv_ratCast' hC, hs]
  simp only [smul_eq_mul, mul_zero, add_zero]
  push_cast
  field_simp
  ring

/-- **Soundness of the chain.** -/
theorem primChain_sound (ηc : GPoly (GFrac ℚ)) (Λ : GPoly (GPoly (GFrac ℚ))) :
    ∀ (j : ℕ) (Q R : GPoly (GFrac ℚ)), primChain Fc ηc Λ j Q = some R →
      ∃ P : ℕ → E, (∀ i, P i ∈ Kc⟮S.x⟯⟮S.y⟯) ∧
        (∀ i, 1 ≤ i → i ≤ j → (P i)′ + ((i + 1 : ℕ) : E) * (cM hC S hx Fc hSF).sem ηc *
          P (i + 1) = (cM hC S hx Fc hSF).sem (Λ.getD i (curveOps Fc).zero)) ∧
        (∃ q : ℚ, P (j + 1) = (cM hC S hx Fc hSF).sem Q + q) ∧ P 1 = (cM hC S hx Fc hSF).sem R := by
  set M := cM hC S hx Fc hSF
  intro j
  induction j with
  | zero =>
    intro Q R h
    simp only [primChain, Option.some.injEq] at h
    subst h
    exact ⟨fun _ ↦ M.sem Q, fun _ ↦ sem_mem hC S hx Fc hSF _, fun i h1 h2 ↦ by omega,
      ⟨0, by simp⟩, rfl⟩
  | succ j ih =>
    intro Q R h
    simp only [primChain] at h
    obtain ⟨Q', hQ', hR⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨P, hPmem, hPrec, ⟨q, hq⟩, hP1⟩ := ih Q' R hR
    obtain ⟨γ, hγ⟩ := chainStep_sound hC S hx Fc hSF ηc _ Q Q' (j + 1) hQ'
    rw [sem_chainRHS] at hγ
    set P' := Function.update P (j + 2) (M.sem Q + ((γ / (j + 2) : ℚ) : E)) with hP'
    have hP'lt : ∀ i, i < j + 2 → P' i = P i := fun i hi ↦
      Function.update_of_ne (by omega) _ _
    refine ⟨P', fun i ↦ ?_, fun i h1 h2 ↦ ?_, ⟨γ / (j + 2), ?_⟩, ?_⟩
    · by_cases hi : i = j + 2
      · rw [hi, hP', Function.update_self]
        exact add_mem (sem_mem hC S hx Fc hSF _) (ratCast_mem S _)
      · rw [hP', Function.update_of_ne hi]; exact hPmem i
    · rw [hP'lt i (by omega)]
      by_cases hij : i ≤ j
      · rw [hP'lt (i + 1) (by omega)]; exact hPrec i h1 hij
      · have hi : i = j + 1 := by omega
        subst hi
        rw [hP', Function.update_self, hq, Derivation.map_add, deriv_ratCast' hC, add_zero]
        have hj2 : (j : E) + 2 ≠ 0 := by exact_mod_cast (by omega : j + 2 ≠ 0)
        have h2 : (((j + 1 + 1 : ℕ) : E)) = ((j + 2 : ℕ) : E) := by push_cast; ring
        rw [h2]
        have hγ' : (M.sem Q')′ = M.sem (Λ.getD (j + 1) (curveOps Fc).zero) -
            ((j + 1 + 1 : ℕ) : E) * M.sem ηc * M.sem Q - (γ : E) * M.sem ηc := by
          rw [← hγ]; ring
        rw [hγ', h2]
        push_cast
        field_simp
        ring
    · rw [hP', Function.update_self]
    · rw [hP'lt 1 (by omega), hP1]

include hmon hdeg in
/-- **Completeness of the chain**: if the recurrence has a solution `p` in the function field
(over the constants `Kc`, all the constants of `E`), and `η` is not a non-zero constant multiple
of a derivative, then the chain succeeds and returns `Q₁` with `p₁ − Q₁` constant. -/
theorem primChain_complete (hconst : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E))
    (ηc : GPoly (GFrac ℚ)) (Λ : GPoly (GPoly (GFrac ℚ)))
    (hnex : ∀ y ∈ Kc⟮S.x⟯⟮S.y⟯, ∀ κ : Kc,
      y′ = algebraMap Kc E κ * (cM hC S hx Fc hSF).sem ηc → κ = 0)
    (p : ℕ → E) (hp : ∀ i, p i ∈ Kc⟮S.x⟯⟮S.y⟯) :
    ∀ (j : ℕ), (∀ i, 1 ≤ i → i ≤ j → (p i)′ + ((i + 1 : ℕ) : E) * (cM hC S hx Fc hSF).sem ηc *
          p (i + 1) = (cM hC S hx Fc hSF).sem (Λ.getD i (curveOps Fc).zero)) →
      ∀ Q : GPoly (GFrac ℚ), (∃ κ : Kc, p (j + 1) = (cM hC S hx Fc hSF).sem Q + algebraMap Kc E κ) →
      ∃ R, primChain Fc ηc Λ j Q = some R ∧
        ∃ κ : Kc, p 1 = (cM hC S hx Fc hSF).sem R + algebraMap Kc E κ := by
  classical
  set M := cM hC S hx Fc hSF
  intro j
  induction j with
  | zero =>
    intro _ Q hQ
    exact ⟨Q, rfl, hQ⟩
  | succ j ih =>
    intro hrec Q ⟨κ, hκ⟩
    set f := chainRHS Fc ηc (Λ.getD (j + 1) (curveOps Fc).zero) Q (j + 1) with hf
    set sols := curveRde Fc (curveOps Fc).zero [f, ηc] with hsols
    -- `p (j + 1)` solves the parametric problem
    have hpj : (p (j + 1))′ + (M.sem (curveOps Fc).zero)′ * p (j + 1) =
        ∑ l ∈ Finset.range [f, ηc].length, algebraMap Kc E
          ([1, -(((j + 2 : ℕ) : Kc)) * κ].getD l 0) * M.sem ([f, ηc].getD l []) := by
      simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ]
      rw [M.sem_zero, Derivation.map_zero, zero_mul, add_zero, hf, sem_chainRHS]
      have := hrec (j + 1) (by omega) le_rfl
      rw [hκ] at this
      simp only [map_one, one_mul, map_mul, map_neg, map_natCast]
      rw [show ((j + 1 + 1 : ℕ) : E) = ((j + 2 : ℕ) : E) by push_cast; ring] at this ⊢
      linear_combination this
    obtain ⟨β, hβ1, -⟩ := curveRde_complete hC S hx Fc hSF hmon hdeg _ [f, ηc] _ _ (hp (j + 1)) hpj
    have h1 := hβ1 0 (by simp)
    simp only [List.getD_cons_zero] at h1
    have hex : ∃ r ∈ sols, r.1.getD 0 0 ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_eq_zero fun l hl ↦ by
        have : (sols.getD l ([], [])).1.getD 0 0 = 0 := hall _ (by
          rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hl)]; exact List.getElem_mem _)
        rw [this, map_zero, mul_zero]] at h1
      exact one_ne_zero h1
    obtain ⟨r, hr⟩ : ∃ r, sols.find? (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = some r := by
      obtain ⟨r, hrm, hr0⟩ := hex
      exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨r, hrm, by simpa using hr0⟩)
    set Q' := (curveOps Fc).mul (ratCode Fc (r.1.getD 0 0)⁻¹) r.2 with hQ'
    have hstep : chainStep Fc ηc (Λ.getD (j + 1) (curveOps Fc).zero) Q (j + 1) = some Q' := by
      simp only [chainStep, ← hf, ← hsols, hr, Option.map_some]
      rfl
    obtain ⟨γ, hγ⟩ := chainStep_sound hC S hx Fc hSF ηc _ Q Q' (j + 1) hstep
    -- `p (j + 1) − Q'` is constant
    have hd : (p (j + 1) - M.sem Q')′ =
        algebraMap Kc E (-(((j + 2 : ℕ) : Kc)) * κ + (γ : Kc)) * M.sem ηc := by
      have := hrec (j + 1) (by omega) le_rfl
      rw [hκ] at this
      rw [Derivation.map_sub]
      have hγ' : (M.sem Q')′ = M.sem f - (γ : E) * M.sem ηc := by rw [← hγ]; ring
      rw [hγ', hf, sem_chainRHS]
      simp only [map_add, map_mul, map_neg, map_natCast, map_ratCast]
      rw [show ((j + 1 + 1 : ℕ) : E) = ((j + 2 : ℕ) : E) by push_cast; ring] at this ⊢
      linear_combination this
    have h0 := hnex _ (sub_mem (hp (j + 1)) (sem_mem hC S hx Fc hSF _)) _ hd
    rw [h0, map_zero, zero_mul] at hd
    obtain ⟨κ', hκ'⟩ := hconst _ hd
    obtain ⟨R, hR, hR1⟩ := ih (fun i h1 h2 ↦ hrec i h1 (by omega)) Q' ⟨κ', by
      rw [hκ']; ring⟩
    refine ⟨R, ?_, hR1⟩
    simp only [primChain, hstep, Option.bind_some]
    exact hR

end Chain

end Curves
