import RischTragerBronstein.Mixed.KQExpand
import RischTragerBronstein.Mixed.KELiouville
import RischTragerBronstein.Algebraic.SupBridge

/-!
# `b(x) y` with `y² = p(x)` over a logarithm, with simple poles at ordinary places

`S : SuperData C L` with `x′ = η ∈ C` (`x` a logarithm over the differential field `C`: no
`α` algebraic over `C` has `α′ = η`), `b = P(x)/(D(x) p(x)ˡ)`, `D = ∏_q (x − c_q)` with distinct
`c_q ∈ C`, `p(c_q) = β_q² ≠ 0`, and the residue of `b y dx` at `(c_q, β_q)` equal to `m_q ρ`
(`m_q ∈ ℕ`, `ρ ∈ C`): `P(c_q) β_q = m_q ρ (η − c_q′) R_q(c_q)`, `R_q = ∏_{q' ≠ q} (x − c_{q'}) pˡ`.

`kq_prep`: a Liouville form for `b y` can be normalized to `ℚ`-independent constants `d_j` and
logarithms `w_j` with no zeros or poles outside the points over the `c_q`, and at the points
`(c_q, β′)` over `c_q`, `(∑ d_j ord w_j) β_q = m_q ρ β′` (`residue_eq`).

The divisor `Γ = ∑ m_q (c_q, β_q)`:
* `kq_liouville_nontors`: if no multiple of `Γ − (deg Γ) ∞` is principal and some `m_q ≠ 0`, there
  is no Liouville form;
* `kq_liouville_tors`: if `W = W₀ + W₁ y` has divisor `N Γ − (N deg Γ) ∞`, then
  `b y = (a y)′ + e B y` with `W′/W = E + B y`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- `D = ∏_q (X − c_q)`. -/
noncomputable def dcP {r : ℕ} (c : Fin r → C) : C[X] := ∏ q, (X - Polynomial.C (c q))

/-- `∏_{q' ≠ q} (X − c_{q'})`. -/
noncomputable def dcR {r : ℕ} (c : Fin r → C) (q : Fin r) : C[X] :=
  ∏ q' ∈ Finset.univ.erase q, (X - Polynomial.C (c q'))

lemma dcP_eq {r : ℕ} (c : Fin r → C) (q : Fin r) :
    dcP c = (X - Polynomial.C (c q)) * dcR c q :=
  (Finset.mul_prod_erase _ (fun q' ↦ X - Polynomial.C (c q')) (Finset.mem_univ q)).symm

lemma dcR_eval_ne {r : ℕ} (c : Fin r → C) (hc : Function.Injective c) (q : Fin r) :
    ((dcR c q).map (algebraMap C K)).eval (algebraMap C K (c q)) ≠ 0 := by
  rw [dcR, Polynomial.map_prod, eval_prod, Finset.prod_ne_zero_iff]
  intro q' hq'
  rw [Polynomial.map_sub, map_X, Polynomial.map_C, eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact (Finset.mem_erase.mp hq').1 (hc ((algebraMap C K).injective h)).symm

lemma dcP_eval_ne {r : ℕ} (c : Fin r → C) (α : K) (hα : ∀ q, α ≠ algebraMap C K (c q)) :
    ((dcP c).map (algebraMap C K)).eval α ≠ 0 := by
  rw [dcP, Polynomial.map_prod, eval_prod, Finset.prod_ne_zero_iff]
  intro q _
  rw [Polynomial.map_sub, map_X, Polynomial.map_C, eval_sub, eval_X, eval_C, sub_ne_zero]
  exact hα q

lemma p_eval_ne (α β : K) (hβ : β ≠ 0) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (S.p.map (algebraMap C K)).eval α ≠ 0 := by
  rw [← hv]; exact pow_ne_zero _ hβ

/-- The divisor `Γ = ∑ m_q (c_q, β_q)`. -/
noncomputable def gammaQ {r : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) : K × K → ℕ :=
  fun Q ↦ ∑ q, if Q = (algebraMap C K (c q), algebraMap C K (β q)) then m q else 0

section Div

variable {r : ℕ} (c β : Fin r → C) (hc : Function.Injective c)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (hn2 : S.n = 2)

include hβ hn2 in
lemma over_cq (q : Fin r) (β' : K)
    (hv : β' ^ S.n = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q))) :
    β' = algebraMap C K (β q) ∨ β' = -algebraMap C K (β q) := by
  rw [eval_map, eval₂_at_apply, ← (hβ q).2, map_pow, hn2] at hv
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hv

include hβ in
lemma neg_ne_q (q : Fin r) : -algebraMap C K (β q) ≠ algebraMap C K (β q) :=
  neg_ne_self ((_root_.map_ne_zero _).mpr (hβ q).1)

include hc in
lemma gammaQ_at (q : Fin r) (b : K) :
    gammaQ c β m (algebraMap C K (c q), b) =
      if b = algebraMap C K (β q) then m q else 0 := by
  rw [gammaQ, Finset.sum_eq_single q]
  · simp [Prod.ext_iff]
  · intro q' _ hq'
    rw [if_neg]
    intro h
    exact hq' (hc ((algebraMap C K).injective (Prod.ext_iff.mp h).1)).symm
  · simp

lemma gammaQ_off (α b : K) (hα : ∀ q, α ≠ algebraMap C K (c q)) :
    gammaQ c β m (α, b) = 0 :=
  Finset.sum_eq_zero fun q _ ↦ by
    rw [if_neg]; intro h; exact hα q (Prod.ext_iff.mp h).1

/-- `∏_q (x − c_q)^{m_q}`. -/
noncomputable def pmE : C⟮S.x⟯⟮S.y⟯ := S.polyX (∏ q, (X - Polynomial.C (c q)) ^ m q)

lemma pmE_ne : S.pmE c m ≠ 0 := by
  rw [pmE]
  apply S.polyX_ne_zero
  exact Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)

end Div

section Logs

variable {r : ℕ} (c β : Fin r → C) (hc : Function.Injective c)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (hn2 : S.n = 2)
  (hcop : Nat.Coprime S.n S.p.natDegree)

/-- The orders of `z` are those of `lam ∑ m_q ((c_q, β_q) − (c_q, −β_q))`. -/
def OrdForm (z : C⟮S.x⟯⟮S.y⟯) (lam : ℚ) : Prop :=
  (∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → (∀ q, α ≠ algebraMap C K (c q)) →
    S.ordAt K z α β' = 0) ∧
  ∀ q, (S.ordAt K z (algebraMap C K (c q)) (algebraMap C K (β q)) : ℚ) = m q * lam ∧
    (S.ordAt K z (algebraMap C K (c q)) (-algebraMap C K (β q)) : ℚ) = -(m q * lam)

include hβ in
lemma over_cq_ne (q : Fin r) (β' : K)
    (hv : β' ^ S.n = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q))) : β' ≠ 0 := by
  intro h0
  rw [h0, zero_pow S.hn.ne', eval_map, eval₂_at_apply, ← (hβ q).2, map_pow] at hv
  exact pow_ne_zero _ ((_root_.map_ne_zero _).mpr (hβ q).1) hv.symm

lemma pmE_coe : ((S.pmE c m : C⟮S.x⟯⟮S.y⟯) : L) = aeval S.x (∏ q, (X - Polynomial.C (c q)) ^ m q) :=
  S.polyX_coe _

include hc hβ hn2 hcop in
/-- **With a witness `W` of `N Γ`, a logarithm of the form `lam Δ` contributes a rational multiple of
`W′/W` plus an element of `C(x)`.** -/
lemma kq_log_tors (ω : C[X]) (hx : S.x′ = aeval S.x ω) (N : ℕ) (hN : 0 < N)
    (W : C⟮S.x⟯⟮S.y⟯) (hW : W ≠ 0)
    (hWord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W α β' = N * gammaQ c β m (α, β'))
    (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) (lam : ℚ) (hform : S.OrdForm (K := K) c β m z lam) :
    ∃ (e : ℚ) (g : L), g ∈ C⟮S.x⟯ ∧ logDeriv (z : L) = (e : L) * logDeriv (W : L) + g := by
  set a : ℤ := lam.num with ha
  set D : ℕ := lam.den with hD
  have hDa : (D : ℚ) * lam = a := by rw [mul_comm]; exact Rat.mul_den_eq_num lam
  have hD0 : 0 < D := lam.den_pos
  set Pm := S.pmE c m with hPm
  have hPm0 : Pm ≠ 0 := S.pmE_ne c m
  set y1 := z ^ ((D * N : ℕ) : ℤ) * W ^ (-(2 * a)) * Pm ^ (a * N) with hy1
  have hA : z ^ ((D * N : ℕ) : ℤ) ≠ 0 := zpow_ne_zero _ hz
  have hB : W ^ (-(2 * a)) ≠ 0 := zpow_ne_zero _ hW
  have hC : Pm ^ (a * N) ≠ 0 := zpow_ne_zero _ hPm0
  have hy10 : y1 ≠ 0 := mul_ne_zero (mul_ne_zero hA hB) hC
  have h0 : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → S.ordAt K y1 α β' = 0 := by
    intro α β' hv
    rw [S.ordAt_mul hv (mul_ne_zero hA hB) hC, S.ordAt_mul hv hA hB, S.ordAt_zpow hv,
      S.ordAt_zpow hv, S.ordAt_zpow hv, hWord α β' hv]
    by_cases hα : ∃ q, α = algebraMap C K (c q)
    · obtain ⟨q, rfl⟩ := hα
      have hb' := S.over_cq_ne c β hβ q β' hv
      rw [hPm, pmE, S.ordAt_polyX_prod_at c hc m q β' hv hb', gammaQ_at c β hc m q β']
      rcases S.over_cq c β hβ hn2 q β' hv with rfl | rfl
      · rw [if_pos rfl]
        have h1 := (hform.2 q).1
        have : (((D * N : ℕ) : ℤ) * S.ordAt K z (algebraMap C K (c q)) (algebraMap C K (β q)) +
            -(2 * a) * ((N : ℤ) * (m q : ℤ)) + a * N * (m q : ℤ) : ℤ) = (0 : ℚ) := by
          push_cast
          rw [h1]
          linear_combination (N * (m q : ℚ)) * hDa
        exact_mod_cast this
      · rw [if_neg (S.neg_ne_q c β hβ q)]
        have h1 := (hform.2 q).2
        have : (((D * N : ℕ) : ℤ) * S.ordAt K z (algebraMap C K (c q)) (-algebraMap C K (β q)) +
            -(2 * a) * ((N : ℤ) * ((0 : ℕ) : ℤ)) + a * N * (m q : ℤ) : ℤ) = (0 : ℚ) := by
          push_cast
          rw [h1]
          linear_combination (-(N * (m q : ℚ))) * hDa
        exact_mod_cast this
    · push Not at hα
      rw [hform.1 α β' hv hα, gammaQ_off c β m α β' hα, hPm, pmE,
        S.ordAt_polyX_prod_off c m α β' hv hα]
      simp
  obtain ⟨γ, hγ⟩ := S.const_of_ordAt_zero K hcop y1 hy10 h0
  have hγ0 : γ ≠ 0 := fun h ↦ hy10 (Subtype.ext (by rw [hγ, h, map_zero]; rfl))
  have hWL : (W : L) ≠ 0 := fun h ↦ hW (Subtype.ext h)
  have hzL : (z : L) ≠ 0 := fun h ↦ hz (Subtype.ext h)
  have hPL : (Pm : L) ≠ 0 := fun h ↦ hPm0 (Subtype.ext h)
  have e1 : ((y1 : C⟮S.x⟯⟮S.y⟯) : L) =
      (z : L) ^ ((D * N : ℕ) : ℤ) * (W : L) ^ (-(2 * a)) * (Pm : L) ^ (a * N) := by
    have e1 : ((z ^ ((D * N : ℕ) : ℤ) : C⟮S.x⟯⟮S.y⟯) : L) = (z : L) ^ ((D * N : ℕ) : ℤ) :=
      map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val z _
    have e2 : ((W ^ (-(2 * a)) : C⟮S.x⟯⟮S.y⟯) : L) = (W : L) ^ (-(2 * a)) :=
      map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val W _
    have e3 : ((Pm ^ (a * N) : C⟮S.x⟯⟮S.y⟯) : L) = (Pm : L) ^ (a * N) :=
      map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val Pm _
    rw [hy1, IntermediateField.coe_mul, IntermediateField.coe_mul, e1, e2, e3]
  have hl := congrArg logDeriv (e1.symm.trans hγ)
  have hAL : (z : L) ^ ((D * N : ℕ) : ℤ) * (W : L) ^ (-(2 * a)) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hzL) (zpow_ne_zero _ hWL)
  rw [logDeriv_mul (a := (z : L) ^ ((D * N : ℕ) : ℤ) * (W : L) ^ (-(2 * a)))
      (b := (Pm : L) ^ (a * N)) hAL (zpow_ne_zero _ hPL),
    logDeriv_mul (a := (z : L) ^ ((D * N : ℕ) : ℤ)) (b := (W : L) ^ (-(2 * a)))
      (zpow_ne_zero _ hzL) (zpow_ne_zero _ hWL), logDeriv_zpow' _ hzL,
    logDeriv_zpow' _ hWL, logDeriv_zpow' _ hPL, logDeriv_algebraMap] at hl
  have hDN : ((D * N : ℕ) : L) ≠ 0 := by
    have : 0 < D * N := Nat.mul_pos hD0 hN
    exact_mod_cast this.ne'
  refine ⟨2 * a / (D * N : ℕ), (algebraMap C L (logDeriv γ) - (a * N : ℤ) * logDeriv (Pm : L)) /
    ((D * N : ℕ) : L), ?_, ?_⟩
  · have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW ω hx
    have hPmem : (Pm : L) ∈ C⟮S.x⟯ := by
      rw [hPm, S.pmE_coe]
      letI := algebraAdjoinSimple (F := C) S.x
      rw [← algebraMap_adjoinSimple (F := C) S.x]; exact SetLike.coe_mem _
    refine div_mem (sub_mem (IntermediateField.algebraMap_mem _ _) (mul_mem (intCast_mem _ _)
      (div_mem (hcl _ hPmem) hPmem))) (IntermediateField.natCast_mem _ _)
  · have hD' : (D : L) ≠ 0 := by exact_mod_cast hD0.ne'
    have hN' : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast at hl ⊢
    field_simp
    linear_combination hl

include hc hβ hn2 in
/-- **A logarithm of the form `lam Δ`, `lam ≠ 0`, makes `Γ` torsion.** -/
lemma kq_log_nontors (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) (lam : ℚ) (hlam : lam ≠ 0)
    (hform : S.OrdForm (K := K) c β m z lam) :
    ∃ N : ℕ, 0 < N ∧ S.IsPrincipalS K (gammaQ c β m) N := by
  set a : ℤ := lam.num with ha
  set D : ℕ := lam.den with hD
  have hDa : (D : ℚ) * lam = a := by rw [mul_comm]; exact Rat.mul_den_eq_num lam
  have ha0 : a ≠ 0 := Rat.num_ne_zero.mpr hlam
  set Pm := S.pmE c m with hPm
  have hPm0 : Pm ≠ 0 := S.pmE_ne c m
  set y1 := z ^ (D : ℤ) * Pm ^ a with hy1
  have hA : z ^ (D : ℤ) ≠ 0 := zpow_ne_zero _ hz
  have hC : Pm ^ a ≠ 0 := zpow_ne_zero _ hPm0
  have hy10 : y1 ≠ 0 := mul_ne_zero hA hC
  have hord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K y1 α β' = 2 * a * gammaQ c β m (α, β') := by
    intro α β' hv
    rw [S.ordAt_mul hv hA hC, S.ordAt_zpow hv, S.ordAt_zpow hv]
    by_cases hα : ∃ q, α = algebraMap C K (c q)
    · obtain ⟨q, rfl⟩ := hα
      have hb' := S.over_cq_ne c β hβ q β' hv
      rw [hPm, pmE, S.ordAt_polyX_prod_at c hc m q β' hv hb', gammaQ_at c β hc m q β']
      rcases S.over_cq c β hβ hn2 q β' hv with rfl | rfl
      · rw [if_pos rfl]
        have h1 := (hform.2 q).1
        have : ((D : ℤ) * S.ordAt K z (algebraMap C K (c q)) (algebraMap C K (β q)) +
            a * (m q : ℤ) : ℤ) = ((2 * a * (m q : ℤ) : ℤ) : ℚ) := by
          push_cast
          rw [h1]
          linear_combination ((m q : ℚ)) * hDa
        exact_mod_cast this
      · rw [if_neg (S.neg_ne_q c β hβ q)]
        have h1 := (hform.2 q).2
        have : ((D : ℤ) * S.ordAt K z (algebraMap C K (c q)) (-algebraMap C K (β q)) +
            a * (m q : ℤ) : ℤ) = ((2 * a * ((0 : ℕ) : ℤ) : ℤ) : ℚ) := by
          push_cast
          rw [h1]
          linear_combination (-(m q : ℚ)) * hDa
        exact_mod_cast this
    · push Not at hα
      rw [hform.1 α β' hv hα, gammaQ_off c β m α β' hα, hPm, pmE,
        S.ordAt_polyX_prod_off c m α β' hv hα]
      simp
  rcases lt_or_gt_of_ne ha0 with hneg | hpos
  · refine ⟨2 * (-a).toNat, by omega, y1⁻¹, inv_ne_zero hy10, fun α β' hv ↦ ?_, fun Q hQ ↦ ?_⟩
    · rw [S.ordAt_inv hv, hord α β' hv]
      have : (0 : ℤ) ≤ gammaQ c β m (α, β') := Int.natCast_nonneg _
      nlinarith
    · rw [S.ordAt_inv hQ, hord Q.1 Q.2 hQ]
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]
      ring
  · refine ⟨2 * a.toNat, by omega, y1, hy10, fun α β' hv ↦ ?_, fun Q hQ ↦ ?_⟩
    · rw [hord α β' hv]
      have : (0 : ℤ) ≤ gammaQ c β m (α, β') := Int.natCast_nonneg _
      positivity
    · rw [hord Q.1 Q.2 hQ]
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]

end Logs

section Log

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, α′ ≠ algebraMap C K η)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r : ℕ} (c β : Fin r → C) (hc : Function.Injective c)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (ρ : C)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hres : ∀ q, P.eval (c q) * β q = m q * ρ * (η - (c q)′) * (R q * S.p ^ l).eval (c q))
  (hpc : ∀ q, S.p.eval (c q) ≠ 0)

include hbP in
lemma kq_mulQ (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯) :
    (⟨b * S.y, hbm⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyX (D * S.p ^ l) =
      S.polyX P * AdjoinSimple.gen C⟮S.x⟯ S.y := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, S.polyX_coe, S.polyX_coe, AdjoinSimple.coe_gen,
    ← hbP]
  ring

include hx hK hgood hconstC hb hDR hRne hDoff hbP hpc in
/-- **The Liouville data, normalized**, with the raw residues at the poles. -/
theorem kq_prep0 (hn1 : 1 < S.n) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      (∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, (t j : C) * d j = 0 → ∀ j < k, t j = 0) ∧
      b * S.y = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (algebraMap C L (d j))′ = 0) ∧
      (∀ j (hj : j < k), ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
        (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K ⟨w j, (hw j hj).1⟩ α β' = 0) ∧
      ∀ q (β' : K), β' ^ S.n = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) →
        (∑ j ∈ Finset.range k, algebraMap C K (d j) *
          (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) β' : K) else 0)) *
            algebraMap C K ((η - (c q)′) * (R q * S.p ^ l).eval (c q)) =
              algebraMap C K (P.eval (c q)) * β' := by
  classical
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s cs u hcs (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd jj hjj))
  have hind' : ∀ t : ℕ → ℚ, ∑ jj ∈ Finset.range k, (t jj : C) * d' jj = 0 →
      ∀ jj < k, t jj = 0 := by
    intro t ht
    apply hind t
    rw [← map_zero (algebraMap C L), ← ht, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hw' : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : b * S.y = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * logDeriv (w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj)]
  have heq'' : b * S.y = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq']; rfl
  have hgα : ∀ α : K, α′ ≠ ((Polynomial.C η).map (algebraMap C K)).eval α := fun α ↦ by
    rw [Polynomial.map_C, eval_C]; exact hgood α
  have hQ := S.kq_mulQ P l b D hbP hbm
  refine ⟨k, d', w, hw', hind', heq', fun j hj ↦ by rw [hdd j hj]; exact hd j hj, ?_, ?_⟩
  · intro j hj α β' hvβ hα
    by_cases hβ0 : β' = 0
    · subst hβ0
      have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hvβ, zero_pow S.hn.ne']
      exact S.ordAt_logs_zero_classW (Polynomial.C η) hx hK k d' w hw' hind' v _ hv hbm heq'' b hb
        1 one_pos hn1 (by rw [pow_one]) α he (hgα α) j hj
    · -- `b y` is regular at `(α, β')`
      have hreg : 0 ≤ S.ordAt K ⟨b * S.y, hbm⟩ α β' := by
        have hR : ((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) =
            X ^ 0 * ((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) := by
          rw [pow_zero, one_mul]
        have hR0 : (((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α)).eval 0 ≠ 0 := by
          rw [eval_comp, eval_add, eval_X, eval_C, zero_add, Polynomial.map_mul, eval_mul,
            Polynomial.map_pow, eval_pow]
          exact mul_ne_zero (hDoff α hα) (pow_ne_zero _ (S.p_eval_ne α β' hβ0 hvβ))
        obtain ⟨h1, -⟩ := S.expand_pole _ P _ hQ α β' hβ0 hvβ 0 _ hR hR0
        rw [S.ordAt_nb _ α β' hβ0 hvβ]
        by_cases h0 : S.embXY α β' hβ0 hvβ ⟨b * S.y, hbm⟩ = 0
        · rw [h0, HahnSeries.order_zero]
        · by_contra hlt
          push Not at hlt
          exact (not_congr HahnSeries.coeff_order_eq_zero).mpr h0 (h1 _ (by simpa using hlt))
      exact S.ordAt_logs_zeroW (Polynomial.C η) hx hK k d' w hw' hind' v _ hv hbm heq'' α β' hvβ
        (hgα α) hreg j hj
  · intro q β' hvβ
    set α := algebraMap C K (c q) with hαdef
    have hpcK : (S.p.map (algebraMap C K)).eval α = algebraMap C K (S.p.eval (c q)) := by
      rw [hαdef, eval_map, eval₂_at_apply]
    have hβ0 : β' ≠ 0 := by
      intro h0
      rw [h0, zero_pow S.hn.ne', hpcK] at hvβ
      exact hpc q ((algebraMap C K).injective (by rw [← hvβ, map_zero]))
    have hα' : α′ = algebraMap C K (c q)′ := hK _
    have hRc : ((R q * S.p ^ l).map (algebraMap C K)).eval α =
        algebraMap C K ((R q * S.p ^ l).eval (c q)) := by
      rw [hαdef, eval_map, eval₂_at_apply]
    have hR : ((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) =
        X ^ 1 * ((R q * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) := by
      rw [hDR q, mul_assoc, Polynomial.map_mul (p := X - Polynomial.C (c q)), mul_comp,
        Polynomial.map_sub, map_X, Polynomial.map_C, sub_comp, X_comp, C_comp, pow_one, ← hαdef,
        add_sub_cancel_right]
    have hR0 : (((R q * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α)).eval 0 ≠ 0 := by
      rw [eval_comp, eval_add, eval_X, eval_C, zero_add, Polynomial.map_mul, eval_mul,
        Polynomial.map_pow, eval_pow]
      exact mul_ne_zero (by rw [eval_map, eval₂_at_apply]; exact (_root_.map_ne_zero _).mpr (hRne q)) (pow_ne_zero _ (S.p_eval_ne α β' hβ0 hvβ))
    obtain ⟨h1, h2⟩ := S.expand_pole _ P _ hQ α β' hβ0 hvβ 1 _ hR hR0
    have h3 := S.ordAt_logs_resW (Polynomial.C η) hx hK k d' w hw' v _ hv hbm heq'' α β' hβ0 hvβ
      (hgα α) (fun kk hkk ↦ h1 kk (by push_cast; omega))
    rw [Polynomial.map_C, eval_C, hα'] at h3
    rw [eval_comp, eval_add, eval_X, eval_C, zero_add, hRc] at h2
    have hPc : (P.map (algebraMap C K)).eval α = algebraMap C K (P.eval (c q)) := by
      rw [hαdef, eval_map, eval₂_at_apply]
    rw [hPc, show (-((1 : ℕ) : ℤ)) = -1 by norm_num, ← h3] at h2
    rw [map_mul, map_sub]
    linear_combination h2

include hx hK hgood hconstC hb hDR hRne hDoff hbP hpc in
/-- **The residues are constant**: if `b y` has an elementary integral, then at each pole,
`P(c)² p(c) = ζ ((η − c′) (R pˡ)(c))²` with `ζ′ = 0` (`ζ` the square of the residue). -/
theorem kq_resid_const (hn2 : S.n = 2) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) (q : Fin r) :
    ∃ ζ : C, ζ′ = 0 ∧ (P.eval (c q)) ^ 2 * S.p.eval (c q) =
      ζ * ((η - (c q)′) * (R q * S.p ^ l).eval (c q)) ^ 2 := by
  classical
  obtain ⟨k, d, w, hw, -, -, hdc, -, hraw⟩ :=
    S.kq_prep0 (K := K) η hx hK hgood hconstC c P l b hb D R hDR hRne hDoff hbP hpc (by omega) hbm
      s cs u hcs hu v hv heq
  obtain ⟨β', hβ'⟩ := IsAlgClosed.exists_pow_nat_eq
    ((S.p.map (algebraMap C K)).eval (algebraMap C K (c q))) S.hn
  have h := hraw q β' hβ'
  set o : ℕ → ℤ := fun j ↦ if hj : j < k then
    S.ordAt K ⟨w j, (hw j hj).1⟩ (algebraMap C K (c q)) β' else 0 with ho
  set σ : C := ∑ j ∈ Finset.range k, d j * (o j : C) with hσ
  have hSm : (∑ j ∈ Finset.range k, algebraMap C K (d j) *
      (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) β' : K) else 0)) =
      algebraMap C K σ := by
    rw [hσ, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_intCast]
    by_cases hj : j < k <;> simp [ho, hj]
  rw [hSm] at h
  have hd0 : ∀ j < k, (d j)′ = 0 := fun j hj ↦ by
    have := hdc j hj
    rw [deriv_algebraMap] at this
    exact (algebraMap C L).injective (by rw [this, map_zero])
  refine ⟨σ ^ 2, ?_, ?_⟩
  · have : σ′ = 0 := by
      rw [hσ, map_sum]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      rw [Derivation.leibniz, hd0 j (Finset.mem_range.mp hj), Derivation.map_intCast]
      simp
    rw [Derivation.leibniz_pow, this, smul_zero, smul_zero]
  · apply (algebraMap C K).injective
    have h2 := congrArg (· ^ 2) h
    have hβ2 : β' ^ 2 = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := by
      rw [← hn2]; exact hβ'
    rw [mul_pow, mul_pow, hβ2, eval_map, eval₂_at_apply] at h2
    simp only [map_mul, map_pow]
    rw [← map_pow, ← map_pow] at h2
    simp only [map_mul, map_pow] at h2 ⊢
    linear_combination -h2

include hx hK hgood hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **The Liouville data, normalized**, with the residues at the poles. -/
theorem kq_prep (hn1 : 1 < S.n) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      (∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, (t j : C) * d j = 0 → ∀ j < k, t j = 0) ∧
      b * S.y = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (algebraMap C L (d j))′ = 0) ∧
      (∀ j (hj : j < k), ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
        (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K ⟨w j, (hw j hj).1⟩ α β' = 0) ∧
      ∀ q (β' : K), β' ^ S.n = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) →
        (∑ j ∈ Finset.range k, algebraMap C K (d j) *
          (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) β' : K) else 0)) *
            algebraMap C K (β q) = algebraMap C K (m q * ρ) * β' := by
  have hpc : ∀ q, S.p.eval (c q) ≠ 0 := fun q h0 ↦ by
    have := (hβ q).2
    rw [h0] at this
    exact (hβ q).1 (pow_eq_zero_iff S.hn.ne' |>.mp this)
  obtain ⟨k, d, w, hw, hind, heq', hdc, hzero, hraw⟩ :=
    S.kq_prep0 η hx hK hgood hconstC c P l b hb D R hDR hRne hDoff hbP hpc hn1 hbm s cs u hcs hu v
      hv heq
  refine ⟨k, d, w, hw, hind, heq', hdc, hzero, fun q β' hvβ ↦ ?_⟩
  have h := hraw q β' hvβ
  have hne : algebraMap C K ((η - (c q)′) * (R q * S.p ^ l).eval (c q)) ≠ 0 := by
    refine (_root_.map_ne_zero _).mpr (mul_ne_zero (fun h0 ↦ ?_) ?_)
    · apply hgood (algebraMap C K (c q))
      rw [hK, sub_eq_zero.mp h0]
    · rw [eval_mul, eval_pow]
      exact mul_ne_zero (hRne q) (pow_ne_zero _ (hpc q))
  refine mul_right_cancel₀ hne ?_
  have hr := congrArg (algebraMap C K) (hres q)
  rw [mul_assoc, mul_comm (algebraMap C K (β q)), ← mul_assoc, h]
  simp only [map_mul, map_sub, map_natCast] at hr ⊢
  linear_combination β' * hr

include hx hK hgood hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **The logarithms are rational multiples of `Δ = ∑ m_q ((c_q, β_q) − (c_q, −β_q))`.** -/
theorem kq_core (hn2 : S.n = 2) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      b * S.y = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (algebraMap C L (d j))′ = 0) ∧
      ∃ lam : ℕ → ℚ, (∀ j (hj : j < k), S.OrdForm (K := K) c β m ⟨w j, (hw j hj).1⟩ (lam j)) ∧
        ((∃ q, m q ≠ 0) → ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam j : K) =
          algebraMap C K ρ) := by
  classical
  obtain ⟨k, d, w, hw, hind, heq', hdc, hzero, hresid⟩ :=
    S.kq_prep η hx hK hgood hconstC c β hc hβ m ρ P l b hb D R hDR hRne hDoff hbP hres (by omega) hbm s cs u hcs hu v
      hv heq
  refine ⟨k, d, w, hw, heq', hdc, ?_⟩
  have hindK : ∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, algebraMap C K (d j) * (t j : K) = 0 →
      ∀ j < k, t j = 0 := by
    intro t ht
    apply hind t
    apply (algebraMap C K).injective
    rw [map_zero, ← ht, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_ratCast, mul_comm]
  have hvP : ∀ q, (algebraMap C K (β q)) ^ S.n =
      (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := fun q ↦ by
    rw [eval_map, eval₂_at_apply, ← (hβ q).2, map_pow]
  have hvM : ∀ q, (-algebraMap C K (β q)) ^ S.n =
      (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := fun q ↦ by
    rw [hn2, neg_sq, ← hn2]; exact hvP q
  -- the orders at the two points over `c_q`
  set oP : Fin r → ℕ → ℤ := fun q j ↦ if h : j < k then
    S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (algebraMap C K (β q)) else 0 with hoP
  set oM : Fin r → ℕ → ℤ := fun q j ↦ if h : j < k then
    S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (-algebraMap C K (β q)) else 0 with hoM
  have hβK : ∀ q, algebraMap C K (β q) ≠ 0 := fun q ↦ (_root_.map_ne_zero _).mpr (hβ q).1
  have hsP : ∀ q, ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP q j : ℚ) : K) =
      algebraMap C K (m q * ρ) := fun q ↦ by
    have h := hresid q _ (hvP q)
    refine mul_right_cancel₀ (hβK q) ?_
    rw [← h]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hoP]
    split_ifs <;> simp
  have hsM : ∀ q, ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oM q j : ℚ) : K) =
      -algebraMap C K (m q * ρ) := fun q ↦ by
    have h := hresid q _ (hvM q)
    refine mul_right_cancel₀ (hβK q) ?_
    rw [neg_mul, ← mul_neg, ← h]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hoM]
    split_ifs <;> simp
  by_cases hm : ∃ q, m q ≠ 0
  · obtain ⟨q0, hq0⟩ := hm
    have hq0K : ((m q0 : ℚ) : K) ≠ 0 := by exact_mod_cast hq0
    set lam : ℕ → ℚ := fun j ↦ (oP q0 j : ℚ) / m q0 with hlam
    have hsl : ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam j : K) = algebraMap C K ρ := by
      have h := hsP q0
      simp only [hlam, Rat.cast_div, Rat.cast_natCast]
      rw [map_mul, map_natCast] at h
      have : ∑ j ∈ Finset.range k, algebraMap C K (d j) * (((oP q0 j : ℚ) : K) / (m q0 : K)) =
          (∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP q0 j : ℚ) : K)) / (m q0 : K) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [this, h]
      field_simp
    refine ⟨lam, fun j hj ↦ ⟨fun α β' hv hα ↦ hzero j hj α β' hv hα, fun q ↦ ?_⟩, fun _ ↦ hsl⟩
    have hP := hindK (fun j ↦ (oP q j : ℚ) - m q * lam j) (by
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, mul_sub, Finset.sum_sub_distrib]
      rw [hsP q]
      have : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((m q : K) * (lam j : K)) =
          (m q : K) * ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam j : K) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [this, hsl, map_mul, map_natCast, sub_self]) j hj
    have hM := hindK (fun j ↦ (oM q j : ℚ) + m q * lam j) (by
      simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, mul_add, Finset.sum_add_distrib]
      rw [hsM q]
      have : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((m q : K) * (lam j : K)) =
          (m q : K) * ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam j : K) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [this, hsl, map_mul, map_natCast, neg_add_cancel]) j hj
    simp only [hoP, hoM, dif_pos hj] at hP hM
    constructor <;> linarith
  · push Not at hm
    refine ⟨fun _ ↦ 0, fun j hj ↦ ⟨fun α β' hv hα ↦ hzero j hj α β' hv hα, fun q ↦ ?_⟩,
      fun h ↦ absurd h (by push Not; exact hm)⟩
    have hP := hindK (fun j ↦ (oP q j : ℚ)) (by rw [hsP q, hm q]; simp) j hj
    have hM := hindK (fun j ↦ (oM q j : ℚ)) (by rw [hsM q, hm q]; simp) j hj
    simp only [hoP, hoM, dif_pos hj] at hP hM
    simp [hP, hM, hm q]

include hx hK hgood hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **Without torsion of `Γ`, and with a non-zero residue, there is no Liouville form.** -/
theorem kq_liouville_nontors (hn2 : S.n = 2)
    (hnt : ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaQ c β m) N)
    (hm : ∃ q, m q ≠ 0) (hρ : ρ ≠ 0) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) : False := by
  obtain ⟨k, d, w, hw, -, -, lam, hform, hsum⟩ :=
    S.kq_core (K := K) η hx hK hgood hconstC c β hc hβ m ρ P l b hb D R hDR hRne hDoff hbP hres hn2 hbm s cs u hcs hu
      v hv heq
  have hs := hsum hm
  obtain ⟨j, hj, hlj⟩ : ∃ j < k, lam j ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hρ
    apply (algebraMap C K).injective
    rw [← hs, map_zero]
    exact Finset.sum_eq_zero fun j hj ↦ by rw [hno j (Finset.mem_range.mp hj)]; simp
  obtain ⟨N, hN, hP⟩ := S.kq_log_nontors c β hc hβ m hn2 ⟨w j, (hw j hj).1⟩
    (fun h ↦ (hw j hj).2 (congrArg Subtype.val h)) (lam j) hlj (hform j hj)
  exact hnt N hN hP

include hx hK hgood hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **With a witness `W = W₀ + W₁ y` of `N Γ`, a Liouville form for `b y` forces
`b y = (a y)′ + e B y`**, `W′/W = E + B y`. -/
theorem kq_liouville_tors (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree)
    (N : ℕ) (hN : 0 < N) (W : C⟮S.x⟯⟮S.y⟯) (hW : W ≠ 0)
    (hWord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W α β' = N * gammaQ c β m (α, β'))
    (W0 W1 : L) (hW0 : W0 ∈ C⟮S.x⟯) (hW1 : W1 ∈ C⟮S.x⟯) (hWe : (W : L) = W0 + W1 * S.y)
    (hNm : W0 ^ 2 - W1 ^ 2 * aeval S.x S.p ≠ 0) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : C, (algebraMap C L e)′ = 0 ∧ b * S.y = (a * S.y)′ + algebraMap C L e *
      ((W0 * (W1′ + W1 * (aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) /
        ((S.n : L) * aeval S.x S.p))) - W0′ * W1) / (W0 ^ 2 - W1 ^ 2 * aeval S.x S.p) * S.y) := by
  classical
  obtain ⟨k, d, w, hw, heq', hdc, lam, hform, -⟩ :=
    S.kq_core (K := K) η hx hK hgood hconstC c β hc hβ m ρ P l b hb D R hDR hRne hDoff hbP hres hn2 hbm s cs u hcs hu
      v hv heq
  have hl : ∀ j < k, ∃ (e : ℚ) (g : L), g ∈ C⟮S.x⟯ ∧
      logDeriv (w j) = (e : L) * logDeriv (W : L) + g := fun j hj ↦
    S.kq_log_tors c β hc hβ m hn2 hcop (Polynomial.C η) hx N hN W hW hWord ⟨w j, (hw j hj).1⟩
      (fun h ↦ (hw j hj).2 (congrArg Subtype.val h)) (lam j) (hform j hj)
  choose! e g hg hℓ using hl
  set gs : L := ∑ j ∈ Finset.range k, algebraMap C L (d j) * g j
  set es : C := ∑ j ∈ Finset.range k, d j * (e j : C)
  have hgs : gs ∈ C⟮S.x⟯ := sum_mem fun j hj ↦
    mul_mem (IntermediateField.algebraMap_mem _ _) (hg j (Finset.mem_range.mp hj))
  have hsum : ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) =
      gs + algebraMap C L es * logDeriv (W : L) := by
    rw [map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [hℓ j (Finset.mem_range.mp hj), map_mul, map_ratCast]; ring
  have hes : (algebraMap C L es)′ = 0 := by
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [map_mul, map_ratCast, Derivation.leibniz, hdc j (Finset.mem_range.mp hj),
      Tower.NestP.deriv_ratCastK (K := L) (e j)]
    simp
  rw [hsum] at heq'
  set P' := aeval S.x S.p with hP
  set r := aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) / ((S.n : L) * P')
    with hr
  have hy2 : S.y ^ 2 = P' := by rw [← hn2]; exact S.hy
  have hyd : S.y′ = r * S.y := by
    rw [S.deriv_yW (Polynomial.C η) hx, hr]; ring
  have hab := logDeriv_ab (y := S.y) W0 W1 P' r hy2 hyd hNm
  rw [hWe, hab] at heq'
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW (Polynomial.C η) hx
  have hrm : r ∈ C⟮S.x⟯ := S.r_memW (Polynomial.C η) hx
  have hPm : P' ∈ C⟮S.x⟯ := by
    letI := algebraAdjoinSimple (F := C) S.x
    rw [hP, ← algebraMap_adjoinSimple (F := C) S.x S.p]; exact SetLike.coe_mem _
  have hNm' : W0 ^ 2 - W1 ^ 2 * P' ∈ C⟮S.x⟯ :=
    sub_mem (pow_mem hW0 2) (mul_mem (pow_mem hW1 2) hPm)
  set B := (W0 * (W1′ + W1 * r) - W0′ * W1) / (W0 ^ 2 - W1 ^ 2 * P') with hB
  have hBm : B ∈ C⟮S.x⟯ := div_mem (sub_mem (mul_mem hW0 (add_mem (hcl _ hW1) (mul_mem hW1 hrm)))
    (mul_mem (hcl _ hW0) hW1)) hNm'
  set E := (W0 * W0′ - W1 * (W1′ + W1 * r) * P') / (W0 ^ 2 - W1 ^ 2 * P') with hE
  have hEm : E ∈ C⟮S.x⟯ := div_mem (sub_mem (mul_mem hW0 (hcl _ hW0))
    (mul_mem (mul_mem hW1 (add_mem (hcl _ hW1) (mul_mem hW1 hrm))) hPm)) hNm'
  have heq2 : (b - algebraMap C L es * B) * S.y ^ 1 = v′ + (gs + algebraMap C L es * E) := by
    rw [pow_one]; linear_combination heq'
  obtain ⟨a, ha, hae⟩ := S.exact_of_even (Polynomial.C η) hx 1 one_pos (by omega) _
    (sub_mem hb (mul_mem (IntermediateField.algebraMap_mem _ _) hBm)) v hv _
    (add_mem hgs (mul_mem (IntermediateField.algebraMap_mem _ _) hEm)) heq2
  refine ⟨a, ha, es, hes, ?_⟩
  simp only [pow_one] at hae
  linear_combination hae

end Log

end SuperData

end Differential
