import RischTragerBronstein.Mixed.NKWitET

/-!
# Multiplicative independence gives the linear independence of the logarithmic derivatives

The decisions with several places at infinity (`nk_decidesInfVGPW` …) assume units whose
logarithmic derivatives are linearly independent over the constants of the code field modulo
`Fₘ₊₁`. Here:

* `codeVals_const_rat`: the constants among the code values are rational (level `0`: a constant
  `W(x, y)/Q(x)` with `deg_y W < n` is a constant polynomial, by the minimality of the curve
  equation; level `m + 1`: `P(t)/Q(t)` constant forces `P = c Q`, by transcendence of `t`);
* `hli_of_mult`: for units certified by `unitsC` (`uᵢ′/uᵢ` with zero trace), multiplicative
  independence modulo the constants implies that linear independence: a rational relation
  `∑ qᵢ uᵢ′/uᵢ = f ∈ Fₘ₊₁` has `f = τ(f) = 0` by the trace, so `∏ uᵢ^{D qᵢ}` is constant.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Constant code values of level `0` are rational.** -/
lemma codeVals0_const_rat (h : T.Tr 0) (z : L) (hz : z ∈ T.codeVals 0 h) (hz' : z′ = 0) :
    ∃ q : ℚ, z = q := by
  classical
  obtain ⟨a, rfl⟩ := hz
  set S := T.S
  set M := cM T.hC T.S T.hx Fc T.hSF
  have hv : (((T.MP 0 h).sem a : T.F 0) : L) = M.sem a := T.sem_MP 0 h a
  rw [hv] at hz' ⊢
  set a' := cvRed Fc a with ha'
  have hred : M.sem a' = M.sem a := sem_cvRed T.hC T.S T.hx Fc T.hSF a
  obtain ⟨c0, hc0⟩ := T.hconst _ hz'
  have hW := eval_codeW T.hC T.S T.hx Fc T.hSF a'
  rw [hred, ← hc0] at hW
  set W : Cc[X][X] := (toB (codeW a')).map (mapRingHom (algebraMap ℚ Cc)) with hWdef
  set Qc : Cc[X] := (toPoly (codeQ a')).map (algebraMap ℚ Cc) with hQc
  have hQ0 : Qc ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ Cc).injective).mpr (codeQ_ne_zero a')
  -- the curve degree is positive
  have hn : 0 < S.F.natDegree := by
    by_contra h0
    have hF1 : S.F = 1 := Polynomial.eq_one_of_monic_natDegree_zero S.monic (by omega)
    have := S.root
    rw [hF1] at this
    simp at this
  set G : Cc[X][X] := W - Polynomial.C (Polynomial.C c0 * Qc) with hG
  have hGdeg : G.natDegree < S.F.natDegree := by
    have hWd : W.natDegree < S.F.natDegree := by
      have h1 := natDegree_toB_le_len' (codeW a')
      have h2 : a'.length ≤ S.F.natDegree := length_cvRed T.hC T.S T.hx Fc T.hSF a
      rw [length_codeW] at h1
      have h3 : W.natDegree ≤ (toB (codeW a')).natDegree := natDegree_map_le
      omega
    calc G.natDegree ≤ max W.natDegree (Polynomial.C (Polynomial.C c0 * Qc)).natDegree :=
          natDegree_sub_le _ _
      _ < S.F.natDegree := by rw [natDegree_C]; omega
  have hGev : (G.map (aeval S.x).toRingHom).eval S.y = 0 := by
    rw [hG, Polynomial.map_sub, eval_sub, Polynomial.map_C, eval_C, hW]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, aeval_C]
    ring
  have hG0 := S.irr G hGdeg hGev
  have hWc : W = Polynomial.C (Polynomial.C c0 * Qc) := sub_eq_zero.mp hG0
  obtain ⟨k, hk⟩ : ∃ k, Qc.coeff k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hQ0 (Polynomial.ext fun k ↦ by rw [hall k, coeff_zero])
  have hcoef := congrArg (fun P : Cc[X][X] ↦ (P.coeff 0).coeff k) hWc
  simp only [coeff_C_zero, coeff_C_mul] at hcoef
  rw [hWdef, Polynomial.coeff_map, coe_mapRingHom, Polynomial.coeff_map] at hcoef
  rw [hQc, Polynomial.coeff_map] at hk hcoef
  refine ⟨((toB (codeW a')).coeff 0).coeff k / (toPoly (codeQ a')).coeff k, ?_⟩
  have hk' : (toPoly (codeQ a')).coeff k ≠ 0 := fun h0 ↦ hk (by rw [h0, map_zero])
  have hc0' : c0 = algebraMap ℚ Cc (((toB (codeW a')).coeff 0).coeff k /
      (toPoly (codeQ a')).coeff k) := by
    rw [map_div₀, hcoef]
    field_simp
  rw [← hc0, hc0', ← IsScalarTower.algebraMap_apply, eq_ratCast]

/-- **Constant code values of level `m + 1` are code values of level `m`.** -/
lemma codeVals_const_succ (m : ℕ) (h : T.Tr (m + 1)) (z : L) (hz : z ∈ T.codeVals (m + 1) h)
    (hz' : z′ = 0) : z ∈ T.codeVals m h.of_succ := by
  classical
  obtain ⟨c, rfl⟩ := hz
  obtain ⟨c0, hc0⟩ := T.hconst _ hz'
  set M := T.MP m h.of_succ
  set P := GPoly.toPoly M c.1
  set Q := GPoly.toPoly M c.2
  have hsem : (T.MP (m + 1) h).sem c = T.phi m P / T.phi m Q := T.sem_MP_succ m h c
  by_cases hQ : T.phi m Q = 0
  · rw [hsem, hQ, div_zero]
    exact (T.codeVals m h.of_succ).zero_mem
  have hQ' : Q ≠ 0 := fun h0 ↦ hQ (by rw [h0, map_zero])
  set zF : T.F m := algebraMap Cc (T.F m) c0
  have hzF : ((T.MP (m + 1) h).sem c : L) = ((zF : T.F m) : L) := by rw [← hc0]; rfl
  have hPQ : T.phi m P = T.phi m (Polynomial.C zF * Q) := by
    rw [map_mul, T.phi_C]
    have : T.phi m P = (T.MP (m + 1) h).sem c * T.phi m Q := by rw [hsem, div_mul_cancel₀ _ hQ]
    rw [this]
    apply Subtype.ext
    push_cast
    rw [hzF]
    rfl
  have hPeq := T.phi_injective (h m (by omega)) hPQ
  obtain ⟨k, hk⟩ : ∃ k, Q.coeff k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hQ' (Polynomial.ext fun k ↦ by rw [hall k, coeff_zero])
  have hck := congrArg (fun p : (T.F m)[X] ↦ p.coeff k) hPeq
  simp only [coeff_C_mul] at hck
  have hzk : zF = P.coeff k / Q.coeff k := by rw [hck]; field_simp
  rw [hzF, hzk]
  push_cast
  rw [coeff_toPoly_sem, coeff_toPoly_sem]
  exact div_mem (T.sem_mem_codeVals m h.of_succ _) (T.sem_mem_codeVals m h.of_succ _)

/-- **The constants among the code values are rational.** -/
theorem codeVals_const_rat : ∀ (m : ℕ) (h : T.Tr m) (z : L), z ∈ T.codeVals m h → z′ = 0 →
    ∃ q : ℚ, z = q
  | 0, h, z, hz, hz' => T.codeVals0_const_rat h z hz hz'
  | m + 1, h, z, hz, hz' => codeVals_const_rat m h.of_succ z (T.codeVals_const_succ m h z hz hz') hz'

end MTower

/-- **The trace kills a rational relation**: if every row has zero trace and the combination of
the rows is `f` in the coordinate `0` only, then `f = 0` (`s₀ = n ≠ 0`). -/
lemma trace_kill {F : Type*} [Field F] [CharZero F] {k n : ℕ} (hn : 0 < n) (q : Fin k → ℚ)
    (gs : Fin k → ℕ → F) (sj : ℕ → F) (hs0 : sj 0 = n)
    (hτ : ∀ i, ∑ j ∈ Finset.range n, gs i j * sj j = 0) (f : F)
    (hco : ∀ j < n, ∑ i, (q i : F) * gs i j = if j = 0 then f else 0) : f = 0 := by
  have h1 : ∑ i, (q i : F) * ∑ j ∈ Finset.range n, gs i j * sj j = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by rw [hτ i, mul_zero]
  have h2 : ∑ i, (q i : F) * ∑ j ∈ Finset.range n, gs i j * sj j =
      ∑ j ∈ Finset.range n, (∑ i, (q i : F) * gs i j) * sj j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h2, Finset.sum_congr rfl fun j hj ↦ by rw [hco j (Finset.mem_range.mp hj)]] at h1
  rw [Finset.sum_eq_single 0 (fun j _ hj ↦ by rw [if_neg hj, zero_mul])
    (fun h0 ↦ absurd (Finset.mem_range.mpr hn) h0), if_pos rfl, hs0] at h1
  have hn' : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_eq_zero.mp h1).resolve_right hn'

/-- **A rational relation among logarithmic derivatives** of elements that are multiplicatively
independent modulo the constants is trivial. -/
lemma rat_logDeriv_rel {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L] {k : ℕ}
    (u : Fin k → L) (hu : ∀ i, u i ≠ 0) (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap K L))
    (hmult : ∀ a : Fin k → ℤ, (∃ c : K, ∏ i, u i ^ a i = algebraMap K L c) → a = 0)
    (q : Fin k → ℚ) [CharZero L] (hrel : ∑ i, (q i : L) * logDeriv (u i) = 0) : q = 0 := by
  classical
  set D : ℕ := ∏ i, (q i).den with hD
  have hdvd : ∀ i, (q i).den ∣ D := fun i ↦ Finset.dvd_prod_of_mem (fun j ↦ (q j).den)
    (Finset.mem_univ i)
  choose e he using hdvd
  set a : Fin k → ℤ := fun i ↦ (q i).num * (e i : ℤ) with ha
  have hD0 : (D : ℚ) ≠ 0 := by
    rw [hD]; push_cast
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ by exact_mod_cast (q i).den_ne_zero
  have haq : ∀ i, (a i : ℚ) = q i * D := fun i ↦ by
    rw [ha, he i]; push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have hw0 : ∏ i, u i ^ a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu i)
  have hlog : logDeriv (∏ i, u i ^ a i) = 0 := by
    rw [logDeriv_prod _ _ _ fun i _ ↦ zpow_ne_zero _ (hu i)]
    have e1 : ∀ i, logDeriv (u i ^ a i) = ((a i : ℚ) : L) * logDeriv (u i) := fun i ↦ by
      rw [logDeriv_zpow' _ (hu i)]; push_cast; ring
    simp only [e1, haq]
    have : ∑ i, ((q i * D : ℚ) : L) * logDeriv (u i) = (D : L) * ∑ i, (q i : L) * logDeriv (u i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
    rw [this, hrel, mul_zero]
  have hder : (∏ i, u i ^ a i)′ = 0 := by
    have := hlog
    rw [logDeriv, div_eq_zero_iff] at this
    exact this.resolve_right hw0
  obtain ⟨c, hc⟩ := hconst _ hder
  have ha0 := hmult a ⟨c, hc.symm⟩
  funext i
  have hai := congrFun ha0 i
  have : q i * D = 0 := by rw [← haq, hai]; simp
  exact (mul_eq_zero.mp this).resolve_right hD0

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Multiplicative independence gives the linear-independence hypothesis** (abstract units):
rows `glsᵢ` with zero trace that are the logarithmic derivatives of `uᵢ ≠ 0`, multiplicatively
independent modulo the constants: no non-trivial combination with constant code values as
coefficients lies in `Fₘ₊₁`. -/
theorem hli_of_mult_core (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (hn0 : 0 < Pp.length)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (gls : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ Pp.length)
    (htau : ∀ i < gls.length, (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s) =
      true)
    (u : Fin gls.length → L)
    (hui : ∀ i : Fin gls.length, u i ≠ 0 ∧ T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (hmult : ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i, u i ^ a i = algebraMap Cc L c) → a = 0) :
    ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) → (∀ i, (c i)′ = 0) →
      (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0 := by
  classical
  intro c hcV hc' ⟨f, hf⟩
  choose q hq using fun i ↦ T.codeVals_const_rat (m + 1) h1 (c i) (hcV i) (hc' i)
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set n := Pp.length with hn
  set G : Fin gls.length → ℕ → T.F (m + 1) := fun i j ↦ M1.sem ((gls.getD i []).getD j O1.zero)
    with hG
  have hev : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) =
      ∑ j ∈ Finset.range n, (G i j : L) * θ ^ j := fun i ↦
    T.evθ_list_le m h1 θ _ n (hlen i i.2)
  -- the coordinates of the relation
  have hco : ∀ j < n, ∑ i, (q i : T.F (m + 1)) * G i j = if j = 0 then f else 0 := by
    have e1 : ∑ j ∈ Finset.range n, (((∑ i, (q i : T.F (m + 1)) * G i j : T.F (m + 1)) : L) *
        θ ^ j) = (f : L) := by
      rw [← hf]
      simp only [hev, Finset.mul_sum]
      push_cast
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hq i]; ring
    have e2 : ∑ j ∈ Finset.range n, (((if j = 0 then f else 0 : T.F (m + 1)) : L) * θ ^ j) =
        (f : L) := by
      rw [Finset.sum_eq_single 0 (fun j _ hj ↦ by rw [if_neg hj]; simp)
        (fun h0 ↦ absurd (Finset.mem_range.mpr hn0) h0), if_pos rfl, pow_zero, mul_one]
    have hz := hind (fun j ↦ ∑ i, (q i : T.F (m + 1)) * G i j - if j = 0 then f else 0) (by
      simp only [AddSubgroupClass.coe_sub, sub_mul, Finset.sum_sub_distrib]
      rw [e1, e2, sub_self])
    intro j hj
    exact sub_eq_zero.mp (hz j hj)
  -- the traces of the rows vanish
  have hτ : ∀ i : Fin gls.length, ∑ j ∈ Finset.range n,
      G i j * M1.sem (s.getD j O1.zero) = 0 := by
    intro i
    have h0 := ((M1.isZero_iff _).mp (htau i i.2))
    rw [T.sem_nkTau m n h1] at h0
    have hn' : (n : T.F (m + 1)) ≠ 0 := by exact_mod_cast hn0.ne'
    exact (mul_eq_zero.mp h0).resolve_right (inv_ne_zero hn')
  have hf0 : f = 0 := trace_kill hn0 q G (fun j ↦ M1.sem (s.getD j O1.zero))
    (T.traceW_sound m h1 Pp θ hP dθ wθ s hs).1 hτ f hco
  -- a rational relation among the logarithmic derivatives
  have hrel : ∑ i, (q i : L) * logDeriv (u i) = 0 := by
    have := hf
    rw [hf0] at this
    simp only [ZeroMemClass.coe_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hq i, logDeriv, (hui i).2]
  have hq0 := rat_logDeriv_rel u (fun i ↦ (hui i).1) T.hconst hmult q hrel
  funext i
  rw [hq i, congrFun hq0 i]
  simp

/-- **`hli_of_mult_core` for the units of `unitsC`.** -/
theorem hli_of_mult (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (hn0 : 0 < Pp.length)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true) (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (hmult : ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
      T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0) :
    ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) → (∀ i, (c i)′ = 0) →
      (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0 :=
  T.hli_of_mult_core m h1 θ Pp hP hn0 hind gls dθ wθ s hs
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (fun i hi ↦ (unitsC_spec hU i hi).2.2.2) _
    (fun i ↦ T.units_logs m h1 θ Pp hP Us Vs gls dθ wθ s hU i i.2) hmult

/-- **`hli_of_mult_core` for the S-units `uᵢ t^{−jᵢ}` of `unitsC0`.** -/
theorem hli_of_mult0 (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (hn0 : 0 < Pp.length)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hU : unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true)
    (hmult : ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
      (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) * T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ))) ^ a i =
        algebraMap Cc L c) → a = 0) :
    ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) → (∀ i, (c i)′ = 0) →
      (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0 :=
  T.hli_of_mult_core m h1 θ Pp hP hn0 hind gls dθ wθ s hs
    (fun i hi ↦ (unitsC0_spec hU i hi).2.2.1) (fun i hi ↦ (unitsC0_spec hU i hi).2.2.2.1) _
    (fun i ↦ T.units0_logs m h1 hm hk htr θ Pp hP Us Vs kk jj gls dθ wθ s hU i i.2) hmult

end MTower

end Curves.MT
