import RischTragerBronstein.Curves.IntBasisScaled
import RischTragerBronstein.Mixed.NKExactTRSome

/-!
# Logarithmic integral bases for constant curves over a primitive level

For `θ` a root of `F₀(t, Y)` with `F₀ ∈ ℚ[t][Y]` monic (a *constant curve*) over a primitive level
`Fₘ₊₁ = Fₘ(t)`, `t′ = η`, the curve `F₀(x, y) = 0` sits in `L` with `x = t`, `y = θ`
(`constCurve`); the derivation of `L` restricted to `ℚ(t, θ)` is `η d/dt`, so
`exists_logBasis_scaled` gives a basis `wᵢ = ∑ₖ (Aᵢₖ/Bᵢₖ)(t) θᵏ` (rational functions over `ℚ`, with
an inverse matrix of the same kind) with `S₀ wᵢ′ = η ∑ⱼ Pᵢⱼ wⱼ`, `S₀` squarefree, and the rescaled
matrix vanishing at infinity (`const_logBasis`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The constant curve** `F₀(t, θ) = 0` as curve data in `L`. -/
noncomputable def constCurve (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (F0 : ℚ[X][X])
    (hF0 : F0.Monic) (θ : L) (hroot : (F0.map (aeval (T.ts m)).toRingHom).eval θ = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0) : Curves.CurveData ℚ L where
  x := T.ts m
  y := θ
  F := F0
  htr := Transcendental.of_tower_top ℚ htr
  monic := hF0
  irr := fun G hG hGy ↦ by
    have htrQ : Transcendental ℚ (T.ts m) := Transcendental.of_tower_top ℚ htr
    set a : ℕ → T.F (m + 1) := fun k ↦ T.phi m ((G.coeff k).map (algebraMap ℚ (T.F m))) with ha
    have hcoe : ∀ k, (a k : L) = aeval (T.ts m) (G.coeff k) := fun k ↦ by
      rw [ha, coe_phi, aeval_map_algebraMap]
    have hsum : ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 := by
      rw [← hGy, eval_eq_sum_range' (n := F0.natDegree) (lt_of_le_of_lt natDegree_map_le hG)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hcoe, coeff_map]; rfl
    have h0 := hind a hsum
    refine Polynomial.ext fun k ↦ ?_
    rw [coeff_zero]
    by_cases hk : k < F0.natDegree
    · have := h0 k hk
      have hL : aeval (T.ts m) (G.coeff k) = 0 := by rw [← hcoe, this]; rfl
      exact transcendental_iff_injective.mp htrQ (by rw [hL, map_zero])
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  root := hroot

/-- `t′ = η` as an identity in `L`. -/
lemma deriv_ts_L (m : ℕ) (h0 : T.Tr m) (hm : m < T.n) {η : LC m} (hk : ks m = .prim η) :
    (T.ts m)′ = (((T.MP m h0).sem η : T.F m) : L) := by
  have h := congrArg (fun z : T.F (m + 1) ↦ (z : L)) (T.phi_DzL m hm hk h0 X)
  have e1 : DzL ((T.MP m h0).sem η) 0 (X : (T.F m)[X]) = Polynomial.C ((T.MP m h0).sem η) := by
    rw [DzL_eq]; simp
  rw [e1] at h
  have e2 : ((T.phi m X : T.F (m + 1)) : L) = T.ts m := by rw [coe_phi, aeval_X]
  have e3 : ((T.phi m (Polynomial.C ((T.MP m h0).sem η)) : T.F (m + 1)) : L) =
      (((T.MP m h0).sem η : T.F m) : L) := by rw [coe_phi, aeval_C]; rfl
  rw [e3] at h
  rw [← e2, h]
  rfl

/-- `t′ = a′ t` as an identity in `L` (exponential level). -/
lemma deriv_ts_L_exp (m : ℕ) (h0 : T.Tr m) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a) :
    (T.ts m)′ = (((T.MP m h0).sem ((MO Fc ks m).deriv a) : T.F m) : L) * T.ts m := by
  have h := congrArg (fun z : T.F (m + 1) ↦ (z : L)) (T.phi_DzL_exp m hm hk h0 X)
  have e1 : DzL 0 ((T.MP m h0).sem ((MO Fc ks m).deriv a)) (X : (T.F m)[X]) =
      Polynomial.C ((T.MP m h0).sem ((MO Fc ks m).deriv a)) * X := by
    rw [DzL_eq]; simp
  rw [e1] at h
  have e2 : ((T.phi m X : T.F (m + 1)) : L) = T.ts m := by rw [coe_phi, aeval_X]
  have e3 : ((T.phi m (Polynomial.C ((T.MP m h0).sem ((MO Fc ks m).deriv a)) * X) : T.F (m + 1)) :
      L) = (((T.MP m h0).sem ((MO Fc ks m).deriv a) : T.F m) : L) * T.ts m := by
    rw [coe_phi, map_mul, aeval_C, aeval_X]; rfl
  rw [e3] at h
  conv_lhs => rw [← e2]
  exact h.symm

/-- Elements of `ℚ(t)` are quotients of polynomials. -/
lemma ratfun_repr (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (c : ℚ⟮(T.ts m : L)⟯) :
    ∃ A B : ℚ[X], B ≠ 0 ∧ (c : L) = aeval (T.ts m) A / aeval (T.ts m) B := by
  letI := algebraAdjoinSimple (F := ℚ) (T.ts m : L)
  haveI := isFractionRing_adjoin_simple (T.ts m : L) (Transcendental.of_tower_top ℚ htr)
  obtain ⟨A, B, hB, hc⟩ := IsFractionRing.div_surjective (A := ℚ[X]) c
  refine ⟨A, B, nonZeroDivisors.ne_zero hB, ?_⟩
  rw [← hc, IntermediateField.coe_div, algebraMap_adjoinSimple, algebraMap_adjoinSimple]

set_option maxHeartbeats 1600000 in
/-- **Logarithmic integral bases for a constant curve with `t′ = e ≠ 0`**, with the residue
matrices at `t = 0` and at infinity. -/
theorem const_logBasisG (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (e : L) (he : e ≠ 0)
    (hx : (T.ts m)′ = e)
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (θ : L) (hroot : (F0.map (aeval (T.ts m)).toRingHom).eval θ = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0) :
    ∃ (A B Ai Bi : Fin F0.natDegree → Fin F0.natDegree → ℚ[X]) (r : Fin F0.natDegree → ℕ)
      (S0 : ℚ[X]) (P : Fin F0.natDegree → Fin F0.natDegree → ℚ[X]),
      (∀ i k, B i k ≠ 0) ∧ (∀ i k, Bi i k ≠ 0) ∧
      (∀ i j, ∑ k, aeval (T.ts m) (A i k) / aeval (T.ts m) (B i k) *
        (aeval (T.ts m) (Ai k j) / aeval (T.ts m) (Bi k j)) = if i = j then 1 else 0) ∧
      (∀ i j, ∑ k, aeval (T.ts m) (Ai i k) / aeval (T.ts m) (Bi i k) *
        (aeval (T.ts m) (A k j) / aeval (T.ts m) (B k j)) = if i = j then 1 else 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, (∑ k, aeval (T.ts m) (A i k) / aeval (T.ts m) (B i k) * θ ^ (k : ℕ))′ *
          aeval (T.ts m) S0 =
        e * ∑ j, aeval (T.ts m) (P i j) *
          ∑ k, aeval (T.ts m) (A j k) / aeval (T.ts m) (B j k) * θ ^ (k : ℕ)) ∧
      (∀ i j, (X ^ (r j + 1) * P i j -
        (if i = j then Polynomial.C (r i : ℚ) * X ^ r i * S0 else 0)).natDegree ≤
          r i + S0.natDegree) ∧
      (∀ S1 : ℚ[X], S0 = X * S1 →
        ((List.range F0.natDegree.factorial).map fun k : ℕ ↦
          S1.eval 0 * (k : ℚ) / F0.natDegree.factorial).foldr
        (fun μ M ↦ M * (Matrix.of (fun i j ↦ (P i j).eval 0) - μ • 1)) 1 = 0) ∧
      ((List.range F0.natDegree.factorial).map fun k : ℕ ↦
          -((k : ℚ) / F0.natDegree.factorial)).foldr
        (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1 = 0 := by
  classical
  set S := T.constCurve m htr F0 hF0 θ hroot hind with hS
  obtain ⟨w0, r0, S0, P0, hindw0, hS0, hsq, hder0, hdeg0, hz0, hinf0⟩ :=
    S.exists_logBasis_scaledA e he hx
  -- re-index by `Fin F0.natDegree`
  let w : Fin F0.natDegree → ℚ⟮S.x⟯⟮S.y⟯ := w0
  let r : Fin F0.natDegree → ℕ := r0
  let P : Fin F0.natDegree → Fin F0.natDegree → ℚ[X] := P0
  have hindw : ∀ c : Fin F0.natDegree → ℚ⟮S.x⟯,
      ∑ j, algebraMap ℚ⟮S.x⟯ (ℚ⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0 := hindw0
  have hder : ∀ i, ((w i : L))′ * aeval (T.ts m) S0 =
      e * ∑ j, aeval (T.ts m) (P i j) * (w j : L) := hder0
  have hdeg : ∀ i j, (X ^ (r j + 1) * P i j -
      (if i = j then Polynomial.C (r i : ℚ) * X ^ r i * S0 else 0)).natDegree ≤
        r i + S0.natDegree := hdeg0
  haveI := IntermediateField.adjoin.finiteDimensional S.isIntegral
  have hfin : Module.finrank ℚ⟮S.x⟯ (ℚ⟮S.x⟯⟮S.y⟯) = F0.natDegree := by
    rw [IntermediateField.adjoin.finrank S.isIntegral, S.natDegree_minpoly]; rfl
  -- the basis `w`
  have hliw : LinearIndependent ℚ⟮S.x⟯ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    exact hindw c (by simpa [Algebra.smul_def] using hc)
  let bw := basisOfLinearIndependentOfCardEqFinrank' _ hliw (by rw [Fintype.card_fin, hfin])
  have hbw : ∀ j, bw j = w j := fun j ↦ by simp [bw]
  -- the powers of `θ`
  set th : Fin F0.natDegree → ℚ⟮S.x⟯⟮S.y⟯ := fun k ↦ (AdjoinSimple.gen ℚ⟮S.x⟯ S.y) ^ (k : ℕ)
    with hth
  have hthL : ∀ k, ((th k : ℚ⟮S.x⟯⟮S.y⟯) : L) = θ ^ (k : ℕ) := fun k ↦ by
    simp [hth]; rfl
  have hlith : LinearIndependent ℚ⟮S.x⟯ th := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    choose A B hB hAB using fun k ↦ T.ratfun_repr m htr (c k)
    set a : ℕ → T.F (m + 1) := fun k ↦ if hk : k < F0.natDegree then
      T.phi m ((A ⟨k, hk⟩).map (algebraMap ℚ (T.F m))) /
        T.phi m ((B ⟨k, hk⟩).map (algebraMap ℚ (T.F m))) else 0 with ha
    have hacoe : ∀ k : Fin F0.natDegree, (a k : L) = (c k : L) := fun k ↦ by
      simp only [ha, dif_pos k.2, IntermediateField.coe_div, coe_phi, aeval_map_algebraMap]
      rw [hAB k]
    have h0 : ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (a j : L) * θ ^ j)]
      have := congrArg (fun z : ℚ⟮S.x⟯⟮S.y⟯ ↦ (z : L)) hc
      simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hacoe j, Algebra.smul_def, IntermediateField.coe_mul, hthL j]
      rfl
    have := hind a h0 k k.2
    have hk0 : (c k : L) = 0 := by rw [← hacoe k, this]; rfl
    exact Subtype.ext hk0
  let bt := basisOfLinearIndependentOfCardEqFinrank' _ hlith (by rw [Fintype.card_fin, hfin])
  have hbt : ∀ k, bt k = th k := fun k ↦ by simp [bt]
  -- coordinates
  set cT : Fin F0.natDegree → Fin F0.natDegree → ℚ⟮S.x⟯ := fun i k ↦ bt.repr (w i) k with hcT
  set cI : Fin F0.natDegree → Fin F0.natDegree → ℚ⟮S.x⟯ := fun k j ↦ bw.repr (th k) j with hcI
  have hwT : ∀ i, (w i : L) = ∑ k, (cT i k : L) * θ ^ (k : ℕ) := fun i ↦ by
    have h2 := congrArg (fun z : ℚ⟮S.x⟯⟮S.y⟯ ↦ (z : L)) (bt.sum_repr (w i))
    simp only [AddSubmonoidClass.coe_finsetSum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hbt, Algebra.smul_def, IntermediateField.coe_mul, hthL]
    rfl
  -- `T⁻¹ T = 1` over `ℚ(t)`
  have hTiT : ∀ l k, ∑ j, cI l j * cT j k = if l = k then 1 else 0 := by
    intro l k
    have h := congrArg (fun z ↦ bt.repr z k) (bw.sum_repr (th l))
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, hbw] at h
    have hr : bt.repr (th l) k = if l = k then 1 else 0 := by
      rw [← hbt l, bt.repr_self, Finsupp.single_apply]
    rw [← hr]
    exact h
  have hTTi : ∀ i j, ∑ k, cT i k * cI k j = if i = j then 1 else 0 := by
    have hM : (Matrix.of cI) * (Matrix.of cT) = 1 := by
      refine Matrix.ext fun l k ↦ ?_
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact hTiT l k
    have hM' := mul_eq_one_comm.mp hM
    intro i j
    have := congrArg (fun M ↦ M i j) hM'
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  -- fractions over `ℚ`
  choose A B hB hAB using fun i k ↦ T.ratfun_repr m htr (cT i k)
  choose Ai Bi hBi hABi using fun k j ↦ T.ratfun_repr m htr (cI k j)
  have hw' : ∀ i, (w i : L) = ∑ k, aeval (T.ts m) (A i k) / aeval (T.ts m) (B i k) *
      θ ^ (k : ℕ) := fun i ↦ by
    rw [hwT i]; exact Finset.sum_congr rfl fun k _ ↦ by rw [← hAB]
  refine ⟨A, B, Ai, Bi, r, S0, P, hB, hBi, fun i j ↦ ?_, fun i j ↦ ?_, hS0, hsq, fun i ↦ ?_, hdeg,
    hz0, hinf0⟩
  · have := congrArg (fun z : ℚ⟮S.x⟯ ↦ (z : L)) (hTTi i j)
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul] at this
    rw [Finset.sum_congr rfl fun k _ ↦ by rw [← hAB, ← hABi], this]
    split_ifs <;> simp
  · have := congrArg (fun z : ℚ⟮S.x⟯ ↦ (z : L)) (hTiT i j)
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul] at this
    rw [Finset.sum_congr rfl fun k _ ↦ by rw [← hAB, ← hABi], this]
    split_ifs <;> simp
  · have := hder i
    rw [hw' i] at this
    rw [this]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hw' j]

/-- **Logarithmic integral bases for a constant curve over a primitive level.** -/
theorem const_logBasis (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (θ : L) (hroot : (F0.map (aeval (T.ts m)).toRingHom).eval θ = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0) :
    ∃ (A B Ai Bi : Fin F0.natDegree → Fin F0.natDegree → ℚ[X]) (r : Fin F0.natDegree → ℕ)
      (S0 : ℚ[X]) (P : Fin F0.natDegree → Fin F0.natDegree → ℚ[X]),
      (∀ i k, B i k ≠ 0) ∧ (∀ i k, Bi i k ≠ 0) ∧
      (∀ i j, ∑ k, aeval (T.ts m) (A i k) / aeval (T.ts m) (B i k) *
        (aeval (T.ts m) (Ai k j) / aeval (T.ts m) (Bi k j)) = if i = j then 1 else 0) ∧
      (∀ i j, ∑ k, aeval (T.ts m) (Ai i k) / aeval (T.ts m) (Bi i k) *
        (aeval (T.ts m) (A k j) / aeval (T.ts m) (B k j)) = if i = j then 1 else 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, (∑ k, aeval (T.ts m) (A i k) / aeval (T.ts m) (B i k) * θ ^ (k : ℕ))′ *
          aeval (T.ts m) S0 =
        (((T.MP m h1.of_succ).sem η : T.F m) : L) * ∑ j, aeval (T.ts m) (P i j) *
          ∑ k, aeval (T.ts m) (A j k) / aeval (T.ts m) (B j k) * θ ^ (k : ℕ)) ∧
      ∀ i j, (X ^ (r j + 1) * P i j -
        (if i = j then Polynomial.C (r i : ℚ) * X ^ r i * S0 else 0)).natDegree ≤
          r i + S0.natDegree := by
  set ηL : L := (((T.MP m h1.of_succ).sem η : T.F m) : L) with hηL
  have he : ηL ≠ 0 := by
    intro h0
    apply hη 0
    rw [Derivation.map_zero]
    have h' : (T.MP m h1.of_succ).sem η = 0 := Subtype.ext (by rw [ZeroMemClass.coe_zero]; exact h0)
    exact h'.symm
  obtain ⟨A, B, Ai, Bi, r, S0, P, h1', h2, h3, h4, h5, h6, h7, h8, -, -⟩ :=
    T.const_logBasisG m htr ηL he (T.deriv_ts_L m h1.of_succ hm hk) F0 hF0 θ hroot hind
  exact ⟨A, B, Ai, Bi, r, S0, P, h1', h2, h3, h4, h5, h6, h7, h8⟩

end MTower

end Curves.MT
