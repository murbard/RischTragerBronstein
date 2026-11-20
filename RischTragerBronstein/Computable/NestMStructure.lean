import RischTragerBronstein.Computable.NestMBasics
import RischTragerBronstein.Computable.NestMInt
import RischTragerBronstein.Liouville.ExpLogDerivStructure
import RischTragerBronstein.RDE.LogDerivRigid
import RischTragerBronstein.Computable.NestPParam
import RischTragerBronstein.Liouville.Transcendence

/-!
# Towers of nested exponentials: the structure theorem

In a tower `Kc(x)(t₀)…(t_{m-1})` of exponentials `tᵢ = exp aᵢ`, `aᵢ ∈ Kᵢ`:

* `exp_structure`: if `Z′ = u′ / u` with `Z, u ∈ F m`, `u ≠ 0` (i.e. `exp Z ∈ F m` up to a
  constant), then `Z = ∑ qᵢ aᵢ + κ` with `qᵢ ∈ ℚ`, `κ ∈ Kc`. By induction: at the base a derivative
  which is a logarithmic derivative is constant (`deriv_eq_zero_of_add_proper_eq_logDeriv`); at an
  exponential level `Z ∈ F m` and `(Z - n aₘ)′` is a logarithmic derivative in `F m`
  (`exp_deriv_eq_logDeriv`).
* Consequences, all reduced to constant linear systems (`consys`): the certificate `expCertM`
  makes every `tₘ` transcendental (`tr_of_expCert`), and `pld` finds the only integer `M` for which
  `exp (V + M aₘ)` can lie in `F m` (`pld_spec`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP

/-- A tower of exponentials: every level is `exp (as m)`. -/
def expK (as : (m : ℕ) → Code (m + 1)) : (m : ℕ) → KindN m := fun m ↦ .exp (as m)

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {as : (m : ℕ) → Code (m + 1)}
variable (T : NestMTower Kc E (expK as))

lemma coe_logDeriv_F {m : ℕ} (y : T.F m) : ((logDeriv y : T.F m) : E) = logDeriv (y : E) := by
  unfold logDeriv
  rw [IntermediateField.coe_div, coe_deriv]

/-- The value of the exponent `aₘ`. -/
noncomputable abbrev aE (m : ℕ) : E := evN Kc T.x T.ts m (as m)

lemma wPoly_expK (m : ℕ) : T.wPoly m = C (T.valN m (as m))′ * X := T.wPoly_exp rfl

/-- **The structure theorem** for towers of exponentials. -/
theorem exp_structure : ∀ (m : ℕ), T.Tr m → ∀ (Z : E), Z ∈ T.F m → ∀ (u : E), u ∈ T.F m →
    u ≠ 0 → Z′ = logDeriv u →
    ∃ (q : ℕ → ℚ) (κ : Kc), Z = ∑ i ∈ Finset.range m, (q i : E) * T.aE i + algebraMap Kc E κ
  | 0, _, Z, hZ, u, hu, hu0, hd => by
    letI : Differential Kc[X] := polynomialOfDeriv 1
    haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
    have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
    have hW := deriv_eq_zero_of_add_proper_eq_logDeriv (K := T.F 0) hD 0 1 squarefree_one
      (by simp) ⟨Z, hZ⟩ ⟨u, hu⟩ (fun h0 ↦ hu0 (congrArg Subtype.val h0)) (Subtype.ext (by
        rw [map_zero, zero_div, add_zero, coe_deriv, T.coe_logDeriv_F]
        exact hd))
    have hZ0 : Z′ = 0 := by
      have := congrArg Subtype.val hW
      rwa [coe_deriv] at this
    obtain ⟨κ, hκ⟩ := T.hCall Z hZ0
    exact ⟨fun _ ↦ 0, κ, by simp [hκ]⟩
  | m + 1, h, Z, hZ, u, hu, hu0, hd => by
    have hm : T.Tr m := fun i hi ↦ h i (by omega)
    have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
    set t := T.ts m with ht
    have hw := T.deriv_ts_aeval m
    let _ := algebraAdjoinSimple (F := T.F m) t
    let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
    have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
    have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
    have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
      algebraMap_adjoinSimple _
    set b := (T.valN m (as m))′ with hb
    have hDe : ∀ P : (T.F m)[X], P′ = implicitDeriv (C b * X) P := fun P ↦ by
      change implicitDeriv (T.wPoly m) P = _
      rw [T.wPoly_expK]
    have hconst : ∀ (P : (T.F m)[X]) (n : ℕ), implicitDeriv (C b * X) P * X ^ n =
        P * implicitDeriv (C b * X) (X ^ n) → ∃ e : T.F m, P = C e * X ^ n := fun P n hP ↦
      T.const_poly m htr P n (by rw [T.wPoly_expK]; exact hP)
    have hZK : Z ∈ (T.F m)⟮t⟯ := (T.mem_F_succ).mp hZ
    have huK : u ∈ (T.F m)⟮t⟯ := (T.mem_F_succ).mp hu
    obtain ⟨Z0, e, n, he, hZe, hZ0⟩ := exp_deriv_eq_logDeriv (F := T.F m) (K := (T.F m)⟮t⟯) hDe
      hconst ⟨Z, hZK⟩ ⟨u, huK⟩ (fun h0 ↦ hu0 (congrArg Subtype.val h0)) (Subtype.ext (by
        change Z′ = _
        rw [hd]
        unfold logDeriv
        rw [IntermediateField.coe_div]
        rfl))
    have hZv : Z = (Z0 : E) := by
      have := congrArg Subtype.val hZe
      rw [hcoe, aeval_C] at this
      exact this
    -- `(Z₀ - n aₘ)′ = e′ / e` in `F m`
    have hrec : ((Z0 - (n : T.F m) * T.valN m (as m) : T.F m) : E)′ = logDeriv ((e : T.F m) : E) := by
      rw [← coe_deriv, ← T.coe_logDeriv_F, map_sub, hZ0, Derivation.leibniz]
      have hn : ((n : T.F m))′ = 0 := by
        have := T.deriv_ratCast (m := m) (n : ℚ)
        simpa using this
      rw [hn, smul_zero, add_zero, smul_eq_mul]
      push_cast
      ring
    obtain ⟨q, κ, hq⟩ := exp_structure m hm _ (Z0 - (n : T.F m) * T.valN m (as m)).2 _ e.2
      (fun h0 ↦ he (Subtype.ext h0)) hrec
    refine ⟨fun i ↦ if i = m then (n : ℚ) else q i, κ, ?_⟩
    rw [Finset.sum_range_succ]
    beta_reduce
    rw [if_pos rfl]
    have hsum : ∑ i ∈ Finset.range m, (((if i = m then (n : ℚ) else q i) : ℚ) : E) * T.aE i =
        ∑ i ∈ Finset.range m, (q i : E) * T.aE i :=
      Finset.sum_congr rfl fun i hi ↦ by rw [if_neg (Finset.mem_range.mp hi).ne]
    rw [hsum, hZv]
    have hq' : (Z0 : E) - (n : E) * T.aE m = ∑ i ∈ Finset.range m, (q i : E) * T.aE i +
        algebraMap Kc E κ := by
      rw [← hq]
      push_cast
      rfl
    push_cast
    linear_combination hq'

/-! ### Constant systems with a distinguished first unknown -/

omit [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] in
lemma getD_mem' {γ : Type*} (l : List γ) (d : γ) {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

section Cert

variable {ks : (m : ℕ) → KindN m} (T' : NestMTower Kc E ks)

/-- If every basis vector of the constant system has first coordinate `0`, so has every
constant relation. -/
lemma coeff0_eq_zero_of_cert (m : ℕ) (h : T'.Tr m) (vs : List (Code (m + 1)))
    (hcert : ∀ u ∈ consys ks m vs, u.getD 0 0 = 0) (c : List Kc) (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T'.F m) c * (T'.MP m h).sem v) c vs).sum = 0) :
    c.getD 0 0 = 0 := by
  obtain ⟨β, hβl, hβ⟩ := T'.consys_complete m h vs c hl h0
  rw [hβ 0, NestTower.zipWith_sum_range _ 0 [] _ _ hβl]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [hcert _ (getD_mem' _ _ (by rw [← hβl]; exact Finset.mem_range.mp hk)), map_zero,
    mul_zero]

/-- A constant relation with non-zero first coefficient forces a basis vector with non-zero first
coordinate. -/
lemma exists_coeff0_ne (m : ℕ) (h : T'.Tr m) (vs : List (Code (m + 1))) (c : List Kc)
    (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T'.F m) c * (T'.MP m h).sem v) c vs).sum = 0)
    (hc : c.getD 0 0 ≠ 0) : ∃ u ∈ consys ks m vs, u.getD 0 0 ≠ 0 := by
  by_contra hne
  push_neg at hne
  exact hc (T'.coeff0_eq_zero_of_cert m h vs hne c hl h0)

end Cert

/-! ### The exponents as codes of level `m` -/

lemma evN_lift (m : ℕ) (h : T.Tr m) (q : Code (m + 1)) :
    evN Kc T.x T.ts (m + 1) (([q], [(opsM (expK as) m).one]) : Code (m + 2)) =
      evN Kc T.x T.ts m q := by
  change evP Kc T.x T.ts m [q] / evP Kc T.x T.ts m [(opsM (expK as) m).one] = _
  simp only [evP, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  rw [← T.sem_MP m h (opsM (expK as) m).one, (T.MP m h).sem_one]
  simp

lemma expsBelow_spec : ∀ (m : ℕ) (_ : T.Tr m), (expsBelow (expK as) m).length = m ∧
    ∀ i < m, evN Kc T.x T.ts m ((expsBelow (expK as) m).getD i (opsM (expK as) m).zero) = T.aE i
  | 0, _ => ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | m + 1, h => by
    obtain ⟨hl, hv⟩ := expsBelow_spec m (fun i hi ↦ h i (by omega))
    have he : expsBelow (expK as) (m + 1) =
        ((expsBelow (expK as) m) ++ [as m]).map (liftE (expK as) m) := rfl
    refine ⟨by rw [he, List.length_map, List.length_append, hl]; rfl, fun i hi ↦ ?_⟩
    rw [he, NestTower.getD_map' _ _ (opsM (expK as) m).zero _ (by simp [hl]; omega),
      liftE, T.evN_lift m (fun i hi ↦ h i (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi)]; exact hv i hi
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self]; rfl

/-- The derivatives of the exponents, as codes of level `m`. -/
def dExps (as : (m : ℕ) → Code (m + 1)) (m : ℕ) : List (Code (m + 1)) :=
  (expsBelow (expK as) m).map (opsM (expK as) m).deriv

lemma dExps_spec (m : ℕ) (h : T.Tr m) : (dExps as m).length = m ∧
    ∀ i < m, (((T.MP m h).sem ((dExps as m).getD i (opsM (expK as) m).zero) : T.F m) : E) =
      (T.aE i)′ := by
  obtain ⟨hl, hv⟩ := T.expsBelow_spec m h
  refine ⟨by rw [dExps, List.length_map, hl], fun i hi ↦ ?_⟩
  rw [dExps, NestTower.getD_map' _ _ (opsM (expK as) m).zero _ (by rw [hl]; exact hi),
    (T.MP m h).sem_deriv, coe_deriv, T.sem_MP, hv i hi]

/-- The value of `∑ cᵢ vᵢ` for the list `v₀ :: dExps`. -/
lemma zipWith_dExps (m : ℕ) (h : T.Tr m) (v0 : Code (m + 1)) (c0 : Kc) (q : ℕ → Kc) :
    (((List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v)
      (c0 :: (List.range m).map q) (v0 :: dExps as m)).sum : T.F m) : E) =
      algebraMap Kc E c0 * (((T.MP m h).sem v0 : T.F m) : E) +
        ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * (T.aE i)′ := by
  obtain ⟨hl, hv⟩ := T.dExps_spec m h
  rw [List.zipWith_cons_cons, List.sum_cons, NestTower.zipWith_sum_range _ 0 (opsM (expK as) m).zero _ _
    (by rw [List.length_map, List.length_range, hl])]
  push_cast
  congr 1
  rw [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi), hv i (Finset.mem_range.mp hi)]

/-! ### Transcendence -/

lemma expCert_succ {n : ℕ} (hc : expCertM (expK as) (n + 1) = true) :
    expCertM (expK as) n = true ∧
      ∀ u ∈ consys (expK as) n ((opsM (expK as) n).deriv (as n) :: dExps as n), u.getD 0 0 = 0 := by
  simp only [expCertM, List.range_succ, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hc
  refine ⟨hc.1, fun u hu ↦ ?_⟩
  have := List.all_eq_true.mp hc.2 u hu
  simpa using this

/-- **The certificate proves the tower**: every `tₘ = exp aₘ` is transcendental over `F m`. -/
theorem tr_of_expCert : ∀ n, expCertM (expK as) n = true → T.Tr n
  | 0, _ => fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  | n + 1, hc => by
    obtain ⟨hc1, hc2⟩ := expCert_succ hc
    have hn := tr_of_expCert n hc1
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hn i hi
    refine transcendental_exponential (T.valN i (as i))′ (T.hts0 i (as i) rfl) (T.ht i) ?_
    intro k hk y hy
    by_contra hy0
    have hyE : ((y : T.F i) : E) ≠ 0 := fun h0 ↦ hy0 (Subtype.ext h0)
    have hd : ((k : E) * T.aE i)′ = logDeriv ((y : T.F i) : E) := by
      have := congrArg Subtype.val hy
      rw [coe_deriv] at this
      unfold logDeriv
      rw [this]
      simp only [IntermediateField.coe_mul, coe_deriv]
      rw [Derivation.leibniz, show ((k : E))′ = 0 by simpa using T.deriv_ratCast_E (k : ℚ)]
      field_simp
      simp [aE, valN]
    have hmem : (k : E) * T.aE i ∈ T.F i := mul_mem (by simpa using (T.F i).natCast_mem k)
      (T.evN_mem i (as i))
    obtain ⟨q, κ, hq⟩ := T.exp_structure i hn _ hmem _ y.2 hyE hd
    have hrel : (k : E) * (T.aE i)′ = ∑ j ∈ Finset.range i, (q j : E) * (T.aE j)′ := by
      have := congrArg (fun z : E ↦ z′) hq
      simp only [map_add, map_sum, Derivation.leibniz, show ∀ r : ℚ, ((r : E))′ = 0 from
        T.deriv_ratCast_E, show ((k : E))′ = 0 by simpa using T.deriv_ratCast_E (k : ℚ),
        deriv_algebraMap, T.hC, map_zero, smul_zero, add_zero, smul_eq_mul, mul_zero] at this
      linear_combination this
    have h0 := T.coeff0_eq_zero_of_cert i hn _ hc2 ((k : Kc) :: (List.range i).map
      fun j ↦ -((q j : ℚ) : Kc)) (by simp [(T.dExps_spec i hn).1]) (Subtype.ext (by
        rw [T.zipWith_dExps i hn, (T.MP i hn).sem_deriv, coe_deriv, T.sem_MP]
        simp only [ZeroMemClass.coe_zero, map_neg, map_natCast, map_ratCast, neg_mul,
          Finset.sum_neg_distrib]
        rw [show evN Kc T.x T.ts i (as i) = T.aE i from rfl]
        linear_combination hrel))
    simp only [List.getD_cons_zero, Nat.cast_eq_zero] at h0
    exact hk h0

/-! ### The logarithmic-derivative bound -/

section Rel

variable {ks : (m : ℕ) → KindN m} (T' : NestMTower Kc E ks)

/-- The value of a constant relation given by a coefficient function. -/
lemma rel_val (m : ℕ) (h : T'.Tr m) (vs : List (Code (m + 1))) (f : ℕ → Kc) :
    (((List.zipWith (fun c v ↦ algebraMap Kc (T'.F m) c * (T'.MP m h).sem v)
      ((List.range vs.length).map f) vs).sum : T'.F m) : E) =
      ∑ j ∈ Finset.range vs.length, algebraMap Kc E (f j) *
        (((T'.MP m h).sem (vs.getD j (opsM ks m).zero) : T'.F m) : E) := by
  rw [NestTower.zipWith_sum_range _ 0 (opsM ks m).zero _ _ (by simp)]
  push_cast
  rw [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hj)]

end Rel

/-- **The logarithmic-derivative bound is correct**: if `exp (V + M aₘ) ∈ F m` (up to a constant)
for an integer `M`, then `pld` returns `M`. -/
theorem pld_spec (m : ℕ) (h : T.Tr m)
    (hc2 : ∀ u ∈ consys (expK as) m ((opsM (expK as) m).deriv (as m) :: dExps as m),
      u.getD 0 0 = 0)
    (V : Code (m + 1)) (M : ℤ) (u : E) (hu : u ∈ T.F m) (hu0 : u ≠ 0)
    (hd : (evN Kc T.x T.ts m V + (M : E) * T.aE m)′ = logDeriv u) :
    pld (expK as) m V (as m) = some (M : ℚ) := by
  set O := opsM (expK as) m with hO
  have hmem : evN Kc T.x T.ts m V + (M : E) * T.aE m ∈ T.F m :=
    add_mem (T.evN_mem m V) (mul_mem (by simpa using (T.F m).intCast_mem M) (T.evN_mem m (as m)))
  obtain ⟨q, κ, hq⟩ := T.exp_structure m h _ hmem u hu hu0 hd
  have hrel : (evN Kc T.x T.ts m V)′ + (M : E) * (T.aE m)′ =
      ∑ j ∈ Finset.range m, (q j : E) * (T.aE j)′ := by
    have := congrArg (fun z : E ↦ z′) hq
    simp only [map_add, map_sum, Derivation.leibniz, show ∀ r : ℚ, ((r : E))′ = 0 from
      T.deriv_ratCast_E, show ((M : E))′ = 0 by simpa using T.deriv_ratCast_E (M : ℚ),
      deriv_algebraMap, T.hC, map_zero, smul_zero, add_zero, smul_eq_mul, mul_zero] at this
    linear_combination this
  set vs : List (Code (m + 1)) := O.deriv V :: O.deriv (as m) :: dExps as m with hvs
  obtain ⟨hlD, hvD⟩ := T.dExps_spec m h
  have hlen : vs.length = m + 2 := by simp [hvs, hlD]
  -- the values of the unknowns
  have hval : ∀ j < m + 2, (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) =
      if j = 0 then (evN Kc T.x T.ts m V)′ else if j = 1 then (T.aE m)′ else (T.aE (j - 2))′ := by
    intro j hj
    rcases j with _ | _ | j
    · show (((T.MP m h).sem (O.deriv V) : T.F m) : E) = _
      rw [(T.MP m h).sem_deriv, coe_deriv, T.sem_MP, if_pos rfl]
    · show (((T.MP m h).sem (O.deriv (as m)) : T.F m) : E) = _
      rw [(T.MP m h).sem_deriv, coe_deriv, T.sem_MP]
      simp [aE]
    · show (((T.MP m h).sem ((dExps as m).getD j O.zero) : T.F m) : E) = _
      rw [hvD j (by omega), if_neg (by omega), if_neg (by omega), show j + 1 + 1 - 2 = j by omega]
  -- the relation `(1, M, -q)`
  set fc : ℕ → Kc := fun j ↦ if j = 0 then 1 else if j = 1 then (M : Kc) else -((q (j - 2) : ℚ) : Kc)
    with hfc
  have hsum : ∀ g : ℕ → Kc, ∑ j ∈ Finset.range vs.length, algebraMap Kc E (g j) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) =
      algebraMap Kc E (g 0) * (evN Kc T.x T.ts m V)′ + algebraMap Kc E (g 1) * (T.aE m)′ +
        ∑ j ∈ Finset.range m, algebraMap Kc E (g (j + 2)) * (T.aE j)′ := by
    intro g
    rw [hlen, Finset.sum_range_succ', Finset.sum_range_succ', zero_add]
    have e : ∀ j ∈ Finset.range m, algebraMap Kc E (g (j + 1 + 1)) *
        (((T.MP m h).sem (vs.getD (j + 1 + 1) O.zero) : T.F m) : E) =
        algebraMap Kc E (g (j + 2)) * (T.aE j)′ := fun j hj ↦ by
      rw [hval (j + 1 + 1) (by have := Finset.mem_range.mp hj; omega), if_neg (by omega),
        if_neg (by omega), show j + 1 + 1 - 2 = j by omega]
    rw [Finset.sum_congr rfl e, hval 0 (by omega), hval 1 (by omega), if_pos rfl,
      if_neg one_ne_zero, if_pos rfl]
    ring
  have h0c : (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fc) vs).sum = 0 := Subtype.ext (by
    rw [T.rel_val m h vs fc, hsum, ZeroMemClass.coe_zero]
    simp only [hfc, if_pos rfl, if_neg one_ne_zero, if_pos rfl, map_one, one_mul, map_intCast,
      show ∀ j, j + 2 ≠ 0 from fun j ↦ by omega, show ∀ j, j + 2 ≠ 1 from fun j ↦ by omega,
      if_false, if_true, Nat.add_sub_cancel, map_neg, map_ratCast, neg_mul, Finset.sum_neg_distrib]
    linear_combination hrel)
  obtain ⟨u0, hu0U, hu00⟩ := T.exists_coeff0_ne m h vs _ (by simp) h0c (by
    rw [NestTower.getD_range_map _ _ (by rw [hlen]; omega)]; simp [hfc])
  -- the first basis vector with a non-zero first coordinate
  obtain ⟨u1, hfind⟩ : ∃ u1, (consys (expK as) m vs).find? (fun u ↦ u.getD 0 0 ≠ 0) = some u1 := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨u0, hu0U, by simpa using hu00⟩
  have hu1U : u1 ∈ consys (expK as) m vs := List.mem_of_find?_eq_some hfind
  have hu10 : u1.getD 0 0 ≠ 0 := by simpa using List.find?_some hfind
  have hpld : pld (expK as) m V (as m) = some (u1.getD 1 0 / u1.getD 0 0) := by
    simp only [pld]
    rw [show (O.deriv V :: O.deriv (as m) :: (expsBelow (expK as) m).map O.deriv) = vs from rfl,
      hfind]
  rw [hpld]
  -- the relation of `u₁`
  have hs1 := T.consys_sound m h vs u1 hu1U
  have hs1E : ∑ j ∈ Finset.range vs.length, algebraMap Kc E (algebraMap ℚ Kc (u1.getD j 0)) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) = 0 := by
    rw [← T.rel_val m h vs, hs1, ZeroMemClass.coe_zero]
  -- the difference has first coefficient `0`, hence is a relation of the certificate
  set d : ℕ → Kc := fun j ↦ algebraMap ℚ Kc (u1.getD 0 0) * fc j - algebraMap ℚ Kc (u1.getD j 0)
    with hd
  have hfcE : ∑ j ∈ Finset.range vs.length, algebraMap Kc E (fc j) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) = 0 := by
    rw [← T.rel_val m h vs fc, h0c, ZeroMemClass.coe_zero]
  have hdE : ∑ j ∈ Finset.range vs.length, algebraMap Kc E (d j) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) = 0 := by
    calc _ = algebraMap Kc E (algebraMap ℚ Kc (u1.getD 0 0)) *
          ∑ j ∈ Finset.range vs.length, algebraMap Kc E (fc j) *
            (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) -
          ∑ j ∈ Finset.range vs.length, algebraMap Kc E (algebraMap ℚ Kc (u1.getD j 0)) *
            (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [hd, map_sub, map_mul]
          ring
      _ = 0 := by rw [hfcE, hs1E]; ring
  have hd0 : d 0 = 0 := by simp [hd, hfc]
  set vs' : List (Code (m + 1)) := O.deriv (as m) :: dExps as m with hvs'
  have htail : (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs'.length).map fun j ↦ d (j + 1)) vs').sum = 0 := Subtype.ext (by
    rw [T.rel_val m h vs', ZeroMemClass.coe_zero, ← hdE]
    rw [show vs.length = vs'.length + 1 by simp [hvs, hvs'], Finset.sum_range_succ', hd0,
      map_zero, zero_mul, add_zero]
    rfl)
  have hd1 := T.coeff0_eq_zero_of_cert m h vs' hc2 _ (by simp) htail
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range
    (show 0 < vs'.length by simp [hvs']), Option.map_some, Option.getD_some, hd, hfc,
    zero_add, if_neg one_ne_zero, if_pos rfl, map_intCast, if_true] at hd1
  simp only [← List.getD_eq_getElem?_getD] at hd1
  congr 1
  have : algebraMap ℚ Kc ((M : ℚ) * u1.getD 0 0) = algebraMap ℚ Kc (u1.getD 1 0) := by
    rw [map_mul, map_intCast]
    linear_combination hd1
  have h2 := (algebraMap ℚ Kc).injective this
  rw [div_eq_iff hu10]
  linarith

/-- **No homogeneous solutions**: under the certificate at level `i`, `y′ = k aᵢ′ y` (`k ≠ 0`)
has no non-zero solution in `F i`. -/
lemma no_hom_exp (i : ℕ) (hn : T.Tr i)
    (hc2 : ∀ u ∈ consys (expK as) i ((opsM (expK as) i).deriv (as i) :: dExps as i),
      u.getD 0 0 = 0) (k : ℕ) (hk : k ≠ 0) (y : T.F i)
    (hy : y′ = (k : T.F i) * (T.valN i (as i))′ * y) : y = 0 := by
  by_contra hy0
  have hyE : ((y : T.F i) : E) ≠ 0 := fun h0 ↦ hy0 (Subtype.ext h0)
  have hd : ((k : E) * T.aE i)′ = logDeriv ((y : T.F i) : E) := by
    have := congrArg Subtype.val hy
    rw [coe_deriv] at this
    unfold logDeriv
    rw [this]
    simp only [IntermediateField.coe_mul, coe_deriv]
    rw [Derivation.leibniz, show ((k : E))′ = 0 by simpa using T.deriv_ratCast_E (k : ℚ)]
    field_simp
    simp [aE, valN]
  have hmem : (k : E) * T.aE i ∈ T.F i := mul_mem (by simpa using (T.F i).natCast_mem k)
    (T.evN_mem i (as i))
  obtain ⟨q, κ, hq⟩ := T.exp_structure i hn _ hmem _ y.2 hyE hd
  have hrel : (k : E) * (T.aE i)′ = ∑ j ∈ Finset.range i, (q j : E) * (T.aE j)′ := by
    have := congrArg (fun z : E ↦ z′) hq
    simp only [map_add, map_sum, Derivation.leibniz, show ∀ r : ℚ, ((r : E))′ = 0 from
      T.deriv_ratCast_E, show ((k : E))′ = 0 by simpa using T.deriv_ratCast_E (k : ℚ),
      deriv_algebraMap, T.hC, map_zero, smul_zero, add_zero, smul_eq_mul, mul_zero] at this
    linear_combination this
  have h0 := T.coeff0_eq_zero_of_cert i hn _ hc2 ((k : Kc) :: (List.range i).map
    fun j ↦ -((q j : ℚ) : Kc)) (by simp [(T.dExps_spec i hn).1]) (Subtype.ext (by
      rw [T.zipWith_dExps i hn, (T.MP i hn).sem_deriv, coe_deriv, T.sem_MP]
      simp only [ZeroMemClass.coe_zero, map_neg, map_natCast, map_ratCast, neg_mul,
        Finset.sum_neg_distrib]
      rw [show evN Kc T.x T.ts i (as i) = T.aE i from rfl]
      linear_combination hrel))
  simp only [List.getD_cons_zero, Nat.cast_eq_zero] at h0
  exact hk h0

/-- The same, in the form `e′ + j aᵢ′ e ≠ 0` for every integer `j ≠ 0`. -/
lemma no_hom_exp_int (i : ℕ) (hn : T.Tr i)
    (hc2 : ∀ u ∈ consys (expK as) i ((opsM (expK as) i).deriv (as i) :: dExps as i),
      u.getD 0 0 = 0) (j : ℤ) (hj : j ≠ 0) (e : T.F i) (he : e ≠ 0) :
    e′ + (j : T.F i) * (T.valN i (as i))′ * e ≠ 0 := by
  intro h0
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · -- `e′ = k b e`, `k = -j > 0`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, j = -(k : ℤ) := ⟨(-j).toNat, by omega⟩
    refine he (T.no_hom_exp i hn hc2 k (by omega) e ?_)
    rw [hk] at h0
    push_cast at h0
    linear_combination h0
  · -- `(1/e)′ = j b (1/e)`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, j = (k : ℤ) := ⟨j.toNat, by omega⟩
    have := T.no_hom_exp i hn hc2 k (by omega) e⁻¹ (by
      rw [hk] at h0
      push_cast at h0
      have hd : (e⁻¹)′ = -(e′) / e ^ 2 := by
        rw [show e⁻¹ = 1 / e by ring, Derivation.leibniz_div, Derivation.map_one_eq_zero]
        simp only [smul_eq_mul]; ring
      rw [hd]
      field_simp
      linear_combination -h0)
    exact inv_ne_zero he this

end NestMTower

end Tower.NestM
