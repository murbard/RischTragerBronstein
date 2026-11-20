import RischTragerBronstein.Mixed.MTRel
import RischTragerBronstein.Mixed.LTExact

/-!
# Mixed towers over a curve: basic facts

Ported from `Tower.NestM` (`NestMBasics`, `NestMConsys`): rational constants (`mcst`), constants of
every level, no new constants (`const_poly`), normality of the primes (every prime at a primitive
level, every prime other than `t` at an exponential level), Hermite reduction as an identity of
values, the constant systems in the form used by the tower algorithms (`consys_complete`), and
the recognition of rational values (`ratValC`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.NestP

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The rational `q` as a code of level `m`. -/
def mcst : (m : ℕ) → ℚ → LC m
  | 0, q => ratCode Fc q
  | m + 1, q => (([mcst m q] : GPoly (LC m)), ([(MO Fc ks m).one] : GPoly (LC m)))

/-- The rational value of a constant code, if rational. -/
def ratValC (m : ℕ) (c : LC m) : Option ℚ :=
  match (mrel Fc ks m [c, (MO Fc ks m).one]).find? (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u => some (-(u.getD 1 0) / u.getD 0 0)
  | none => none

lemma getD_memC {γ : Type*} (l : List γ) (d : γ) {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma coe_ratCast {m : ℕ} (c : ℚ) : ((c : T.F m) : L) = (c : L) := by simp

include T in
lemma deriv_ratCast_E (c : ℚ) : (c : L)′ = 0 := by
  rw [← map_ratCast (algebraMap Cc L) c, deriv_algebraMap, T.hC, map_zero]

lemma deriv_ratCast {m : ℕ} (c : ℚ) : (c : T.F m)′ = 0 :=
  Subtype.ext (by rw [coe_deriv, coe_ratCast, T.deriv_ratCast_E]; rfl)

lemma deriv_algebraMap_Cc {m : ℕ} (κ : Cc) : (algebraMap Cc (T.F m) κ)′ = 0 :=
  Subtype.ext (by
    rw [coe_deriv]
    change (algebraMap Cc L κ)′ = 0
    rw [deriv_algebraMap, T.hC, map_zero])

lemma const_F {m : ℕ} (y : T.F m) (hy : y′ = 0) : ∃ κ : Cc, y = algebraMap Cc (T.F m) κ := by
  obtain ⟨κ, hκ⟩ := T.hconst (y : L) (by rw [← coe_deriv, hy]; rfl)
  exact ⟨κ, Subtype.ext hκ.symm⟩

lemma algebraMap_ratCast {m : ℕ} (q : ℚ) :
    algebraMap Cc (T.F m) (algebraMap ℚ Cc q) = (q : T.F m) := by
  rw [eq_ratCast (algebraMap ℚ Cc) q, map_ratCast]

lemma sem_mcst : ∀ (m : ℕ) (h : T.Tr m) (c : ℚ), (T.MP m h).sem (mcst Fc ks m c) = (c : T.F m)
  | 0, h, c => by
    apply Subtype.ext
    rw [T.sem_MP]
    change (cM T.hC T.S T.hx Fc T.hSF).sem (ratCode Fc c) = _
    rw [sem_ratCode]
    simp
  | m + 1, h, c => by
    rw [sem_MP_succ]
    simp only [mcst, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one,
      sem_mcst m, map_one, div_one]
    rw [phi, coe_eval₂RingHom, eval₂_C]
    exact map_ratCast _ c

lemma phi_C_ratCast (m : ℕ) (q : ℚ) : T.phi m (C ((q : ℚ) : T.F m)) = ((q : ℚ) : T.F (m + 1)) := by
  rw [T.phi_C]
  exact map_ratCast _ q

/-- No new constants at level `m + 1`: `(P(t) / t ^ n)′ = 0` forces `P = e X ^ n`. -/
lemma const_poly (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (P : (T.F m)[X]) (n : ℕ)
    (hP : implicitDeriv (T.wPoly m) P * X ^ n = P * implicitDeriv (T.wPoly m) (X ^ n)) :
    ∃ e : T.F m, P = C e * X ^ n := by
  set t := T.ts m with htd
  have hinjt : Function.Injective (aeval (R := T.F m) t) := transcendental_iff_injective.mp htr
  have ht0 : t ≠ 0 := fun h0 ↦ by
    have : aeval t (X : (T.F m)[X]) = aeval t (0 : (T.F m)[X]) := by rw [aeval_X, map_zero, h0]
    exact X_ne_zero (hinjt this)
  have hder : ∀ Q : (T.F m)[X], (aeval t Q)′ = aeval t (implicitDeriv (T.wPoly m) Q) :=
    deriv_aeval_eq_implicitDeriv t (T.wPoly m) (T.deriv_ts_aeval m)
  have htn : (t ^ n : L) ≠ 0 := pow_ne_zero n ht0
  have hz : (aeval t P / t ^ n)′ = 0 := by
    rw [Derivation.leibniz_div, show (t ^ n : L) = aeval (R := T.F m) t (X ^ n) by simp, hder, hder]
    have := congrArg (aeval t) hP
    simp only [map_mul, map_pow, aeval_X] at this
    simp only [map_pow, aeval_X, smul_eq_mul]
    rw [mul_comm (t ^ n) _, this]
    simp
  obtain ⟨κ, hκ⟩ := T.hconst _ hz
  refine ⟨algebraMap Cc (T.F m) κ, hinjt ?_⟩
  rw [map_mul, map_pow, aeval_X, aeval_C]
  change aeval t P = algebraMap Cc L κ * t ^ n
  rw [hκ]
  field_simp

/-- At a primitive level every irreducible polynomial is normal. -/
lemma normal_prim (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) {η : LC m}
    (hk : ks m = .prim η) (p : (T.F m)[X]) (hp : Irreducible p) :
    ¬p ∣ implicitDeriv (T.wPoly m) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (C (T.val m η))
  have hw : T.wPoly m = C (T.val m η) := T.wPoly_prim (T.lt_of_transcendental htr) hk
  rw [hw]
  exact not_dvd_deriv_of_irreducible_primitive (T.val m η) (fun _ ↦ rfl)
    (fun P hP ↦ by
      obtain ⟨e, he⟩ := T.const_poly m htr P 0 (by
        rw [hw]; change P′ * X ^ 0 = P * implicitDeriv (C (T.val m η)) (X ^ 0)
        simp [hP])
      exact ⟨e, by simpa using he⟩) hp

/-- At an exponential level every irreducible polynomial other than `X` is normal. -/
lemma normal_exp (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) {a : LC m}
    (hk : ks m = .exp a) (p : (T.F m)[X]) (hp : Irreducible p) (hX : ¬X ∣ p) :
    ¬p ∣ implicitDeriv (T.wPoly m) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  have hw : T.wPoly m = C (T.val m a)′ * X := T.wPoly_exp (T.lt_of_transcendental htr) hk
  intro hsp
  refine hX (dvd_X_of_irreducible_special (T.val m a)′
    (fun P ↦ by change implicitDeriv (T.wPoly m) P = _; rw [hw])
    (fun P n hP ↦ T.const_poly m htr P n hP) hp hsp)

/-- **Hermite reduction at level `m + 1`**, as an identity of values, when the primes of the
denominator are normal. -/
lemma hermite_value (m : ℕ) (hm : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    (A D : GPoly (LC m)) (hD : GPoly.toPoly (T.MP m hm) D ≠ 0)
    (hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m hm) D →
      ¬p ∣ implicitDeriv (T.wPoly m) p) :
    T.phi m (GPoly.toPoly (T.MP m hm) A) / T.phi m (GPoly.toPoly (T.MP m hm) D) =
      (T.phi m (GPoly.toPoly (T.MP m hm)
          (GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) A D).gn) /
        T.phi m (GPoly.toPoly (T.MP m hm)
          (GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) A D).gd))′ +
      T.phi m (GPoly.toPoly (T.MP m hm)
          (GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) A D).b) /
        T.phi m (GPoly.toPoly (T.MP m hm)
          (GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) A D).s) ∧
    Squarefree (GPoly.toPoly (T.MP m hm)
      (GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) A D).s) := by
  set M := T.MP m hm
  have hwk := T.toPoly_wKC m hm (T.lt_of_transcendental htr)
  have hnormal' : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M (wKC (MO Fc ks m) (ks m))) p := fun p hp hpD ↦ by
    rw [hwk]
    exact hnormal p hp hpD
  have hc := GPoly.hermiteCheck_hermite M (wKC (MO Fc ks m) (ks m)) A D hnormal' hD
  obtain ⟨hD0, hgd0, hs0, hid, hsq⟩ := (GPoly.hermiteCheck_iff M _ _ _ _).mp hc
  rw [hwk] at hid
  refine ⟨?_, GPoly.squarefreeCheck_sound M hsq⟩
  have hinj := T.phi_injective htr
  have h1 : T.phi m (GPoly.toPoly M D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have h2 : T.phi m (GPoly.toPoly M
      (GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) A D).gd) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hgd0
  have h3 : T.phi m (GPoly.toPoly M
      (GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) A D).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hs0
  have hidL := congrArg (T.phi m) hid
  simp only [map_mul, map_add, map_sub] at hidL
  rw [Derivation.leibniz_div, T.deriv_phi, T.deriv_phi]
  simp only [smul_eq_mul]
  field_simp
  linear_combination hidL

/-- **Completeness of the constant system**, in the form of `Tower.NestP.consys_complete`. -/
theorem consys_complete (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (c : List Cc)
    (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0) :
    ∃ β : List Cc, β.length = (mrel Fc ks m vs).length ∧ ∀ j,
      c.getD j 0 = (List.zipWith (fun b w ↦ b * algebraMap ℚ Cc (w.getD j 0)) β
        (mrel Fc ks m vs)).sum := by
  have hc := (T.MCols_spec m h vs c hl).mp h0
  obtain ⟨β, hβ, heq⟩ := nullBasis_complete (algebraMap ℚ Cc) (MCols Fc ks m vs) c
    (by rw [length_MCols]; exact hl) hc
  refine ⟨β, hβ, fun j ↦ ?_⟩
  have hsnd : (nsItems (MCols Fc ks m vs)).map Prod.snd =
      (List.range c.length).map unitL := by
    simp only [nsItems, List.map_map]
    rw [length_MCols, ← hl]
    rfl
  rw [hsnd, NestTower.lcombS_range_unitL] at heq
  have := congrArg (fun P : Cc[X] ↦ P.coeff j) heq
  simp only [coeff_toPoly] at this
  rw [this, NestTower.coeff_lcombS]
  rfl

/-- A relation with a non-zero first coefficient gives a basis vector with non-zero first
coefficient. -/
lemma exists_coeff0_ne (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (c : List Cc)
    (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0)
    (hc0 : c.getD 0 0 ≠ 0) : ∃ u ∈ mrel Fc ks m vs, u.getD 0 0 ≠ 0 := by
  obtain ⟨β, hβ, hβc⟩ := T.consys_complete m h vs c hl h0
  by_contra hall
  push Not at hall
  apply hc0
  rw [hβc 0]
  have : ∀ (β : List Cc) (ws : List (CPoly ℚ)), (∀ w ∈ ws, w.getD 0 0 = 0) →
      (List.zipWith (fun b w ↦ b * algebraMap ℚ Cc (w.getD 0 0)) β ws).sum = 0 := by
    intro β ws hws
    induction ws generalizing β with
    | nil => simp
    | cons w ws ih =>
      cases β with
      | nil => simp
      | cons b β =>
        simp only [List.zipWith_cons_cons, List.sum_cons, hws w List.mem_cons_self, map_zero,
          mul_zero, zero_add]
        exact ih β fun w' hw' ↦ hws w' (List.mem_cons_of_mem _ hw')
  exact this β _ hall

/-- **`ratValC` recognizes rational values.** -/
theorem ratVal_spec (m : ℕ) (h : T.Tr m) (c : LC m) (q : ℚ)
    (hc : (T.MP m h).sem c = (q : T.F m)) : ratValC Fc ks m c = some q := by
  classical
  set vs : List (LC m) := [c, (MO Fc ks m).one] with hvs
  have hrel : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      [(1 : Cc), -((q : ℚ) : Cc)] vs).sum = 0 := by
    simp only [hvs, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
      (T.MP m h).sem_one, hc, map_one, map_neg, map_ratCast]
    ring
  obtain ⟨u, hu, hu0⟩ := T.exists_coeff0_ne m h vs _ rfl hrel (by simp)
  unfold ratValC
  obtain ⟨u', hu'⟩ : ∃ u', (mrel Fc ks m vs).find? (fun u ↦ u.getD 0 0 ≠ 0) = some u' := by
    rcases hf : (mrel Fc ks m vs).find? (fun u ↦ u.getD 0 0 ≠ 0) with _ | u'
    · exact absurd (List.find?_eq_none.mp hf u hu) (by simpa using hu0)
    · exact ⟨u', hf⟩
  rw [← hvs, hu']
  simp only
  have hmem := List.mem_of_find?_eq_some hu'
  have hne : u'.getD 0 0 ≠ 0 := by simpa using List.find?_some hu'
  have hs := T.mrel_sound m h vs u' hmem
  simp only [hvs, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
    (T.MP m h).sem_one, hc, mul_one, add_zero] at hs
  congr 1
  have hq : ((u'.getD 0 0 * q + u'.getD 1 0 : ℚ) : T.F m) = 0 := by
    rw [← map_ratCast (algebraMap Cc (T.F m)), ← map_ratCast (algebraMap ℚ Cc)]
    simp only [map_ratCast] at hs ⊢
    rw [← hs]
    simp only [eq_ratCast]
    push_cast
    ring
  have hq' : u'.getD 0 0 * q + u'.getD 1 0 = 0 := by exact_mod_cast hq
  field_simp
  linarith

end MTower

end Curves.MT
