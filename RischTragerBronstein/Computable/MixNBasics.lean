import RischTragerBronstein.Computable.MixNLog
import RischTragerBronstein.Computable.PrimNSound
import RischTragerBronstein.Liouville.HermiteExponential

/-!
# Mixed towers: rational constants, sums, the base `Kc(x)`, Hermite reduction at a level

Ported from `PrimNSound` (the base case of limited integration is the same), plus Hermite
reduction at a level of either kind (`hermite_value`), whose normality hypothesis is supplied by
`normal_prim` / `normal_exp` (no new constants: `hCall`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.MixN

open Tower.PrimN

namespace MixTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : List Kind} (T : MixTower Kc E ks)

lemma sem_lift_code (m : ℕ) (h : T.Tr m) (q : Code 1) :
    (((T.MP m h).sem (lift m q) : T.F m) : E) = evx Kc T.x q := T.sem_lift m h q

/-! ### Rational constants -/

lemma coe_ratCast {m : ℕ} (c : ℚ) : ((c : T.F m) : E) = (c : E) := by simp

include T in
lemma deriv_ratCast_E (c : ℚ) : (c : E)′ = 0 := by
  rw [← map_ratCast (algebraMap Kc E) c, deriv_algebraMap, T.hC, map_zero]

lemma deriv_ratCast {m : ℕ} (c : ℚ) : (c : T.F m)′ = 0 :=
  Subtype.ext (by rw [coe_deriv, coe_ratCast, T.deriv_ratCast_E]; rfl)

lemma sem_constC : ∀ (m : ℕ) (h : T.Tr m) (c : ℚ), (T.MP m h).sem (constC (m + 1) c) = (c : T.F m)
  | 0, h, c => by
    apply Subtype.ext
    change ((T.phi0 _ / T.phi0 _ : T.F 0) : E) = _
    rw [IntermediateField.coe_div, coe_phi0, coe_phi0, toPoly_ofHom', toPoly_ofHom']
    simp [constC, oneC, CPoly.toPoly]
  | m + 1, h, c => by
    rw [sem_MP_succ]
    change T.phi m (GPoly.toPoly _ [constC (m + 1) c]) /
      T.phi m (GPoly.toPoly _ [oneC (m + 1)]) = _
    rw [oneC_succ' ks m]
    simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one,
      sem_constC m, map_one, div_one]
    rw [phi, coe_eval₂RingHom, eval₂_C]
    exact map_ratCast _ c

/-! ### The sums `∑ cᵢ wᵢ` -/

/-- `∑ cᵢ wᵢ` in `E`. -/
noncomputable def zsum (cs : List ℚ) (W : List (Code 1)) : E :=
  (List.zipWith (fun (c : ℚ) w ↦ (c : E) * evx Kc T.x w) cs W).sum

lemma coe_zipWith_sum {m : ℕ} (h : T.Tr m) :
    ∀ (cs : List ℚ) (W : List (Code 1)),
      (((List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * (T.MP m h).sem (lift m w)) cs W).sum :
        T.F m) : E) = T.zsum cs W
  | [], W => by cases W <;> rfl
  | _ :: _, [] => rfl
  | c :: cs, w :: W => by
    have := coe_zipWith_sum h cs W
    simp only [zsum] at this ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons, IntermediateField.coe_add,
      IntermediateField.coe_mul, T.coe_ratCast, T.sem_lift_code, this]
    rfl

/-- The soundness statement of `limIntP` at level `m`. -/
def LimSound (m : ℕ) (h : T.Tr m) (A : Code (m + 1)) (W : List (Code 1)) (cs : List ℚ)
    (Y : Code (m + 1)) : Prop :=
  cs.length = W.length ∧
    (((T.MP m h).sem Y : T.F m) : E)′ + T.zsum cs W = (((T.MP m h).sem A : T.F m) : E)

/-! ### The base `Kc(x)` -/

lemma model0_sem_eq (q : GFrac ℚ) :
    T.model0.sem q = T.phi0 ((CPoly.toPoly q.1).map (algebraMap ℚ Kc)) /
      T.phi0 ((CPoly.toPoly q.2).map (algebraMap ℚ Kc)) := by
  change T.phi0 (GPoly.toPoly _ q.1) / T.phi0 (GPoly.toPoly _ q.2) = _
  rw [toPoly_ofHom', toPoly_ofHom']

lemma phi0_map_injective :
    Function.Injective (T.phi0.comp (mapRingHom (algebraMap ℚ Kc))) :=
  T.phi0_injective.comp (Polynomial.map_injective _ (algebraMap ℚ Kc).injective)

/-- **The rational decomposition** `q = L′ + r / s` of an element of `ℚ(x)`, inside `Kc(x)`. -/
lemma ratInt_spec (q : GFrac ℚ) :
    T.model0.sem q = (T.model0.sem (ratPart (ratInt q)))′ +
      T.phi0 ((CPoly.toPoly (ratInt q).r).map (algebraMap ℚ Kc)) /
        T.phi0 ((CPoly.toPoly (ratInt q).s).map (algebraMap ℚ Kc)) ∧
    Squarefree ((CPoly.toPoly (ratInt q).s).map (algebraMap ℚ Kc)) ∧
    ((CPoly.toPoly (ratInt q).r).map (algebraMap ℚ Kc)).degree <
      ((CPoly.toPoly (ratInt q).s).map (algebraMap ℚ Kc)).degree := by
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  obtain ⟨h1, h2, h3⟩ := CPoly.rationalCheck_sound_map (K := T.F 0) (algebraMap ℚ Kc) hD _ _
    (ratInt q) (CPoly.rationalCheck_integrateRational _ _ (CPoly.normCoeff_den_ne_zero q))
  refine ⟨?_, h2, h3⟩
  have hn := CPoly.normCoeff_spec _ T.phi0_map_injective q
  simp only [RingHom.comp_apply, coe_mapRingHom] at hn
  rw [T.model0_sem_eq, ← hn]
  simp only [phi0] at h1 ⊢
  rw [h1]
  congr 2
  symm
  change T.model0.sem ((opsM ks 0).add _ _) = _
  refine (T.model0.sem_add _ _).trans ?_
  rw [T.model0_sem_eq, T.model0_sem_eq]
  simp [CPoly.toPoly, phi0]

lemma sem0_add (a b : GFrac ℚ) :
    T.model0.sem ((ops₁g ℚ).add a b) = T.model0.sem a + T.model0.sem b := T.model0.sem_add a b

lemma sem0_neg (a : GFrac ℚ) : T.model0.sem ((ops₁g ℚ).neg a) = -T.model0.sem a :=
  T.model0.sem_neg a

lemma sem0_mul (a b : GFrac ℚ) :
    T.model0.sem ((ops₁g ℚ).mul a b) = T.model0.sem a * T.model0.sem b := T.model0.sem_mul a b

lemma sem0_const (c : ℚ) : T.model0.sem (([c], [1]) : GFrac ℚ) = (c : T.F 0) :=
  T.sem_constC 0 (fun _ h ↦ absurd h (Nat.not_lt_zero _)) c

/-- The fold computing the particular solution in `limIntP` at the base. -/
lemma sem_ratFold : ∀ (cs : List ℚ) (W : List (Code 1)) (acc : Code 1),
    T.model0.sem (ratFold cs W acc) =
    T.model0.sem acc - (List.zipWith (fun (c : ℚ) w ↦ (c : T.F 0) *
      T.model0.sem (ratPart (ratInt w))) cs W).sum
  | [], W, acc => by cases W <;> simp [ratFold]
  | _ :: _, [], acc => by simp [ratFold]
  | c :: cs, w :: W, acc => by
    rw [ratFold]
    refine (sem_ratFold cs W _).trans ?_
    have e : T.model0.sem ((ops₁g ℚ).add acc ((ops₁g ℚ).neg ((ops₁g ℚ).mul ([c], [1])
        (ratPart (ratInt w))))) = T.model0.sem acc - (c : T.F 0) * T.model0.sem (ratPart (ratInt w)) :=
      calc _ = T.model0.sem acc + T.model0.sem ((ops₁g ℚ).neg ((ops₁g ℚ).mul ([c], [1])
            (ratPart (ratInt w)))) := T.model0.sem_add _ _
        _ = T.model0.sem acc + -T.model0.sem ((ops₁g ℚ).mul ([c], [1]) (ratPart (ratInt w))) := by
            congr 1; exact T.model0.sem_neg _
        _ = T.model0.sem acc + -(T.model0.sem (([c], [1]) : GFrac ℚ) *
            T.model0.sem (ratPart (ratInt w))) := by
            congr 2; exact T.model0.sem_mul _ _
        _ = _ := by rw [T.sem0_const]; ring
    rw [e, List.zipWith_cons_cons, List.sum_cons]
    ring

/-- **Soundness at the base** `Kc(x)`. -/
theorem limIntM_sound_zero (h : T.Tr 0) (A : Code 1) (W : List (Code 1)) (cs : List ℚ)
    (Y : Code 1) (hres : limIntM ks 0 A W = some (cs, Y)) : T.LimSound 0 h A W cs Y := by
  simp only [limIntM] at hres
  split at hres
  · exact absurd hres (by simp)
  rename_i cs' hcrit
  simp only [Option.some.injEq, Prod.mk.injEq] at hres
  obtain ⟨hcs, rfl⟩ := hres
  subst cs'
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  obtain ⟨hA, hsA, hdA⟩ := T.ratInt_spec A
  have hηs : ∀ η ∈ W.map (fun w ↦ ((ratInt w).r, (ratInt w).s)),
      Squarefree ((CPoly.toPoly η.2).map (algebraMap ℚ Kc)) ∧
        ((CPoly.toPoly η.1).map (algebraMap ℚ Kc)).degree <
          ((CPoly.toPoly η.2).map (algebraMap ℚ Kc)).degree := by
    intro η hη
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hη
    exact ⟨(T.ratInt_spec w).2.1, (T.ratInt_spec w).2.2⟩
  have hfrac := CPoly.limitedCritN_frac (K := T.F 0) (algebraMap ℚ Kc) hD hsA hdA hηs hcrit
  obtain ⟨hlen, -⟩ := CPoly.limitedCritN_sound hcrit
  rw [List.length_map] at hlen
  refine ⟨hlen, ?_⟩
  set L : Code 1 → T.F 0 := fun w ↦ T.model0.sem (ratPart (ratInt w)) with hL
  set R : Code 1 → T.F 0 := fun w ↦ T.phi0 ((CPoly.toPoly (ratInt w).r).map (algebraMap ℚ Kc)) /
    T.phi0 ((CPoly.toPoly (ratInt w).s).map (algebraMap ℚ Kc)) with hR
  have hfrac' : R A = (List.zipWith (fun (c : ℚ) w ↦ (c : T.F 0) * R w) cs W).sum := by
    rw [← sum_fin_map_eq_zipWith (fun w ↦ ((ratInt w).r, (ratInt w).s))
      (fun (c : ℚ) (η : CPoly ℚ × CPoly ℚ) ↦ (c : T.F 0) *
        (T.phi0 ((CPoly.toPoly η.1).map (algebraMap ℚ Kc)) /
          T.phi0 ((CPoly.toPoly η.2).map (algebraMap ℚ Kc)))) cs W hlen]
    simp only [hR, phi0]
    rw [hfrac]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    apply Subtype.ext
    rw [← phi0, coe_phi0, aeval_C, T.coe_ratCast]
    exact eq_ratCast ((algebraMap Kc E).comp (algebraMap ℚ Kc)) _
  have hsem : ∀ w, T.model0.sem w = (L w)′ + R w := fun w ↦ (T.ratInt_spec w).1
  have hfun : (fun (c : ℚ) (w : Code 1) ↦ (c : T.F 0) * (T.MP 0 h).sem (lift 0 w)) =
      fun (c : ℚ) w ↦ (c : T.F 0) * ((L w)′ + R w) := by
    funext c w
    exact congrArg _ (hsem w)
  suffices hF : (T.model0.sem (ratFold cs W (ratPart (ratInt A))))′ + (List.zipWith (fun (c : ℚ) (w : Code 1) ↦ (c : T.F 0) *
          (T.MP 0 h).sem (lift 0 w)) cs W).sum = T.model0.sem A by
    have := congrArg (fun z : T.F 0 ↦ (z : E)) hF
    simp only [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum] at this
    exact this
  rw [hfun, zipWith_sum_add, T.sem_ratFold, map_sub, deriv_zipWith_sum _ T.deriv_ratCast, hsem A,
    hfrac']
  ring

/-! ### Hermite reduction at a level -/

lemma coe_phi_C (m : ℕ) (z : T.F m) : ((T.phi m (C z) : T.F (m + 1)) : E) = (z : E) := by
  rw [coe_phi, aeval_C]
  rfl


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
  have htn : (t ^ n : E) ≠ 0 := pow_ne_zero n ht0
  have hz : (aeval t P / t ^ n)′ = 0 := by
    rw [Derivation.leibniz_div, show (t ^ n : E) = aeval (R := T.F m) t (X ^ n) by simp, hder, hder]
    have := congrArg (aeval t) hP
    simp only [map_mul, map_pow, aeval_X] at this
    simp only [map_pow, aeval_X, smul_eq_mul]
    rw [mul_comm (t ^ n) _, this]
    simp
  obtain ⟨κ, hκ⟩ := T.hCall _ hz
  refine ⟨algebraMap Kc (T.F m) κ, hinjt ?_⟩
  rw [map_mul, map_pow, aeval_X, aeval_C]
  change aeval t P = algebraMap Kc E κ * t ^ n
  rw [hκ]
  field_simp

/-- At a primitive level every irreducible polynomial is normal. -/
lemma normal_prim (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) {η : Code 1}
    (hk : kind ks m = .prim η) (p : (T.F m)[X]) (hp : Irreducible p) :
    ¬p ∣ implicitDeriv (T.wPoly m) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (C (T.ratF m η))
  have hw : T.wPoly m = C (T.ratF m η) := by simp only [wPoly, hk]
  rw [hw]
  exact not_dvd_deriv_of_irreducible_primitive (T.ratF m η) (fun _ ↦ rfl)
    (fun P hP ↦ by
      obtain ⟨e, he⟩ := T.const_poly m htr P 0 (by
        rw [hw]; change P′ * X ^ 0 = P * implicitDeriv (C (T.ratF m η)) (X ^ 0)
        simp [hP])
      exact ⟨e, by simpa using he⟩) hp

/-- At an exponential level every irreducible polynomial other than `X` is normal. -/
lemma normal_exp (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) {b : Code 1}
    (hk : kind ks m = .exp b) (p : (T.F m)[X]) (hp : Irreducible p) (hX : ¬X ∣ p) :
    ¬p ∣ implicitDeriv (T.wPoly m) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  have hw : T.wPoly m = C (T.ratF m b) * X := by simp only [wPoly, hk]
  intro hsp
  refine hX (dvd_X_of_irreducible_special (T.ratF m b)
    (fun P ↦ by change implicitDeriv (T.wPoly m) P = _; rw [hw]) (fun P n hP ↦ T.const_poly m htr P n hP)
    hp hsp)

/-- **Hermite reduction at level `m + 1`**, as an identity of values, when the primes of the
denominator are normal. -/
lemma hermite_value (m : ℕ) (hm : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    (A D : GPoly (Code (m + 1))) (hD : GPoly.toPoly (T.MP m hm) D ≠ 0)
    (hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m hm) D →
      ¬p ∣ implicitDeriv (T.wPoly m) p) :
    T.phi m (GPoly.toPoly (T.MP m hm) A) / T.phi m (GPoly.toPoly (T.MP m hm) D) =
      (T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK ks m) A D).gn) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK ks m) A D).gd))′ +
      T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK ks m) A D).b) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK ks m) A D).s) ∧
    Squarefree (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK ks m) A D).s) := by
  set M := T.MP m hm
  have hnormal' : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M (wK ks m)) p := fun p hp hpD ↦ by
    rw [T.toPoly_wK]
    exact hnormal p hp hpD
  have hc := GPoly.hermiteCheck_hermite M (wK ks m) A D hnormal' hD
  obtain ⟨hD0, hgd0, hs0, hid, hsq⟩ := (GPoly.hermiteCheck_iff M _ _ _ _).mp hc
  rw [T.toPoly_wK] at hid
  refine ⟨?_, GPoly.squarefreeCheck_sound M hsq⟩
  have hinj := T.phi_injective htr
  have h1 : T.phi m (GPoly.toPoly M D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have h2 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsM ks m) (wK ks m) A D).gd) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hgd0
  have h3 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsM ks m) (wK ks m) A D).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hs0
  have hidL := congrArg (T.phi m) hid
  simp only [map_mul, map_add, map_sub] at hidL
  rw [Derivation.leibniz_div, T.deriv_phi, T.deriv_phi]
  simp only [smul_eq_mul]
  field_simp
  linear_combination hidL

end MixTower

end Tower.MixN
