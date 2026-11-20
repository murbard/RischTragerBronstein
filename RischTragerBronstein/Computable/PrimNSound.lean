import RischTragerBronstein.Computable.PrimNTower
import RischTragerBronstein.Computable.PrimNPoly
import RischTragerBronstein.Computable.GHermiteComplete
import RischTragerBronstein.Computable.LogTimes
import RischTragerBronstein.Computable.LimitedCritNDecide
import RischTragerBronstein.Computable.RationalComplete
import RischTragerBronstein.Liouville.HermitePrimitive
import RischTragerBronstein.Liouville.PrimitiveConstants

/-!
# Towers of `n` primitives: soundness of parametric limited integration

`limIntP_sound`: if `limIntP ηs m A W = some (cs, Y)` then `Y′ + ∑ cᵢ wᵢ = A` in `F m`. The only
hypothesis on the tower is `ND m`: each `ηᵢ` (`i < m`) is not a derivative in `F i`, which makes
every `tᵢ` transcendental (so that the models exist) and every irreducible polynomial of
`F i [tᵢ]` normal (so that Hermite reduction is correct).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.PrimN

/-! ### List sums -/

section Lists

variable {K : Type*} [Field K]

lemma zipWith_sum_add {β : Type*} (f g : β → K) :
    ∀ (cs : List ℚ) (W : List β),
      (List.zipWith (fun (c : ℚ) w ↦ (c : K) * (f w + g w)) cs W).sum =
        (List.zipWith (fun (c : ℚ) w ↦ (c : K) * f w) cs W).sum +
          (List.zipWith (fun (c : ℚ) w ↦ (c : K) * g w) cs W).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, w :: W => by
    simp only [List.zipWith_cons_cons, List.sum_cons, zipWith_sum_add f g cs W]
    ring

lemma zipWith_sum_sub {β : Type*} (f g : β → K) :
    ∀ (cs : List ℚ) (W : List β),
      (List.zipWith (fun (c : ℚ) w ↦ (c : K) * (f w - g w)) cs W).sum =
        (List.zipWith (fun (c : ℚ) w ↦ (c : K) * f w) cs W).sum -
          (List.zipWith (fun (c : ℚ) w ↦ (c : K) * g w) cs W).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, w :: W => by
    simp only [List.zipWith_cons_cons, List.sum_cons, zipWith_sum_sub f g cs W]
    ring

lemma zipWith_sum_zero {β : Type*} (f : β → K) (W : List β) :
    (List.zipWith (fun (c : ℚ) w ↦ (c : K) * f w) (W.map fun _ ↦ (0 : ℚ)) W).sum = 0 := by
  induction W with
  | nil => simp
  | cons w W ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]
    simp

variable [Differential K]

lemma deriv_zipWith_sum {β : Type*} (f : β → K) (hc : ∀ c : ℚ, (c : K)′ = 0) :
    ∀ (cs : List ℚ) (W : List β),
      ((List.zipWith (fun (c : ℚ) w ↦ (c : K) * f w) cs W).sum)′ =
        (List.zipWith (fun (c : ℚ) w ↦ (c : K) * (f w)′) cs W).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, w :: W => by
    simp only [List.zipWith_cons_cons, List.sum_cons, map_add, Derivation.leibniz, hc,
      smul_eq_mul, mul_zero, add_zero, deriv_zipWith_sum f hc cs W]

end Lists

lemma sum_fin_map_eq_zipWith {β γ M : Type*} [AddCommMonoid M] (f : β → γ) (g : ℚ → γ → M) :
    ∀ (cs : List ℚ) (W : List β), cs.length = W.length →
      ∑ i : Fin (W.map f).length, g (cs.getD i 0) ((W.map f)[i]) =
        (List.zipWith (fun c w ↦ g c (f w)) cs W).sum
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, w :: W, h => by
    show ∑ i : Fin ((W.map f).length + 1), g ((c :: cs).getD i 0) ((f w :: W.map f)[i]) = _
    rw [Fin.sum_univ_succ]
    simp only [List.zipWith_cons_cons, List.sum_cons]
    rw [← sum_fin_map_eq_zipWith f g cs W (by simpa using h)]
    simp

namespace PrimTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : List (Code 1)} (T : PrimTower Kc E ηs)

/-! ### The non-derivative hypothesis -/

/-- `ηᵢ` is not a derivative in `F i`, for every `i < m`. -/
def ND (m : ℕ) : Prop := ∀ i < m, ∀ y : T.F i, y′ ≠ T.etaF i i

lemma ND.mono {T : PrimTower Kc E ηs} {m k : ℕ} (h : T.ND m) (hk : k ≤ m) : T.ND k :=
  fun i hi ↦ h i (by omega)

lemma tr_of_ND {m : ℕ} (h : T.ND m) : T.Tr m := fun i hi ↦
  transcendental_primitive (T.etaF i i) (T.deriv_ts_F i) (h i hi)

/-- In `F m [tₘ]`, every irreducible polynomial is normal. -/
lemma normal {m : ℕ} (hη : ∀ y : T.F m, y′ ≠ T.etaF m m) (p : (T.F m)[X]) (hp : Irreducible p) :
    ¬p ∣ implicitDeriv (C (T.etaF m m)) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (C (T.etaF m m))
  exact not_dvd_deriv_of_irreducible_primitive (T.etaF m m) (fun _ ↦ rfl)
    (fun P hP ↦ const_of_implicitDeriv_eq_zero _ hη hP) hp

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
    rw [oneC_succ ηs m]
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
      IntermediateField.coe_mul, T.coe_ratCast, T.sem_lift, this]
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
  change T.model0.sem ((opsP ηs 0).add _ _) = _
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
theorem limIntP_sound_zero (h : T.Tr 0) (A : Code 1) (W : List (Code 1)) (cs : List ℚ)
    (Y : Code 1) (hres : limIntP ηs 0 A W = some (cs, Y)) : T.LimSound 0 h A W cs Y := by
  simp only [limIntP] at hres
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

/-! ### The step `F m → F (m + 1)` -/

lemma coe_phi_C (m : ℕ) (z : T.F m) : ((T.phi m (C z) : T.F (m + 1)) : E) = (z : E) := by
  rw [coe_phi, aeval_C]
  rfl

/-- **Hermite reduction at level `m + 1`**, as an identity of values. -/
lemma hermite_value (m : ℕ) (hm : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    (hη : ∀ y : T.F m, y′ ≠ T.etaF m m) (A D : GPoly (Code (m + 1)))
    (hD : GPoly.toPoly (T.MP m hm) D ≠ 0) :
    T.phi m (GPoly.toPoly (T.MP m hm) A) / T.phi m (GPoly.toPoly (T.MP m hm) D) =
      (T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsP ηs m) (wP ηs m) A D).gn) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsP ηs m) (wP ηs m) A D).gd))′ +
      T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsP ηs m) (wP ηs m) A D).b) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsP ηs m) (wP ηs m) A D).s) ∧
    Squarefree (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsP ηs m) (wP ηs m) A D).s) := by
  set M := T.MP m hm
  have hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M (wP ηs m)) p := fun p hp _ ↦ by
    rw [T.toPoly_wP]
    exact T.normal hη p hp
  have hc := GPoly.hermiteCheck_hermite M (wP ηs m) A D hnormal hD
  obtain ⟨hD0, hgd0, hs0, hid, hsq⟩ := (GPoly.hermiteCheck_iff M _ _ _ _).mp hc
  rw [T.toPoly_wP] at hid
  refine ⟨?_, GPoly.squarefreeCheck_sound M hsq⟩
  have hinj := T.phi_injective htr
  have h1 : T.phi m (GPoly.toPoly M D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have h2 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsP ηs m) (wP ηs m) A D).gd) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hgd0
  have h3 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsP ηs m) (wP ηs m) A D).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hs0
  have hidL := congrArg (T.phi m) hid
  simp only [map_mul, map_add, map_sub] at hidL
  rw [Derivation.leibniz_div, T.deriv_phi, T.deriv_phi]
  simp only [smul_eq_mul]
  field_simp
  linear_combination hidL

/-- **Soundness, inductive step.** -/
theorem limIntP_sound_succ (m : ℕ) (hnd : T.ND (m + 1))
    (ih : ∀ A W cs Y, limIntP ηs m A W = some (cs, Y) →
      T.LimSound m (T.tr_of_ND (hnd.mono (Nat.le_succ m))) A W cs Y)
    (A : Code (m + 2)) (W : List (Code 1)) (cs : List ℚ) (Y : Code (m + 2))
    (hres : limIntP ηs (m + 1) A W = some (cs, Y)) :
    T.LimSound (m + 1) (T.tr_of_ND hnd) A W cs Y := by
  set hm := T.tr_of_ND (hnd.mono (Nat.le_succ m)) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) (T.tr_of_ND hnd) with hM'
  have htr : Transcendental (T.F m) (T.ts m) := T.tr_of_ND hnd m (Nat.lt_succ_self m)
  have hη : ∀ y : T.F m, y′ ≠ T.etaF m m := hnd m (Nat.lt_succ_self m)
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  have hsem' : ∀ q : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  have hcst : ∀ c : ℚ, M.sem (constC (m + 1) c) = (c : T.F m) := T.sem_constC m hm
  simp only [limIntP] at hres
  split_ifs at hres with hz hr0
  · -- a zero denominator: the value is `0`
    simp only [Option.some.injEq, Prod.mk.injEq] at hres
    obtain ⟨rfl, rfl⟩ := hres
    refine ⟨by simp, ?_⟩
    have hA2 : GPoly.toPoly M A.2 = 0 := (GPoly.isZero_iff M _).mp hz
    rw [M'.sem_zero, hsem A, hA2, map_zero, div_zero]
    simp only [ZeroMemClass.coe_zero, map_zero, zero_add, zsum]
    exact zipWith_sum_zero _ W
  -- Hermite reduction and the division
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr hη A.1 A.2 hA2
  generalize GPoly.hermite (opsP ηs m) (wP ηs m) A.1 A.2 = hr at hres hval hr0 hsq
  have hdm := GPoly.divMod_spec M hr.b hr.s
  generalize GPoly.divMod (opsP ηs m) hr.b hr.s = qr at hres hdm hr0
  have hr0' : GPoly.toPoly M qr.2 = 0 := (GPoly.isZero_iff M _).mp hr0
  rw [hr0', add_zero] at hdm
  -- the polynomial part
  generalize hpd : polyDown (opsP ηs m) (lift m (eta ηs m)) (eta ηs m) (limIntP ηs m)
    (constC (m + 1)) qr.1 (qr.1.length - 1) (opsP ηs m).zero [] = pd at hres
  rcases pd with _ | ⟨Q, Ys⟩
  · exact absurd hres (by simp)
  simp only at hres
  generalize hl : limIntP ηs m ((opsP ηs m).add (qr.1.getD 0 (opsP ηs m).zero)
    ((opsP ηs m).neg ((opsP ηs m).mul Q (lift m (eta ηs m))))) (eta ηs m :: W) = l at hres
  rcases l with _ | ⟨_ | ⟨e, cs'⟩, Y₀⟩
  · exact absurd hres (by simp)
  · exact absurd hres (by simp)
  simp only [Option.some.injEq, Prod.mk.injEq] at hres
  obtain ⟨hcs, rfl⟩ := hres
  subst cs'
  -- the solver at level `m`, in `F m`
  have hsolve : ∀ G W r, limIntP ηs m G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
        M.sem G := by
    intro G W r hr
    obtain ⟨h1, h2⟩ := ih G W r.1 r.2 hr
    refine ⟨h1, Subtype.ext ?_⟩
    rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
    exact h2
  have hηv : M.sem (lift m (eta ηs m)) = T.etaF m m := T.sem_lift_eta m hm
  have hinit : implicitDeriv (C (M.sem (lift m (eta ηs m))))
      (X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M ((opsP ηs m).zero :: [])) =
      X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M (qr.1.drop (qr.1.length - 1 + 1)) +
        C (((qr.1.length - 1 : ℕ) + 1 : T.F m) * M.sem (opsP ηs m).zero *
          M.sem (lift m (eta ηs m))) * X ^ (qr.1.length - 1) := by
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [M.sem_zero]
  have hpoly := polyDown_sound M (lift m (eta ηs m)) (eta ηs m) (fun w ↦ M.sem (lift m w))
    (limIntP ηs m) (constC (m + 1)) hsolve rfl (T.sem_constC m hm) T.deriv_ratCast qr.1
    (qr.1.length - 1) (opsP ηs m).zero [] Q Ys hinit hpd
  obtain ⟨hlen, hY₀⟩ := hsolve _ _ _ hl
  simp only [List.length_cons, add_left_inj] at hlen
  refine ⟨hlen, ?_⟩
  simp only [List.zipWith_cons_cons, List.sum_cons, M.sem_add, M.sem_neg, M.sem_mul] at hY₀
  rw [hηv] at hY₀ hpoly
  set η := T.etaF m m
  set SF := (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) cs W).sum with hSF
  -- the polynomial identity for the output
  have hout : implicitDeriv (C η) (GPoly.toPoly M (Y₀ :: (opsP ηs m).add Q (constC (m + 1) e) :: Ys))
      = GPoly.toPoly M qr.1 - C SF := by
    have hsplit : GPoly.toPoly M (Y₀ :: (opsP ηs m).add Q (constC (m + 1) e) :: Ys) =
        C (M.sem Y₀) + C (e : T.F m) * X + X * GPoly.toPoly M (Q :: Ys) := by
      simp only [GPoly.toPoly_cons, M.sem_add, hcst, C_add]
      ring
    have hq : GPoly.toPoly M qr.1 = C (M.sem (qr.1.getD 0 (opsP ηs m).zero)) +
        X * GPoly.toPoly M (qr.1.drop 1) := by
      rw [← toPoly_drop M qr.1 0, List.drop_zero]
    rw [hsplit, map_add, map_add, hpoly, hq, implicitDeriv_C, Derivation.leibniz, implicitDeriv_C,
      implicitDeriv_X, T.deriv_ratCast]
    have hY' : (M.sem Y₀)′ = M.sem (qr.1.getD 0 (opsP ηs m).zero) - M.sem Q * η - (e : T.F m) * η -
        SF := by linear_combination hY₀
    rw [hY']
    simp only [smul_eq_mul, C_0, mul_zero, add_zero, C_sub, C_mul]
    ring
  -- values
  have hone : GPoly.toPoly M [(opsP ηs m).one] = 1 := by simp [M.sem_one]
  have hvalY : M'.sem ((opsP ηs (m + 1)).add (hr.gn, hr.gd)
      (Y₀ :: (opsP ηs m).add Q (constC (m + 1) e) :: Ys, [(opsP ηs m).one])) =
      T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) +
        T.phi m (GPoly.toPoly M (Y₀ :: (opsP ηs m).add Q (constC (m + 1) e) :: Ys)) := by
    refine (M'.sem_add _ _).trans ?_
    rw [hsem', hsem']
    simp only [hone, map_one, div_one]
  have hbs : T.phi m (GPoly.toPoly M hr.b) / T.phi m (GPoly.toPoly M hr.s) =
      T.phi m (GPoly.toPoly M qr.1) := by
    have hs0 : T.phi m (GPoly.toPoly M hr.s) ≠ 0 :=
      (map_ne_zero_iff _ (T.phi_injective htr)).mpr hsq.ne_zero
    rw [hdm, map_mul, mul_div_assoc, div_self hs0, mul_one]
  have hfinal : (M'.sem ((opsP ηs (m + 1)).add (hr.gn, hr.gd)
      (Y₀ :: (opsP ηs m).add Q (constC (m + 1) e) :: Ys, [(opsP ηs m).one])))′ +
        T.phi m (C SF) = M'.sem A := by
    rw [hvalY, map_add, T.deriv_phi, hout, hsem A, hval, hbs, map_sub]
    ring
  have := congrArg (fun z : T.F (m + 1) ↦ (z : E)) hfinal
  simp only [IntermediateField.coe_add, coe_deriv, T.coe_phi_C, hSF, hM, hM'] at this
  rw [T.coe_zipWith_sum] at this
  exact this

/-- **Soundness of parametric limited integration** in `F m`: if `limIntP ηs m A W` returns
`(cs, Y)`, then `Y′ + ∑ cᵢ wᵢ = A`. -/
theorem limIntP_sound : ∀ (m : ℕ) (hnd : T.ND m) (A : Code (m + 1)) (W : List (Code 1))
    (cs : List ℚ) (Y : Code (m + 1)), limIntP ηs m A W = some (cs, Y) →
    T.LimSound m (T.tr_of_ND hnd) A W cs Y
  | 0, _, A, W, cs, Y, h => T.limIntP_sound_zero _ A W cs Y h
  | m + 1, hnd, A, W, cs, Y, h =>
    T.limIntP_sound_succ m hnd (fun A W cs Y h' ↦ limIntP_sound m (hnd.mono (Nat.le_succ m))
      A W cs Y h') A W cs Y h

end PrimTower

end Tower.PrimN
