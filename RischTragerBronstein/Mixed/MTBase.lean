import RischTragerBronstein.Mixed.MTStructure
import RischTragerBronstein.Computable.NestXRdeLoop

/-!
# Mixed towers over a curve: the models of a level and its derivation

Ported from `Tower.NestX` (`NestXBase`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


section Level

variable (m : ℕ) (h : T.Tr (m + 1))

/-- The model of level `m`. -/
noncomputable abbrev MX : CField (LC m) (T.F m) (MO Fc ks m) :=
  T.MP m fun i hi ↦ h i (by omega)

/-- The model of level `m + 1`, typed with pairs of polynomials. -/
noncomputable abbrev M1X : CField (GPoly (LC m) × GPoly (LC m)) (T.F (m + 1))
    ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) := T.MP (m + 1) h

/-- The value at `tₘ` of a polynomial over level `m`. -/
noncomputable abbrev σX (p : GPoly (LC m)) : T.F (m + 1) :=
  T.phi m (GPoly.toPoly (T.MX m h) p)

lemma semX (q : GPoly (LC m) × GPoly (LC m)) :
    (T.M1X m h).sem q = T.σX m h q.1 / T.σX m h q.2 := rfl

include h in
lemma phi_injX : Function.Injective (T.phi m) := T.phi_injective (h m (by omega))

lemma σX_eq_zero_iff (p : GPoly (LC m)) :
    T.σX m h p = 0 ↔ GPoly.isZero (MO Fc ks m) p = true := by
  rw [GPoly.isZero_iff (T.MX m h), σX, map_eq_zero_iff _ (T.phi_injX m h)]

lemma semX_cleanG (q : GPoly (LC m) × GPoly (LC m)) :
    (T.M1X m h).sem (cleanG (MO Fc ks m) q) = (T.M1X m h).sem q := by
  unfold cleanG
  split_ifs with hz
  · rw [T.semX, T.semX, (T.σX_eq_zero_iff m h q.2).mpr hz]
    simp [σX, (T.MX m h).sem_one]
  · rfl

lemma σX_cleanG_ne (q : GPoly (LC m) × GPoly (LC m)) :
    T.σX m h (cleanG (MO Fc ks m) q).2 ≠ 0 := by
  unfold cleanG
  split_ifs with hz
  · simp [σX, (T.MX m h).sem_one]
  · rw [Ne, T.σX_eq_zero_iff]; exact hz

lemma σX_mul (a b : GPoly (LC m)) :
    T.σX m h (GPoly.mul (MO Fc ks m) a b) = T.σX m h a * T.σX m h b := by
  simp [σX]

lemma σX_one : T.σX m h [(MO Fc ks m).one] = 1 := by
  simp [σX, (T.MX m h).sem_one]

lemma semX_poly (Q : GPoly (LC m)) :
    (T.M1X m h).sem (Q, [(MO Fc ks m).one]) = T.σX m h Q := by
  rw [T.semX, T.σX_one, div_one]

lemma toPoly_wKX : GPoly.toPoly (T.MX m h) (wKC (MO Fc ks m) (ks m)) = T.wPoly m :=
  T.toPoly_wKC m _ (T.lt_of_transcendental (h m (by omega)))

lemma deriv_σX (p : GPoly (LC m)) :
    (T.σX m h p)′ = T.phi m (implicitDeriv (GPoly.toPoly (T.MX m h) (wKC (MO Fc ks m) (ks m)))
      (GPoly.toPoly (T.MX m h) p)) := by
  rw [σX, T.deriv_phi, T.toPoly_wKX]

lemma sem_cstX (q : ℚ) : (T.MX m h).sem (mcst Fc ks m q) = (q : T.F m) := T.sem_mcst m _ q

lemma phi_C_ratX (q : ℚ) : T.phi m (C ((q : ℚ) : T.F m)) = ((q : ℚ) : T.F (m + 1)) := by
  rw [T.phi_C]; exact map_ratCast _ q

lemma algebraMap_ratX {k : ℕ} (q : ℚ) :
    algebraMap Cc (T.F k) (algebraMap ℚ Cc q) = ((q : ℚ) : T.F k) := by
  rw [← map_ratCast (algebraMap Cc (T.F k)), ← map_ratCast (algebraMap ℚ Cc)]; rfl

lemma toPoly_peQX (kap : ℕ) (D : GPoly (LC m)) :
    GPoly.toPoly (T.MX m h) (peQ (MO Fc ks m) kap D) = X ^ kap * GPoly.toPoly (T.MX m h) D := by
  rw [peQ, GPoly.toPoly_append, List.length_replicate]
  have : GPoly.toPoly (T.MX m h) (List.replicate kap (MO Fc ks m).zero) = 0 := by
    induction kap with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, GPoly.toPoly_cons, ih, (T.MX m h).sem_zero]; simp
  rw [this, zero_add]

/-- A relation of the constant system on polynomials over `1`, as a polynomial identity. -/
lemma consys_poly_relX (vs : List (LC (m + 1))) (N : ℕ)
    (g : ℕ → GPoly (LC m)) (hlen : vs.length = N)
    (hvs : ∀ l < N, vs.getD l (MO Fc ks (m + 1)).zero =
      ((g l, [(MO Fc ks m).one]) : LC (m + 1)))
    (u : CPoly ℚ) (hu : u ∈ mrel Fc ks (m + 1) vs) :
    ∑ l ∈ Finset.range N, C ((u.getD l 0 : ℚ) : T.F m) * GPoly.toPoly (T.MX m h) (g l) = 0 := by
  have hs := T.mrel_sound (m + 1) h _ u hu
  rw [NestTower.zipWith_sum_range _ 0 (MO Fc ks (m + 1)).zero _ _ (by simp)] at hs
  apply T.phi_injX m h
  rw [map_zero, ← hs, map_sum]
  simp only [List.length_map, List.length_range]
  rw [hlen]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := Finset.mem_range.mp hl
  have hq : algebraMap Cc (T.F (m + 1)) (algebraMap ℚ Cc (u.getD l 0)) =
      T.phi m (C ((u.getD l 0 : ℚ) : T.F m)) := by
    rw [eq_ratCast (algebraMap ℚ Cc), map_ratCast, T.phi_C, map_ratCast]
  rw [NestTower.getD_range_map _ _ (by simpa [hlen] using hl'), hq, hvs l hl', map_mul]
  congr 1
  change _ = T.σX m h _ / T.σX m h [(MO Fc ks m).one]
  rw [T.σX_one, div_one]

end Level

section ExpLevel

variable (m : ℕ) (h : T.Tr (m + 1)) {a : LC m} (hk : ks m = .exp a)

/-- The exponent derivative `b = aₘ′`. -/
noncomputable abbrev bX (a : LC m) : T.F m := ((T.MX m h).sem a)′

include hk in
lemma bX_eq : T.bX m h a = (T.val m a)′ := by rw [bX, T.sem_MP_F]

include hk in
lemma wPoly_eq_bX : T.wPoly m = C (T.bX m h a) * X := by
  rw [T.wPoly_exp (T.lt_of_transcendental (h m (by omega))) hk, T.bX_eq m h hk]

include hk in
lemma toPoly_wK_exp : GPoly.toPoly (T.MX m h) (wKC (MO Fc ks m) (ks m)) = C (T.bX m h a) * X := by
  rw [T.toPoly_wKX, T.wPoly_eq_bX m h hk]

include hk in
lemma deriv_phi_expX (P : (T.F m)[X]) :
    (T.phi m P)′ = T.phi m (implicitDeriv (C (T.bX m h a) * X) P) := by
  rw [T.deriv_phi, T.wPoly_eq_bX m h hk]

include hk in
lemma deriv_ts_expX : (T.ts m)′ = algebraMap (T.F m) L (T.bX m h a) * T.ts m := by
  rw [T.deriv_ts_aeval m, T.wPoly_eq_bX m h hk, map_mul, aeval_C, aeval_X]

end ExpLevel

section PrimLevel

variable (m : ℕ) (h : T.Tr (m + 1)) {η : LC m} (hk : ks m = .prim η)

/-- The derivative `ηₘ` of a logarithmic level. -/
noncomputable abbrev ηX (η : LC m) : T.F m := (T.MX m h).sem η

include hk in
lemma ηX_eq : T.ηX m h η = T.val m η := T.sem_MP_F _ _ _

include hk in
lemma wPoly_eq_ηX : T.wPoly m = C (T.ηX m h η) := by
  rw [T.wPoly_prim (T.lt_of_transcendental (h m (by omega))) hk, T.ηX_eq m h hk]

include hk in
lemma toPoly_wK_prim : GPoly.toPoly (T.MX m h) (wKC (MO Fc ks m) (ks m)) = C (T.ηX m h η) := by
  rw [T.toPoly_wKX, T.wPoly_eq_ηX m h hk]

include hk in
lemma deriv_phi_primX (P : (T.F m)[X]) :
    (T.phi m P)′ = T.phi m (implicitDeriv (C (T.ηX m h η)) P) := by
  rw [T.deriv_phi, T.wPoly_eq_ηX m h hk]

include hk in
lemma deriv_ts_primX : (T.ts m)′ = algebraMap (T.F m) L (T.ηX m h η) := by
  rw [T.deriv_ts_aeval m, T.wPoly_eq_ηX m h hk, aeval_C]

end PrimLevel

/-! ### Consequences of `MixHyp` at a level -/

section Hyp

variable {n : ℕ} (hM : T.MixHyp n)

include hM in
lemma MixHyp.homX {m : ℕ} (hm : m < n) {a : LC m} (hk : ks m = .exp a) (h : T.Tr (m + 1)) :
    ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + (j : T.F m) * T.bX m h a * e ≠ 0 := by
  intro j hj e he
  rw [T.bX_eq m h hk]
  exact hM.hom m hm a hk j hj e he

include hM in
lemma MixHyp.ndX {m : ℕ} (hm : m < n) {η : LC m} (hk : ks m = .prim η) (h : T.Tr (m + 1)) :
    ∀ y : T.F m, y′ ≠ T.ηX m h η := by
  intro y
  rw [T.ηX_eq m h hk]
  exact hM.nd m hm η hk y

end Hyp


end MTower

end Curves.MT
