import RischTragerBronstein.Mixed.LTRel
import RischTragerBronstein.Computable.NestPPoly

/-!
# Towers of logarithms over a curve: parametric exact integration

`lex Fc us m W` returns a basis of the pairs `(e, y)`, `e ∈ ℚⁿ`, `y` a level-`m` code, with
`y′ = ∑ eᵢ wᵢ`, and it is **complete for constant coefficients** in every realization:

* level `0`: the Risch solver on the curve with potential `0` (`curveRde`);
* level `m + 1`: every weight is Hermite-reduced in `tₘ`, `wᵢ = gᵢ′ + Pᵢ + rᵢ / sᵢ`; a solution
  forces `∑ cᵢ rᵢ / sᵢ = 0` (sums of proper fractions are not derivatives: every irreducible is
  normal for a primitive) — a constant system (`lrel`) — and then `y − ∑ cᵢ gᵢ` is a polynomial
  in `tₘ` solving the parametric polynomial problem (`Tower.NestP.paramPoly`), whose solver one
  level down is `lex m`.

This file: the definitions, basic facts on the levels, and the level-`0` specification.
The inductive step is `LTExactStep`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.LT

open CPoly Sup
open Tower.NestP (lcombCode lcombGP vcomb paramPoly LimSpec sQ sC Dη polySumC polySumQ)

/-! ### The algorithm -/

variable (Fc : BPoly ℚ) (us : (m : ℕ) → LC m)

/-- The rational `q` as a code of level `m`. -/
def lcst : (m : ℕ) → ℚ → LC m
  | 0, q => ratCode Fc q
  | m + 1, q => (([lcst m q] : GPoly (LC m)), ([(LO Fc us m).one] : GPoly (LC m)))

/-- The zero code of level `m`. -/
def zc (m : ℕ) : LC m := (LO Fc us m).zero

/-- The Hermite data of a (cleaned) weight at level `m + 1`. -/
def hermW (m : ℕ) (w : LC (m + 1)) : GPoly.HermiteResult (LC m) :=
  let w' : GFrac (LC m) := if GPoly.isZero (LO Fc us m) (w : GFrac (LC m)).2 then
    (([] : GPoly (LC m)), [(LO Fc us m).one]) else w
  GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2

/-- The simple parts `rᵢ / sᵢ` of the weights, as codes of level `m + 1`. -/
def simpleCodes (m : ℕ) (W : List (LC (m + 1))) : List (LC (m + 1)) :=
  (List.zip ((W.map (hermW Fc us m)).map fun h ↦ GPoly.divMod (LO Fc us m) h.b h.s)
    (W.map (hermW Fc us m))).map fun p ↦ ((p.1.2, p.2.s) : GFrac (LC m))

/-- The Hermite part `gᵢ` of a weight, as a code. -/
def gCode (m : ℕ) (w : LC (m + 1)) : LC (m + 1) :=
  (((hermW Fc us m w).gn, (hermW Fc us m w).gd) : GFrac (LC m))

/-- The polynomial part `Pᵢ` of a weight. -/
def pPart (m : ℕ) (w : LC (m + 1)) : GPoly (LC m) :=
  (GPoly.divMod (LO Fc us m) (hermW Fc us m w).b (hermW Fc us m w).s).1

/-- **Parametric exact integration** at level `m`: a basis of the `(e, y)` with
`y′ = ∑ eᵢ wᵢ`. -/
def lex : (m : ℕ) → List (LC m) → List (List ℚ × LC m)
  | 0, W => curveRde Fc (curveOps Fc).zero W
  | m + 1, W =>
    let O := LO Fc us m
    let O' := LO Fc us (m + 1)
    let n := W.length
    let H := W.map (hermW Fc us m)
    let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
    let U := lrel Fc us (m + 1) (simpleCodes Fc us m W)
    let E := U.map (Tower.NestP.NestTower.vecOf n)
    let Pu := E.map fun e ↦ lcombGP O (lcst Fc us m) e (QR.map Prod.fst)
    let Gu := E.map fun e ↦ lcombCode O' (lcst Fc us (m + 1)) e
      (H.map fun h ↦ ((h.gn, h.gd) : GFrac (LC m)))
    (paramPoly O (lcst Fc us m) (etaC Fc us m) (lex m) Pu).map fun r ↦
      (vcomb n r.1 E, O'.add (lcombCode O' (lcst Fc us (m + 1)) r.1 Gu)
        ((r.2, [O.one]) : GFrac (LC m)))

/-! ### Basic facts on the levels -/

universe u

variable {Fc us} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace LTower

variable (T : LTower Fc us Cc L)

lemma coe_ratCast {m : ℕ} (c : ℚ) : ((c : T.F m) : L) = (c : L) := by simp

include T in
lemma deriv_ratCast_L (c : ℚ) : (c : L)′ = 0 := by
  rw [← map_ratCast (algebraMap Cc L) c, deriv_algebraMap, T.hC, map_zero]

lemma deriv_ratCast {m : ℕ} (c : ℚ) : (c : T.F m)′ = 0 :=
  Subtype.ext (by rw [coe_deriv, coe_ratCast, T.deriv_ratCast_L]; rfl)

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

lemma sem_lcst : ∀ (m : ℕ) (h : T.Tr m) (c : ℚ), (T.MP m h).sem (lcst Fc us m c) = (c : T.F m)
  | 0, h, c => by
    apply Subtype.ext
    rw [T.sem_MP]
    change (cM T.hC T.S T.hx Fc T.hSF).sem (ratCode Fc c) = _
    rw [sem_ratCode]
    simp
  | m + 1, h, c => by
    rw [sem_MP_succ]
    simp only [lcst, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one,
      sem_lcst m, map_one, div_one]
    rw [phi, coe_eval₂RingHom, eval₂_C]
    exact map_ratCast _ c

lemma phi_C_ratCast (m : ℕ) (q : ℚ) : T.phi m (C ((q : ℚ) : T.F m)) = ((q : ℚ) : T.F (m + 1)) := by
  rw [T.phi_C]
  exact map_ratCast _ q

/-- No new constants at level `m + 1`: `P(t)′ = 0` forces `P` constant. -/
lemma const_poly (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (P : (T.F m)[X])
    (hP : implicitDeriv (T.wPoly m) P = 0) : ∃ e : T.F m, P = C e := by
  set t := T.ts m with htd
  have hinjt : Function.Injective (aeval (R := T.F m) t) := transcendental_iff_injective.mp htr
  have hder : ∀ Q : (T.F m)[X], (aeval t Q)′ = aeval t (implicitDeriv (T.wPoly m) Q) :=
    deriv_aeval_eq_implicitDeriv t (T.wPoly m) (T.deriv_ts_aeval m)
  have hz : (aeval t P)′ = 0 := by rw [hder, hP, map_zero]
  obtain ⟨κ, hκ⟩ := T.hconst _ hz
  refine ⟨algebraMap Cc (T.F m) κ, hinjt ?_⟩
  rw [aeval_C]
  change aeval t P = algebraMap Cc L κ
  rw [hκ]

/-- Every irreducible polynomial over `F m` is normal for `t′ = ηₘ`. -/
lemma normal (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (p : (T.F m)[X])
    (hp : Irreducible p) : ¬p ∣ implicitDeriv (T.wPoly m) p := by
  have hw := T.wPoly_of_lt (T.lt_of_transcendental htr)
  rw [hw]
  letI : Differential (T.F m)[X] := polynomialOfDeriv (C (T.eta m))
  exact not_dvd_deriv_of_irreducible_primitive (T.eta m) (fun _ ↦ rfl)
    (fun P hP ↦ T.const_poly m htr P (by rw [hw]; exact hP)) hp

/-- **Hermite reduction at level `m + 1`**, as an identity of values. -/
lemma hermite_value (m : ℕ) (hm : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    (A D : GPoly (LC m)) (hD : GPoly.toPoly (T.MP m hm) D ≠ 0) :
    T.phi m (GPoly.toPoly (T.MP m hm) A) / T.phi m (GPoly.toPoly (T.MP m hm) D) =
      (T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (LO Fc us m) [etaC Fc us m] A D).gn) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (LO Fc us m) [etaC Fc us m] A D).gd))′ +
      T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (LO Fc us m) [etaC Fc us m] A D).b) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (LO Fc us m) [etaC Fc us m] A D).s) ∧
    Squarefree (GPoly.toPoly (T.MP m hm) (GPoly.hermite (LO Fc us m) [etaC Fc us m] A D).s) := by
  set M := T.MP m hm
  have hw : GPoly.toPoly M [etaC Fc us m] = T.wPoly m :=
    (T.toPoly_eta m hm).trans (T.wPoly_of_lt (T.lt_of_transcendental htr)).symm
  have hnormal' : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M [etaC Fc us m]) p := fun p hp _ ↦ by
    rw [hw]
    exact T.normal m htr p hp
  have hc := GPoly.hermiteCheck_hermite M [etaC Fc us m] A D hnormal' hD
  obtain ⟨hD0, hgd0, hs0, hid, hsq⟩ := (GPoly.hermiteCheck_iff M _ _ _ _).mp hc
  rw [hw] at hid
  refine ⟨?_, GPoly.squarefreeCheck_sound M hsq⟩
  have hinj := T.phi_injective htr
  have h1 : T.phi m (GPoly.toPoly M D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have h2 : T.phi m (GPoly.toPoly M (GPoly.hermite (LO Fc us m) [etaC Fc us m] A D).gd) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hgd0
  have h3 : T.phi m (GPoly.toPoly M (GPoly.hermite (LO Fc us m) [etaC Fc us m] A D).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hs0
  have hidL := congrArg (T.phi m) hid
  simp only [map_mul, map_add, map_sub] at hidL
  rw [Derivation.leibniz_div, T.deriv_phi, T.deriv_phi]
  simp only [smul_eq_mul]
  field_simp
  linear_combination hidL

lemma deriv_sum_ratCast {m : ℕ} (n : ℕ) (q : ℕ → ℚ) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, (q i : T.F m) * a i)′ = ∑ i ∈ Finset.range n, (q i : T.F m) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_ratCast, smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_comm]

lemma deriv_sum_Cc {m : ℕ} (n : ℕ) (q : ℕ → Cc) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, algebraMap Cc (T.F m) (q i) * a i)′ =
      ∑ i ∈ Finset.range n, algebraMap Cc (T.F m) (q i) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_algebraMap_Cc, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
    mul_comm]

lemma sem_eta (m : ℕ) (hm : T.Tr m) : (T.MP m hm).sem (etaC Fc us m) = T.eta m := by
  have := T.toPoly_eta m hm
  rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero] at this
  exact C_injective this

lemma wPoly_eq (m : ℕ) (hm : T.Tr m) (hlt : m < T.n) :
    T.wPoly m = C ((T.MP m hm).sem (etaC Fc us m)) := by
  rw [T.wPoly_of_lt hlt, T.sem_eta]

/-- `ηₘ` is not a derivative in `F m` when `tₘ` is transcendental over it. -/
lemma eta_not_deriv (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (y : T.F m) :
    y′ ≠ T.eta m := by
  intro hy
  have hc : (T.ts m - (y : L))′ = 0 := by
    rw [Derivation.map_sub, T.ht' (T.lt_of_transcendental htr), ← coe_deriv, hy]
    exact sub_self _
  obtain ⟨κ, hκ⟩ := T.hconst _ hc
  apply htr
  have hmem : T.ts m ∈ T.F m := by
    have : T.ts m = algebraMap Cc L κ + (y : L) := by rw [hκ]; ring
    rw [this]
    exact add_mem (T.const_mem m κ) y.2
  exact isAlgebraic_algebraMap (R := T.F m) (⟨T.ts m, hmem⟩ : T.F m)

/-! ### The specification -/

/-- `∑ cᵢ wᵢ` with constant coefficients. -/
noncomputable def sumK (m : ℕ) (h : T.Tr m) (c : List Cc) (W : List (LC m)) : T.F m :=
  ∑ i ∈ Finset.range W.length,
    algebraMap Cc (T.F m) (c.getD i 0) * (T.MP m h).sem (W.getD i (zc Fc us m))

/-- `∑ eᵢ wᵢ` with rational coefficients. -/
noncomputable def sumQ (m : ℕ) (h : T.Tr m) (e : List ℚ) (W : List (LC m)) : T.F m :=
  ∑ i ∈ Finset.range W.length, ((e.getD i 0 : ℚ) : T.F m) * (T.MP m h).sem (W.getD i (zc Fc us m))

/-- The soundness statement of a parametric solution list. -/
def PLSound (m : ℕ) (h : T.Tr m) (W : List (LC m)) (out : List (List ℚ × LC m)) : Prop :=
  ∀ r ∈ out, ((T.MP m h).sem r.2)′ = T.sumQ m h r.1 W

/-- The completeness statement of a parametric solution list. -/
def PLComplete (m : ℕ) (h : T.Tr m) (W : List (LC m)) (out : List (List ℚ × LC m)) : Prop :=
  ∀ c : List Cc, (∀ i, W.length ≤ i → c.getD i 0 = 0) → ∀ z : T.F m, z′ = T.sumK m h c W →
    ∃ β : List Cc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range out.length,
        β.getD k 0 * algebraMap ℚ Cc ((out.getD k ([], zc Fc us m)).1.getD i 0)) ∧
      (z - ∑ k ∈ Finset.range out.length,
        algebraMap Cc (T.F m) (β.getD k 0) * (T.MP m h).sem (out.getD k ([], zc Fc us m)).2)′ = 0

lemma getD_rdeOut_ge (ws : List (GPoly (GFrac ℚ))) (u : CPoly ℚ) {i : ℕ} (hi : ws.length ≤ i) :
    (rdeOut Fc ws u).1.getD i 0 = 0 :=
  List.getD_eq_default _ _ (by simp [rdeOut]; omega)

/-- **Parametric exact integration at the curve level.** -/
theorem lex_zero (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (h : T.Tr 0)
    (W : List (LC 0)) : T.PLSound 0 h W (lex Fc us 0 W) ∧ T.PLComplete 0 h W (lex Fc us 0 W) := by
  set M := cM T.hC T.S T.hx Fc T.hSF with hM
  refine ⟨fun r hr ↦ ?_, fun c hc z hz ↦ ?_⟩
  · have hs := curveRde_sound T.hC T.S T.hx Fc T.hSF (curveOps Fc).zero W r hr
    rw [M.sem_zero, Derivation.map_zero, zero_mul, add_zero] at hs
    apply Subtype.ext
    rw [coe_deriv, T.sem_MP, sumQ, AddSubmonoidClass.coe_finsetSum]
    refine hs.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [IntermediateField.coe_mul, T.sem_MP, coe_ratCast]
    rfl
  · have hzE : (z : L)′ + (M.sem (curveOps Fc).zero)′ * (z : L) = ∑ j ∈ Finset.range W.length,
        algebraMap Cc L (c.getD j 0) * M.sem (W.getD j []) := by
      rw [M.sem_zero, Derivation.map_zero, zero_mul, add_zero, ← coe_deriv, hz, sumK,
        AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [IntermediateField.coe_mul, T.sem_MP]
      rfl
    obtain ⟨β, hβ1, hβ2⟩ := curveRde_complete T.hC T.S T.hx Fc T.hSF hmon hdeg _ W c (z : L)
      z.2 hzE
    refine ⟨β, fun i ↦ ?_, ?_⟩
    · by_cases hi : i < W.length
      · rw [hβ1 i hi]
        rfl
      · rw [hc i (by omega)]
        symm
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        have hk' : k < (nullBasis (rdeCols Fc (curveOps Fc).zero W)).length := by
          exact lt_of_lt_of_eq (Finset.mem_range.mp hk) (List.length_map _)
        change β.getD k 0 * algebraMap ℚ Cc ((((nullBasis (rdeCols Fc (curveOps Fc).zero W)).map
          (rdeOut Fc W)).getD k ([], zc Fc us 0)).1.getD i 0) = 0
        rw [Tower.NestP.NestTower.getD_map' (rdeOut Fc W) _ [] _ hk',
          getD_rdeOut_ge W _ (le_of_not_gt hi), map_zero, mul_zero]
    · have : z = ∑ k ∈ Finset.range (lex Fc us 0 W).length, algebraMap Cc (T.F 0) (β.getD k 0) *
          (T.MP 0 h).sem ((lex Fc us 0 W).getD k ([], zc Fc us 0)).2 := by
        apply Subtype.ext
        rw [hβ2, AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [IntermediateField.coe_mul, T.sem_MP]
        rfl
      rw [← this, sub_self, map_zero]

end LTower

end Curves.LT
