import RischTragerBronstein.Mixed.MTAlg
import RischTragerBronstein.Mixed.CurveConst
import RischTragerBronstein.Liouville.LogSumStructure

/-!
# Mixed towers over a curve: the structure theorem

Ported from `Tower.NestX` (`NestXStructure`): if `Z′ = ∑ cₖ uₖ′ / uₖ` with constant `cₖ` and
`Z, uₖ ∈ F m`, then `Z = ∑ᵢ qᵢ gᵢ + κ` with constants `qᵢ`, where `gᵢ = tᵢ` at a logarithmic level
and `gᵢ = aᵢ` at an exponential level. At the base (the curve) such a `Z` is constant
(`CurveData.logsum_const_gen`: it has no poles).
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

/-- If every basis vector of the constant system has first coordinate `0`, so has every
constant relation. -/
lemma coeff0_eq_zero_of_cert (m : ℕ) (h : T.Tr m) (vs : List (LC m))
    (hcert : ∀ u ∈ mrel Fc ks m vs, u.getD 0 0 = 0) (c : List Cc) (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0) :
    c.getD 0 0 = 0 := by
  obtain ⟨β, hβl, hβ⟩ := T.consys_complete m h vs c hl h0
  rw [hβ 0, NestTower.zipWith_sum_range _ 0 [] _ _ hβl]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [hcert _ (getD_memC _ _ (by rw [← hβl]; exact Finset.mem_range.mp hk)), map_zero,
    mul_zero]

/-- The value of a constant relation given by a coefficient function. -/
lemma rel_val (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (f : ℕ → Cc) :
    (((List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map f) vs).sum : T.F m) : L) =
      ∑ j ∈ Finset.range vs.length, algebraMap Cc L (f j) *
        (((T.MP m h).sem (vs.getD j (MO Fc ks m).zero) : T.F m) : L) := by
  rw [NestTower.zipWith_sum_range _ 0 (MO Fc ks m).zero _ _ (by simp)]
  push_cast
  rw [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hj)]

/-- The generator of level `i` in the structure theorem: `tᵢ` (logarithm) or `aᵢ` (exponential). -/
noncomputable def genX (i : ℕ) : L :=
  match ks i with
  | .prim _ => T.ts i
  | .exp a => T.ev i a

/-- The hypotheses of the structure theorem at height `m`. -/
structure MixHyp (m : ℕ) : Prop where
  tr : T.Tr m
  log : ∀ i < m, ∀ η, ks i = .prim η → ∃ v : T.F i, v ≠ 0 ∧ T.val i η = logDeriv v
  nd : ∀ i < m, ∀ η, ks i = .prim η → ∀ y : T.F i, y′ ≠ T.val i η
  hom : ∀ i < m, ∀ a, ks i = .exp a → ∀ j : ℤ, j ≠ 0 → ∀ e : T.F i, e ≠ 0 →
    e′ + (j : T.F i) * (T.val i a)′ * e ≠ 0

lemma MixHyp.mono {m : ℕ} (h : T.MixHyp (m + 1)) : T.MixHyp m :=
  ⟨fun i hi ↦ h.tr i (by omega), fun i hi ↦ h.log i (by omega), fun i hi ↦ h.nd i (by omega),
    fun i hi ↦ h.hom i (by omega)⟩

lemma coe_logDeriv_FX {m : ℕ} (y : T.F m) : ((logDeriv y : T.F m) : L) = logDeriv (y : L) := by
  unfold logDeriv
  rw [IntermediateField.coe_div, coe_deriv]

set_option maxHeartbeats 1600000 in
/-- **The structure theorem** for mixed towers of logarithms and exponentials. -/
theorem mix_structure : ∀ (m : ℕ), T.MixHyp m → ∀ (Z : L), Z ∈ T.F m →
    ∀ {ι : Type} (s : Finset ι) (c : ι → Cc) (u : ι → L), (∀ i ∈ s, u i ∈ T.F m ∧ u i ≠ 0) →
    Z′ = ∑ i ∈ s, algebraMap Cc L (c i) * logDeriv (u i) →
    ∃ (q : ℕ → Cc) (κ : Cc), Z = ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * T.genX i +
      algebraMap Cc L κ
  | 0, _, Z, hZ, ι, s, c, u, hu, hd => by
    classical
    set u'' : ι → L := fun i ↦ if i ∈ s then u i else 1 with hu''
    have hmem : ∀ i, u'' i ∈ Cc⟮T.S.x⟯⟮T.S.y⟯ := fun i ↦ by
      simp only [hu'']; split_ifs with hi
      · exact (hu i hi).1
      · exact one_mem _
    have hne : ∀ i, u'' i ≠ 0 := fun i ↦ by
      simp only [hu'']; split_ifs with hi
      · exact (hu i hi).2
      · exact one_ne_zero
    have hd' : Z′ = ∑ i ∈ s, algebraMap Cc L (c i) * ((u'' i)′ / u'' i) := by
      rw [hd]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [hu'', if_pos hi, logDeriv]
    obtain ⟨κ, hκ⟩ := T.S.logsum_const_gen T.hC T.hx T.hconst Z hZ s c u'' hmem hne hd'
    exact ⟨fun _ ↦ 0, κ, by rw [← hκ]; simp⟩
  | m + 1, h, Z, hZ, ι, s, c, u, hu, hd => by
    classical
    have hm := h.mono
    have htr : Transcendental (T.F m) (T.ts m) := h.tr m (by omega)
    set t := T.ts m with ht
    have hw := T.deriv_ts_aeval m
    let _ := algebraAdjoinSimple (F := T.F m) t
    let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
    have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
    have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
    have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : L) = aeval t P :=
      algebraMap_adjoinSimple _
    have hdK : ∀ y : (T.F m)⟮t⟯, ((y′ : (T.F m)⟮t⟯) : L) = (y : L)′ := fun y ↦ rfl
    have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : L) = logDeriv (y : L) := by
      intro y; unfold logDeriv; rw [IntermediateField.coe_div]; rfl
    set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if h : u i ∈ (T.F m)⟮t⟯ then ⟨u i, h⟩ else 1 with hu''d
    have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : L) = u i := fun i hi ↦ by
      simp only [hu''d]; rw [dif_pos ((T.mem_F_succ).mp (hu i hi).1)]
    have hu''0 : ∀ i ∈ s, u'' i ≠ 0 := fun i hi h0 ↦ (hu i hi).2 (by rw [← hu'' i hi, h0]; rfl)
    set ZK : (T.F m)⟮t⟯ := ⟨Z, (T.mem_F_succ).mp hZ⟩ with hZK
    have hcK : ∀ i, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ (C (algebraMap Cc (T.F m) (c i))) :
        (T.F m)⟮t⟯) : L) = algebraMap Cc L (c i) := fun i ↦ by
      rw [hcoe, aeval_C]; rfl
    have hdK' : ZK′ = ∑ i ∈ s, algebraMap (T.F m)[X] (T.F m)⟮t⟯ (C (algebraMap Cc (T.F m) (c i))) *
        logDeriv (u'' i) := Subtype.ext (by
      rw [hdK, AddSubmonoidClass.coe_finset_sum]
      change Z′ = _
      rw [hd]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcK, hcoeLog, hu'' i hi])
    have hsumE : ∀ (z0 : T.F m), ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ (C z0) : (T.F m)⟮t⟯) : L) =
        (z0 : L) := fun z0 ↦ by rw [hcoe, aeval_C]; rfl
    cases hk : ks m with
    | exp a =>
      have hDe : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.val m a)′ * X) P := fun P ↦ by
        change implicitDeriv (T.wPoly m) P = _
        rw [T.wPoly_exp (T.lt_of_transcendental htr) hk]
      obtain ⟨z0, e, n, he, hZz, hz0⟩ := exp_logsum_structure (K := (T.F m)⟮t⟯) hDe
        (fun p hp hXp ↦ T.normal_exp m htr hk p hp hXp) (h.hom m (by omega) a hk) s
        (fun i ↦ algebraMap Cc (T.F m) (c i)) u'' hu''0 ZK hdK'
      -- recurse on `z₀ - (∑ cᵢ nᵢ) aₘ`
      set N : Cc := ∑ i ∈ s, c i * (n i : Cc) with hN
      have hsplit : ∑ i ∈ s, algebraMap Cc (T.F m) (c i) *
          (logDeriv (e i) + (n i : T.F m) * (T.val m a)′) =
          ∑ i ∈ s, algebraMap Cc (T.F m) (c i) * logDeriv (e i) +
            algebraMap Cc (T.F m) N * (T.val m a)′ := by
        rw [hN, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, map_intCast]; ring
      have hrecF : (z0 - algebraMap Cc (T.F m) N * T.val m a)′ =
          ∑ i ∈ s, algebraMap Cc (T.F m) (c i) * logDeriv (e i) := by
        rw [map_sub, Derivation.leibniz, T.deriv_algebraMap_Cc, hz0, hsplit]
        simp only [smul_eq_mul, mul_zero, add_zero]
        ring
      have hrec : ((z0 - algebraMap Cc (T.F m) N * T.val m a : T.F m) : L)′ =
          ∑ i ∈ s, algebraMap Cc L (c i) * logDeriv ((e i : T.F m) : L) := by
        rw [← coe_deriv, hrecF, AddSubmonoidClass.coe_finset_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [IntermediateField.coe_mul, T.coe_logDeriv_FX]
        rfl
      obtain ⟨q, κ, hq⟩ := mix_structure m hm _ (z0 - algebraMap Cc (T.F m) N * T.val m a).2 s c
        (fun i ↦ ((e i : T.F m) : L)) (fun i hi ↦ ⟨(e i).2, fun h0 ↦ he i hi (Subtype.ext h0)⟩)
        hrec
      refine ⟨fun i ↦ if i = m then N else q i, κ, ?_⟩
      rw [Finset.sum_range_succ]
      beta_reduce
      rw [if_pos rfl]
      have hsum : ∑ i ∈ Finset.range m, algebraMap Cc L (if i = m then N else q i) * T.genX i =
          ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * T.genX i :=
        Finset.sum_congr rfl fun i hi ↦ by rw [if_neg (Finset.mem_range.mp hi).ne]
      have hg : T.genX m = T.ev m a := by simp only [genX, hk]
      rw [hsum, hg]
      have hZv : Z = (z0 : L) := by
        have := congrArg Subtype.val hZz
        rw [hsumE] at this
        exact this
      rw [hZv]
      have hq' : (z0 : L) - algebraMap Cc L N * T.ev m a =
          ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * T.genX i + algebraMap Cc L κ := by
        rw [← hq]; rfl
      linear_combination hq'
    | prim η =>
      have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.val m η)) P := fun P ↦ by
        change implicitDeriv (T.wPoly m) P = _
        rw [T.wPoly_prim (T.lt_of_transcendental htr) hk]
      obtain ⟨d, z0, e, hd0, he, hZz, hz0⟩ := prim_logsum_structure (K := (T.F m)⟮t⟯) hD
        (fun p hp ↦ T.normal_prim m htr hk p hp) (h.nd m (by omega) η hk) s
        (fun i ↦ algebraMap Cc (T.F m) (c i)) u'' hu''0 ZK hdK'
      obtain ⟨κd, rfl⟩ := T.const_F d hd0
      obtain ⟨v, hv0, hv⟩ := h.log m (by omega) η hk
      -- recurse on `z₀`: `z₀′ = ∑ cᵢ eᵢ′ / eᵢ - κd v′ / v`
      set c' : Option ι → Cc := fun o ↦ o.elim (-κd) c with hc'
      set u' : Option ι → L := fun o ↦ o.elim (v : L) fun i ↦ ((e i : T.F m) : L) with hu'
      have hrecF : z0′ = ∑ i ∈ s, algebraMap Cc (T.F m) (c i) * logDeriv (e i) -
          algebraMap Cc (T.F m) κd * logDeriv v := by
        rw [← hv]; linear_combination hz0
      have hrec : ((z0 : T.F m) : L)′ = ∑ o ∈ Finset.insertNone s,
          algebraMap Cc L (c' o) * logDeriv (u' o) := by
        rw [Finset.sum_insertNone, ← coe_deriv, hrecF]
        simp only [hc', hu', Option.elim]
        rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finset_sum, IntermediateField.coe_mul,
          T.coe_logDeriv_FX, map_neg]
        have e1 : ∑ i ∈ s, (((algebraMap Cc (T.F m) (c i) * logDeriv (e i) : T.F m)) : L) =
            ∑ i ∈ s, algebraMap Cc L (c i) * logDeriv ((e i : T.F m) : L) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [IntermediateField.coe_mul, T.coe_logDeriv_FX]; rfl
        rw [e1]
        change _ - algebraMap Cc L κd * _ = _
        ring
      obtain ⟨q, κ, hq⟩ := mix_structure m hm _ z0.2 (Finset.insertNone s) c' u' (by
        intro o ho
        cases o with
        | none => exact ⟨v.2, fun h0 ↦ hv0 (Subtype.ext h0)⟩
        | some i =>
          have hi : i ∈ s := by simpa using ho
          exact ⟨(e i).2, fun h0 ↦ he i hi (Subtype.ext h0)⟩) hrec
      refine ⟨fun i ↦ if i = m then κd else q i, κ, ?_⟩
      rw [Finset.sum_range_succ]
      beta_reduce
      rw [if_pos rfl]
      have hsum : ∑ i ∈ Finset.range m, algebraMap Cc L (if i = m then κd else q i) * T.genX i =
          ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * T.genX i :=
        Finset.sum_congr rfl fun i hi ↦ by rw [if_neg (Finset.mem_range.mp hi).ne]
      have hg : T.genX m = T.ts m := by simp only [genX, hk]
      rw [hsum, hg]
      have hZv : Z = algebraMap Cc L κd * T.ts m + (z0 : L) := by
        have := congrArg Subtype.val hZz
        rw [hcoe] at this
        change Z = _ at this
        rw [this, map_add, map_mul, aeval_C, aeval_C, aeval_X]
        rfl
      rw [hZv, hq]
      ring
end MTower

end Curves.MT
