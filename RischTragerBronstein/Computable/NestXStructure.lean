import RischTragerBronstein.Computable.NestMStructure
import RischTragerBronstein.Liouville.LogSumStructure

/-!
# Mixed towers of logarithms and exponentials: the structure theorem

`NestMTower Kc E ks` with every primitive level a **logarithm** (`tᵢ′ = vᵢ′ / vᵢ`, `vᵢ ∈ Kᵢ`) and
every other level an exponential (`tᵢ = exp aᵢ`). `mix_structure`: if
`Z′ = ∑ cₖ uₖ′ / uₖ` with constant `cₖ` and `Z, uₖ ∈ F m`, then
`Z = ∑ᵢ qᵢ gᵢ + κ` with constants `qᵢ`, where `gᵢ = tᵢ` at a logarithmic level and `gᵢ = aᵢ` at
an exponential level. The proof descends the tower with `prim_logsum_structure` and
`exp_logsum_structure` (`Liouville/LogSumStructure.lean`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

/-- The generator of level `i` in the structure theorem: `tᵢ` (logarithm) or `aᵢ` (exponential). -/
noncomputable def genX (i : ℕ) : E :=
  match ks i with
  | .prim _ => T.ts i
  | .exp a => evN Kc T.x T.ts i a

/-- The hypotheses of the structure theorem at height `m`. -/
structure MixHyp (m : ℕ) : Prop where
  tr : T.Tr m
  log : ∀ i < m, ∀ η, ks i = .prim η → ∃ v : T.F i, v ≠ 0 ∧ T.valN i η = logDeriv v
  nd : ∀ i < m, ∀ η, ks i = .prim η → ∀ y : T.F i, y′ ≠ T.valN i η
  hom : ∀ i < m, ∀ a, ks i = .exp a → ∀ j : ℤ, j ≠ 0 → ∀ e : T.F i, e ≠ 0 →
    e′ + (j : T.F i) * (T.valN i a)′ * e ≠ 0

lemma MixHyp.mono {m : ℕ} (h : T.MixHyp (m + 1)) : T.MixHyp m :=
  ⟨fun i hi ↦ h.tr i (by omega), fun i hi ↦ h.log i (by omega), fun i hi ↦ h.nd i (by omega),
    fun i hi ↦ h.hom i (by omega)⟩

lemma coe_logDeriv_FX {m : ℕ} (y : T.F m) : ((logDeriv y : T.F m) : E) = logDeriv (y : E) := by
  unfold logDeriv
  rw [IntermediateField.coe_div, coe_deriv]

set_option maxHeartbeats 1600000 in
/-- **The structure theorem** for mixed towers of logarithms and exponentials. -/
theorem mix_structure : ∀ (m : ℕ), T.MixHyp m → ∀ (Z : E), Z ∈ T.F m →
    ∀ {ι : Type} (s : Finset ι) (c : ι → Kc) (u : ι → E), (∀ i ∈ s, u i ∈ T.F m ∧ u i ≠ 0) →
    Z′ = ∑ i ∈ s, algebraMap Kc E (c i) * logDeriv (u i) →
    ∃ (q : ℕ → Kc) (κ : Kc), Z = ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * T.genX i +
      algebraMap Kc E κ
  | 0, _, Z, hZ, ι, s, c, u, hu, hd => by
    classical
    letI : Differential Kc[X] := polynomialOfDeriv 1
    haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
    have hD : ∀ P : Kc[X], P′ = implicitDeriv (C 1) P := fun P ↦ by
      rw [C_1]; rfl
    have hD0 : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
    have hnorm : ∀ p : Kc[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦ by
      rw [hD0]; exact Differential.not_dvd_derivative_self hp
    set u' : ι → T.F 0 := fun i ↦ if h : u i ∈ T.F 0 then ⟨u i, h⟩ else 1 with hu'd
    have hu'E : ∀ i ∈ s, ((u' i : T.F 0) : E) = u i := fun i hi ↦ by
      simp only [hu'd]; rw [dif_pos (hu i hi).1]
    obtain ⟨d, z0, e, hd0, -, hZe, hz0⟩ := prim_logsum_structure (K := T.F 0) hD hnorm
      (fun y hy ↦ by rw [T.hC y] at hy; exact zero_ne_one hy) s c u'
      (fun i hi h0 ↦ (hu i hi).2 (by rw [← hu'E i hi, h0]; rfl)) ⟨Z, hZ⟩ (Subtype.ext (by
        change Z′ = _
        rw [hd, AddSubmonoidClass.coe_finset_sum]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [IntermediateField.coe_mul, T.coe_logDeriv_FX, hu'E i hi]
        rw [show ((algebraMap Kc[X] (T.F 0) (C (c i)) : T.F 0) : E) = algebraMap Kc E (c i) by
          change ((T.phi0 (C (c i)) : T.F 0) : E) = _
          rw [T.coe_phi0, aeval_C]]))
    -- in `Kc`, all derivatives vanish
    have he0 : ∀ i, logDeriv (e i) = 0 := fun i ↦ by rw [logDeriv, T.hC, zero_div]
    rw [T.hC z0, Finset.sum_eq_zero fun i _ ↦ by rw [he0, mul_zero], zero_add, mul_one] at hz0
    refine ⟨fun _ ↦ 0, z0, ?_⟩
    have := congrArg Subtype.val hZe
    rw [hz0, C_0, zero_mul, zero_add] at this
    change Z = _ at this
    rw [this]
    change ((T.phi0 (C z0) : T.F 0) : E) = _
    rw [T.coe_phi0, aeval_C]
    simp
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
    have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
      algebraMap_adjoinSimple _
    have hdK : ∀ y : (T.F m)⟮t⟯, ((y′ : (T.F m)⟮t⟯) : E) = (y : E)′ := fun y ↦ rfl
    have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : E) = logDeriv (y : E) := by
      intro y; unfold logDeriv; rw [IntermediateField.coe_div]; rfl
    set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if h : u i ∈ (T.F m)⟮t⟯ then ⟨u i, h⟩ else 1 with hu''d
    have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : E) = u i := fun i hi ↦ by
      simp only [hu''d]; rw [dif_pos ((T.mem_F_succ).mp (hu i hi).1)]
    have hu''0 : ∀ i ∈ s, u'' i ≠ 0 := fun i hi h0 ↦ (hu i hi).2 (by rw [← hu'' i hi, h0]; rfl)
    set ZK : (T.F m)⟮t⟯ := ⟨Z, (T.mem_F_succ).mp hZ⟩ with hZK
    have hcK : ∀ i, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ (C (algebraMap Kc (T.F m) (c i))) :
        (T.F m)⟮t⟯) : E) = algebraMap Kc E (c i) := fun i ↦ by
      rw [hcoe, aeval_C]; rfl
    have hdK' : ZK′ = ∑ i ∈ s, algebraMap (T.F m)[X] (T.F m)⟮t⟯ (C (algebraMap Kc (T.F m) (c i))) *
        logDeriv (u'' i) := Subtype.ext (by
      rw [hdK, AddSubmonoidClass.coe_finset_sum]
      change Z′ = _
      rw [hd]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcK, hcoeLog, hu'' i hi])
    have hsumE : ∀ (z0 : T.F m), ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ (C z0) : (T.F m)⟮t⟯) : E) =
        (z0 : E) := fun z0 ↦ by rw [hcoe, aeval_C]; rfl
    cases hk : ks m with
    | exp a =>
      have hDe : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.valN m a)′ * X) P := fun P ↦ by
        change implicitDeriv (T.wPoly m) P = _
        rw [T.wPoly_exp hk]
      obtain ⟨z0, e, n, he, hZz, hz0⟩ := exp_logsum_structure (K := (T.F m)⟮t⟯) hDe
        (fun p hp hXp ↦ T.normal_exp m htr hk p hp hXp) (h.hom m (by omega) a hk) s
        (fun i ↦ algebraMap Kc (T.F m) (c i)) u'' hu''0 ZK hdK'
      -- recurse on `z₀ - (∑ cᵢ nᵢ) aₘ`
      set N : Kc := ∑ i ∈ s, c i * (n i : Kc) with hN
      have hsplit : ∑ i ∈ s, algebraMap Kc (T.F m) (c i) *
          (logDeriv (e i) + (n i : T.F m) * (T.valN m a)′) =
          ∑ i ∈ s, algebraMap Kc (T.F m) (c i) * logDeriv (e i) +
            algebraMap Kc (T.F m) N * (T.valN m a)′ := by
        rw [hN, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, map_intCast]; ring
      have hrecF : (z0 - algebraMap Kc (T.F m) N * T.valN m a)′ =
          ∑ i ∈ s, algebraMap Kc (T.F m) (c i) * logDeriv (e i) := by
        rw [map_sub, Derivation.leibniz, T.deriv_algebraMap_Kc, hz0, hsplit]
        simp only [smul_eq_mul, mul_zero, add_zero]
        ring
      have hrec : ((z0 - algebraMap Kc (T.F m) N * T.valN m a : T.F m) : E)′ =
          ∑ i ∈ s, algebraMap Kc E (c i) * logDeriv ((e i : T.F m) : E) := by
        rw [← coe_deriv, hrecF, AddSubmonoidClass.coe_finset_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [IntermediateField.coe_mul, T.coe_logDeriv_FX]
        rfl
      obtain ⟨q, κ, hq⟩ := mix_structure m hm _ (z0 - algebraMap Kc (T.F m) N * T.valN m a).2 s c
        (fun i ↦ ((e i : T.F m) : E)) (fun i hi ↦ ⟨(e i).2, fun h0 ↦ he i hi (Subtype.ext h0)⟩)
        hrec
      refine ⟨fun i ↦ if i = m then N else q i, κ, ?_⟩
      rw [Finset.sum_range_succ]
      beta_reduce
      rw [if_pos rfl]
      have hsum : ∑ i ∈ Finset.range m, algebraMap Kc E (if i = m then N else q i) * T.genX i =
          ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * T.genX i :=
        Finset.sum_congr rfl fun i hi ↦ by rw [if_neg (Finset.mem_range.mp hi).ne]
      have hg : T.genX m = evN Kc T.x T.ts m a := by simp only [genX, hk]
      rw [hsum, hg]
      have hZv : Z = (z0 : E) := by
        have := congrArg Subtype.val hZz
        rw [hsumE] at this
        exact this
      rw [hZv]
      have hq' : (z0 : E) - algebraMap Kc E N * evN Kc T.x T.ts m a =
          ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * T.genX i + algebraMap Kc E κ := by
        rw [← hq]; rfl
      linear_combination hq'
    | prim η =>
      have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.valN m η)) P := fun P ↦ by
        change implicitDeriv (T.wPoly m) P = _
        rw [T.wPoly_prim hk]
      obtain ⟨d, z0, e, hd0, he, hZz, hz0⟩ := prim_logsum_structure (K := (T.F m)⟮t⟯) hD
        (fun p hp ↦ T.normal_prim m htr hk p hp) (h.nd m (by omega) η hk) s
        (fun i ↦ algebraMap Kc (T.F m) (c i)) u'' hu''0 ZK hdK'
      obtain ⟨κd, rfl⟩ := T.const_F d hd0
      obtain ⟨v, hv0, hv⟩ := h.log m (by omega) η hk
      -- recurse on `z₀`: `z₀′ = ∑ cᵢ eᵢ′ / eᵢ - κd v′ / v`
      set c' : Option ι → Kc := fun o ↦ o.elim (-κd) c with hc'
      set u' : Option ι → E := fun o ↦ o.elim (v : E) fun i ↦ ((e i : T.F m) : E) with hu'
      have hrecF : z0′ = ∑ i ∈ s, algebraMap Kc (T.F m) (c i) * logDeriv (e i) -
          algebraMap Kc (T.F m) κd * logDeriv v := by
        rw [← hv]; linear_combination hz0
      have hrec : ((z0 : T.F m) : E)′ = ∑ o ∈ Finset.insertNone s,
          algebraMap Kc E (c' o) * logDeriv (u' o) := by
        rw [Finset.sum_insertNone, ← coe_deriv, hrecF]
        simp only [hc', hu', Option.elim]
        rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finset_sum, IntermediateField.coe_mul,
          T.coe_logDeriv_FX, map_neg]
        have e1 : ∑ i ∈ s, (((algebraMap Kc (T.F m) (c i) * logDeriv (e i) : T.F m)) : E) =
            ∑ i ∈ s, algebraMap Kc E (c i) * logDeriv ((e i : T.F m) : E) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [IntermediateField.coe_mul, T.coe_logDeriv_FX]; rfl
        rw [e1]
        change _ - algebraMap Kc E κd * _ = _
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
      have hsum : ∑ i ∈ Finset.range m, algebraMap Kc E (if i = m then κd else q i) * T.genX i =
          ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * T.genX i :=
        Finset.sum_congr rfl fun i hi ↦ by rw [if_neg (Finset.mem_range.mp hi).ne]
      have hg : T.genX m = T.ts m := by simp only [genX, hk]
      rw [hsum, hg]
      have hZv : Z = algebraMap Kc E κd * T.ts m + (z0 : E) := by
        have := congrArg Subtype.val hZz
        rw [hcoe] at this
        change Z = _ at this
        rw [this, map_add, map_mul, aeval_C, aeval_C, aeval_X]
        rfl
      rw [hZv, hq]
      ring
