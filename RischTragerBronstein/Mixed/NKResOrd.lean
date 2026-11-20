import RischTragerBronstein.Mixed.NKResMultiC
import RischTragerBronstein.Mixed.NKTorsion

/-!
# Residues matched by units: the Liouville argument

`logSum_qindepP`: `logSum_qindep` keeping a multiplicative property of the logarithms (e.g. "no
zeros or poles at the finite places"). `nk_liouville_resU`: if the residues at infinity of `f` are
those of `∑ κᵢ uᵢ′/uᵢ` for units `uᵢ` (no zeros or poles at the finite places), an elementary `f`
is `v′ + ∑ κᵢ uᵢ′/uᵢ + ℓ`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- **Reduction to `ℚ`-independent coefficients, keeping a multiplicative property.** -/
theorem logSum_qindepP (S : Subfield K) (Pr : K → Prop) (hPmul : ∀ a b, Pr a → Pr b → Pr (a * b))
    (hPpow : ∀ a (n : ℕ), Pr a → Pr (a ^ n)) (hPzpow : ∀ a (n : ℤ), Pr a → Pr (a ^ n))
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c u : ι → K) (hc : ∀ i ∈ s, (c i)′ = 0) (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ S)
    (hP : ∀ i ∈ s, Pr (u i)) (hP1 : Pr 1) :
    ∃ (k : ℕ) (d w : ℕ → K), QIndepFam S k d w ∧ (∀ j < k, Pr (w j)) ∧
      ∑ i ∈ s, c i * logDeriv (u i) = ∑ j ∈ Finset.range k, d j * logDeriv (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, fun _ ↦ 0, fun _ ↦ 1, ⟨fun j hj ↦ absurd hj (by omega),
      fun j hj ↦ absurd hj (by omega), fun g _ j hj ↦ absurd hj (by omega)⟩,
      fun j hj ↦ absurd hj (by omega), by simp⟩
  | insert i0 s hi0 ih =>
    obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hPw, heq⟩ := ih (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)) (fun i hi ↦ hP i (Finset.mem_insert_of_mem hi))
    have hP0 := hP i0 (Finset.mem_insert_self _ _)
    have hc0 := hc i0 (Finset.mem_insert_self _ _)
    obtain ⟨hu0, hu0S⟩ := hu i0 (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi0, heq]
    by_cases hspan : ∃ q : ℕ → ℚ, c i0 = ∑ j ∈ Finset.range k, (q j : K) * d j
    · -- `c₀` is a rational combination: absorb `u₀` into the `wⱼ`
      obtain ⟨q, hq⟩ := hspan
      set D : ℕ := ∏ j ∈ Finset.range k, (q j).den with hD
      have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ (q j).den_nz
      have hDK : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD0
      have hint : ∀ j ∈ Finset.range k, ∃ n : ℤ, (n : ℚ) = q j * D := by
        intro j hj
        obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun j ↦ (q j).den) hj
        refine ⟨(q j).num * m, ?_⟩
        rw [hD, hm]
        push_cast
        rw [← mul_assoc, Rat.mul_den_eq_num]
      choose! n hn using hint
      refine ⟨k, fun j ↦ d j / D, fun j ↦ w j ^ D * u i0 ^ n j,
        ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, fun g hg j hj ↦ ?_⟩,
        fun j hj ↦ hPmul _ _ (hPpow _ _ (hPw j hj)) (hPzpow _ _ hP0), ?_⟩
      · show (d j / D)′ = 0
        rw [div_eq_mul_inv, Derivation.leibniz, hd j hj,
          show ((D : K)⁻¹)′ = 0 by rw [← Rat.cast_natCast, ← Rat.cast_inv]; exact deriv_ratCast_K _]
        simp
      · obtain ⟨hwj, hwS⟩ := hw j hj
        exact ⟨mul_ne_zero (pow_ne_zero _ hwj) (zpow_ne_zero _ hu0),
          mul_mem (pow_mem hwS _) (zpow_mem hu0S _)⟩
      · have := hind (fun j ↦ g j / D) (by
          rw [← hg]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          push_cast
          ring) j hj
        have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD0
        simpa [hD'] using this
      · have e : ∀ j ∈ Finset.range k, d j / D * logDeriv (w j ^ D * u i0 ^ n j) =
            d j * logDeriv (w j) + ((q j : K) * d j) * logDeriv (u i0) := by
          intro j hj
          have hwj := (hw j (Finset.mem_range.mp hj)).1
          rw [logDeriv_mul _ _ (pow_ne_zero _ hwj) (zpow_ne_zero _ hu0), logDeriv_pow,
            logDeriv_zpow' _ hu0]
          have hnq : ((n j : ℤ) : K) = (q j : K) * D := by
            rw [← Rat.cast_intCast, hn j hj]; push_cast; ring
          rw [hnq]
          field_simp
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, ← hq]
        ring
    · -- `c₀` is independent: append `(c₀, u₀)`
      have hspan' : ∀ q : ℕ → ℚ, c i0 ≠ ∑ j ∈ Finset.range k, (q j : K) * d j :=
        fun q h ↦ hspan ⟨q, h⟩
      refine ⟨k + 1, fun j ↦ if j < k then d j else c i0, fun j ↦ if j < k then w j else u i0,
        ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, fun g hg j hj ↦ ?_⟩, fun j hj ↦ ?_, ?_⟩
      · beta_reduce; split_ifs with h
        · exact hd j h
        · exact hc0
      · beta_reduce; split_ifs with h
        · exact hw j h
        · exact ⟨hu0, hu0S⟩
      · beta_reduce at hg
        rw [Finset.sum_range_succ, if_neg (lt_irrefl k)] at hg
        have hs : ∑ j ∈ Finset.range k, (g j : K) * (if j < k then d j else c i0) =
            ∑ j ∈ Finset.range k, (g j : K) * d j :=
          Finset.sum_congr rfl fun j hj ↦ by rw [if_pos (Finset.mem_range.mp hj)]
        rw [hs] at hg
        have hgk : g k = 0 := by
          by_contra hgk
          have hgk' : (g k : K) ≠ 0 := by exact_mod_cast hgk
          apply hspan' (fun j ↦ -g j / g k)
          have hc' : c i0 = -(∑ j ∈ Finset.range k, (g j : K) * d j) / g k := by
            field_simp
            linear_combination hg
          rw [hc', neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          push_cast
          ring
        rw [hgk, Rat.cast_zero, zero_mul, add_zero] at hg
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hind g hg j hj
        · exact hgk
      · beta_reduce; split_ifs with h
        · exact hPw j h
        · exact hP0
      · beta_reduce
        rw [Finset.sum_range_succ, if_neg (lt_irrefl k), if_neg (lt_irrefl k)]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [if_pos (Finset.mem_range.mp hj), if_pos (Finset.mem_range.mp hj)]

end Differential

namespace Curves

open Differential

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- No zeros or poles at the finite places. -/
def UnitFin (K : Type*) [Field K] [Algebra C K] (z : C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l),
    (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S.root_of_mem hl hr) z).order = 0

lemma unitFin_mul {a b : C⟮S.x⟯⟮S.y⟯} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : S.UnitFin K a)
    (hb : S.UnitFin K b) : S.UnitFin K (a * b) := by
  intro x N hN l hl r hr
  rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff _ (RingHom.injective _)).mpr ha0)
    ((map_ne_zero_iff _ (RingHom.injective _)).mpr hb0), ha x N hN l hl r hr, hb x N hN l hl r hr,
    add_zero]

lemma unitFin_zpow {a : C⟮S.x⟯⟮S.y⟯} (ha0 : a ≠ 0) (ha : S.UnitFin K a) (n : ℤ) :
    S.UnitFin K (a ^ n) := by
  intro x N hN l hl r hr
  rw [map_zpow₀, order_zpow_nk _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr ha0),
    ha x N hN l hl r hr, mul_zero]

lemma unitFin_one : S.UnitFin K 1 := by
  intro x N hN l hl r hr
  rw [map_one, HahnSeries.order_one]


variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- The residue term of a logarithmic derivative along a branch above infinity. -/
lemma coeff_logDeriv_embG (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) :
    ∃ β : K, (S.embG (infSub N) (infSub_injective N hN) r hr
      ⟨(u : L)′ / (u : L), div_mem (S.derivClosedXYW' (Polynomial.C η) hx u u.2) u.2⟩).coeff
        (N : ℤ) +
      ((S.embG (infSub N) (infSub_injective N hN) r hr u).order : K) / N * algebraMap C K η =
        β′ := by
  have h := S.coeff_liouville_top η hx hK N hN r hr ({()} : Finset Unit) (fun _ ↦ 1)
    (fun _ _ ↦ Derivation.map_one_eq_zero _) (fun _ ↦ u) (fun _ _ ↦ hu) 0
    ⟨(u : L)′ / (u : L), div_mem (S.derivClosedXYW' (Polynomial.C η) hx u u.2) u.2⟩
    (by simp)
  simpa using h


include hx hK in
/-- **Residues at infinity matched by units.** For a Liouville form `f = v′ + ∑ cᵢ uᵢ′/uᵢ`
with `f` regular at the finite places, units `w₁, …, w_μ` (no zeros or poles at the finite places)
and rationals `κⱼ` such that along every branch above infinity `[s^N] f + (∑ κⱼ ord wⱼ)/N · η` is a
derivative: then `f = v′ + ∑ κⱼ wⱼ′/wⱼ + ℓ` with `ℓ ∈ C`. -/
theorem nk_liouville_resU (hnd : ∀ a : K, a′ ≠ algebraMap C K η)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
    (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K ⟨f, hf⟩)
    {mu : ℕ} (u0 : Fin mu → C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u0 i ≠ 0) (hfin0 : ∀ i, S.UnitFin K (u0 i))
    (κ : Fin mu → ℚ)
    (hzero : ∀ r (hr : r ∈ li), ∃ γ : K, (S.embG (infSub Ni) (infSub_injective Ni hNi) r
      (S.root_of_mem hli hr) ⟨f, hf⟩).coeff (Ni : ℤ) +
        (∑ i, (κ i : K) * ((S.embG (infSub Ni) (infSub_injective Ni hNi) r (S.root_of_mem hli hr)
          (u0 i)).order : K)) / Ni * algebraMap C K η = γ′)
    {ι' : Type*} [DecidableEq ι'] (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ ℓ : C, f = v′ + ∑ i, (κ i : L) * logDeriv (u0 i : L) + algebraMap C L ℓ := by
  classical
  -- `ℚ`-independent logarithms of `f`, without zeros or poles at the finite places
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
  have hd'c : ∀ jj < k, (d' jj)′ = 0 := fun jj hjj ↦ by
    apply (algebraMap C L).injective
    rw [← deriv_algebraMap, hdd jj hjj, hd' jj hjj, map_zero]
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hww : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  have hgoodη : ∀ a : K, a′ ≠ ((Polynomial.C η).map (algebraMap C K)).eval a := fun a ↦ by
    rw [Polynomial.map_C, eval_C]; exact hnd a
  have hfinw : ∀ jj (hjj : jj < k), S.UnitFin K ⟨w jj, (hww jj hjj).1⟩ :=
    fun jj hjj a N hN l hl r hr ↦
      S.logs_zero_branchW (Polynomial.C η) hx hK k d' w hww hind' v f hv hf heq' a (hgoodη a) N
        (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (Or.inr (hreg a N hN l hl r hr)) jj hjj
  -- the combined family `(d', w) ∪ (−κ, u₀)`
  set Pr : L → Prop := fun z ↦ ∃ hz : z ∈ C⟮S.x⟯⟮S.y⟯, z ≠ 0 ∧ S.UnitFin K ⟨z, hz⟩ with hPr
  have hPzpow : ∀ a (n : ℤ), Pr a → Pr (a ^ n) := by
    rintro a n ⟨ha, ha0, haU⟩
    refine ⟨zpow_mem ha n, zpow_ne_zero _ ha0, ?_⟩
    have h0 : (⟨a, ha⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦ ha0 (congrArg Subtype.val h)
    have := S.unitFin_zpow (K := K) h0 haU n
    convert this using 2
  have hPmul : ∀ a b, Pr a → Pr b → Pr (a * b) := by
    rintro a b ⟨ha, ha0, haU⟩ ⟨hb, hb0, hbU⟩
    refine ⟨mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have := S.unitFin_mul (K := K) (fun h ↦ ha0 (congrArg Subtype.val h))
      (fun h ↦ hb0 (congrArg Subtype.val h)) haU hbU
    convert this using 2
  have hPpow : ∀ a (n : ℕ), Pr a → Pr (a ^ n) := fun a n ha ↦ by
    have := hPzpow a n ha; rwa [zpow_natCast] at this
  have hP1 : Pr 1 := ⟨one_mem _, one_ne_zero, by convert S.unitFin_one (K := K) using 2⟩
  set s2 : Finset (ℕ ⊕ Fin mu) := (Finset.range k).disjSum Finset.univ with hs2
  set c2 : ℕ ⊕ Fin mu → L := Sum.elim (fun jj ↦ algebraMap C L (d' jj)) (fun i ↦ -((κ i : ℚ) : L))
    with hc2
  set u2 : ℕ ⊕ Fin mu → L := Sum.elim w (fun i ↦ ((u0 i : C⟮S.x⟯⟮S.y⟯) : L)) with hu2
  have hc2' : ∀ i ∈ s2, (c2 i)′ = 0 := by
    rintro (jj | i) hi
    · simp only [hc2, Sum.elim_inl]
      rw [deriv_algebraMap, hd'c jj (by simpa [hs2] using hi), map_zero]
    · simp only [hc2, Sum.elim_inr, Derivation.map_neg, deriv_ratCast_K, neg_zero]
  have hu2' : ∀ i ∈ s2, u2 i ≠ 0 ∧ u2 i ∈ (C⟮S.x⟯⟮S.y⟯).toSubfield := by
    rintro (jj | i) hi
    · have := hww jj (by simpa [hs2] using hi)
      exact ⟨this.2, this.1⟩
    · exact ⟨fun h ↦ hu0 i (Subtype.ext h), (u0 i).2⟩
  have hP2 : ∀ i ∈ s2, Pr (u2 i) := by
    rintro (jj | i) hi
    · have hjj : jj < k := by simpa [hs2] using hi
      exact ⟨(hww jj hjj).1, (hww jj hjj).2, hfinw jj hjj⟩
    · exact ⟨(u0 i).2, fun h ↦ hu0 i (Subtype.ext h), hfin0 i⟩
  obtain ⟨k2, e, W, ⟨he, hW, hind2⟩, hPW, hsum2⟩ :=
    logSum_qindepP (C⟮S.x⟯⟮S.y⟯).toSubfield Pr hPmul hPpow hPzpow s2 c2 u2 hc2' hu2' hP2 hP1
  -- `f₁ = f − ∑ κᵢ u₀ᵢ′/u₀ᵢ = v′ + ∑ eⱼ Wⱼ′/Wⱼ`
  set g0 : Fin mu → L := fun i ↦ ((u0 i : C⟮S.x⟯⟮S.y⟯) : L)′ / ((u0 i : C⟮S.x⟯⟮S.y⟯) : L) with hg0
  have hg0mem : ∀ i, g0 i ∈ C⟮S.x⟯⟮S.y⟯ := fun i ↦
    div_mem (S.derivClosedXYW' (Polynomial.C η) hx (u0 i) (u0 i).2) (u0 i).2
  set f₁ : L := f - ∑ i, ((κ i : ℚ) : L) * g0 i with hf₁
  have hf₁mem : f₁ ∈ C⟮S.x⟯⟮S.y⟯ := sub_mem hf (sum_mem fun i _ ↦
    mul_mem (SubfieldClass.ratCast_mem _ (κ i)) (hg0mem i))
  have heq₁ : f₁ = v′ + ∑ j ∈ Finset.range k2, e j * logDeriv (W j) := by
    rw [← hsum2, hf₁, heq', hs2, Finset.sum_disjSum, add_sub_assoc]
    congr 1
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [logDeriv]
    rw [hg0, hc2, hu2]
    simp only [Sum.elim_inr]
    ring
  set e' : ℕ → C := fun j ↦ if h : j < k2 then Classical.choose (hconstC (e j) (he j h)) else 0
    with he'def
  have hee : ∀ j < k2, algebraMap C L (e' j) = e j := fun j hj ↦ by
    simp only [he'def, dif_pos hj]
    exact Classical.choose_spec (hconstC (e j) (he j hj))
  have he'c : ∀ j < k2, (e' j)′ = 0 := fun j hj ↦ by
    apply (algebraMap C L).injective
    rw [← deriv_algebraMap, hee j hj, he j hj, map_zero]
  have hind2' : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k2, (q j : C) * e' j = 0 →
      ∀ j < k2, q j = 0 := by
    intro q hq
    apply hind2 q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [map_mul, map_ratCast, hee j (Finset.mem_range.mp hj)]
  have hWW : ∀ j < k2, W j ∈ C⟮S.x⟯⟮S.y⟯ ∧ W j ≠ 0 := fun j hj ↦ ⟨(hW j hj).2, (hW j hj).1⟩
  have heq₁' : f₁ = v′ + ∑ j ∈ Finset.range k2, algebraMap C L (e' j) * ((W j)′ / W j) := by
    rw [heq₁]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hee j (Finset.mem_range.mp hj), logDeriv]
  -- the `Wⱼ` have no zeros or poles above infinity
  have hinfW : ∀ j (hj : j < k2) r (hr : r ∈ li),
      (S.embG (infSub Ni) (infSub_injective Ni hNi) r (S.root_of_mem hli hr)
        ⟨W j, (hWW j hj).1⟩).order = 0 := by
    intro j0 hj0 r hr
    obtain ⟨γ, hγ⟩ := hzero r hr
    set φ := S.embG (infSub Ni) (infSub_injective Ni hNi) r (S.root_of_mem hli hr) with hφ
    obtain ⟨β, hβ⟩ := S.coeff_liouville_top η hx hK Ni hNi r (S.root_of_mem hli hr)
      (Finset.range k2) e' (fun j hj ↦ he'c j (Finset.mem_range.mp hj))
      (fun j ↦ if h : j < k2 then ⟨W j, (hWW j h).1⟩ else 1)
      (fun j hj ↦ by
        rw [dif_pos (Finset.mem_range.mp hj)]
        exact fun h0 ↦ (hWW j (Finset.mem_range.mp hj)).2 (congrArg Subtype.val h0))
      ⟨v, hv⟩ ⟨f₁, hf₁mem⟩ (by
        show f₁ = _
        rw [heq₁']
        congr 1
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [dif_pos (Finset.mem_range.mp hj)])
    have hlog : ∀ i, ∃ βi : K, (φ ⟨g0 i, hg0mem i⟩).coeff (Ni : ℤ) +
        ((φ (u0 i)).order : K) / Ni * algebraMap C K η = βi′ := fun i ↦
      S.coeff_logDeriv_embG η hx hK Ni hNi r _ (u0 i) (hu0 i)
    choose βi hβi using hlog
    have hsplit : (⟨f₁, hf₁mem⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨f, hf⟩ -
        ∑ i, ((κ i : ℚ) : C⟮S.x⟯⟮S.y⟯) * ⟨g0 i, hg0mem i⟩ := by
      apply Subtype.ext
      show f₁ = _
      push_cast
      rfl
    have hf1 : (φ ⟨f₁, hf₁mem⟩).coeff (Ni : ℤ) = (φ ⟨f, hf⟩).coeff (Ni : ℤ) -
        ∑ i, (κ i : K) * (φ ⟨g0 i, hg0mem i⟩).coeff (Ni : ℤ) := by
      rw [hsplit, map_sub, map_sum, HahnSeries.coeff_sub, HahnSeries.coeff_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul, map_ratCast, ← map_ratCast (HahnSeries.C (R := K) (Γ := ℤ)),
        HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    have hκd : ∀ i, ((κ i : K) * βi i)′ = (κ i : K) * (βi i)′ := fun i ↦ by
      rw [Derivation.leibniz, deriv_ratCast_K, smul_zero, add_zero, smul_eq_mul]
    have hcomb : (φ ⟨f₁, hf₁mem⟩).coeff (Ni : ℤ) = (γ - ∑ i, (κ i : K) * βi i)′ := by
      rw [hf1, Derivation.map_sub, map_sum, Finset.sum_congr rfl fun i _ ↦ hκd i]
      have e1 : ∀ i, (φ ⟨g0 i, hg0mem i⟩).coeff (Ni : ℤ) =
          (βi i)′ - ((φ (u0 i)).order : K) / Ni * algebraMap C K η := fun i ↦ by
        rw [← hβi i]; ring
      simp only [e1, mul_sub, Finset.sum_sub_distrib]
      rw [← hγ, Finset.sum_div, Finset.sum_mul]
      have e2 : ∀ i, (κ i : K) * (((φ (u0 i)).order : K) / Ni * algebraMap C K η) =
          (κ i : K) * ((φ (u0 i)).order : K) / Ni * algebraMap C K η := fun i ↦ by ring
      simp only [e2]
      ring
    rw [hcomb] at hβ
    set ρ : K := (∑ j ∈ Finset.range k2, algebraMap C K (e' j) *
      ((φ (if h : j < k2 then ⟨W j, (hWW j h).1⟩ else 1)).order : K)) / Ni with hρ
    have hsum' : (∑ j ∈ Finset.range k2, algebraMap C K (e' j) *
        ((φ (if h : j < k2 then ⟨W j, (hWW j h).1⟩ else 1)).order : K))′ = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      rw [Derivation.leibniz, hK, he'c j (Finset.mem_range.mp hj), map_zero, smul_zero, add_zero,
        smul_eq_mul]
      rw [show ((φ (if h : j < k2 then ⟨W j, (hWW j h).1⟩ else 1)).order : K) =
        (((φ (if h : j < k2 then ⟨W j, (hWW j h).1⟩ else 1)).order : ℤ) : K) from rfl,
        Derivation.map_intCast, mul_zero]
    have hρ' : ρ′ = 0 := by
      have hn : ((Ni : K))′ = 0 := Derivation.map_natCast _ _
      rw [hρ, Derivation.leibniz_div, hsum', hn]
      simp
    have hρ0 : ρ = 0 := residue_unique η hnd _ β ρ 0 hρ' (Derivation.map_zero _) (by
      rw [zero_mul, add_zero]; exact hβ)
    have hN0 : (Ni : K) ≠ 0 := by exact_mod_cast hNi.ne'
    have hsum0 : ∑ j ∈ Finset.range k2,
        ((((φ (if h : j < k2 then ⟨W j, (hWW j h).1⟩ else 1)).order : ℤ) : ℚ) : C) * e' j = 0 := by
      apply (algebraMap C K).injective
      rw [map_zero, map_sum]
      have := hρ0
      rw [hρ, div_eq_zero_iff, or_iff_left hN0] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, map_ratCast]
      push_cast
      ring
    have h0 := hind2' (fun j ↦ (((φ (if h : j < k2 then ⟨W j, (hWW j h).1⟩ else 1)).order : ℤ) : ℚ))
      hsum0 j0 hj0
    simp only [dif_pos hj0, Int.cast_eq_zero] at h0
    exact h0
  -- hence the `Wⱼ` are constants
  have hconst : ∀ j < k2, ∃ cj : C, W j = algebraMap C L cj := by
    intro j hj
    obtain ⟨hz, -, hU⟩ := hPW j hj
    have hregW : S.RegularFinite K ⟨W j, (hWW j hj).1⟩ :=
      fun a N hN l hl r hr ↦ (hU a N hN l hl r hr).ge
    obtain ⟨M0, hM0, hwM⟩ := S.algebraic_of_regular_l ⟨W j, (hWW j hj).1⟩ hregW Ni hNi li hli
      fun r hr ↦ (hinfW j hj r hr).ge
    exact S.mem_const_of_alg_geo hgeo ⟨W j, (hWW j hj).1⟩ M0 hM0 hwM
  choose! cj hcj using hconst
  refine ⟨∑ j ∈ Finset.range k2, e' j * ((cj j)′ / cj j), ?_⟩
  have hf₁' : f₁ = v′ + algebraMap C L (∑ j ∈ Finset.range k2, e' j * ((cj j)′ / cj j)) := by
    rw [heq₁', map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hcj j (Finset.mem_range.mp hj), map_mul, map_div₀, deriv_algebraMap]
  have : f = f₁ + ∑ i, ((κ i : ℚ) : L) * logDeriv ((u0 i : C⟮S.x⟯⟮S.y⟯) : L) := by
    rw [hf₁]
    simp only [logDeriv, hg0]
    ring
  rw [this, hf₁']
  ring

end CurveData

end Curves

namespace Curves

open Differential

section SegK

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- **The coefficient at `T^k` along `ρ = T^{−ds} Θ`**, from a truncation `Θ̃ ≡ Θ mod T^{M}`. -/
theorem coeff_eval_segK (Q : C[X][X]) (N d : ℕ) (s : ℤ) (Θ Θt : PowerSeries K) (Mt : ℕ) (k : ℤ)
    (hX : (PowerSeries.X : PowerSeries K) ^ Mt ∣ Θ - Θt)
    (hM : ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      k + N * l + d * s * j < Mt) :
    ((Q.map (infSub (K := K) N)).eval (single (-((d : ℤ) * s)) 1 * ofPowerSeries ℤ K Θ)).coeff k =
      ∑ j ∈ Finset.range (Q.natDegree + 1), ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1),
        algebraMap C K ((Q.coeff j).coeff l) *
          (ofPowerSeries ℤ K (Θt ^ j)).coeff (k + N * l + d * s * j) := by
  rw [eval_map, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [infSub_eq_sum, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' : l ≤ (Q.coeff j).natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hpow : (single (-((d : ℤ) * s)) (1 : K) * ofPowerSeries ℤ K Θ) ^ j =
      single (-((d : ℤ) * s * j)) 1 * ofPowerSeries ℤ K (Θ ^ j) := by
    rw [mul_pow, map_pow, HahnSeries.single_pow, one_pow]
    congr 2
    rw [nsmul_eq_mul]; ring
  have hsg : single (-((N : ℤ) * l)) (algebraMap C K ((Q.coeff j).coeff l)) =
      HahnSeries.C (algebraMap C K ((Q.coeff j).coeff l)) * single (-((N : ℤ) * l)) 1 := by
    rw [HahnSeries.C_mul_eq_smul]
    ext n
    simp only [HahnSeries.coeff_smul, HahnSeries.coeff_single, smul_eq_mul]
    split_ifs <;> simp
  rw [hpow, hsg, mul_assoc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, ← mul_assoc,
    HahnSeries.single_mul_single, one_mul, LaurentSeries.coeff_single_mul, smul_eq_mul]
  congr 1
  rw [show k - (-((N : ℤ) * l) + -((d : ℤ) * s * j)) = k + N * l + d * s * j by ring]
  rw [LaurentSeries.coeff_ofPS, LaurentSeries.coeff_ofPS]
  split_ifs with h0
  · have hdj : (PowerSeries.X : PowerSeries K) ^ Mt ∣ Θ ^ j - Θt ^ j :=
      hX.trans (sub_dvd_pow_sub_pow _ _ _)
    have hlt : (k + N * l + d * s * j).toNat < Mt := by
      have := hM j hj' l hl'; omega
    have h0' := (PowerSeries.X_pow_dvd_iff.mp hdj) _ hlt
    rw [map_sub, sub_eq_zero] at h0'
    exact h0'
  · rfl


lemma coeff_ofPS_phiD_pow_ndvd (d : ℕ) (hd : 0 < d) (Θ : C[X]) (j : ℕ) (n : ℤ)
    (hn : ¬ (d : ℤ) ∣ n) : (ofPowerSeries ℤ K (phiD (K := K) d Θ ^ j)).coeff n = 0 := by
  rw [← map_pow, LaurentSeries.coeff_ofPS]
  split_ifs with h0
  · rw [coeff_phiD d hd, if_neg]
    intro hdv
    apply hn
    rw [← Int.toNat_of_nonneg h0]
    exact_mod_cast hdv
  · rfl

lemma order_eq_of_coeffs (X0 : LaurentSeries K) (o : ℤ) (h1 : X0.coeff o ≠ 0)
    (h0 : ∀ k < o, X0.coeff k = 0) : X0.order = o := by
  have hX : X0 ≠ 0 := fun h ↦ h1 (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push_neg at hlt
  exact hX (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

/-- **The order along `ρ = T^{−ds} Θ`** from the coefficients of a truncation. -/
theorem order_eval_seg (U : C[X][X]) (N d e : ℕ) (hN : N = d * e) (hd : 0 < d) (s : ℤ)
    (Θ : PowerSeries K) (Θt : C[X]) (M : ℕ)
    (hX : (PowerSeries.X : PowerSeries K) ^ (d * M) ∣ Θ - phiD d Θt) (o : ℤ)
    (hprec : ∀ j ≤ U.natDegree, ∀ l ≤ (U.coeff j).natDegree, o + e * l + s * j < M)
    (h1 : ∑ j ∈ Finset.range (U.natDegree + 1), ∑ l ∈ Finset.range ((U.coeff j).natDegree + 1),
      (U.coeff j).coeff l * (if 0 ≤ o + e * l + s * j then
        (Θt ^ j).coeff (o + e * l + s * j).toNat else 0) ≠ 0)
    (h0 : ∀ κ < o, ∑ j ∈ Finset.range (U.natDegree + 1),
      ∑ l ∈ Finset.range ((U.coeff j).natDegree + 1),
      (U.coeff j).coeff l * (if 0 ≤ κ + e * l + s * j then
        (Θt ^ j).coeff (κ + e * l + s * j).toNat else 0) = 0) :
    ((U.map (infSub (K := K) N)).eval (single (-((d : ℤ) * s)) 1 * ofPowerSeries ℤ K Θ)).order =
      d * o := by
  have hval : ∀ κ : ℤ, κ ≤ o →
      ((U.map (infSub (K := K) N)).eval (single (-((d : ℤ) * s)) 1 * ofPowerSeries ℤ K Θ)).coeff
        (d * κ) = algebraMap C K (∑ j ∈ Finset.range (U.natDegree + 1),
          ∑ l ∈ Finset.range ((U.coeff j).natDegree + 1),
          (U.coeff j).coeff l * (if 0 ≤ κ + e * l + s * j then
            (Θt ^ j).coeff (κ + e * l + s * j).toNat else 0)) := by
    intro κ hκ
    rw [coeff_eval_segK U N d s Θ (phiD d Θt) (d * M) (d * κ) hX (fun j hj l hl ↦ by
      have := hprec j hj l hl
      have h2 : (d : ℤ) * κ + N * l + d * s * j = d * (κ + e * l + s * j) := by
        rw [hN]; push_cast; ring
      rw [h2]; push_cast
      have h3 : κ + e * l + s * j < M := by linarith
      exact mul_lt_mul_of_pos_left h3 (by exact_mod_cast hd))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have h2 : (d : ℤ) * κ + N * l + d * s * j = d * (κ + e * l + s * j) := by
      rw [hN]; push_cast; ring
    rw [h2, coeff_ofPS_phiD_pow d hd, map_mul]
    split_ifs
    · rfl
    · rw [map_zero, mul_zero]
  refine order_eq_of_coeffs _ _ ?_ ?_
  · rw [hval o le_rfl]
    exact fun h ↦ h1 ((algebraMap C K).injective (by rw [h, map_zero]))
  · intro k hk
    obtain ⟨κ, ρ, hρ0, hρd, rfl⟩ : ∃ κ ρ : ℤ, 0 ≤ ρ ∧ ρ < d ∧ k = d * κ + ρ :=
      ⟨k / d, k % d, Int.emod_nonneg _ (by exact_mod_cast hd.ne'),
        Int.emod_lt_of_pos _ (by exact_mod_cast hd), by
          have := Int.mul_ediv_add_emod k d; linarith⟩
    have hκo : κ < o := by
      by_contra h; push_neg at h
      have : (d : ℤ) * o ≤ d * κ := mul_le_mul_of_nonneg_left h (by positivity)
      linarith
    rcases eq_or_lt_of_le hρ0 with hρ | hρ
    · rw [← hρ, add_zero, hval κ hκo.le, h0 κ hκo, map_zero]
    · rw [coeff_eval_segK U N d s Θ (phiD d Θt) (d * M) _ hX (fun j hj l hl ↦ by
        have := hprec j hj l hl
        have h2 : (d : ℤ) * κ + ρ + N * l + d * s * j < d * (o + e * l + s * j) := by
          rw [hN]; push_cast
          have : (d : ℤ) * κ + ρ < d * o := hk
          nlinarith
        have h3 : (d : ℤ) * (o + e * l + s * j) < d * M :=
          mul_lt_mul_of_pos_left this (by exact_mod_cast hd)
        push_cast at h3 ⊢
        linarith)]
      refine Finset.sum_eq_zero fun j _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
      rw [coeff_ofPS_phiD_pow_ndvd d hd, mul_zero]
      intro hdv
      have : (d : ℤ) ∣ ρ := by
        have h4 : (d : ℤ) ∣ d * κ + N * l + d * s * j := by
          rw [hN]; push_cast
          exact ⟨κ + e * l + s * j, by ring⟩
        have e5 : ρ = ((d : ℤ) * κ + ρ + N * l + d * s * j) - ((d : ℤ) * κ + N * l + d * s * j) := by
          ring
        rw [e5]
        exact dvd_sub hdv h4
      have := Int.le_of_dvd hρ this
      omega

end SegK

end Curves

namespace Curves

open Differential

section CurveRes

variable {C L Kb : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]
  [Field Kb] [CharZero Kb] [Algebra C Kb] [Differential Kb] [IsAlgClosed Kb]

namespace CurveData

variable (S : CurveData C L)

/-- **Residues at infinity matched by units, several Newton segments**: with the place data of
`zero_res_multi`, units `wᵢ = Uᵢ/dᵢ` whose expansions along the place `(k, γ)` have `τ`-order
`oₖᵢ` (certified by the coefficients of the truncation), and rationals `κᵢ` such that
`resₖ(f) + (∑ κᵢ (oₖᵢ + e deg dᵢ)/e) η` is a derivative: then along a branch system above
infinity `[T^N] f + (∑ κᵢ ord wᵢ)/N · η` is a derivative. -/
theorem res_match_multi {q : ℕ} (e : Fin (q + 1) → ℕ) (he : ∀ k, 0 < e k) (s : Fin (q + 1) → ℤ)
    (hcop : ∀ k, Int.gcd (s k) (e k) = 1)
    (hdec : ∀ k : Fin q, s k.succ * e k.castSucc < s k.castSucc * e k.succ)
    (K0 : Fin (q + 1) → ℤ) (c : Fin (q + 1) → C) (hc : ∀ k, c k ≠ 0) (lo : Fin (q + 1) → ℕ)
    (Γ : Fin (q + 1) → List C) (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : C) ∉ Γ k)
    (hbound : ∀ k, ∀ i ≤ S.F.natDegree, S.F.coeff i ≠ 0 →
      (e k : ℤ) * (S.F.coeff i).natDegree + i * s k ≤ K0 k)
    (hres : ∀ k, ∑ i ∈ Finset.range (S.F.natDegree + 1),
      Polynomial.C (coeffZe (S.F.coeff i) (e k) (K0 k - i * s k)) * X ^ i =
        Polynomial.C (c k) * X ^ (lo k) * ((Γ k).map fun γ ↦ X ^ (e k) - Polynomial.C γ).prod)
    (htop : lo 0 + e 0 * (Γ 0).length = S.F.natDegree)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + e k.succ * (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0)
    (β : ∀ k, Fin (Γ k).length → C) (hβ : ∀ k i, β k i ^ e k = (Γ k)[(i : ℕ)])
    (Θt : ∀ k, Fin (Γ k).length → C[X]) (hΘ0 : ∀ k i, (Θt k i).coeff 0 = β k i)
    (hu : ∀ k i, ((derivative (segPoly (e k) (s k) (K0 k) S.F)).eval (Θt k i)).coeff 0 ≠ 0)
    (M : ℕ) (hM : ∀ k i, ∀ n < M, ((segPoly (e k) (s k) (K0 k) S.F).eval (Θt k i)).coeff n = 0)
    (Q : C[X][X])
    (hMb : ∀ k, ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      (e k : ℤ) + e k * l + s k * j < M)
    (z : ∀ k, Fin (Γ k).length → C)
    {mu : ℕ} (Uu : Fin mu → C[X][X]) (dd : Fin mu → C[X]) (hdd : ∀ i, dd i ≠ 0)
    (hU0 : ∀ i, S.evT (Uu i) ≠ 0)
    (o : ∀ k, Fin (Γ k).length → Fin mu → ℤ)
    (hprec : ∀ k p i, ∀ j ≤ (Uu i).natDegree, ∀ l ≤ ((Uu i).coeff j).natDegree,
      o k p i + e k * l + s k * j < M)
    (ho1 : ∀ k p i, ∑ j ∈ Finset.range ((Uu i).natDegree + 1),
      ∑ l ∈ Finset.range (((Uu i).coeff j).natDegree + 1), ((Uu i).coeff j).coeff l *
        (if 0 ≤ o k p i + e k * l + s k * j then
          ((Θt k p) ^ j).coeff (o k p i + e k * l + s k * j).toNat else 0) ≠ 0)
    (ho0 : ∀ k p i, ∀ κ < o k p i, ∑ j ∈ Finset.range ((Uu i).natDegree + 1),
      ∑ l ∈ Finset.range (((Uu i).coeff j).natDegree + 1), ((Uu i).coeff j).coeff l *
        (if 0 ≤ κ + e k * l + s k * j then
          ((Θt k p) ^ j).coeff (κ + e k * l + s k * j).toNat else 0) = 0)
    (κs : Fin mu → ℚ)
    (η : C)
    (hz : ∀ k i, (z k i)′ = ∑ j ∈ Finset.range (Q.natDegree + 1),
      ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
        (if 0 ≤ (e k : ℤ) + e k * l + s k * j then
          ((Θt k i) ^ j).coeff ((e k : ℤ) + e k * l + s k * j).toNat else 0) +
      (∑ ii, ((κs ii : ℚ) : C) * ((o k i ii + e k * (dd ii).natDegree : ℤ) : C)) / (e k : C) * η)
    (hK : ∀ c : C, (algebraMap C Kb c)′ = algebraMap C Kb c′) :
    ∃ (N : ℕ) (hN : 0 < N) (li : List (LaurentSeries Kb)) (hli : S.F.map (infSub (K := Kb) N) =
      (li.map fun r ↦ X - Polynomial.C r).prod),
      ∀ r (hr : r ∈ li), ∃ b : Kb, (S.embG (infSub N) (infSub_injective N hN) r
        (S.root_of_mem hli hr) (S.evT Q)).coeff (N : ℤ) +
        (∑ i, (κs i : Kb) * ((S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hli hr)
          (S.evT (Uu i) / S.evT (Polynomial.C (dd i)))).order : Kb)) / N * algebraMap C Kb η =
            b′ := by
  classical
  have hF0 : S.F.coeff 0 ≠ 0 := coeff0_ne_of_resR S.F (e (Fin.last q)) (he _) (s (Fin.last q))
    (K0 (Fin.last q)) (c (Fin.last q)) (hc _) (Γ (Fin.last q)) (hΓ _).2
    (by rw [← hlast]; exact hres _)
  obtain ⟨Nb, hNb, lb, -, hlb⟩ := S.hasBranchesInf (K := Kb)
  have hNb' := Nat.pos_of_ne_zero hNb
  set E : ℕ := ∏ k, e k with hE
  have hE0 : 0 < E := Finset.prod_pos fun k _ ↦ he k
  set N : ℕ := Nb * E with hNdef
  have hN : 0 < N := Nat.mul_pos hNb' hE0
  set lr := lb.map (lsub E hE0) with hlr
  have hl : S.F.map (infSub N) = (lr.map fun r ↦ X - Polynomial.C r).prod :=
    branchSys_lsub S.F Nb E hE0 lb hlb
  have hed : ∀ k, e k ∣ N := fun k ↦
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  have hsA := strictAnti_weights N hN e he hed s hdec
  obtain ⟨hord, huniq, -⟩ := multi_hdataR (K := Kb) N hN S.F S.monic hF0 lr hl e he hed s
    hsA K0 c hc lo Γ hΓ hbound hres htop hchain hlast
  have hl0 : ∀ r ∈ lr, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h1 : (S.F.map (infSub (K := Kb) N)).eval 0 = 0 := S.root_of_mem hl hr
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h1
    exact hF0 ((infSub_injective N hN) (by rw [h1, map_zero]))
  have : NeZero ((N : ℕ) : Kb) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Kb N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  refine ⟨N, hN, lr, hl, fun r hr ↦ ?_⟩
  obtain ⟨k, hk, γ, hγ, hγe⟩ := hord r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hγ
  set ι := algebraMap C Kb with hι
  set cr := r.coeff r.order with hcr
  have hcr0 : cr ≠ 0 := fun h ↦ hl0 r hr (HahnSeries.coeff_order_eq_zero.mp h)
  set bK := ι (β k ⟨i, hi⟩) with hbK
  set uu := bK / cr with huu
  have hue : uu ^ e k = 1 := by
    rw [huu, div_pow, hγe, hbK, ← map_pow, hβ k ⟨i, hi⟩, div_self]
    rw [← hγe]; exact pow_ne_zero _ hcr0
  obtain ⟨d, hd⟩ := hed k
  have hNe : N / e k = d := by rw [hd, Nat.mul_div_cancel_left _ (he k)]
  have hω : IsPrimitiveRoot (ζ ^ d) (e k) := hζ.pow hN (by rw [hd, mul_comm])
  have hωs : IsPrimitiveRoot ((ζ ^ d) ^ (-s k)) (e k) :=
    hω.zpow_of_gcd_eq_one (-s k) (by rw [Int.neg_gcd]; exact hcop k)
  haveI : NeZero (e k) := ⟨(he k).ne'⟩
  obtain ⟨j, -, hj⟩ := hωs.eq_pow_of_pow_eq_one hue
  have hζj0 : ζ ^ j ≠ 0 := pow_ne_zero _ hζ0
  have hζjN : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  set r' := rot (ζ ^ j) hζj0 r with hr'
  have hr'mem : r' ∈ lr := S.rot_mem N hζj0 hζjN lr hl hr
  have hr'o : r'.order = -((d : ℤ) * s k) := by rw [hr', rot_order, hk, hNe]
  have hr'c : r'.coeff r'.order = bK := by
    rw [hr', rot_lc]
    have hpow' : (ζ ^ j) ^ r.order = ((ζ ^ d) ^ (-s k)) ^ j := by
      rw [hk, hNe, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
        ← zpow_mul]
      congr 1
      ring
    rw [hpow', hj, huu, div_mul_cancel₀ _ hcr0]
  -- the residue along `r` is the one along `r'`
  have hrr := S.root_of_mem hl hr
  have hrr' := S.root_of_mem hl hr'mem
  have hrot := S.embG_rot_coeff N hN hζj0 hζjN r hrr hrr' (S.evT Q) (N : ℤ)
  rw [show (ζ ^ j) ^ (N : ℤ) = 1 by rw [zpow_natCast, hζjN], one_mul] at hrot
  -- the power series of `r'`
  set Θ := r'.powerSeriesPart with hΘ
  have hr'eq : r' = single (-((d : ℤ) * s k)) 1 * ofPowerSeries ℤ Kb Θ := by
    rw [← hr'o]; exact (single_order_mul_powerSeriesPart r').symm
  have hΘc : PowerSeries.constantCoeff Θ = ι ((Θt k ⟨i, hi⟩).coeff 0) := by
    rw [hΘ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff, Nat.cast_zero,
      add_zero, hr'c, hΘ0]
  have hNde : N = d * e k := by rw [hd, mul_comm]
  have hroot : ((segPoly (e k) (s k) (K0 k) S.F).map (phiD (K := Kb) d)).eval Θ = 0 :=
    segPoly_root N d (e k) hNde (s k) (K0 k) S.F (hbound k) Θ (by rw [← hr'eq]; exact hrr')
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hd; omega)
  have hagree := seg_trunc d hd0 _ Θ hroot (Θt k ⟨i, hi⟩) hΘc (hu k ⟨i, hi⟩) M (hM k ⟨i, hi⟩)
  -- (A) the residue coefficient
  have hA : (S.embG (infSub N) (infSub_injective N hN) r hrr (S.evT Q)).coeff (N : ℤ) =
      ι (∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
          (if 0 ≤ (e k : ℤ) + e k * l + s k * j then
            ((Θt k ⟨i, hi⟩) ^ j).coeff ((e k : ℤ) + e k * l + s k * j).toNat else 0)) := by
    rw [← hrot, S.embG_evT]
    rw [show (rot (ζ ^ j) hζj0) r = r' from rfl, hr'eq]
    rw [coeff_eval_seg Q N d (s k) Θ (phiD d (Θt k ⟨i, hi⟩)) (d * M) hagree (fun j' hj' l hl' ↦ by
      have := hMb k j' hj' l hl'
      have h2 : (N : ℤ) + N * l + d * s k * j' = d * ((e k : ℤ) + e k * l + s k * j') := by
        rw [hNde]; push_cast; ring
      rw [h2]; push_cast
      exact mul_lt_mul_of_pos_left this (by exact_mod_cast hd0))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have h2 : (N : ℤ) + N * l + d * s k * j' = d * ((e k : ℤ) + e k * l + s k * j') := by
      rw [hNde]; push_cast; ring
    rw [h2, coeff_ofPS_phiD_pow d hd0, map_mul]
    split_ifs
    · rfl
    · rw [map_zero, mul_zero]
  -- (B) the orders of the units
  have hB : ∀ ii, (S.embG (infSub N) (infSub_injective N hN) r hrr
      (S.evT (Uu ii) / S.evT (Polynomial.C (dd ii)))).order =
        d * o k ⟨i, hi⟩ ii + N * (dd ii).natDegree := by
    intro ii
    have hrw := S.embG_rot_inf (ζ ^ j) hζj0 N hN hζjN r hrr
      (S.evT (Uu ii) / S.evT (Polynomial.C (dd ii)))
    have e1 : (S.embG (infSub N) (infSub_injective N hN) r hrr
        (S.evT (Uu ii) / S.evT (Polynomial.C (dd ii)))).order =
        (S.embG (infSub N) (infSub_injective N hN) r' hrr'
        (S.evT (Uu ii) / S.evT (Polynomial.C (dd ii)))).order := by
      rw [show (S.embG (infSub N) (infSub_injective N hN) r' hrr') =
        S.embG (infSub N) (infSub_injective N hN) (rot (ζ ^ j) hζj0 r)
          (rot_root_inf (ζ ^ j) hζj0 N hζjN S.F r hrr) from rfl, hrw, rot_order]
    rw [e1, map_div₀, S.embG_evT, S.embG_evT, Polynomial.map_C, eval_C]
    have hnum : ((Uu ii).map (infSub (K := Kb) N)).eval r' ≠ 0 := by
      rw [← S.embG_evT (infSub N) (infSub_injective N hN) r' hrr']
      exact (map_ne_zero_iff _ (RingHom.injective _)).mpr (hU0 ii)
    have hden : infSub (K := Kb) N (dd ii) ≠ 0 :=
      (map_ne_zero_iff _ (infSub_injective N hN)).mpr (hdd ii)
    rw [div_eq_mul_inv, HahnSeries.order_mul hnum (inv_ne_zero hden), order_inv_nk _ hden,
      order_infSub N hN (dd ii) (hdd ii), hr'eq,
      order_eval_seg (Uu ii) N d (e k) hNde hd0 (s k) Θ (Θt k ⟨i, hi⟩) M hagree (o k ⟨i, hi⟩ ii)
        (hprec k ⟨i, hi⟩ ii) (ho1 k ⟨i, hi⟩ ii) (ho0 k ⟨i, hi⟩ ii)]
    ring
  refine ⟨ι (z k ⟨i, hi⟩), ?_⟩
  rw [hA, hK, hz k ⟨i, hi⟩, map_add]
  congr 1
  simp only [hB]
  have hN0 : (N : Kb) ≠ 0 := by exact_mod_cast hN.ne'
  have he0 : (e k : Kb) ≠ 0 := by exact_mod_cast (he k).ne'
  have hd0' : (d : Kb) ≠ 0 := by exact_mod_cast hd0.ne'
  have hNK : (N : Kb) = d * e k := by rw [hNde]; push_cast; ring
  rw [map_mul, map_div₀, map_sum, map_natCast]
  rw [Finset.sum_div, Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ii _ ↦ ?_
  rw [map_mul, map_ratCast, map_intCast]
  push_cast
  rw [hNK]
  field_simp


end CurveData

end CurveRes

end Curves
