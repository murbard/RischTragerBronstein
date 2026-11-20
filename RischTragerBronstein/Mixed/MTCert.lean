import RischTragerBronstein.Mixed.MTBase

/-!
# Mixed towers over a curve: the certificate and the logarithmic-derivative bound

Ported from `Tower.NestX` (`NestXCert`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

/-- The check of `certC` at level `m`. -/
def certLevel (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m) (m : ℕ) : Bool :=
  let O := MO Fc ks m
  match ks m with
  | .prim η => !O.isZero (lv m) &&
      O.isZero (O.add η (O.neg (O.mul (O.deriv (lv m)) (O.inv (lv m))))) &&
      (paramLimC Fc ks lv m [η]).all fun r ↦ r.1.getD 0 0 == 0
  | .exp a => (mrel Fc ks m (O.deriv a :: gensDC Fc ks m)).all fun u ↦ u.getD 0 0 == 0

lemma certX_eq (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m) (n : ℕ) :
    certC Fc ks lv n = (List.range n).all (certLevel Fc ks lv) := rfl

lemma certX_succ (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m) (n : ℕ) :
    certC Fc ks lv (n + 1) = (certC Fc ks lv n && certLevel Fc ks lv n) := by
  rw [certX_eq, certX_eq, List.range_succ, List.all_append]
  simp


namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


lemma certLevel_exp {lv : (m : ℕ) → LC m} {m : ℕ} {a : LC m}
    (hk : ks m = .exp a) (hc : certLevel Fc ks lv m = true) :
    ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0 := by
  simp only [certLevel, hk] at hc
  intro u hu
  simpa using List.all_eq_true.mp hc u hu

lemma certLevel_prim {lv : (m : ℕ) → LC m} {m : ℕ} {η : LC m}
    (hk : ks m = .prim η) (h : T.Tr m) (hc : certLevel Fc ks lv m = true) :
    (T.MP m h).sem (lv m) ≠ 0 ∧ (T.MP m h).sem η = logDeriv ((T.MP m h).sem (lv m)) := by
  simp only [certLevel, hk, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨h1, h2⟩, -⟩ := hc
  have hv : (T.MP m h).sem (lv m) ≠ 0 := by
    intro h0
    rw [← (T.MP m h).isZero_iff] at h0
    rw [h0] at h1
    exact Bool.noConfusion h1
  refine ⟨hv, ?_⟩
  rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, (T.MP m h).sem_mul,
    (T.MP m h).sem_deriv, (T.MP m h).sem_inv] at h2
  unfold logDeriv
  rw [div_eq_mul_inv]
  linear_combination h2

lemma certLevel_lim {lv : (m : ℕ) → LC m} {m : ℕ} {η : LC m}
    (hk : ks m = .prim η) (hc : certLevel Fc ks lv m = true) :
    ∀ r ∈ paramLimC Fc ks lv m [η], r.1.getD 0 0 = 0 := by
  simp only [certLevel, hk, Bool.and_eq_true] at hc
  intro r hr
  simpa using List.all_eq_true.mp hc.2 r hr

/-! ### The derivatives of the generators as codes -/

lemma evN_liftX (m : ℕ) (h : T.Tr m) (q : LC m) :
    T.ev (m + 1) (liftEC Fc ks m q) = T.ev m q := by
  change T.evP m [q] / T.evP m [(MO Fc ks m).one] = _
  simp only [evP, evPL, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  have h1 : T.ev m (MO Fc ks m).one = 1 := by rw [← T.sem_MP m h, (T.MP m h).sem_one]; rfl
  change T.ev m q / T.ev m (MO Fc ks m).one = T.ev m q
  rw [h1, div_one]

lemma gensD_last (m : ℕ) (h : T.Tr m) (hmn : m < T.n) :
    T.ev m (match ks m with
      | .exp a => (MO Fc ks m).deriv a
      | .prim η => η) = (T.genX m)′ := by
  unfold genX
  rcases hk : ks m with η | a
  · rw [T.ht m hmn, hk]; rfl
  · rw [← T.sem_MP m h, (T.MP m h).sem_deriv, coe_deriv, T.sem_MP]

lemma gensD_spec : ∀ (m : ℕ) (h : T.Tr m), (gensDC Fc ks m).length = m ∧ ∀ i < m,
    (((T.MP m h).sem ((gensDC Fc ks m).getD i (MO Fc ks m).zero) : T.F m) : L) = (T.genX i)′
  | 0, _ => ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | m + 1, h => by
    have hm : T.Tr m := fun i hi ↦ h i (by omega)
    obtain ⟨hl, hv⟩ := gensD_spec m hm
    have he : gensDC Fc ks (m + 1) = ((gensDC Fc ks m) ++ [match ks m with
      | .exp a => (MO Fc ks m).deriv a
      | .prim η => η]).map (liftEC Fc ks m) := rfl
    refine ⟨by rw [he, List.length_map, List.length_append, hl]; rfl, fun i hi ↦ ?_⟩
    rw [T.sem_MP, he, NestTower.getD_map' _ _ (MO Fc ks m).zero _ (by simp [hl]; omega),
      T.evN_liftX m hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi), ← T.sem_MP m hm]; exact hv i hi
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self]
      exact T.gensD_last i hm (T.lt_of_transcendental (h i (by omega)))

/-- Under the exponential check, `aₘ′` is not a constant combination of the `genX i′`. -/
lemma no_rel_gensD (m : ℕ) (h : T.Tr m) {a : LC m}
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0) (c0 : Cc)
    (q : ℕ → Cc)
    (hrel : algebraMap Cc L c0 * (T.ev m a)′ =
      ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * (T.genX i)′) : c0 = 0 := by
  set vs : List (LC m) := (MO Fc ks m).deriv a :: gensDC Fc ks m with hvs
  obtain ⟨hl, hv⟩ := T.gensD_spec m h
  have hlen : vs.length = m + 1 := by simp [hvs, hl]
  set f : ℕ → Cc := fun j ↦ if j = 0 then c0 else -q (j - 1) with hf
  have h0 := T.coeff0_eq_zero_of_cert m h vs hc2 ((List.range vs.length).map f) (by simp)
    (Subtype.ext (by
      rw [T.rel_val m h vs f, ZeroMemClass.coe_zero, hlen, Finset.sum_range_succ']
      have e : ∀ j ∈ Finset.range m, algebraMap Cc L (f (j + 1)) *
          (((T.MP m h).sem (vs.getD (j + 1) (MO Fc ks m).zero) : T.F m) : L) =
          -(algebraMap Cc L (q j) * (T.genX j)′) := fun j hj ↦ by
        rw [hvs, List.getD_cons_succ, hv j (Finset.mem_range.mp hj)]
        simp [hf]
      rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
      have e0 : (((T.MP m h).sem (vs.getD 0 (MO Fc ks m).zero) : T.F m) : L) =
          (T.ev m a)′ := by
        rw [hvs, List.getD_cons_zero, (T.MP m h).sem_deriv, coe_deriv, T.sem_MP]
      rw [e0]
      simp only [hf, if_pos rfl]
      rw [hrel]
      ring))
  rw [NestTower.getD_range_map _ _ (by rw [hlen]; omega)] at h0
  simpa [hf] using h0

/-- Differentiating the conclusion of the structure theorem. -/
lemma deriv_structure (m : ℕ) (Z : L) (q : ℕ → Cc) (κ : Cc)
    (hZ : Z = ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * T.genX i + algebraMap Cc L κ) :
    Z′ = ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * (T.genX i)′ := by
  have hK : ∀ c : Cc, (algebraMap Cc L c)′ = 0 := fun c ↦ by
    rw [deriv_algebraMap, T.hC, map_zero]
  rw [hZ, map_add, hK, add_zero, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, hK, smul_zero, add_zero, smul_eq_mul]

/-! ### The logarithmic-derivative bound -/

set_option maxHeartbeats 1600000 in
/-- **The logarithmic-derivative bound is correct**: if `(V + μ aₘ)′` is a constant combination
of logarithmic derivatives in `F m`, then `pldC` returns `μ` (which is rational). -/
theorem pldX_spec (m : ℕ) (hM : T.MixHyp m) {a : LC m}
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (V : LC m) (μ : Cc) {ι : Type} (s : Finset ι) (c : ι → Cc) (u : ι → L)
    (hu : ∀ i ∈ s, u i ∈ T.F m ∧ u i ≠ 0)
    (hd : (T.ev m V + algebraMap Cc L μ * T.ev m a)′ =
      ∑ i ∈ s, algebraMap Cc L (c i) * logDeriv (u i)) :
    ∃ q : ℚ, pldC Fc ks m V a = some q ∧ μ = (q : Cc) := by
  classical
  have h := hM.tr
  set O := MO Fc ks m with hO
  have hmem : T.ev m V + algebraMap Cc L μ * T.ev m a ∈ T.F m :=
    add_mem (T.ev_mem m V) (mul_mem ((T.F m).algebraMap_mem μ) (T.ev_mem m a))
  obtain ⟨q, κ, hq⟩ := T.mix_structure m hM _ hmem s c u hu hd
  have hK : ∀ c : Cc, (algebraMap Cc L c)′ = 0 := fun c ↦ by
    rw [deriv_algebraMap, T.hC, map_zero]
  have hrel : (T.ev m V)′ + algebraMap Cc L μ * (T.ev m a)′ =
      ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * (T.genX i)′ := by
    rw [← T.deriv_structure m _ q κ hq, map_add, Derivation.leibniz, hK, smul_zero, add_zero,
      smul_eq_mul]
  set vs : List (LC m) := O.deriv V :: O.deriv a :: gensDC Fc ks m with hvs
  obtain ⟨hlD, hvD⟩ := T.gensD_spec m h
  have hlen : vs.length = m + 2 := by simp [hvs, hlD]
  have hsum : ∀ g : ℕ → Cc, ∑ j ∈ Finset.range vs.length, algebraMap Cc L (g j) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : L) =
      algebraMap Cc L (g 0) * (T.ev m V)′ +
        algebraMap Cc L (g 1) * (T.ev m a)′ +
        ∑ j ∈ Finset.range m, algebraMap Cc L (g (j + 2)) * (T.genX j)′ := by
    intro g
    rw [hlen, Finset.sum_range_succ', Finset.sum_range_succ', zero_add]
    have e : ∀ j ∈ Finset.range m, algebraMap Cc L (g (j + 1 + 1)) *
        (((T.MP m h).sem (vs.getD (j + 1 + 1) O.zero) : T.F m) : L) =
        algebraMap Cc L (g (j + 2)) * (T.genX j)′ := fun j hj ↦ by
      rw [hvs, List.getD_cons_succ, List.getD_cons_succ, hvD j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl e]
    have e0 : (((T.MP m h).sem (vs.getD 0 O.zero) : T.F m) : L) = (T.ev m V)′ := by
      rw [hvs, List.getD_cons_zero, (T.MP m h).sem_deriv, coe_deriv, T.sem_MP]
    have e1 : (((T.MP m h).sem (vs.getD 1 O.zero) : T.F m) : L) = (T.ev m a)′ := by
      rw [hvs, List.getD_cons_succ, List.getD_cons_zero, (T.MP m h).sem_deriv, coe_deriv,
        T.sem_MP]
    rw [e0, e1]
    ring
  -- the relation `(1, μ, -q)`
  set fc : ℕ → Cc := fun j ↦ if j = 0 then 1 else if j = 1 then μ else -q (j - 2) with hfc
  have h0c : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fc) vs).sum = 0 := Subtype.ext (by
    rw [T.rel_val m h vs fc, hsum, ZeroMemClass.coe_zero]
    have e : ∀ j ∈ Finset.range m, algebraMap Cc L (fc (j + 2)) * (T.genX j)′ =
        -(algebraMap Cc L (q j) * (T.genX j)′) := fun j _ ↦ by
      simp [hfc]
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
    simp only [hfc, if_pos rfl, if_neg one_ne_zero, ↓reduceIte, map_one, one_mul]
    linear_combination hrel)
  obtain ⟨u0, hu0U, hu00⟩ := T.exists_coeff0_ne m h vs _ (by simp) h0c (by
    rw [NestTower.getD_range_map _ _ (by rw [hlen]; omega)]; simp [hfc])
  obtain ⟨u1, hfind⟩ : ∃ u1, (mrel Fc ks m vs).find? (fun u ↦ u.getD 0 0 ≠ 0) = some u1 := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨u0, hu0U, by simpa using hu00⟩
  have hu1U : u1 ∈ mrel Fc ks m vs := List.mem_of_find?_eq_some hfind
  have hu10 : u1.getD 0 0 ≠ 0 := by simpa using List.find?_some hfind
  have hpld : pldC Fc ks m V a = some (u1.getD 1 0 / u1.getD 0 0) := by
    simp only [pldC]
    rw [show (O.deriv V :: O.deriv a :: gensDC Fc ks m) = vs from rfl, hfind]
  refine ⟨_, hpld, ?_⟩
  -- the relation of `u₁`
  have hs1 := T.mrel_sound m h vs u1 hu1U
  have hs1E : ∑ j ∈ Finset.range vs.length, algebraMap Cc L (algebraMap ℚ Cc (u1.getD j 0)) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : L) = 0 := by
    rw [← T.rel_val m h vs, hs1, ZeroMemClass.coe_zero]
  rw [hsum] at hs1E
  -- eliminate `V′`
  set r0 : Cc := algebraMap ℚ Cc (u1.getD 0 0) with hr0
  set r1 : Cc := algebraMap ℚ Cc (u1.getD 1 0) with hr1
  have hkey := T.no_rel_gensD m h hc2 (r0 * μ - r1)
    (fun j ↦ r0 * q j + algebraMap ℚ Cc (u1.getD (j + 2) 0)) (by
      simp only [map_add, map_mul, map_sub, add_mul, Finset.sum_add_distrib]
      have e1 : ∑ i ∈ Finset.range m, algebraMap Cc L r0 * algebraMap Cc L (q i) *
          (T.genX i)′ = algebraMap Cc L r0 *
            ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * (T.genX i)′ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [e1, ← hrel]
      linear_combination -hs1E)
  have hr0' : r0 ≠ 0 := by
    rw [hr0]; exact (map_ne_zero_iff _ (algebraMap ℚ Cc).injective).mpr hu10
  rw [Rat.cast_div, ← eq_ratCast (algebraMap ℚ Cc), ← eq_ratCast (algebraMap ℚ Cc), ← hr0, ← hr1]
  field_simp
  linear_combination hkey

/-! ### The hypotheses of the next level -/

theorem mixHyp_zero : T.MixHyp 0 :=
  ⟨fun i hi ↦ absurd hi (Nat.not_lt_zero i), fun i hi ↦ absurd hi (Nat.not_lt_zero i),
    fun i hi ↦ absurd hi (Nat.not_lt_zero i), fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩

/-- At a certified exponential level there is no `e′ + j aₘ′ e = 0`. -/
lemma hom_of_cert (m : ℕ) (hM : T.MixHyp m) {a : LC m}
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (j : ℤ) (hj : j ≠ 0) (e : T.F m) (he : e ≠ 0) :
    e′ + (j : T.F m) * (T.val m a)′ * e ≠ 0 := by
  intro h0
  have heE : (e : L) ≠ 0 := fun h ↦ he (Subtype.ext h)
  have hjE : ((j : L))′ = 0 := by simpa using T.deriv_ratCast_E (j : ℚ)
  have h0E : (e : L)′ + (j : L) * (T.ev m a)′ * (e : L) = 0 := by
    have := congrArg Subtype.val h0
    simp only [IntermediateField.coe_add, IntermediateField.coe_mul, coe_deriv,
      ZeroMemClass.coe_zero] at this
    rw [← this]
    push_cast
    rfl
  have hmem : -(j : L) * T.ev m a ∈ T.F m :=
    mul_mem (by simpa using neg_mem ((T.F m).intCast_mem j)) (T.ev_mem m a)
  have hd : (-(j : L) * T.ev m a)′ =
      ∑ i ∈ ({()} : Finset Unit), algebraMap Cc L ((fun _ ↦ (1 : Cc)) i) *
        logDeriv ((fun _ ↦ (e : L)) i) := by
    simp only [Finset.sum_singleton, map_one, one_mul]
    unfold logDeriv
    rw [Derivation.leibniz, map_neg, hjE]
    simp only [smul_eq_mul, neg_zero, mul_zero, add_zero]
    field_simp
    linear_combination -h0E
  obtain ⟨q, κ, hq⟩ := T.mix_structure m hM _ hmem {()} (fun _ ↦ 1) (fun _ ↦ (e : L))
    (fun _ _ ↦ ⟨e.2, heE⟩) hd
  have hrel := T.deriv_structure m _ q κ hq
  rw [Derivation.leibniz, map_neg, hjE] at hrel
  simp only [smul_eq_mul, neg_zero, mul_zero, add_zero] at hrel
  have := T.no_rel_gensD m hM.tr hc2 (-(j : Cc)) q (by
    rw [← hrel]; simp)
  exact hj (by exact_mod_cast neg_eq_zero.mp this)

/-- **The level check proves the next level's hypotheses.** -/
theorem mixHyp_succ (lv : (m : ℕ) → LC m) (m : ℕ) (hM : T.MixHyp m) (hmn : m < T.n)
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m hM.tr) (paramLimC Fc ks lv m))
    (hc : certLevel Fc ks lv m = true) : T.MixHyp (m + 1) := by
  classical
  have h := hM.tr
  -- the properties at level `m`
  have hnd : ∀ η, ks m = .prim η → ∀ y : T.F m, y′ ≠ T.val m η := by
    intro η hk y hy
    have hl0 := certLevel_lim hk hc
    obtain ⟨β, hβ, -⟩ := hlim.complete [η] [1] (fun k hk ↦ by
      rcases k with _ | k
      · simp at hk
      · rfl) y (by
        rw [hy]
        simp [sC, T.sem_MP_F])
    have h0 := hβ 0
    rw [Finset.sum_eq_zero fun k hk ↦ ?_] at h0
    · simp at h0
    · rw [hl0 _ (getD_memC _ _ (Finset.mem_range.mp hk)), map_zero, mul_zero]
  have hhom : ∀ a, ks m = .exp a → ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 →
      e′ + (j : T.F m) * (T.val m a)′ * e ≠ 0 := fun a hk ↦
    T.hom_of_cert m hM (certLevel_exp hk hc)
  have htr : Transcendental (T.F m) (T.ts m) := by
    rcases hk : ks m with η | a
    · exact transcendental_primitive (T.val m η) (by rw [T.ht m hmn, hk]; rfl) (hnd η hk)
    · refine transcendental_exponential (T.val m a)′ (T.hts0 m hmn a hk) (by rw [T.ht m hmn, hk]; rfl) ?_
      intro n hn b hb
      by_contra hb0
      refine hhom a hk (-(n : ℤ)) (by omega) b hb0 ?_
      rw [hb]
      push_cast
      ring
  refine ⟨fun i hi ↦ ?_, fun i hi η hk ↦ ?_, fun i hi η hk ↦ ?_, fun i hi a hk ↦ ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h i hi
    · exact htr
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hM.log i hi η hk
    · obtain ⟨hv, hη⟩ := T.certLevel_prim hk h hc
      refine ⟨(T.MP i h).sem (lv i), hv, ?_⟩
      rw [← T.sem_MP_F i h, hη]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hM.nd i hi η hk
    · exact hnd η hk
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hM.hom i hi a hk
    · exact hhom a hk


end MTower

end Curves.MT
