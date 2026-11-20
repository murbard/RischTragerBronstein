import RischTragerBronstein.Computable.NestXBase

/-!
# Mixed towers: soundness of the certificate and of the logarithmic-derivative bound

* `certLevel`: the check of `certX` at one level; `certX_succ`.
* `gensD_spec`: the codes `gensD ks m` are the derivatives of the generators `genX i` (`i < m`).
* `pldX_spec`: if `(V + μ aₘ)′` is a constant combination of logarithmic derivatives in `F m`
  (`μ` a constant), then `pldX` returns `μ`, which is rational (structure theorem
  `mix_structure`).
* `mixHyp_succ`: the level check (with a sound and complete limited integration one level down)
  proves the hypotheses `MixHyp` of the next level: transcendence, `ηₘ = vₘ′ / vₘ`, `ηₘ` not a
  derivative, and no `e′ + j aₘ′ e = 0`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX

/-- The check of `certX` at level `m`. -/
def certLevel (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) (m : ℕ) : Bool :=
  let O := opsM ks m
  match ks m with
  | .prim η => !O.isZero (lv m) &&
      O.isZero (O.add η (O.neg (O.mul (O.deriv (lv m)) (O.inv (lv m))))) &&
      (paramLimX ks lv m [η]).all fun r ↦ r.1.getD 0 0 == 0
  | .exp a => (consys ks m (O.deriv a :: gensD ks m)).all fun u ↦ u.getD 0 0 == 0

lemma certX_eq (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) (n : ℕ) :
    certX ks lv n = (List.range n).all (certLevel ks lv) := rfl

lemma certX_succ (ks : (m : ℕ) → KindN m) (lv : (m : ℕ) → Code (m + 1)) (n : ℕ) :
    certX ks lv (n + 1) = (certX ks lv n && certLevel ks lv n) := by
  rw [certX_eq, certX_eq, List.range_succ, List.all_append]
  simp

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

lemma certLevel_exp {lv : (m : ℕ) → Code (m + 1)} {m : ℕ} {a : Code (m + 1)}
    (hk : ks m = .exp a) (hc : certLevel ks lv m = true) :
    ∀ u ∈ consys ks m ((opsM ks m).deriv a :: gensD ks m), u.getD 0 0 = 0 := by
  simp only [certLevel, hk] at hc
  intro u hu
  simpa using List.all_eq_true.mp hc u hu

lemma certLevel_prim {lv : (m : ℕ) → Code (m + 1)} {m : ℕ} {η : Code (m + 1)}
    (hk : ks m = .prim η) (h : T.Tr m) (hc : certLevel ks lv m = true) :
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

lemma certLevel_lim {lv : (m : ℕ) → Code (m + 1)} {m : ℕ} {η : Code (m + 1)}
    (hk : ks m = .prim η) (hc : certLevel ks lv m = true) :
    ∀ r ∈ paramLimX ks lv m [η], r.1.getD 0 0 = 0 := by
  simp only [certLevel, hk, Bool.and_eq_true] at hc
  intro r hr
  simpa using List.all_eq_true.mp hc.2 r hr

/-! ### The derivatives of the generators as codes -/

lemma evN_liftX (m : ℕ) (h : T.Tr m) (q : Code (m + 1)) :
    evN Kc T.x T.ts (m + 1) (liftE ks m q) = evN Kc T.x T.ts m q := by
  change evP Kc T.x T.ts m [q] / evP Kc T.x T.ts m [(opsM ks m).one] = _
  simp only [evP, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  rw [← T.sem_MP m h (opsM ks m).one, (T.MP m h).sem_one]
  simp

lemma gensD_last (m : ℕ) (h : T.Tr m) :
    evN Kc T.x T.ts m (match ks m with
      | .exp a => (opsM ks m).deriv a
      | .prim η => η) = (T.genX m)′ := by
  unfold genX
  rcases hk : ks m with η | a
  · rw [T.ht m, hk]; rfl
  · rw [← T.sem_MP m h, (T.MP m h).sem_deriv, coe_deriv, T.sem_MP]

lemma gensD_spec : ∀ (m : ℕ) (h : T.Tr m), (gensD ks m).length = m ∧ ∀ i < m,
    (((T.MP m h).sem ((gensD ks m).getD i (opsM ks m).zero) : T.F m) : E) = (T.genX i)′
  | 0, _ => ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | m + 1, h => by
    have hm : T.Tr m := fun i hi ↦ h i (by omega)
    obtain ⟨hl, hv⟩ := gensD_spec m hm
    have he : gensD ks (m + 1) = ((gensD ks m) ++ [match ks m with
      | .exp a => (opsM ks m).deriv a
      | .prim η => η]).map (liftE ks m) := rfl
    refine ⟨by rw [he, List.length_map, List.length_append, hl]; rfl, fun i hi ↦ ?_⟩
    rw [T.sem_MP, he, NestTower.getD_map' _ _ (opsM ks m).zero _ (by simp [hl]; omega),
      T.evN_liftX m hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi), ← T.sem_MP m hm]; exact hv i hi
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self]
      exact T.gensD_last i hm

/-- Under the exponential check, `aₘ′` is not a constant combination of the `genX i′`. -/
lemma no_rel_gensD (m : ℕ) (h : T.Tr m) {a : Code (m + 1)}
    (hc2 : ∀ u ∈ consys ks m ((opsM ks m).deriv a :: gensD ks m), u.getD 0 0 = 0) (c0 : Kc)
    (q : ℕ → Kc)
    (hrel : algebraMap Kc E c0 * (evN Kc T.x T.ts m a)′ =
      ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * (T.genX i)′) : c0 = 0 := by
  set vs : List (Code (m + 1)) := (opsM ks m).deriv a :: gensD ks m with hvs
  obtain ⟨hl, hv⟩ := T.gensD_spec m h
  have hlen : vs.length = m + 1 := by simp [hvs, hl]
  set f : ℕ → Kc := fun j ↦ if j = 0 then c0 else -q (j - 1) with hf
  have h0 := T.coeff0_eq_zero_of_cert m h vs hc2 ((List.range vs.length).map f) (by simp)
    (Subtype.ext (by
      rw [T.rel_val m h vs f, ZeroMemClass.coe_zero, hlen, Finset.sum_range_succ']
      have e : ∀ j ∈ Finset.range m, algebraMap Kc E (f (j + 1)) *
          (((T.MP m h).sem (vs.getD (j + 1) (opsM ks m).zero) : T.F m) : E) =
          -(algebraMap Kc E (q j) * (T.genX j)′) := fun j hj ↦ by
        rw [hvs, List.getD_cons_succ, hv j (Finset.mem_range.mp hj)]
        simp [hf]
      rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
      have e0 : (((T.MP m h).sem (vs.getD 0 (opsM ks m).zero) : T.F m) : E) =
          (evN Kc T.x T.ts m a)′ := by
        rw [hvs, List.getD_cons_zero, (T.MP m h).sem_deriv, coe_deriv, T.sem_MP]
      rw [e0]
      simp only [hf, if_pos rfl]
      rw [hrel]
      ring))
  rw [NestTower.getD_range_map _ _ (by rw [hlen]; omega)] at h0
  simpa [hf] using h0

/-- Differentiating the conclusion of the structure theorem. -/
lemma deriv_structure (m : ℕ) (Z : E) (q : ℕ → Kc) (κ : Kc)
    (hZ : Z = ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * T.genX i + algebraMap Kc E κ) :
    Z′ = ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * (T.genX i)′ := by
  have hK : ∀ c : Kc, (algebraMap Kc E c)′ = 0 := fun c ↦ by
    rw [deriv_algebraMap, T.hC, map_zero]
  rw [hZ, map_add, hK, add_zero, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, hK, smul_zero, add_zero, smul_eq_mul]

/-! ### The logarithmic-derivative bound -/

set_option maxHeartbeats 1600000 in
/-- **The logarithmic-derivative bound is correct**: if `(V + μ aₘ)′` is a constant combination
of logarithmic derivatives in `F m`, then `pldX` returns `μ` (which is rational). -/
theorem pldX_spec (m : ℕ) (hM : T.MixHyp m) {a : Code (m + 1)}
    (hc2 : ∀ u ∈ consys ks m ((opsM ks m).deriv a :: gensD ks m), u.getD 0 0 = 0)
    (V : Code (m + 1)) (μ : Kc) {ι : Type} (s : Finset ι) (c : ι → Kc) (u : ι → E)
    (hu : ∀ i ∈ s, u i ∈ T.F m ∧ u i ≠ 0)
    (hd : (evN Kc T.x T.ts m V + algebraMap Kc E μ * evN Kc T.x T.ts m a)′ =
      ∑ i ∈ s, algebraMap Kc E (c i) * logDeriv (u i)) :
    ∃ q : ℚ, pldX ks m V a = some q ∧ μ = (q : Kc) := by
  classical
  have h := hM.tr
  set O := opsM ks m with hO
  have hmem : evN Kc T.x T.ts m V + algebraMap Kc E μ * evN Kc T.x T.ts m a ∈ T.F m :=
    add_mem (T.evN_mem m V) (mul_mem ((T.F m).algebraMap_mem μ) (T.evN_mem m a))
  obtain ⟨q, κ, hq⟩ := T.mix_structure m hM _ hmem s c u hu hd
  have hK : ∀ c : Kc, (algebraMap Kc E c)′ = 0 := fun c ↦ by
    rw [deriv_algebraMap, T.hC, map_zero]
  have hrel : (evN Kc T.x T.ts m V)′ + algebraMap Kc E μ * (evN Kc T.x T.ts m a)′ =
      ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * (T.genX i)′ := by
    rw [← T.deriv_structure m _ q κ hq, map_add, Derivation.leibniz, hK, smul_zero, add_zero,
      smul_eq_mul]
  set vs : List (Code (m + 1)) := O.deriv V :: O.deriv a :: gensD ks m with hvs
  obtain ⟨hlD, hvD⟩ := T.gensD_spec m h
  have hlen : vs.length = m + 2 := by simp [hvs, hlD]
  have hsum : ∀ g : ℕ → Kc, ∑ j ∈ Finset.range vs.length, algebraMap Kc E (g j) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) =
      algebraMap Kc E (g 0) * (evN Kc T.x T.ts m V)′ +
        algebraMap Kc E (g 1) * (evN Kc T.x T.ts m a)′ +
        ∑ j ∈ Finset.range m, algebraMap Kc E (g (j + 2)) * (T.genX j)′ := by
    intro g
    rw [hlen, Finset.sum_range_succ', Finset.sum_range_succ', zero_add]
    have e : ∀ j ∈ Finset.range m, algebraMap Kc E (g (j + 1 + 1)) *
        (((T.MP m h).sem (vs.getD (j + 1 + 1) O.zero) : T.F m) : E) =
        algebraMap Kc E (g (j + 2)) * (T.genX j)′ := fun j hj ↦ by
      rw [hvs, List.getD_cons_succ, List.getD_cons_succ, hvD j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl e]
    have e0 : (((T.MP m h).sem (vs.getD 0 O.zero) : T.F m) : E) = (evN Kc T.x T.ts m V)′ := by
      rw [hvs, List.getD_cons_zero, (T.MP m h).sem_deriv, coe_deriv, T.sem_MP]
    have e1 : (((T.MP m h).sem (vs.getD 1 O.zero) : T.F m) : E) = (evN Kc T.x T.ts m a)′ := by
      rw [hvs, List.getD_cons_succ, List.getD_cons_zero, (T.MP m h).sem_deriv, coe_deriv,
        T.sem_MP]
    rw [e0, e1]
    ring
  -- the relation `(1, μ, -q)`
  set fc : ℕ → Kc := fun j ↦ if j = 0 then 1 else if j = 1 then μ else -q (j - 2) with hfc
  have h0c : (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fc) vs).sum = 0 := Subtype.ext (by
    rw [T.rel_val m h vs fc, hsum, ZeroMemClass.coe_zero]
    have e : ∀ j ∈ Finset.range m, algebraMap Kc E (fc (j + 2)) * (T.genX j)′ =
        -(algebraMap Kc E (q j) * (T.genX j)′) := fun j _ ↦ by
      simp [hfc]
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
    simp only [hfc, if_pos rfl, if_neg one_ne_zero, ↓reduceIte, map_one, one_mul]
    linear_combination hrel)
  obtain ⟨u0, hu0U, hu00⟩ := T.exists_coeff0_ne m h vs _ (by simp) h0c (by
    rw [NestTower.getD_range_map _ _ (by rw [hlen]; omega)]; simp [hfc])
  obtain ⟨u1, hfind⟩ : ∃ u1, (consys ks m vs).find? (fun u ↦ u.getD 0 0 ≠ 0) = some u1 := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨u0, hu0U, by simpa using hu00⟩
  have hu1U : u1 ∈ consys ks m vs := List.mem_of_find?_eq_some hfind
  have hu10 : u1.getD 0 0 ≠ 0 := by simpa using List.find?_some hfind
  have hpld : pldX ks m V a = some (u1.getD 1 0 / u1.getD 0 0) := by
    simp only [pldX]
    rw [show (O.deriv V :: O.deriv a :: gensD ks m) = vs from rfl, hfind]
  refine ⟨_, hpld, ?_⟩
  -- the relation of `u₁`
  have hs1 := T.consys_sound m h vs u1 hu1U
  have hs1E : ∑ j ∈ Finset.range vs.length, algebraMap Kc E (algebraMap ℚ Kc (u1.getD j 0)) *
      (((T.MP m h).sem (vs.getD j O.zero) : T.F m) : E) = 0 := by
    rw [← T.rel_val m h vs, hs1, ZeroMemClass.coe_zero]
  rw [hsum] at hs1E
  -- eliminate `V′`
  set r0 : Kc := algebraMap ℚ Kc (u1.getD 0 0) with hr0
  set r1 : Kc := algebraMap ℚ Kc (u1.getD 1 0) with hr1
  have hkey := T.no_rel_gensD m h hc2 (r0 * μ - r1)
    (fun j ↦ r0 * q j + algebraMap ℚ Kc (u1.getD (j + 2) 0)) (by
      simp only [map_add, map_mul, map_sub, add_mul, Finset.sum_add_distrib]
      have e1 : ∑ i ∈ Finset.range m, algebraMap Kc E r0 * algebraMap Kc E (q i) *
          (T.genX i)′ = algebraMap Kc E r0 *
            ∑ i ∈ Finset.range m, algebraMap Kc E (q i) * (T.genX i)′ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [e1, ← hrel]
      linear_combination -hs1E)
  have hr0' : r0 ≠ 0 := by
    rw [hr0]; exact (map_ne_zero_iff _ (algebraMap ℚ Kc).injective).mpr hu10
  rw [Rat.cast_div, ← eq_ratCast (algebraMap ℚ Kc), ← eq_ratCast (algebraMap ℚ Kc), ← hr0, ← hr1]
  field_simp
  linear_combination hkey

/-! ### The hypotheses of the next level -/

theorem mixHyp_zero : T.MixHyp 0 :=
  ⟨fun i hi ↦ absurd hi (Nat.not_lt_zero i), fun i hi ↦ absurd hi (Nat.not_lt_zero i),
    fun i hi ↦ absurd hi (Nat.not_lt_zero i), fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩

/-- At a certified exponential level there is no `e′ + j aₘ′ e = 0`. -/
lemma hom_of_cert (m : ℕ) (hM : T.MixHyp m) {a : Code (m + 1)}
    (hc2 : ∀ u ∈ consys ks m ((opsM ks m).deriv a :: gensD ks m), u.getD 0 0 = 0)
    (j : ℤ) (hj : j ≠ 0) (e : T.F m) (he : e ≠ 0) :
    e′ + (j : T.F m) * (T.valN m a)′ * e ≠ 0 := by
  intro h0
  have heE : (e : E) ≠ 0 := fun h ↦ he (Subtype.ext h)
  have hjE : ((j : E))′ = 0 := by simpa using T.deriv_ratCast_E (j : ℚ)
  have h0E : (e : E)′ + (j : E) * (evN Kc T.x T.ts m a)′ * (e : E) = 0 := by
    have := congrArg Subtype.val h0
    simp only [IntermediateField.coe_add, IntermediateField.coe_mul, coe_deriv,
      ZeroMemClass.coe_zero] at this
    rw [← this]
    push_cast
    rfl
  have hmem : -(j : E) * evN Kc T.x T.ts m a ∈ T.F m :=
    mul_mem (by simpa using neg_mem ((T.F m).intCast_mem j)) (T.evN_mem m a)
  have hd : (-(j : E) * evN Kc T.x T.ts m a)′ =
      ∑ i ∈ ({()} : Finset Unit), algebraMap Kc E ((fun _ ↦ (1 : Kc)) i) *
        logDeriv ((fun _ ↦ (e : E)) i) := by
    simp only [Finset.sum_singleton, map_one, one_mul]
    unfold logDeriv
    rw [Derivation.leibniz, map_neg, hjE]
    simp only [smul_eq_mul, neg_zero, mul_zero, add_zero]
    field_simp
    linear_combination -h0E
  obtain ⟨q, κ, hq⟩ := T.mix_structure m hM _ hmem {()} (fun _ ↦ 1) (fun _ ↦ (e : E))
    (fun _ _ ↦ ⟨e.2, heE⟩) hd
  have hrel := T.deriv_structure m _ q κ hq
  rw [Derivation.leibniz, map_neg, hjE] at hrel
  simp only [smul_eq_mul, neg_zero, mul_zero, add_zero] at hrel
  have := T.no_rel_gensD m hM.tr hc2 (-(j : Kc)) q (by
    rw [← hrel]; simp)
  exact hj (by exact_mod_cast neg_eq_zero.mp this)

/-- **The level check proves the next level's hypotheses.** -/
theorem mixHyp_succ (lv : (m : ℕ) → Code (m + 1)) (m : ℕ) (hM : T.MixHyp m)
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MP m hM.tr) (paramLimX ks lv m))
    (hc : certLevel ks lv m = true) : T.MixHyp (m + 1) := by
  classical
  have h := hM.tr
  -- the properties at level `m`
  have hnd : ∀ η, ks m = .prim η → ∀ y : T.F m, y′ ≠ T.valN m η := by
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
    · rw [hl0 _ (getD_mem' _ _ (Finset.mem_range.mp hk)), map_zero, mul_zero]
  have hhom : ∀ a, ks m = .exp a → ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 →
      e′ + (j : T.F m) * (T.valN m a)′ * e ≠ 0 := fun a hk ↦
    T.hom_of_cert m hM (certLevel_exp hk hc)
  have htr : Transcendental (T.F m) (T.ts m) := by
    rcases hk : ks m with η | a
    · exact transcendental_primitive (T.valN m η) (by rw [T.ht m, hk]; rfl) (hnd η hk)
    · refine transcendental_exponential (T.valN m a)′ (T.hts0 m a hk) (by rw [T.ht m, hk]; rfl) ?_
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

end NestMTower

end Tower.NestM
