import RischTragerBronstein.Computable.MixNTower
import RischTragerBronstein.Liouville.PrimitivePolyPart
import RischTragerBronstein.Liouville.Transcendence
import RischTragerBronstein.RDE.LogDerivRigid

/-!
# Mixed towers: transcendence and uniqueness of Risch equations

`ND m`: each primitive `ηᵢ` (`i < m`) is not a derivative in `F i`, and each exponent `bᵢ` is a
derivative in `F 0` and not a `ℚ`-combination of the exponents below it.

`tr_noHom_of_ND`: then every `tᵢ` (`i < m`) is transcendental over `F i`, and for every
derivative `f ∈ ℚ(x)` outside the `ℚ`-span of the exponents below `m`, `y′ + f y = 0` has only the
solution `y = 0` in `F m` (at the base: `f = g′` would be a logarithmic derivative,
`deriv_eq_zero_of_add_proper_eq_logDeriv`). Proof: `y′ / y = e′ / e + n bₘ + (proper fraction)` in `F m (tₘ)`
(`logDeriv_sub_isProperFrac`, `logDeriv_sub_isProperFrac_exp`), which pushes a solution down one
level with `f + n bₘ`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.MixN

open Tower.PrimN

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : List Kind}

namespace MixTower

variable (T : MixTower Kc E ks)

/-- The `ℚ`-combination `∑ cᵢ bᵢ` in `F 0`. -/
noncomputable def lcombF (cs : List ℚ) (bs : List (Code 1)) : T.F 0 :=
  (List.zipWith (fun (c : ℚ) (b : Code 1) ↦ (c : T.F 0) * T.ratF 0 b) cs bs).sum

/-- `f` is not a `ℚ`-combination of `bs` (in `F 0`). -/
def NotSpan (bs : List (Code 1)) (f : Code 1) : Prop :=
  ∀ cs : List ℚ, cs.length = bs.length → T.lcombF cs bs ≠ T.ratF 0 f

lemma lcombF_cons (c : ℚ) (cs : List ℚ) (b : Code 1) (bs : List (Code 1)) :
    T.lcombF (c :: cs) (b :: bs) = (c : T.F 0) * T.ratF 0 b + T.lcombF cs bs := by
  simp [lcombF]

lemma lcombF_nil_left (bs : List (Code 1)) : T.lcombF [] bs = 0 := by simp [lcombF]

lemma lcombF_nil_right (cs : List ℚ) : T.lcombF cs [] = 0 := by cases cs <;> simp [lcombF]

lemma lcombF_append (cs : List ℚ) (bs : List (Code 1)) (c : ℚ) (b : Code 1)
    (h : cs.length = bs.length) :
    T.lcombF (cs ++ [c]) (bs ++ [b]) = T.lcombF cs bs + (c : T.F 0) * T.ratF 0 b := by
  rw [lcombF, lcombF, List.zipWith_append h]
  simp

lemma lcombF_map_div (z : ℚ) : ∀ (cs : List ℚ) (bs : List (Code 1)),
    T.lcombF (cs.map (· / z)) bs = (z⁻¹ : T.F 0) * T.lcombF cs bs
  | [], _ => by simp [lcombF]
  | _ :: _, [] => by simp [lcombF]
  | c :: cs, b :: bs => by
    have ih := lcombF_map_div z cs bs
    simp only [lcombF, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

lemma lcombF_zeros : ∀ bs : List (Code 1), T.lcombF (bs.map fun _ ↦ (0 : ℚ)) bs = 0
  | [] => rfl
  | b :: bs => by
    have := lcombF_zeros bs
    simp only [lcombF, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at this ⊢
    rw [this]; simp

lemma evx_const (z : ℚ) :
    evx Kc T.x ((([z] : CPoly ℚ), ([1] : CPoly ℚ)) : GFrac ℚ) = algebraMap Kc E (z : Kc) := by
  simp [evx, CPoly.toPoly]

lemma deriv_ratCast0 (z : ℚ) : (z : T.F 0)′ = 0 :=
  Subtype.ext (by
    rw [coe_deriv, SubfieldClass.coe_ratCast, ← map_ratCast (algebraMap Kc E) z,
      deriv_algebraMap, T.hC, map_zero]
    rfl)

/-- The value of `smulQ`. -/
lemma ratF_smulQ (m : ℕ) (z : ℚ) (b : Code 1) :
    T.ratF m (smulQ z b) = (z : T.F m) * T.ratF m b := by
  apply Subtype.ext
  set c : Code 1 := ((([z] : CPoly ℚ), ([1] : CPoly ℚ)) : GFrac ℚ) with hc_def
  have h1 := congrArg Subtype.val (T.model0.sem_mul c b)
  have hc : ((T.model0.sem c : T.F 0) : E) = algebraMap Kc E (z : Kc) :=
    (T.sem_model0 c).trans (T.evx_const z)
  rw [IntermediateField.coe_mul, hc, T.sem_model0, T.sem_model0] at h1
  refine h1.trans ?_
  simp [ratF]

/-- The value of `shiftF`. -/
lemma ratF_shift (m : ℕ) (f b : Code 1) (z : ℤ) :
    T.ratF m (shiftF f b z) = T.ratF m f + (z : T.F m) * T.ratF m b := by
  apply Subtype.ext
  have h1 := congrArg Subtype.val (T.model0.sem_add f (smulQ (z : ℚ) b))
  rw [IntermediateField.coe_add, T.sem_model0, T.sem_model0, T.sem_model0] at h1
  refine h1.trans ?_
  have h2 := congrArg Subtype.val (T.ratF_smulQ m (z : ℚ) b)
  simp only [ratF, IntermediateField.coe_mul] at h2
  simp only [ratF, IntermediateField.coe_add, IntermediateField.coe_mul]
  rw [h2]
  simp

lemma NotSpan.shift {T : MixTower Kc E ks} {bs : List (Code 1)} {b f : Code 1}
    (h : T.NotSpan (bs ++ [b]) f) (z : ℤ) : T.NotSpan bs (shiftF f b z) := fun cs hl heq ↦ by
  refine h (cs ++ [-(z : ℚ)]) (by simp [hl]) ?_
  rw [T.lcombF_append _ _ _ _ hl, heq, T.ratF_shift]
  push_cast
  ring

lemma NotSpan.smul {T : MixTower Kc E ks} {bs : List (Code 1)} {b : Code 1} (h : T.NotSpan bs b)
    {z : ℚ} (hz : z ≠ 0) : T.NotSpan bs (smulQ z b) := fun cs hl heq ↦ by
  refine h (cs.map (· / z)) (by simp [hl]) ?_
  have hz' : (z : T.F 0) ≠ 0 := by exact_mod_cast hz
  rw [T.lcombF_map_div, heq, T.ratF_smulQ]
  field_simp

lemma NotSpan.ne_zero {T : MixTower Kc E ks} {bs : List (Code 1)} {f : Code 1}
    (h : T.NotSpan bs f) : T.ratF 0 f ≠ 0 := fun h0 ↦
  h (bs.map fun _ ↦ 0) (by simp) (by rw [h0, T.lcombF_zeros])

lemma lcombF_add : ∀ (cs ds : List ℚ) (bs : List (Code 1)), cs.length = ds.length →
    T.lcombF (List.zipWith (· + ·) cs ds) bs = T.lcombF cs bs + T.lcombF ds bs
  | [], [], bs, _ => by simp [lcombF_nil_left]
  | c :: cs, d :: ds, [], _ => by simp [lcombF_nil_right]
  | c :: cs, d :: ds, b :: bs, h => by
    simp only [List.zipWith_cons_cons, lcombF_cons, lcombF_add cs ds bs (by simpa using h)]
    push_cast
    ring

lemma lcombF_mapMul (z : ℚ) : ∀ (cs : List ℚ) (bs : List (Code 1)),
    T.lcombF (cs.map (z * ·)) bs = (z : T.F 0) * T.lcombF cs bs
  | [], bs => by simp [lcombF_nil_left]
  | c :: cs, [] => by simp [lcombF_nil_right]
  | c :: cs, b :: bs => by
    simp only [List.map_cons, lcombF_cons, lcombF_mapMul z cs bs]
    push_cast
    ring

lemma lcombF_single : ∀ {b : Code 1} {bs : List (Code 1)}, b ∈ bs →
    ∃ cs : List ℚ, cs.length = bs.length ∧ T.lcombF cs bs = T.ratF 0 b
  | _, [], h => absurd h List.not_mem_nil
  | b, b' :: bs, h => by
    by_cases hb : b = b'
    · subst hb
      refine ⟨1 :: bs.map fun _ ↦ 0, by simp, ?_⟩
      rw [lcombF_cons, T.lcombF_zeros]
      simp
    · obtain ⟨cs, hl, hcs⟩ := lcombF_single ((List.mem_cons.mp h).resolve_left hb)
      refine ⟨0 :: cs, by simp [hl], ?_⟩
      rw [lcombF_cons, hcs]
      simp

lemma mem_allExps : ∀ {ks : List Kind} {m : ℕ} {b : Code 1}, kind ks m = .exp b → b ∈ allExps ks
  | [], m, b, h => by simp [kind] at h
  | k :: ks, 0, b, h => by
    simp only [kind, List.getD_cons_zero] at h
    subst h
    simp [allExps]
  | k :: ks, m + 1, b, h => by
    have h' : kind ks m = .exp b := by simpa [kind] using h
    have := mem_allExps h'
    cases k <;> simp [allExps, this]

/-- `f` is a `ℚ`-combination of the exponents of the tower (in `F 0`). -/
def Adm (f : Code 1) : Prop :=
  ∃ cs : List ℚ, cs.length = (allExps ks).length ∧ T.lcombF cs (allExps ks) = T.ratF 0 f

lemma Adm.shift {T : MixTower Kc E ks} {f b : Code 1} (hf : T.Adm f) (hb : T.Adm b)
    (z : ℤ) : T.Adm (shiftF f b z) := by
  obtain ⟨cf, hlf, hf⟩ := hf
  obtain ⟨cb, hlb, hb⟩ := hb
  refine ⟨List.zipWith (· + ·) cf (cb.map ((z : ℚ) * ·)), by simp [hlf, hlb], ?_⟩
  rw [T.lcombF_add _ _ _ (by simp [hlf, hlb]), T.lcombF_mapMul, hf, hb, T.ratF_shift]
  push_cast
  ring

lemma Adm.smul {T : MixTower Kc E ks} {b : Code 1} (hb : T.Adm b) (z : ℚ) :
    T.Adm (smulQ z b) := by
  obtain ⟨cb, hlb, hb⟩ := hb
  refine ⟨cb.map (z * ·), by simp [hlb], ?_⟩
  rw [T.lcombF_mapMul, hb, T.ratF_smulQ]

lemma adm_of_kind {m : ℕ} {b : Code 1} (hk : kind ks m = .exp b) : T.Adm b :=
  T.lcombF_single (mem_allExps hk)

/-- No non-zero `ℚ`-combination of the exponents is a logarithmic derivative in `F 0`. -/
def LogIndep : Prop :=
  ∀ cs : List ℚ, cs.length = (allExps ks).length → T.lcombF cs (allExps ks) ≠ 0 →
    ∀ y : T.F 0, y ≠ 0 → y′ + T.lcombF cs (allExps ks) * y ≠ 0

/-- `f` is a derivative in `F 0`. -/
def IsDerF (f : Code 1) : Prop := ∃ g : T.F 0, g′ = T.ratF 0 f

lemma isDerF_lcombF : ∀ (cs : List ℚ) (bs : List (Code 1)), (∀ b ∈ bs, T.IsDerF b) →
    ∃ g : T.F 0, g′ = T.lcombF cs bs
  | [], bs, _ => ⟨0, by simp [lcombF_nil_left]⟩
  | c :: cs, [], _ => ⟨0, by simp [lcombF_nil_right]⟩
  | c :: cs, b :: bs, h => by
    obtain ⟨g, hg⟩ := isDerF_lcombF cs bs fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')
    obtain ⟨a, ha⟩ := h b List.mem_cons_self
    refine ⟨(c : T.F 0) * a + g, ?_⟩
    rw [lcombF_cons, map_add, Derivation.leibniz, ha, hg, T.deriv_ratCast0]
    simp

/-- **Exponents that are derivatives are independent modulo logarithmic derivatives**: a
non-zero derivative `g′` is not a logarithmic derivative in `Kc(x)`. -/
theorem logIndep_of_isDerF (h : ∀ b ∈ allExps ks, T.IsDerF b) : T.LogIndep := by
  intro cs _ hne y hy0 hy
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  obtain ⟨g, hg⟩ := T.isDerF_lcombF cs _ h
  have h0 := deriv_eq_zero_of_add_proper_eq_logDeriv (K := T.F 0) hD 0 1 squarefree_one
    (by simp) (-g) y hy0 (by
      rw [map_zero, zero_div, add_zero, logDeriv, map_neg, hg]
      field_simp
      linear_combination -hy)
  rw [map_neg, hg, neg_eq_zero] at h0
  exact hne h0

/-- The non-degeneracy hypothesis below level `m`. -/
def ND (m : ℕ) : Prop :=
  T.LogIndep ∧ ∀ i < m, match kind ks i with
    | .prim η => ∀ y : T.F i, y′ ≠ T.ratF i η
    | .exp b => T.NotSpan (expsBelow ks i) b

lemma ND.mono {T : MixTower Kc E ks} {m k : ℕ} (h : T.ND m) (hk : k ≤ m) : T.ND k :=
  ⟨h.1, fun i hi ↦ h.2 i (by omega)⟩

/-- No non-zero solution of `y′ + f y = 0` in `F m`. -/
def NoHom (m : ℕ) : Prop :=
  ∀ f : Code 1, T.Adm f → T.NotSpan (expsBelow ks m) f → ∀ y : T.F m,
    y′ + T.ratF m f * y = 0 → y = 0

lemma expsBelow_prim {m : ℕ} {η : Code 1} (hk : kind ks m = .prim η) :
    expsBelow ks (m + 1) = expsBelow ks m := by
  simp [expsBelow, hk]

lemma expsBelow_exp {m : ℕ} {b : Code 1} (hk : kind ks m = .exp b) :
    expsBelow ks (m + 1) = expsBelow ks m ++ [b] := by
  simp [expsBelow, hk]

/-- The inclusion `F m → F (m + 1)`. -/
noncomputable def up (m : ℕ) : T.F m →+* T.F (m + 1) :=
  (IntermediateField.inclusion (T.le_succ m)).toRingHom

@[simp] lemma coe_up (m : ℕ) (z : T.F m) : ((T.up m z : T.F (m + 1)) : E) = (z : E) := rfl

lemma ratF_succ (m : ℕ) (q : GFrac ℚ) : T.ratF (m + 1) q = T.up m (T.ratF m q) := rfl

/-- The fraction field `F m (tₘ)`, with the image of `z ∈ F (m + 1)`. -/
lemma logDeriv_push (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (y : T.F (m + 1))
    (hy0 : y ≠ 0) (f : T.F m) (hy : y′ + T.up m f * y = 0) :
    ∃ e : T.F m, e ≠ 0 ∧
      match kind ks m with
      | .prim _ => e′ + f * e = 0
      | .exp b => ∃ n : ℤ, e′ + (f + (n : T.F m) * T.ratF m b) * e = 0 := by
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) (T.ts m)
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮T.ts m⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple (T.ts m) _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮T.ts m⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮T.ts m⟯ :=
    differentialAlgebra_adjoin_simple _ _ hw
  have hinj : Function.Injective (algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯) :=
    IsFractionRing.injective _ _
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ P : (T.F m)⟮T.ts m⟯) : E) =
      aeval (T.ts m) P := algebraMap_adjoinSimple _
  set yK : (T.F m)⟮T.ts m⟯ := ⟨y, (T.mem_F_succ).mp y.2⟩ with hyK
  have hyK0 : yK ≠ 0 := fun h0 ↦ hy0 (Subtype.ext (show (y : E) = 0 from congrArg Subtype.val h0))
  have hlog : logDeriv yK = algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ (C (-f)) := by
    apply Subtype.ext
    unfold logDeriv
    rw [IntermediateField.coe_div, hcoe, aeval_C]
    change (y : E)′ / (y : E) = _
    have h1 := congrArg Subtype.val hy
    simp only [IntermediateField.coe_add, coe_deriv, IntermediateField.coe_mul,
      ZeroMemClass.coe_zero] at h1
    have hyE : (y : E) ≠ 0 := fun h0 ↦ hy0 (Subtype.ext h0)
    rw [show (y : E)′ = -(((T.up m f : T.F (m + 1)) : E) * y) by
      linear_combination h1]
    field_simp
    rfl
  have key : ∀ g : T.F m, IsProperFrac (T.F m) (logDeriv yK -
      algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ (C g)) → -f - g = 0 := fun g hg ↦ by
    rw [hlog, ← map_sub, ← C_sub] at hg
    have := eq_zero_of_isProperFrac_poly hg hinj
    exact C_eq_zero.mp this
  unfold wPoly at hw
  cases hk : kind ks m with
  | prim η =>
    have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ratF m η)) P := fun P ↦ by
      change implicitDeriv (T.wPoly m) P = _
      simp only [wPoly, hk]
    obtain ⟨e, he0, hp⟩ := logDeriv_sub_isProperFrac hD yK hyK0
    refine ⟨e, he0, ?_⟩
    have h2 := key _ hp
    unfold logDeriv at h2
    field_simp at h2
    linear_combination -h2
  | exp b =>
    have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ratF m b) * X) P := fun P ↦ by
      change implicitDeriv (T.wPoly m) P = _
      simp only [wPoly, hk]
    obtain ⟨e, n, he0, hp⟩ := logDeriv_sub_isProperFrac_exp hD yK hyK0
    refine ⟨e, he0, n, ?_⟩
    have h2 := key _ hp
    unfold logDeriv at h2
    field_simp at h2
    linear_combination -h2

/-- **Transcendence and uniqueness**, by induction on the level. -/
theorem tr_noHom_of_ND : ∀ m : ℕ, T.ND m → T.Tr m ∧ T.NoHom m
  | 0, hnd => by
    refine ⟨fun i hi ↦ absurd hi (Nat.not_lt_zero i), fun f hder hf y hy ↦ ?_⟩
    by_contra hy0
    obtain ⟨cs, hl, hcs⟩ := hder
    exact hnd.1 cs hl (by rw [hcs]; exact hf.ne_zero) y hy0 (by rw [hcs]; exact hy)
  | m + 1, hnd => by
    obtain ⟨htr, hnh⟩ := tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))
    have hm := hnd.2 m (Nat.lt_succ_self m)
    -- transcendence of `tₘ`
    have htrm : Transcendental (T.F m) (T.ts m) := by
      have ht := T.deriv_ts_aeval m
      unfold wPoly at ht
      revert hm ht
      cases hk : kind ks m with
      | prim η =>
        intro hm ht
        refine transcendental_primitive (T.ratF m η) (by rw [ht, aeval_C]; try rfl) hm
      | exp b =>
        intro hm ht
        refine transcendental_exponential (T.ratF m b) (T.hts0 m b hk)
          (by rw [ht, map_mul, aeval_C, aeval_X]; try rfl) fun n hn c hc ↦ ?_
        have hn' : -(n : ℚ) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
        refine hnh (smulQ (-(n : ℚ)) b) ((T.adm_of_kind hk).smul _) (hm.smul hn') c ?_
        rw [T.ratF_smulQ, hc]
        push_cast
        ring
    have htr' : T.Tr (m + 1) := fun i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact htr i hi
      · exact htrm
    refine ⟨htr', fun f hder hf y hy ↦ ?_⟩
    by_contra hy0
    have hfF : T.ratF (m + 1) f = T.up m (T.ratF m f) := rfl
    rw [hfF] at hy
    obtain ⟨e, he0, he⟩ := T.logDeriv_push m htrm y hy0 _ hy
    revert he hm
    cases hk : kind ks m with
    | prim η =>
      intro _ he
      rw [expsBelow_prim hk] at hf
      exact he0 (hnh f hder hf e he)
    | exp b =>
      intro hm he
      rw [expsBelow_exp hk] at hf
      obtain ⟨n, hn⟩ := he
      refine he0 (hnh _ (hder.shift (T.adm_of_kind hk) n) (hf.shift n) e ?_)
      rw [T.ratF_shift]
      exact_mod_cast hn

end MixTower

end Tower.MixN
