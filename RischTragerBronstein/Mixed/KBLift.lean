import RischTragerBronstein.Mixed.KBIrr

/-!
# Changing the base curve: the new realization

The new coordinate `w` is algebraic over the old base field `K₀ = ℚ(x, y)` with minimal polynomial
`Q` (codes of level `0`; `Fact`: irreducible over the code field). In `K₀[W]/(Q)` two identities
are checked (`bcOK`): `Fc'(x, W) = 0` and `Yc(x, W) = y`. For any root `w'` of `Q` over `L`,
`L' = L(w')` carries the realization `T'` of the translated tower over the new base curve `Fc'`
(`base_change`), with the same values.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

section Codes

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (Q : GPoly (LC 0))

/-- `Q` over the code field `K₀`. -/
def qK : CPoly (KF Fc 0) := CPoly.trim (Q.map (trC Fc 0))

variable [Fact (Irreducible (toPoly (qK Fc Q)))]

/-- `K₀[W]/(Q)`. -/
abbrev FW : Type := NFK.NF (qK Fc Q)

/-- A rational function of `x` in `K₀[W]/(Q)`. -/
def fW (c : GFrac ℚ) : FW Fc Q := NFK.mk _ [trC Fc 0 [c]]

/-- A code of the new curve, evaluated at `(x, w)`. -/
def evW (a : GPoly (GFrac ℚ)) (w : FW Fc Q) : FW Fc Q := a.foldr (fun c acc ↦ fW Fc Q c + w * acc) 0

/-- The generator `W`. -/
def genW : FW Fc Q := NFK.mk _ [0, 1]

/-- The equation of a curve as a code. -/
def fcCode (Fc' : BPoly ℚ) : GPoly (GFrac ℚ) := Fc'.map fun p ↦ (p, [1])

/-- The code of `y`. -/
def yCode : GPoly (GFrac ℚ) := [([], [1]), ([1], [1])]

/-- **The checks of the base change**: `Fc'(x, W) = 0`, `Yc(x, W) = y`. -/
def bcOK (Fc' : BPoly ℚ) (Yc : GPoly (GFrac ℚ)) : Bool :=
  evW Fc Q (fcCode Fc') (genW Fc Q) == 0 &&
    evW Fc Q Yc (genW Fc Q) == NFK.mk _ [trC Fc 0 yCode]

end Codes

section Sem

variable {Fc : BPoly ℚ} [Fact (Irreducible (toPoly (fKc Fc)))] {Q : GPoly (LC 0)}
  [Fact (Irreducible (toPoly (qK Fc Q)))]

/-- **Evaluation through a homomorphism.** -/
lemma map_evW {Ω : Type*} [Field Ω] (φ : FW Fc Q →+* Ω) (xv : GFrac ℚ → Ω)
    (hx : ∀ c, φ (fW Fc Q c) = xv c) (a : GPoly (GFrac ℚ)) (w : FW Fc Q) :
    φ (evW Fc Q a w) = (a.map xv).foldr (fun c acc ↦ c + φ w * acc) 0 := by
  induction a with
  | nil => simp [evW]
  | cons c a ih =>
    simp only [evW, List.foldr_cons, List.map_cons] at ih ⊢
    rw [map_add, map_mul, hx, ih]

end Sem

section Helpers

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

/-- The value of a code of the curve, by Horner in `y`. -/
lemma sem_cM_foldr (a : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem a = (a.map (xM hC S hx).sem).foldr (fun c acc ↦ c + S.y * acc) 0 := by
  rw [sem_cM]
  induction a with
  | nil => simp
  | cons c a ih =>
    rw [GPoly.toPoly_cons, List.map_cons, List.foldr_cons, eval_add, eval_mul, eval_C, eval_X, ih]

lemma sem_yCode : (cM hC S hx Fc hSF).sem yCode = S.y := by
  rw [sem_cM_foldr]
  simp [yCode, sem_xModel]

/-- The equation of the curve, by Horner in `y`. -/
lemma eval_toB_foldr (Fc' : BPoly ℚ) (w : E) :
    (((toB Fc').map (mapRingHom (algebraMap ℚ Kc))).map (aeval S.x).toRingHom).eval w =
      ((fcCode Fc').map (xM hC S hx).sem).foldr (fun c acc ↦ c + w * acc) 0 := by
  induction Fc' with
  | nil => simp [fcCode]
  | cons p W ih =>
    simp only [fcCode, List.map_cons, List.foldr_cons] at ih ⊢
    rw [toB_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_add, eval_mul,
      eval_C, eval_X, ih, sem_xModel]
    simp [aeval_map_algebraMap]

/-- The equation of the curve by Horner, for any values of the rational functions. -/
lemma eval_toB_foldr' {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] (Fc' : BPoly ℚ) (x w : E)
    (xv : GFrac ℚ → E) (hxv : ∀ p, xv (p, [1]) = aeval x ((CPoly.toPoly p).map (algebraMap ℚ K))) :
    (((toB Fc').map (mapRingHom (algebraMap ℚ K))).map (aeval x).toRingHom).eval w =
      ((fcCode Fc').map xv).foldr (fun c acc ↦ c + w * acc) 0 := by
  induction Fc' with
  | nil => simp [fcCode]
  | cons p W ih =>
    simp only [fcCode, List.map_cons, List.foldr_cons] at ih ⊢
    rw [toB_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_add, eval_mul,
      eval_C, eval_X, ih, hxv]
    rfl

end Helpers

universe u

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 1600000 in
/-- **The realization over the new base curve** in `L' = L(w')`, `w'` a root of `Q`. -/
theorem base_change [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) (Yc : GPoly (GFrac ℚ)) (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc') :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L'), Algebra.IsAlgebraic L L' ∧
      ∃ T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L', T'.n = T.n ∧
        (∀ i, T'.ts i = algebraMap L L' (T.ts i)) ∧
        (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
        (∀ m, ∀ z ∈ T.F m, algebraMap L L' z ∈ T'.F m) ∧
        ∀ z : L', z ∈ IntermediateField.adjoin L {T'.S.y} := by
  classical
  simp only [bcOK, Bool.and_eq_true, beq_iff_eq] at hbc
  obtain ⟨hF0, hY⟩ := hbc
  have h0 : T.Tr 0 := fun i hi ↦ absurd hi (Nat.not_lt_zero _)
  set ψ₀ : KF Fc 0 →+* L := T.psiC 0 h0 with hψ₀
  -- a root of `Q`
  set Ω := AlgebraicClosure L
  have hQirr := (Fact.out : Irreducible (toPoly (qK Fc Q)))
  set P : L[X] := (toPoly (qK Fc Q)).map ψ₀ with hP
  have hPdeg : P.degree ≠ 0 := by
    rw [hP, degree_map]
    exact fun h ↦ (Polynomial.degree_pos_of_irreducible hQirr).ne' h
  have hP0 : P ≠ 0 := by
    rw [hP, Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact hQirr.ne_zero
  obtain ⟨w0, hw0⟩ := IsAlgClosed.exists_aeval_eq_zero Ω P hPdeg
  have hint : IsIntegral L w0 := by
    refine ⟨P * Polynomial.C P.leadingCoeff⁻¹, ?_, ?_⟩
    · exact monic_mul_leadingCoeff_inv hP0
    · rw [eval₂_mul, ← aeval_def, hw0, zero_mul]
  -- the field `L' = L(w0)`
  set L' := L⟮w0⟯ with hL'
  haveI : FiniteDimensional L L' := IntermediateField.adjoin.finiteDimensional hint
  letI : Differential L' := differentialFiniteDimensional L L'
  haveI : DifferentialAlgebra L L' := differentialAlgebraFiniteDimensional
  haveI : CharZero L' := charZero_of_injective_algebraMap (algebraMap L L').injective
  set ι := algebraMap L L' with hι
  set w' : L' := AdjoinSimple.gen L w0 with hw'
  have hroot' : (toPoly (qK Fc Q)).eval₂ (ι.comp ψ₀) w' = 0 := by
    apply (algebraMap L' Ω).injective
    rw [map_zero, hom_eval₂]
    have : (algebraMap L' Ω).comp (ι.comp ψ₀) = (algebraMap L Ω).comp ψ₀ := by
      ext z; rfl
    rw [this, show algebraMap L' Ω w' = w0 from rfl, ← eval₂_map, ← aeval_def]
    exact hw0
  set φ : FW Fc Q →+* L' :=
    (AdjoinRoot.lift (ι.comp ψ₀) w' hroot').comp (NFK.toARHom _) with hφ
  have hφmk : ∀ l, φ (NFK.mk _ l) = (toPoly l).eval₂ (ι.comp ψ₀) w' := fun l ↦ by
    simp only [hφ, RingHom.comp_apply]
    change AdjoinRoot.lift _ _ _ (NFK.toAR _ (NFK.mk _ l)) = _
    rw [NFK.toAR_mk, AdjoinRoot.lift_mk]
  have hφgen : φ (genW Fc Q) = w' := by
    rw [genW, hφmk]; simp
  have hφc : ∀ l : LC 0, φ (NFK.mk _ [trC Fc 0 l]) = ι (T.ev 0 l) := fun l ↦ by
    rw [hφmk]; simp [hψ₀, T.psiC_trC 0 h0]
  -- the new curve
  set Cc' := constants L'
  have hCc' : ∀ z : Cc', z′ = 0 := fun _ ↦ rfl
  have hx' : (ι T.S.x)′ = 1 := by rw [deriv_algebraMap, T.hx, map_one]
  have htr' : Transcendental Cc' (ι T.S.x) :=
    transcendental_of_deriv_ne_zero hCc' (by rw [hx']; exact one_ne_zero)
  set F' : Cc'[X][X] := (toB Fc').map (mapRingHom (algebraMap ℚ Cc')) with hF'
  have hF'm : F'.Monic := hmon'.map _
  have hF'irr : Irreducible F' := hgeo Cc'
  -- values of the rational functions of `x`
  set xv : GFrac ℚ → L' := fun q ↦ ι ((xM T.hC T.S T.hx).sem q) with hxv
  have hfW : ∀ q, φ (fW Fc Q q) = xv q := fun q ↦ by
    rw [fW]
    refine (hφc [q]).trans ?_
    simp only [hxv]
    congr 1
    show (cM T.hC T.S T.hx Fc T.hSF).sem [q] = _
    rw [sem_cM_foldr]; simp
  have hxvp : ∀ p, xv (p, [1]) = aeval (ι T.S.x) ((CPoly.toPoly p).map (algebraMap ℚ Cc')) := by
    intro p
    simp only [hxv, sem_xModel, aeval_map_algebraMap]
    simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_one, Polynomial.map_C, aeval_C,
      map_one, div_one]
    rw [aeval_def, aeval_def, hom_eval₂]
    congr 1
  have hroot : (F'.map (aeval (ι T.S.x)).toRingHom).eval w' = 0 := by
    rw [hF', eval_toB_foldr' Fc' _ w' xv hxvp, ← hφgen, ← map_evW φ xv hfW, hF0, map_zero]
  let S' : CurveData Cc' L' :=
    { x := ι T.S.x
      y := w'
      F := F'
      htr := htr'
      monic := hF'm
      irr := curve_irr _ _ htr' F' hF'm hF'irr hroot
      root := hroot }
  have hSF' : S'.F = (toB Fc').map (mapRingHom (algebraMap ℚ Cc')) := rfl
  have hxS' : S'.x′ = 1 := hx'
  -- the values of the codes
  have hxM : ∀ q, (xM hCc' S' hxS').sem q = xv q := fun q ↦
    sem_xM_map T.hC T.S T.hx hCc' S' hxS' ι rfl q
  have hpolyval : ∀ a : GPoly (GFrac ℚ), (GPoly.toPoly (xM hCc' S' hxS') a).eval (ι T.S.y) =
      ι ((GPoly.toPoly (xM T.hC T.S T.hx) a).eval T.S.y) := by
    intro a
    induction a with
    | nil => simp
    | cons q a ih =>
      rw [GPoly.toPoly_cons, GPoly.toPoly_cons, eval_add, eval_add, eval_mul, eval_mul, eval_C,
        eval_C, eval_X, eval_X, ih, hxM, map_add, map_mul]
  have hsemY : (cM hCc' S' hxS' Fc' hSF').sem Yc = ι T.S.y := by
    rw [sem_cM_foldr, show S'.y = φ (genW Fc Q) from hφgen.symm]
    rw [show Yc.map (xM hCc' S' hxS').sem = Yc.map xv from List.map_congr_left fun q _ ↦ hxM q,
      ← map_evW φ xv hfW, hY]
    refine (hφc yCode).trans ?_
    congr 1
    exact sem_yCode T.hC T.S T.hx Fc T.hSF
  have h0rel : ∀ a, (cM hCc' S' hxS' Fc' hSF').sem (tau0 Fc' Yc a) =
      ι ((cM T.hC T.S T.hx Fc T.hSF).sem a) := fun a ↦ by
    rw [sem_tau0, hsemY, hpolyval, sem_cM]
  have hev' := tau_evL Fc' Yc ι (cM T.hC T.S T.hx Fc T.hSF).sem (cM hCc' S' hxS' Fc' hSF').sem
    h0rel T.ts
  -- the tower
  let T' : MTower Fc' (tauK Fc' Yc ks) Cc' L' :=
    { S := S'
      hC := hCc'
      hx := hxS'
      hSF := hSF'
      n := T.n
      ts := fun i ↦ ι (T.ts i)
      hts := fun m hm ↦ by simp only [T.hts m hm, map_zero]
      ht := fun m hm ↦ by
        have e : evL (cM hCc' S' hxS' Fc' hSF').sem (fun i ↦ ι (T.ts i)) m =
            fun q ↦ evL (cM hCc' S' hxS' Fc' hSF').sem (fun i ↦ ι (T.ts i)) m q := rfl
        have hTt := T.ht m hm
        unfold tauK
        rcases hk : ks m with η | a
        · simp only [hk, kderC] at hTt ⊢
          rw [hev' m η, deriv_algebraMap, hTt]
        · simp only [hk, kderC] at hTt ⊢
          rw [hev' m a, deriv_algebraMap, deriv_algebraMap, hTt, map_mul]
      hts0 := fun m hm a hk ↦ by
        unfold tauK at hk
        rcases hk' : ks m with η | a0
        · rw [hk'] at hk; simp at hk
        · exact (map_ne_zero ι).mpr (T.hts0 m hm a0 hk')
      hconst := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩ }
  -- memberships
  have hF0' : ∀ z ∈ T.F 0, ι z ∈ T'.F 0 := by
    have hx0 : ι T.S.x ∈ T'.F 0 := by
      show ι T.S.x ∈ ((Cc'⟮S'.x⟯)⟮S'.y⟯).restrictScalars Cc'
      exact IntermediateField.algebraMap_mem _ (AdjoinSimple.gen Cc' S'.x)
    have hy0 : ι T.S.y ∈ T'.F 0 := by
      rw [← hsemY]; exact T'.ev_mem 0 Yc
    let N0 : IntermediateField Cc L :=
      { carrier := {w | ι w ∈ T'.F 0}
        mul_mem' := fun {a b} ha hb ↦ by
          change ι (a * b) ∈ T'.F 0; rw [map_mul]; exact mul_mem ha hb
        one_mem' := by change ι 1 ∈ T'.F 0; rw [map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          change ι (a + b) ∈ T'.F 0; rw [map_add]; exact add_mem ha hb
        zero_mem' := by change ι 0 ∈ T'.F 0; rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun c0 ↦ by
          change ι (algebraMap Cc L c0) ∈ T'.F 0
          have hd : (ι (algebraMap Cc L c0))′ = 0 := by
            rw [deriv_algebraMap, deriv_algebraMap, T.hC, map_zero, map_zero]
          exact T'.const_mem 0 ⟨_, hd⟩
        inv_mem' := fun a ha ↦ by
          change ι a⁻¹ ∈ T'.F 0; rw [map_inv₀]; exact inv_mem ha }
    have hle0 : Cc⟮T.S.x⟯ ≤ N0 := by
      rw [IntermediateField.adjoin_le_iff]; rintro w rfl; exact hx0
    let N1 : IntermediateField (Cc⟮T.S.x⟯) L :=
      { carrier := {w | ι w ∈ T'.F 0}
        mul_mem' := fun {a b} ha hb ↦ by
          change ι (a * b) ∈ T'.F 0; rw [map_mul]; exact mul_mem ha hb
        one_mem' := by change ι 1 ∈ T'.F 0; rw [map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          change ι (a + b) ∈ T'.F 0; rw [map_add]; exact add_mem ha hb
        zero_mem' := by change ι 0 ∈ T'.F 0; rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun f ↦ hle0 f.2
        inv_mem' := fun a ha ↦ by
          change ι a⁻¹ ∈ T'.F 0; rw [map_inv₀]; exact inv_mem ha }
    have hle1 : (Cc⟮T.S.x⟯)⟮T.S.y⟯ ≤ N1 := by
      rw [IntermediateField.adjoin_le_iff]; rintro w rfl; exact hy0
    intro z hz
    exact hle1 hz
  have hmemT : ∀ m, ∀ z ∈ T.F m, ι z ∈ T'.F m := by
    intro m
    induction m with
    | zero => exact hF0'
    | succ m ih =>
      intro z hz
      let N : IntermediateField (T.F m) L :=
        { carrier := {w | ι w ∈ T'.F (m + 1)}
          mul_mem' := fun {a b} ha hb ↦ by
            change ι (a * b) ∈ T'.F (m + 1); rw [map_mul]; exact mul_mem ha hb
          one_mem' := by change ι 1 ∈ T'.F (m + 1); rw [map_one]; exact one_mem _
          add_mem' := fun {a b} ha hb ↦ by
            change ι (a + b) ∈ T'.F (m + 1); rw [map_add]; exact add_mem ha hb
          zero_mem' := by change ι 0 ∈ T'.F (m + 1); rw [map_zero]; exact zero_mem _
          algebraMap_mem' := fun f ↦ T'.le_succ m (ih f f.2)
          inv_mem' := fun a ha ↦ by
            change ι a⁻¹ ∈ T'.F (m + 1); rw [map_inv₀]; exact inv_mem ha }
      have hle : IntermediateField.adjoin (T.F m) {T.ts m} ≤ N := by
        rw [IntermediateField.adjoin_le_iff]
        rintro w rfl
        exact T'.ts_mem m
      exact hle ((T.mem_F_succ).mp hz)
  -- generation
  have hgen : ∀ z : L', z ∈ IntermediateField.adjoin L {T'.S.y} := by
    intro z
    have hmap := IntermediateField.adjoin_map L {w'} (IntermediateField.val L')
    rw [Set.image_singleton] at hmap
    have hz : (z : Ω) ∈ (IntermediateField.adjoin L {w'}).map (IntermediateField.val L') := by
      rw [hmap]
      exact z.2
    obtain ⟨z', hz', hzz⟩ := hz
    have : z' = z := Subtype.ext hzz
    rw [← this]
    exact hz'
  exact ⟨L', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.IsAlgebraic.of_finite L L', T', rfl, fun _ ↦ rfl, fun m q ↦ hev' m q, hmemT, hgen⟩

end MTower

end Curves.MT
