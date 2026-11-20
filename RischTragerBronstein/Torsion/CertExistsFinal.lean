import RischTragerBronstein.Torsion.NonTorsFinal
import RischTragerBronstein.Torsion.MobInf
import RischTragerBronstein.Torsion.CertExists
import Mathlib.Data.List.DropRight

/-!
# Certificates always exist

**`certExists_of_curve`**: for every problem over `ℚ` with valid shape whose curve exists over an
algebraically closed field of constants, valid certificates exist. After a Möbius transformation
`t = 1/(x − e)` at a point with `D(e) ≠ 0`, the residues above infinity vanish
(`resInf_mob_eq_zero`). Certificates without the Möbius option then exist for the transformed
problem (`certExistsN_of_inf0`), and they give certificates for the original problem
(`certExists_of_mobN`).

**`decideTotal_complete_curve`**: the total decision `decideTotal` answers for every large search
bound. Together with `decideTotal_spec`, this decides elementary integrability.

* `mobT_shapeOK`: the transformed problem has valid shape.
-/

open Polynomial

namespace Curves

open CPoly Sup NFC

section Lists

variable {R : Type*} [Field R] [DecidableEq R]

lemma length_add' : ∀ p q : CPoly R, (add p q).length = max p.length q.length
  | [], q => by simp [add]
  | a :: p, [] => by simp [add]
  | a :: p, b :: q => by
    simp only [add, List.length_cons, length_add' p q]; omega

lemma length_mul_le (q : CPoly R) : ∀ p : CPoly R, (mul p q).length ≤ p.length + q.length
  | [] => by simp [mul]
  | a :: p => by
    have := length_mul_le q p
    simp only [mul, length_add', smul, List.length_map, List.length_cons]
    omega

lemma length_mul_shiftC_le (e : R) (p : CPoly R) (hp : 0 < p.length) :
    (mul p (shiftC e 1)).length ≤ p.length + 1 := by
  induction p with
  | nil => simp at hp
  | cons a p ih =>
    simp only [mul, length_add', smul, List.length_map, List.length_cons]
    have hs : (shiftC e 1 : CPoly R).length = 2 := by simp [shiftC, xPowC, add]
    rcases p with _ | ⟨b, p⟩
    · simp [mul, hs]
    · have := ih (by simp)
      simp only [List.length_cons] at this ⊢
      omega

lemma length_compC_shiftC_le (e : R) : ∀ c : CPoly R, (compC c (shiftC e 1)).length ≤ c.length
  | [] => by simp [compC]
  | a :: c => by
    have ih := length_compC_shiftC_le e c
    show (add [a] (mul (compC c (shiftC e 1)) (shiftC e 1))).length ≤ c.length + 1
    rw [length_add']
    by_cases h0 : (compC c (shiftC e 1)).length = 0
    · rw [List.length_eq_zero_iff.mp h0]; simp [mul]
    · have := length_mul_shiftC_le e _ (Nat.pos_of_ne_zero h0)
      simp only [List.length_singleton]; omega

lemma length_reflectC (M : ℕ) (P : CPoly R) : (reflectC M P).length = M + 1 := by
  simp [reflectC]

lemma length_invBAux (k M : ℕ) : ∀ (j : ℕ) (W : BPoly R), (invBAux k M j W).length = W.length
  | _, [] => rfl
  | j, c :: W => by simp [invBAux, length_invBAux k M (j + 1) W]

lemma length_invB (W : BPoly R) (k M : ℕ) : (invB W k M).length = W.length :=
  length_invBAux k M 0 W

end Lists

section Shape

variable {F : Type*} [Field F] [DecidableEq F]

lemma shiftB_getD (W : BPoly F) (e : F) (i : ℕ) :
    (shiftB W e).getD i [] = compC (W.getD i []) (shiftC e 1) := by
  by_cases hi : i < W.length
  · rw [shiftB, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  · rw [shiftB, List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega)]
    rfl

lemma trim_trim (p : CPoly F) : trim (trim p) = trim p := by
  simp only [trim, List.reverse_reverse, List.dropWhile_idempotent]

lemma length_trim_le_degT (p : CPoly F) : (trim p).length ≤ degT (trim p) + 1 := by
  rw [degT, trim_trim]; omega

lemma stripB_getD (W : BPoly F) (j : ℕ) (hj : j < (stripB W).length) :
    (stripB W).getD j [] = W.getD j [] := by
  conv_rhs => rw [← List.reverse_reverse W, ← List.takeWhile_append_dropWhile
    (p := fun P ↦ isZero P) (l := W.reverse), List.reverse_append]
  rw [List.getD_append _ _ _ _ (by simpa [stripB] using hj)]
  rfl

lemma mobA_getD (A : BPoly F) (e : F) (k0 DA j : ℕ) (hj : j < (mobA A e k0 DA).length) :
    ∃ p, (mobA A e k0 DA).getD j [] = trim p := by
  rw [mobA, stripB_getD _ _ hj]
  by_cases hj' : j < (smulB [-1] (invB (shiftB A e) k0 DA)).length
  · exact ⟨_, by rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map]⟩
  · exact ⟨[], by rw [List.getD_eq_default _ _ (by simpa using hj')]; rfl⟩

/-- The shape condition on the numerator holds for trimmed coefficients. -/
lemma A_shape_of_trim (P : CurveProb F) (h : ∀ j < P.A.length, ∃ p, P.A.getD j [] = trim p) :
    ∀ j < P.A.length, (P.A.getD j []).length + P.k * j ≤ P.DA + 1 := by
  intro j hj
  obtain ⟨p, hp⟩ := h j hj
  have h1 := le_foldr_max (fun i ↦ degT (P.A.getD i []) + P.k * i) (List.range P.A.length) j
    (List.mem_range.mpr hj)
  have h2 := length_trim_le_degT p
  rw [← hp] at h2
  have h1' : degT (P.A.getD j []) + P.k * j ≤ P.DA := h1
  omega

/-- `D(e + 1/t)` times a power of `t` is non-zero. -/
lemma toPoly_mobD_ne_zero (D : CPoly F) (hD : toPoly D ≠ 0) (e : F) (DA : ℕ) :
    toPoly (mul (reflectC (D.length - 1) (compC D (shiftC e 1))) (xPowC (DA + 2 - (D.length - 1))))
      ≠ 0 := by
  have hl : (compC D (shiftC e 1)).length ≤ D.length - 1 + 1 :=
    (length_compC_shiftC_le e D).trans (by omega)
  rw [toPoly_mul, toPoly_reflectC _ _ hl, toPoly_xPowC, toPoly_compC_shiftC, pow_one]
  refine mul_ne_zero ?_ (pow_ne_zero _ X_ne_zero)
  rw [Ne, reflect_eq_zero_iff]
  intro h0
  rcases comp_eq_zero_iff.mp h0 with h1 | ⟨-, h2⟩
  · exact hD h1
  · have := congrArg (fun q ↦ q.coeff 1) h2
    simp at this

/-- The list facts of the transformed equation. -/
lemma mobFc_facts (P : CurveProb F) (hS : P.shapeOK = true) (e : F) :
    (invB (shiftB P.Fc e) P.k (P.k * P.n)).length = P.n + 1 ∧
    (invB (shiftB P.Fc e) P.k (P.k * P.n)).getD P.n [] = [1] ∧
    (∀ j < P.n + 1, ((invB (shiftB P.Fc e) P.k (P.k * P.n)).getD j []).length =
      P.k * P.n - P.k * j + 1) := by
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, h6⟩, h7⟩, -⟩, -⟩, h10⟩, -⟩ := hS'
  set n := P.n
  set k := P.k
  set W := shiftB P.Fc e with hW
  have hWl : W.length = n + 1 := by rw [hW, shiftB, List.length_map, h2]
  set Fc' := invB W k (k * n) with hFc'
  have hFl : Fc'.length = n + 1 := by rw [hFc', length_invB, hWl]
  have hFg : ∀ j < n + 1, Fc'.getD j [] = reflectC (k * n - k * j) (W.getD j []) := fun j hj ↦ by
    rw [hFc', invB, invBAux_getD, if_pos (by omega), zero_add]
  have hFn : Fc'.getD n [] = [1] := by
    rw [hFg n (by omega), Nat.sub_self, hW, shiftB_getD, h3]
    simp [reflectC, compC, mul, add]
  have hFj : ∀ j < n + 1, (Fc'.getD j []).length = k * n - k * j + 1 := fun j hj ↦ by
    rw [hFg j hj, length_reflectC]
  have hk7 : ∀ j < Fc'.length, (Fc'.getD j []).length ≤ k * n + 1 := fun j hj ↦ by
    rw [hFj j (by omega)]; omega
  exact ⟨hFl, hFn, hFj⟩

/-- The transformed equation is monic of degree `n`. -/
lemma mobFc_monic (P : CurveProb F) (hS : P.shapeOK = true) (e : F) :
    (toB (invB (shiftB P.Fc e) P.k (P.k * P.n))).Monic ∧
    (toB (invB (shiftB P.Fc e) P.k (P.k * P.n))).natDegree = P.n ∧
    ∀ i, ((toB (invB (shiftB P.Fc e) P.k (P.k * P.n))).coeff i).natDegree ≤ P.k * P.n := by
  obtain ⟨hFl, hFn, hFj⟩ := mobFc_facts P hS e
  exact shape_monic _ _ _ hFl hFn fun j hj ↦ by rw [hFj j (by omega)]; omega

lemma mob_arith (k n j : ℕ) (hj : j ≤ n) (hn : 1 ≤ n) :
    k * n - k * j + 1 + k * n * j ≤ k * n * n + 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
  rw [show k * (j + d) - k * j = k * d by rw [Nat.mul_add, Nat.add_sub_cancel_left]]
  nlinarith [Nat.mul_le_mul_left k (Nat.mul_le_mul_left d hn)]

/-- **The Möbius transform has valid shape** (given its discriminant). -/
theorem mobT_shapeOK [CharZero F] (P : CurveProb F) (hS : P.shapeOK = true) (e : F) (DA : ℕ)
    (pts : List (F × BranchCert F)) (inf : BranchCert F)
    (hres : resultant (toB (invB (shiftB P.Fc e) P.k (P.k * P.n)))
      (derivative (toB (invB (shiftB P.Fc e) P.k (P.k * P.n)))) P.n (P.n - 1) ≠ 0) :
    (P.mobT e P.k DA (P.k * P.n) pts inf).shapeOK = true := by
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, h6⟩, h7⟩, -⟩, -⟩, h10⟩, -⟩ := hS'
  obtain ⟨hFl, hFn, hFj⟩ := mobFc_facts P hS e
  set n := P.n
  set k := P.k
  set Fc' := invB (shiftB P.Fc e) k (k * n) with hFc'
  have hk7 : ∀ j < Fc'.length, (Fc'.getD j []).length ≤ k * n + 1 := fun j hj ↦ by
    rw [hFj j (by omega)]; omega
  have hD0 : toPoly P.D ≠ 0 := fun h0 ↦ by
    rw [← trim_eq_nil_iff] at h0; rw [h0] at h10; simp at h10
  have hD' := toPoly_mobD_ne_zero P.D hD0 e DA
  obtain ⟨hmon', hn', hk'⟩ := shape_monic Fc' n (k * n) hFl hFn hk7
  simp only [CurveProb.shapeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨decide_eq_true h1, decide_eq_true hFl⟩, decide_eq_true hFn⟩,
    decide_eq_true ?_⟩, decide_eq_true ?_⟩, fun j hj ↦ decide_eq_true ?_⟩,
    fun j hj ↦ decide_eq_true (hk7 j hj)⟩, ?_⟩, decide_eq_true ?_⟩, decide_eq_true ?_⟩,
    fun j hj ↦ decide_eq_true ?_⟩
  · show (invB Fc' (k * n) (k * n * n)).length = n + 1
    rw [length_invB, hFl]
  · show (invB Fc' (k * n) (k * n * n)).getD n [] = [1]
    rw [invB, invBAux_getD, if_pos (by omega), zero_add, Nat.sub_self, hFn]
    simp [reflectC]
  · show (Fc'.getD j []).length + k * n * j ≤ k * n * n + 1
    replace hj : j < Fc'.length := hj
    rw [hFj j (by omega)]
    exact mob_arith k n j (by omega) h1
  · rw [Bool.eq_false_iff, Ne, isZero_iff]; exact hD'
  · show 0 < (trim (trim (mul (discRC Fc' n (k * n)) _))).length
    rw [List.length_pos_iff, Ne, trim_eq_nil_iff, toPoly_trim, CPoly.toPoly_mul,
      toPoly_discRC _ _ _ hmon' hn' hk']
    exact mul_ne_zero hres hD'
  · rw [List.length_pos_iff, Ne, trim_eq_nil_iff]; exact hD'
  · exact A_shape_of_trim (P.mobT e k DA (k * n) pts inf) (fun j hj ↦ mobA_getD _ _ _ _ j hj) j hj

end Shape

section Final

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [CharZero Kc] [IsAlgClosed Kc]

/-- **Certificates exist** for every problem over `ℚ` with valid shape whose curve exists. -/
theorem certExists_of_curve (P0 : CurveProb ℚ) (hS : P0.shapeOK = true) (S : CurveData Kc E)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) : CertExists P0 := by
  classical
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, h6⟩, h7⟩, -⟩, -⟩, h10⟩, h11⟩ := hS'
  have hD0 : toPoly P0.D ≠ 0 := fun h0 ↦ by
    rw [← trim_eq_nil_iff] at h0; rw [h0] at h10; simp at h10
  -- the point of the transformation
  obtain ⟨e, he⟩ : ∃ e : ℚ, (toPoly P0.D).eval e ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hD0 (Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_univ.mono fun x _ ↦ hall x))
  set n := P0.n with hn
  set k := P0.k with hk
  set DA := P0.DA + P0.D.length with hDAdef
  set P0m := P0.mobT e k DA (k * n) [] ⟨1, [], 0⟩ with hP0m
  -- the conditions of the Möbius check
  have hF : invOKb k (k * n) (shiftB P0.Fc e) = true := by
    refine List.all_eq_true.mpr fun j hj ↦ decide_eq_true ?_
    have hj' : j < P0.Fc.length := by simpa [shiftB] using List.mem_range.mp hj
    rw [shiftB_getD]
    have := h6 j hj'
    have := length_compC_shiftC_le e (P0.Fc.getD j [])
    omega
  have hA : invOKb k DA (shiftB P0.A e) = true := by
    refine List.all_eq_true.mpr fun j hj ↦ decide_eq_true ?_
    have hj' : j < P0.A.length := by simpa [shiftB] using List.mem_range.mp hj
    rw [shiftB_getD]
    have := h11 j hj'
    have := length_compC_shiftC_le e (P0.A.getD j [])
    omega
  have hl : (compC P0.D (shiftC e 1)).length ≤ P0.D.length - 1 + 1 :=
    (length_compC_shiftC_le e P0.D).trans (by omega)
  have hDA : P0.D.length - 1 ≤ DA + 2 := by omega
  -- the transformed curve
  obtain ⟨hmon', hn', -⟩ := mobFc_monic P0 hS e
  obtain ⟨hmon, hnF, -⟩ := shape_monic P0.Fc P0.n P0.k h2 h3 h7
  have hSn : S.F.natDegree = n := by rw [hSF, hmon.natDegree_map, hnF]
  set c : Kc := algebraMap ℚ Kc e with hc
  have hFs : shiftP S.F c = (shiftP (toB P0.Fc) e).map (mapRingHom (algebraMap ℚ Kc)) := by
    rw [hSF, shiftP_map]
  have hInvF : InvOK k (k * n) 0 (shiftB P0.Fc e) := invOKb_spec hF
  have hG : invP (shiftP S.F c) k (k * n) =
      (toB (invB (shiftB P0.Fc e) k (k * n))).map (mapRingHom (algebraMap ℚ Kc)) := by
    rw [hFs, ← invP_map, ← toB_shiftB, ← toB_invB _ _ _ hInvF]
  have hGm : (invP (shiftP S.F c) k (k * n)).Monic := by rw [hG]; exact hmon'.map _
  have hGn : (invP (shiftP S.F c) k (k * n)).natDegree = S.F.natDegree := by
    rw [hG, hmon'.natDegree_map, hSn]; exact hn'
  have hM : ∀ i ≤ (shiftP S.F c).natDegree,
      ((shiftP S.F c).coeff i).natDegree + k * i ≤ k * n := by
    intro i hi
    have hb := invBound_of_invOK _ _ _ hInvF i (by
      rw [toB_shiftB]
      refine le_trans hi ?_
      rw [hFs]; exact natDegree_map_le)
    rw [hFs, coeff_map, ← toB_shiftB, coe_mapRingHom]
    have h2 := natDegree_map_le (f := algebraMap ℚ Kc) (p := (toB (shiftB P0.Fc e)).coeff i)
    omega
  set S' := mobCurve S c k (k * n) hM hGm hGn with hS'
  have hS'F : S'.F = (toB P0m.Fc).map (mapRingHom (algebraMap ℚ Kc)) := hG
  -- the transformed problem has valid shape
  have hres : resultant (toB (invB (shiftB P0.Fc e) P0.k (P0.k * P0.n)))
      (derivative (toB (invB (shiftB P0.Fc e) P0.k (P0.k * P0.n)))) P0.n (P0.n - 1) ≠ 0 := by
    intro h0
    apply S'.discR_ne_zero
    have hdeg : S'.F.natDegree = n := by
      show (invP (shiftP S.F c) k (k * n)).natDegree = n
      rw [hGn, hSn]
    rw [CurveData.discR, hdeg, show S'.F = _ from hG, ← resultant_map_deriv]
    exact (congrArg _ h0).trans (map_zero _)
  have hSm : P0m.shapeOK = true := mobT_shapeOK P0 hS e DA [] ⟨1, [], 0⟩ hres
  -- no residues above infinity
  have hinf0 : ∀ (M : CPoly ℚ) (hM : Kron.irredQ M = true),
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)),
        (P0m.baseChange (algebraMap ℚ (NF M)) P0m.k pts inf).valid = true →
        ∀ wt ∈ inf.ys, (P0m.baseChange (algebraMap ℚ (NF M)) P0m.k pts inf).resInf wt = 0 := by
    intro M hM
    haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    intro pts inf hvalid wt hwt
    set φ := algebraMap ℚ (NF M) with hφ
    set ψ : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom
    have hψ : ψ.comp φ = algebraMap ℚ Kc := Subsingleton.elim _ _
    set P := P0.baseChange φ P0.k [] ⟨1, [], 0⟩ with hP
    have hSFP : S.F = (toB P.Fc).map (mapRingHom ψ) := by
      rw [hSF, hP, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hψ]
    have hmob := mobCheck_baseChange φ P0 e k DA (k * n) [] ⟨1, [], 0⟩ pts inf hF hA hl hDA
    rw [baseChange_mobT φ P0 e k DA (k * n) [] ⟨1, [], 0⟩ pts inf [] ⟨1, [], 0⟩] at hmob
    have hV' := (P0m.baseChange φ P0m.k pts inf).valid_spec hvalid
    refine resInf_mob_eq_zero S P _ ψ hSFP (φ e) k DA hmob hV' ?_ wt hwt
    show (toPoly (P0.D.map φ)).eval (φ e) ≠ 0
    rw [toPoly_mapHom, eval_map, eval₂_at_apply]
    exact fun h ↦ he (φ.injective (by rw [h, map_zero]))
  exact certExists_of_mobN P0 e k DA (k * n) hF hA hl hDA
    (certExistsN_of_inf0 P0m hSm (hsep_of_shapeOK P0m hSm) (hsepI_of_shapeOK P0m hSm) S' hS'F
      hinf0)

/-- **The total decision answers** for every large search bound, for every problem with valid
shape whose curve exists. -/
theorem decideTotal_complete_curve (Fc A : BPoly ℚ) (D : CPoly ℚ)
    (hS : (curveProbQ Fc A D).shapeOK = true) (S : CurveData Kc E)
    (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc))) :
    ∃ N₀, ∀ N, N₀ ≤ N → (decideTotal Fc A D N).isSome :=
  decideTotal_complete Fc A D (certExists_of_curve _ hS S hSF)

end Final

section Decision

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

open IntermediateField Differential

/-- **The decision of elementary integrability** on curves over `ℚ`: for every large search bound
the total decision answers, and its answer says whether `A(x, y)/D(x)` has an elementary
antiderivative. -/
theorem decideTotal_decides (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (Fc A : BPoly ℚ) (D : CPoly ℚ)
    (hS : (curveProbQ Fc A D).shapeOK = true)
    (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, decideTotal Fc A D N = some b ∧
      (HasElementaryIntegral ((S.fE (curveProbQ Fc A D) (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔
        b = true) := by
  obtain ⟨N₀, hN₀⟩ := decideTotal_complete_curve Fc A D hS S hSF
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hN₀ N hN)
  exact ⟨b, hb, decideTotal_spec hC S hx hgen Fc A D hSF N b hb⟩

end Decision

end Curves
