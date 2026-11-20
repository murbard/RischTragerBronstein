import RischTragerBronstein.Mixed.KRTors
import RischTragerBronstein.Torsion.SubRoot

/-!
# Radicals over an exponential level: the witness through the norm

* `evalW`: the evaluation `W(x, y)` of `W ∈ C[X][X]` in `C(x, y)` (a ring homomorphism; it agrees
  with `elemW` when `deg_Y W < n`);
* `kr_norm_witness`: the witness `W` over `Kₘ(ζ)` of `N Γ`, its norm `∏_u τ_u W` descended to `Kₘ`,
  read on `yⁿ = A` (untwisted by `μ₀`), has divisor `|U| N Γ`, `U` the units modulo `n`.
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Differential.SuperData

variable {C L : Type*} [Field C] [Field L] [Algebra C L] (S : SuperData C L)

/-- `C[X] → C(x, y)`. -/
noncomputable def polyXHom : C[X] →+* C⟮S.x⟯⟮S.y⟯ :=
  letI := algebraAdjoinSimple (F := C) S.x
  (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).comp (algebraMap C[X] C⟮S.x⟯)

lemma polyXHom_apply (P : C[X]) : S.polyXHom P = S.polyX P := rfl

/-- **The evaluation** `W(x, y)`. -/
noncomputable def evalW (W : C[X][X]) : C⟮S.x⟯⟮S.y⟯ := W.eval₂ S.polyXHom (AdjoinSimple.gen C⟮S.x⟯ S.y)

lemma evalW_mul (V W : C[X][X]) : S.evalW (V * W) = S.evalW V * S.evalW W := eval₂_mul _ _

lemma evalW_prod {ι : Type*} (s : Finset ι) (W : ι → C[X][X]) :
    S.evalW (∏ i ∈ s, W i) = ∏ i ∈ s, S.evalW (W i) :=
  map_prod (Polynomial.eval₂RingHom S.polyXHom (AdjoinSimple.gen C⟮S.x⟯ S.y)) W s

lemma evalW_eq_elemW (W : C[X][X]) (hW : ∀ i, S.n ≤ i → W.coeff i = 0) : S.evalW W = S.elemW W := by
  rw [evalW, elemW, eval₂_eq_sum_range' S.polyXHom (n := S.n)]
  · rfl
  · by_contra h
    push Not at h
    by_cases hW0 : W = 0
    · subst hW0; simp at h; exact absurd h S.hn.ne'
    exact (leadingCoeff_ne_zero.mpr hW0) (hW _ h)

end Differential.SuperData

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- Mapping a bivariate list by a function read through ring homomorphisms. -/
lemma toB_map_fun {A B C' : Type*} [CommRing A] [CommRing B] [CommRing C'] (f : A → B)
    (ψB : B →+* C') (ψA : A →+* C') (W : BPoly A) (hf : ∀ c ∈ W, ∀ a ∈ c, ψB (f a) = ψA a) :
    (toB (W.map (·.map f))).map (mapRingHom ψB) = (toB W).map (mapRingHom ψA) := by
  rw [← toB_mapL', ← toB_mapL', List.map_map]
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  exact List.map_congr_left fun a ha ↦ hf c hc a ha

lemma toB_foldr_mulB {F : Type*} [Field F] [DecidableEq F] (l : List (BPoly F)) :
    toB (l.foldr (fun V acc ↦ mulB V acc) [[1]]) = (l.map toB).prod := by
  induction l with
  | nil => simp [CPoly.toPoly]
  | cons a l ih => simp [ih]

/-- Units modulo `n`. -/
def unitsN (n : ℕ) : List ℕ := (List.range n).filter fun u ↦ Nat.Coprime u n

lemma normNF_eq [Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
    [Fact (Irreducible (toPoly (cycK Fc m n)))] (W : BPoly (NFz Fc m n)) :
    normNF Fc m n W = ((unitsN n).map fun u ↦ W.map fun c ↦ c.map (tauN Fc m n u)).foldr
      (fun V acc ↦ mulB V acc) [[1]] := by
  rw [normNF, unitsN, List.foldr_map]

namespace MTower

variable (T : MTower Fc ks Cc L)

section NormW

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
  (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  [Fact (Irreducible (toPoly (cycK Fc m n)))]
  (ω : T.F m) (hω : IsPrimitiveRoot ω n) (θ : L) (hθ : θ ^ n = T.evP m A)
  (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
  (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
    (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))

include hn hω in
/-- The points of the class for `ωᵘ` are those for `ω`, permuted. -/
lemma gammaPts_units (μ₀ : T.F m) (hμ₀ : μ₀ ≠ 0) (u : ℕ) (hu : Nat.Coprime u n) (Q : AlgebraicClosure (T.F m) × AlgebraicClosure (T.F m)) :
    Differential.SuperData.gammaPts (fun _ : Fin n ↦ (0 : T.F m)) (fun k ↦ (ω ^ u) ^ (k : ℕ) / μ₀)
      (ramMult n) Q =
    Differential.SuperData.gammaPts (fun _ : Fin n ↦ (0 : T.F m)) (fun k ↦ ω ^ (k : ℕ) / μ₀)
      (ramMult n) Q := by
  classical
  have hmod : ∀ x : ℕ, ramC n (x % n) = ramC n x := fun x ↦ by
    rw [← ramC_gcd, Nat.gcd_comm, ← Nat.gcd_rec, ramC_gcd]
  have hmul : ∀ k : ℕ, ramC n (u * k) = ramC n k := fun k ↦ by
    rw [← ramC_gcd, Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel k hu, Nat.gcd_comm, ramC_gcd]
  set e : Fin n → Fin n := fun k ↦ ⟨u * k % n, Nat.mod_lt _ hn⟩ with he
  have hinj : Function.Injective e := fun k l h ↦ by
    have h1 : u * k % n = u * l % n := congrArg Fin.val h
    have := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hu).gcd_eq_one h1
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt this k.2 l.2)
  have hbij : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).mpr ⟨hinj, rfl⟩
  unfold Differential.SuperData.gammaPts
  refine Fintype.sum_bijective e hbij _ _ fun k ↦ ?_
  have hpow : (ω ^ u) ^ (k : ℕ) = ω ^ ((e k : Fin n) : ℕ) := by
    simp only [he]
    rw [← pow_mul]
    conv_lhs => rw [← Nat.mod_add_div (u * k) n, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  have hm : ramMult n k = ramMult n (e k) := by
    simp only [ramMult, he, hmod, hmul]
  simp only [hpow, hm]

include hsq hcopA hω hZ0 hzκ hκ0 hsF in
/-- **The norm witness**: the descended norm of the witness, untwisted, has divisor `|U| N Γ`. -/
theorem kr_norm_witness (hn1 : 1 < n) (N : ℕ) (Wb : BPoly (NFz Fc m n))
    (hWb : krWit Fc ks m n A z κ N = some Wb) (W0 : BPoly (KF Fc m))
    (hW0 : descendNF Fc m n (normNF Fc m n Wb) = some W0) :
    let S := T.krS m hTr A hsq hdegA n hn θ hθ
    let hTm : T.Tr m := hTr.of_succ
    let μ₀ : T.F m := (T.MP m hTm).sem z / sF
    let Wt := S.evalW (((toB W0).map (mapRingHom (T.psiF m hTm))).comp
      (Polynomial.C (Polynomial.C μ₀) * X))
    Wt ≠ 0 ∧ ∀ a b : AlgebraicClosure (T.F m), b ^ S.n = (S.p.map (algebraMap _ _)).eval a →
      S.ordAt (AlgebraicClosure (T.F m)) Wt a b = ((unitsN n).length * N : ℕ) *
        Differential.SuperData.gammaPts (fun _ : Fin n ↦ (0 : T.F m)) (fun k ↦ ω ^ (k : ℕ) / μ₀)
          (ramMult n) (a, b) := by
  intro S hTm μ₀ Wt
  set K := AlgebraicClosure (T.F m)
  set ψ := T.psiNF m hTm n hn ω hω with hψ
  set q : (T.F m)[X][X] := Polynomial.C (Polynomial.C μ₀) * X with hq
  set G := Differential.SuperData.gammaPts (K := K) (fun _ : Fin n ↦ (0 : T.F m))
    (fun k ↦ ω ^ (k : ℕ) / μ₀) (ramMult n) with hG
  -- the descent
  have hdesc : W0 = (normNF Fc m n Wb).map (fun c ↦ c.map fun a ↦ a.1.getD 0 0) ∧
      (normNF Fc m n Wb).all (·.all fun a ↦ decide (a.1.length ≤ 1)) := by
    unfold descendNF at hW0
    split_ifs at hW0 with h
    exact ⟨(Option.some.inj hW0).symm, h⟩
  have e1 : (toB W0).map (mapRingHom (T.psiF m hTm)) =
      (toB (normNF Fc m n Wb)).map (mapRingHom ψ) := by
    rw [hdesc.1]
    refine toB_map_fun _ _ _ _ fun c hc a ha ↦ ?_
    have hl : a.1.length ≤ 1 := by
      have := List.all_eq_true.mp hdesc.2 c hc
      simpa using List.all_eq_true.mp this a ha
    rw [hψ, psiNF_val]
    rcases hx : a.1 with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp [CPoly.toPoly_nil]
    · simp [CPoly.toPoly_cons, CPoly.toPoly_nil]
    · rw [hx] at hl; simp at hl
  -- the ring homomorphism
  set Rh : (NFz Fc m n)[X][X] →+* (T.F m)⟮S.x⟯⟮S.y⟯ :=
    (Polynomial.eval₂RingHom S.polyXHom (AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y)).comp
      ((Polynomial.compRingHom q).comp (mapRingHom (mapRingHom ψ))) with hRh
  set V : ℕ → (T.F m)⟮S.x⟯⟮S.y⟯ := fun u ↦ Rh (toB (Wb.map fun c ↦ c.map (tauN Fc m n u))) with hV
  have hWt : Wt = ((unitsN n).map V).prod := by
    have : Wt = Rh (toB (normNF Fc m n Wb)) := by
      simp only [Wt, e1]; rfl
    rw [this, normNF_eq, toB_foldr_mulB, List.map_map, map_list_prod, List.map_map]
    rfl
  -- one factor
  have key : ∀ u ∈ unitsN n, V u ≠ 0 ∧ ∀ a b : K, b ^ S.n = (S.p.map (algebraMap _ _)).eval a →
      S.ordAt K (V u) a b = N * G (a, b) := by
    intro u hu
    have hu' : Nat.Coprime u n := (List.mem_filter.mp hu).2 |> of_decide_eq_true
    have hu0 : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · subst h; rw [Nat.coprime_zero_left] at hu'; omega
      · exact h
    have hωu := hω.pow_of_coprime u hu'
    obtain ⟨hμ₀, hpf, hd, hsqK, hcop2, hΓK, hvK, hinj, hβS, hP, hβ'⟩ :=
      T.kr_facts m hTr A hsq hdegA n hn hcopA (ω ^ u) hωu θ hθ z κ hZ0 hzκ hκ0 sF hsF
    have hmap : (toB (Wb.map fun c ↦ c.map (tauN Fc m n u))).map (mapRingHom ψ) =
        (toB Wb).map (mapRingHom (T.psiNF m hTm n hn (ω ^ u) hωu)) :=
      toB_map_fun _ _ _ _ fun c _ a _ ↦ T.psiNF_tauN m hTm n hn ω hω u hu' hu0 a
    have hVu : V u = S.evalW (((toB Wb).map (mapRingHom (T.psiNF m hTm n hn (ω ^ u) hωu))).comp q) := by
      show S.evalW (((toB (Wb.map fun c ↦ c.map (tauN Fc m n u))).map (mapRingHom ψ)).comp q) = _
      rw [hmap]
    have hcopS : Nat.Coprime S.n S.p.natDegree := hcopA
    have hw := S.pts_witness (K := K) hcopS (fun _ ↦ (0 : T.F m)) _ hP hβS (ramMult n)
      (T.psiNF m hTm n hn (ω ^ u) hωu) (krFK Fc ks m n A z κ) μ₀ hμ₀ hpf hd (fun _ ↦ 0)
      (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (fun _ ↦ map_zero _) hβ' hΓK N Wb hWb
    obtain ⟨-, hWs, -⟩ := witW_spec (krFK Fc ks m n A z κ) S.n S.hn _ _ _ (ramMult n) N hΓK hWb
    have hel : S.evalW (((toB Wb).map (mapRingHom (T.psiNF m hTm n hn (ω ^ u) hωu))).comp q) =
        S.elemW (((toB Wb).map (mapRingHom (T.psiNF m hTm n hn (ω ^ u) hωu))).comp q) := by
      refine S.evalW_eq_elemW _ fun i hi ↦ ?_
      rw [hq, comp_C_mul_X_coeff, coeff_map]
      by_cases h0 : (toB Wb).coeff i = 0
      · simp [h0]
      · obtain ⟨a, ha⟩ : ∃ a, ((toB Wb).coeff i).coeff a ≠ 0 := by
          by_contra hc; push Not at hc; exact h0 (Polynomial.ext hc)
        exact absurd hi (not_le.mpr (hWs i a ha).1)
    rw [hVu, hel]
    refine ⟨hw.1, fun a b hv ↦ ?_⟩
    rw [hw.2 a b hv, hG, gammaPts_units (Fc := Fc) T m n hn ω hω μ₀ hμ₀ u hu']
  -- the product
  have hprod : ∀ l : List ℕ, (∀ u ∈ l, u ∈ unitsN n) → (l.map V).prod ≠ 0 ∧
      ∀ a b : K, b ^ S.n = (S.p.map (algebraMap _ _)).eval a →
        S.ordAt K (l.map V).prod a b = ((l.length * N : ℕ) : ℤ) * G (a, b) := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨by simp, fun a b hv ↦ ?_⟩
      have := S.ordAt_zpow (K := K) hv (1 : (T.F m)⟮S.x⟯⟮S.y⟯) 0
      simpa using this
    | cons u l ih =>
      intro hl
      obtain ⟨h0, hord⟩ := ih fun v hv ↦ hl v (List.mem_cons_of_mem _ hv)
      obtain ⟨hu0, huord⟩ := key u (hl u List.mem_cons_self)
      refine ⟨by rw [List.map_cons, List.prod_cons]; exact mul_ne_zero hu0 h0, fun a b hv ↦ ?_⟩
      rw [List.map_cons, List.prod_cons, S.ordAt_mul hv hu0 h0, huord a b hv, hord a b hv]
      rw [List.length_cons]
      push_cast
      ring
  obtain ⟨h0, hord⟩ := hprod (unitsN n) fun u hu ↦ hu
  rw [hWt]
  exact ⟨h0, hord⟩

end NormW

end MTower

end Curves.MT
