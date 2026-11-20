import RischTragerBronstein.Mixed.NKInf2UnitDecide
import RischTragerBronstein.Mixed.NKExactTL

/-!
# Several places at infinity with a full set of units

A curve over `ℚ` whose `r` places at infinity lie in one fibre of the inverted curve and which has
`r − 1` units `u₁, …, u_{r−1}` (`uᵢ = ∑ Uᵢⱼ θʲ` with inverses `∑ Vᵢⱼ θʲ`: `unitC`, logarithmic
derivatives `gᵢ` certified by `logDerChk`), multiplicatively independent modulo `Fₘ` (certificate
`indepC`: the coordinates `j ≥ 1` of the `gᵢ` have a right inverse). Every unit is then, up to
a power, `c ∏ uᵢ^{aᵢ}` (`mem_pow_units`), so the logarithmic part of an elementary integral is
`∑ κᵢ gᵢ + ℓ` (`nk_liouville_units`), and when `τ(gᵢ) = 0`, `∫ f` is elementary iff
`f − τ(f)/n − ∑ cᵢ gᵢ` is exact for some constants `cᵢ` (`exactTL`) and `∫ τ(f)/n` is elementary
(`nk_iffInf`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open CPoly Sup GTors

/-- **The place data of a curve over `ℚ`** (over `F ⊇ ℚ`): one fibre at `0`, `r` places. -/
def RPlaceDataP (F : Type*) [Field F] [DecidableEq F] [CharZero F] (Fc0 : BPoly ℚ) (r : ℕ) : Prop :=
  ∃ (Fc' : BPoly F) (Pc : PlaceCert F),
    toB Fc' = (toB Fc0).map (mapRingHom (algebraMap ℚ F)) ∧ Pc.check Fc' (toB Fc').natDegree = true ∧
    Pc.fib.length = 1 ∧ Pc.pl.length = r ∧ Pc.fα 0 = 0

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The `d`-th derivative of a code. -/
def iterDC (m : ℕ) : ℕ → LC (m + 1) → LC (m + 1)
  | 0, c => c
  | d + 1, c => (MO Fc ks (m + 1)).deriv (iterDC m d c)

/-- **The generalized Wronskian certificate**: positions `Jₚ ≥ 1`, derivative orders `Dₚ` and a
right inverse `H` of the matrix `((gᵢ)_{Jₚ})^{(Dₚ)}`. -/
def indepWC (m : ℕ) (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ)
    (H : List (List (LC (m + 1)))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let z := (MOr Fc ks (m + 1)).zero
  let k := gls.length
  (List.range k).all (fun p ↦ decide (1 ≤ J.getD p 0)) &&
  (List.range k).all fun i ↦ (List.range k).all fun l ↦
    O1.isZero (O1.add (lsumC O1 ((List.range k).map fun p ↦
      O1.mul (iterDC Fc ks m (D.getD p 0) ((gls.getD i []).getD (J.getD p 0) z))
        ((H.getD p []).getD l z)))
      (O1.neg (if i = l then O1.one else O1.zero)))

/-- **The independence certificate**: positions `Jₚ ≥ 1` of the coordinate matrix of the `gᵢ`
and a right inverse `H`, as the generalized Wronskian `indepWC` whose derivative orders are the
entries of `J` after the first `k = #gls` (absent entries: order `0`, so `J` of length `k` is the
plain minor `∑ₚ g_{i,Jₚ} H_{p,l} = δ_{il}`). -/
def indepC (m : ℕ) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ) (H : List (List (LC (m + 1)))) :
    Bool :=
  indepWC Fc ks m gls J (J.drop gls.length) H

/-- The unit checks: `uᵢ vᵢ ≡ 1`, `gᵢ = uᵢ′/uᵢ`, `deg gᵢ < n`, `τ(gᵢ) = 0`. -/
def unitsC (m : ℕ) (Pp : List (GPoly (LC m))) (Us Vs : List (List (GPoly (LC m))))
    (gls : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1))) : Bool :=
  (List.range gls.length).all fun i ↦
    unitC Fc ks m Pp (Us.getD i []) (Vs.getD i []) &&
    logDerChk Fc ks m Pp (Us.getD i []) (Vs.getD i []) (gls.getD i []) dθ wθ &&
    decide ((gls.getD i []).length ≤ Pp.length) &&
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s)

/-- **The trace check with a derivative certificate** (unnormalized code arithmetic): `θ′ = dθ`
(as in `logDerChk`), `s₀ = n` and `∑ⱼ Mᵢⱼ sⱼ = sᵢ′` with `(θⁱ)′ = ∑ⱼ Mᵢⱼ θʲ` (`dPowC`). -/
def traceW (m : ℕ) (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1))) :
    Bool :=
  let O1 := MO Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let z := (MOr Fc ks (m + 1)).zero
  zeroModC Fc ks m Pp (GPoly.add O1 (GPoly.mul O1 dθ (GPoly.derivX O1 P)) (GPoly.mapD O1 P)) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 wθ (GPoly.derivX O1 P)) [O1.one]) &&
  O1.isZero (O1.add (s.getD 0 z) (O1.neg (O1.natCast Pp.length))) &&
  (List.range Pp.length).all fun i ↦ O1.isZero (O1.add (lsumC O1 ((List.range Pp.length).map fun j ↦
      O1.mul ((dPowC O1 P dθ i).getD j O1.zero) (s.getD j z)))
      (O1.neg (O1.deriv (s.getD i z))))

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma unitsC_spec {m : ℕ} {Pp : List (GPoly (LC m))} {Us Vs : List (List (GPoly (LC m)))}
    {gls : List (GPoly (LC (m + 1)))} {dθ wθ : GPoly (LC (m + 1))} {s : List (LC (m + 1))}
    (h : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true) (i : ℕ) (hi : i < gls.length) :
    unitC Fc ks m Pp (Us.getD i []) (Vs.getD i []) = true ∧
    logDerChk Fc ks m Pp (Us.getD i []) (Vs.getD i []) (gls.getD i []) dθ wθ = true ∧
    (gls.getD i []).length ≤ Pp.length ∧
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s) = true := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- `θ′ = dθ(θ)` from the first two checks of `logDerChk`/`traceW`. -/
lemma deriv_θ_of_chk (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (dθ wθ : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (hd : zeroModC Fc ks m Pp (GPoly.add (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) dθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) (GPoly.mapD (MO Fc ks (m + 1))
        (nkPC Fc ks m Pp))) = true)
    (hw : zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) wθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) [(MO Fc ks (m + 1)).one]) = true) :
    θ′ = T.evθ m h1 θ dθ := by
  set O1 := MO Fc ks (m + 1)
  have hd' := T.zeroModC_sound m h1 θ Pp _ hP hd
  have hw' := T.zeroModC_sound m h1 θ Pp _ hP hw
  have hev : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.add O1 a b) =
      T.evθ m h1 θ a + T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_add, map_add]
  have hem : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.mul O1 a b) =
      T.evθ m h1 θ a * T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_mul, map_mul]
  have hes : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.sub O1 a b) =
      T.evθ m h1 θ a - T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_sub, map_sub]
  rw [hev, hem] at hd'
  rw [hes, hem, T.evθ_one_MO m h1 θ, sub_eq_zero] at hw'
  have hPd := T.deriv_evθ_MO m h1 θ (nkPC Fc ks m Pp)
  rw [hP, Derivation.map_zero] at hPd
  have hne : T.evθ m h1 θ (GPoly.derivX O1 (nkPC Fc ks m Pp)) ≠ 0 :=
    right_ne_zero_of_mul_eq_one hw'
  have : T.evθ m h1 θ (GPoly.derivX O1 (nkPC Fc ks m Pp)) * (θ′ - T.evθ m h1 θ dθ) = 0 := by
    linear_combination -hPd - hd'
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)

lemma toPoly_MPr (m : ℕ) (h1 : T.Tr (m + 1)) (p : GPoly (LC (m + 1))) :
    GPoly.toPoly (T.MPr (m + 1) h1) p = GPoly.toPoly (T.MP (m + 1) h1) p := by
  induction p with
  | nil => simp [GPoly.toPoly_nil]
  | cons a p ih => rw [GPoly.toPoly_cons, GPoly.toPoly_cons, ih, MPr_sem]

/-- **Soundness of `traceW`** (the conclusion of `traceC_sound`). -/
lemma traceW_sound (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (θ : L)
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true) :
    (T.MPr (m + 1) h1).sem (s.getD 0 (MOr Fc ks (m + 1)).zero) = (Pp.length : T.F (m + 1)) ∧
    ∀ i < Pp.length, ∃ c : ℕ → T.F (m + 1),
      (θ ^ i)′ = ∑ j ∈ Finset.range Pp.length, (c j : L) * θ ^ j ∧
      ∑ j ∈ Finset.range Pp.length, c j * (T.MPr (m + 1) h1).sem (s.getD j (MOr Fc ks (m + 1)).zero) =
        ((T.MPr (m + 1) h1).sem (s.getD i (MOr Fc ks (m + 1)).zero))′ := by
  set P := nkPC Fc ks m Pp with hPdef
  unfold traceW at hs
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨⟨hd, hw⟩, h0⟩, hall⟩ := hs
  have hθ' := T.deriv_θ_of_chk m h1 θ Pp dθ wθ hP hd hw
  have hPm : (GPoly.toPoly (T.MP (m + 1) h1) P).Monic := by
    rw [← T.toPoly_MPr m h1, T.toPoly_nkPC m h1 Pp]; exact polyF_monic _ _
  have hPd : (GPoly.toPoly (T.MP (m + 1) h1) P).natDegree = Pp.length := by
    rw [← T.toPoly_MPr m h1, T.toPoly_nkPC m h1 Pp]; exact polyF_natDegree _ _
  refine ⟨?_, fun i hi ↦ ⟨fun j ↦ (T.MP (m + 1) h1).sem ((dPowC (MO Fc ks (m + 1)) P dθ i).getD j (MO Fc ks (m + 1)).zero), ?_, ?_⟩⟩
  · have := ((T.MP (m + 1) h1).isZero_iff _).mp h0
    rw [(T.MP (m + 1) h1).sem_add, (T.MP (m + 1) h1).sem_neg, (T.MP (m + 1) h1).sem_natCast,
      add_neg_eq_zero] at this
    rw [MPr_sem]; exact this
  · -- `(θⁱ)′ = evθ (dPowC …)`
    have e1 : (θ ^ i)′ = T.evθ m h1 θ (dPowC (MO Fc ks (m + 1)) P dθ i) := by
      unfold dPowC
      split_ifs with hi0
      · subst hi0; simp [evθ]
      · rw [T.evθ_remP_MO m h1 θ P _ hP]
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [Derivation.leibniz_pow, hθ', evθ_MP, evθ_MP]
        simp only [GPoly.toPoly_mul, GPoly.toPoly_monomial, map_mul, map_pow, aeval_C, aeval_X,
          (T.MP (m + 1) h1).sem_natCast, nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
        rw [map_natCast]
        ring
    rw [e1, evθ_MP]
    have hdeg : (GPoly.toPoly (T.MP (m + 1) h1) (dPowC (MO Fc ks (m + 1)) P dθ i)).natDegree < Pp.length ∨
        GPoly.toPoly (T.MP (m + 1) h1) (dPowC (MO Fc ks (m + 1)) P dθ i) = 0 := by
      unfold dPowC
      split_ifs
      · right; simp
      · by_cases h0' : GPoly.toPoly (T.MP (m + 1) h1) (remP (MO Fc ks (m + 1)) P (GPoly.mul (MO Fc ks (m + 1)) (GPoly.monomial (MO Fc ks (m + 1)) (i - 1)
            ((MO Fc ks (m + 1)).natCast i)) dθ)) = 0
        · right; exact h0'
        · left
          have := GPoly.divMod_degree_lt (T.MP (m + 1) h1) (GPoly.mul (MO Fc ks (m + 1)) (GPoly.monomial (MO Fc ks (m + 1)) (i - 1)
            ((MO Fc ks (m + 1)).natCast i)) dθ) P hPm.ne_zero
          rw [← hPd]
          exact natDegree_lt_natDegree h0' this
    rcases hdeg with hlt | hz
    · rw [aeval_eq_sum_range' hlt]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [coeff_toPoly_sem, Algebra.smul_def]
      rfl
    · rw [hz, map_zero]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have : (GPoly.toPoly (T.MP (m + 1) h1) (dPowC (MO Fc ks (m + 1)) P dθ i)).coeff j = 0 := by rw [hz, coeff_zero]
      rw [coeff_toPoly_sem] at this
      simp only [this, ZeroMemClass.coe_zero, zero_mul]
  · have := ((T.MP (m + 1) h1).isZero_iff _).mp (hall i (List.mem_range.mpr hi))
    rw [(T.MP (m + 1) h1).sem_add, (T.MP (m + 1) h1).sem_neg, (T.MP (m + 1) h1).sem_deriv, sem_lsumC, List.map_map, add_neg_eq_zero,
      ← List.sum_toFinset _ List.nodup_range, List.toFinset_range] at this
    rw [MPr_sem, ← this]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Function.comp_apply, (T.MP (m + 1) h1).sem_mul]; rfl

/-- `evθ` of a list of length `≤ n` as a sum over `range n`. -/
lemma evθ_list_le (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (gl : List (LC (m + 1))) (n : ℕ)
    (hgl : gl.length ≤ n) :
    T.evθ m h1 θ gl = ∑ j ∈ Finset.range n,
      (((T.MPr (m + 1) h1).sem (gl.getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ j := by
  rw [T.evθ_list m h1 θ gl, ← Finset.sum_range_add_sum_Ico _ hgl,
    Finset.sum_eq_zero (s := Finset.Ico gl.length n) fun j hj ↦ by
      rw [List.getD_eq_default _ _ (by have := (Finset.mem_Ico.mp hj).1; omega),
        (T.MPr (m + 1) h1).sem_zero]
      simp, add_zero]

lemma sem_iterDC (m : ℕ) (h1 : T.Tr (m + 1)) (d : ℕ) (c : LC (m + 1)) :
    (T.MP (m + 1) h1).sem (iterDC Fc ks m d c) = (Differential.deriv)^[d] ((T.MP (m + 1) h1).sem c) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [iterDC, (T.MP (m + 1) h1).sem_deriv, ih, Function.iterate_succ_apply']

lemma iterate_deriv_intSum {F : Type*} [Field F] [Differential F] {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (x : ι → F) (d : ℕ) :
    (Differential.deriv)^[d] (∑ i ∈ s, (a i : F) * x i) =
      ∑ i ∈ s, (a i : F) * (Differential.deriv)^[d] (x i) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Function.iterate_succ_apply', ← zsmul_eq_mul, Derivation.map_smul, zsmul_eq_mul]

set_option maxHeartbeats 1600000 in
/-- **Independence modulo `Fₘ₊₁`** from the generalized Wronskian certificate `indepWC`. -/
theorem indepWC_sound1 (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (n : ℕ) (hn0 : 0 < n)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0)
    (gls : List (GPoly (LC (m + 1)))) (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ n)
    (u : Fin gls.length → L) (hu : ∀ i, u i ≠ 0)
    (hlog : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (J D : List ℕ) (H : List (List (LC (m + 1)))) (hc : indepWC Fc ks m gls J D H = true) :
    ∀ a : Fin gls.length → ℤ, (∃ c : T.F (m + 1), ∏ i, (u i) ^ (a i) = (c : L)) → a = 0 := by
  classical
  rintro a ⟨c, hc'⟩
  set M1 := T.MPr (m + 1) h1 with hM1
  set z := (MOr Fc ks (m + 1)).zero with hz
  set G : ℕ → ℕ → T.F (m + 1) := fun i j ↦ M1.sem ((gls.getD i []).getD j z) with hG
  have hld : (c : L)′ / c = ∑ i, (a i : L) * ((u i)′ / u i) := by
    rw [← hc', logDeriv_finset_prod _ _ (fun i _ ↦ zpow_ne_zero _ (hu i))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := logDeriv_zpow' (u i) (hu i) (a i)
    simp only [logDeriv] at this
    exact this
  set cd : T.F (m + 1) := c′ / c with hcdd
  have hcdv : (cd : L) = (c : L)′ / c := by
    rw [hcdd, IntermediateField.coe_div, MTower.coe_deriv]
  set b : ℕ → T.F (m + 1) := fun j ↦
    ∑ i : Fin gls.length, (a i : T.F (m + 1)) * G i j - if j = 0 then cd else 0 with hb
  have hsum : ∑ j ∈ Finset.range n, (b j : L) * θ ^ j = 0 := by
    have e1 : ∀ i : Fin gls.length, (u i)′ / u i = ∑ j ∈ Finset.range n, (G i j : L) * θ ^ j :=
      fun i ↦ by rw [← hlog i, T.evθ_list_le m h1 θ _ n (hlen i i.2)]
    have hite : ∑ j ∈ Finset.range n, (((if j = 0 then cd else 0 : T.F (m + 1))) : L) * θ ^ j =
        cd := by
      rw [Finset.sum_eq_single 0 (fun j _ hj ↦ by rw [if_neg hj]; simp)
        (fun h ↦ absurd (Finset.mem_range.mpr hn0) h), if_pos rfl, pow_zero, mul_one]
    simp only [hb, AddSubgroupClass.coe_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hite, hcdv, hld]
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul]
    simp only [e1, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    ring
  have hb0 := hind b hsum
  have hcol : ∀ j, 1 ≤ j → ∑ i : Fin gls.length, (a i : T.F (m + 1)) * G i j = 0 := by
    intro j hj
    by_cases hjn : j < n
    · have := hb0 j hjn
      simp only [hb, if_neg (show j ≠ 0 by omega), sub_zero] at this
      exact this
    · refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp only [hG]
      rw [List.getD_eq_default _ _ (by have := hlen i i.2; omega), M1.sem_zero, mul_zero]
  have hcolD : ∀ j, 1 ≤ j → ∀ d, ∑ i : Fin gls.length, (a i : T.F (m + 1)) *
      (Differential.deriv)^[d] (G i j) = 0 := by
    intro j hj d
    rw [← iterate_deriv_intSum, hcol j hj]
    induction d with
    | zero => rfl
    | succ d ih => rw [Function.iterate_succ_apply', ih, Derivation.map_zero]
  simp only [indepWC, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨hJ, hH⟩ := hc
  set Hs : ℕ → ℕ → T.F (m + 1) := fun p l ↦ M1.sem ((H.getD p []).getD l z) with hHs
  set W : ℕ → ℕ → T.F (m + 1) := fun i p ↦ (Differential.deriv)^[D.getD p 0] (G i (J.getD p 0))
    with hW
  have hinv : ∀ i < gls.length, ∀ l < gls.length, ∑ p ∈ Finset.range gls.length, W i p * Hs p l =
      if i = l then 1 else 0 := by
    intro i hi l hl
    have h := hH i hi l hl
    rw [(T.MP (m + 1) h1).isZero_iff, (T.MP (m + 1) h1).sem_add, (T.MP (m + 1) h1).sem_neg,
      sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      add_neg_eq_zero] at h
    have e2 : (T.MP (m + 1) h1).sem (if i = l then (MO Fc ks (m + 1)).one else
        (MO Fc ks (m + 1)).zero) = if i = l then 1 else 0 := by
      split_ifs
      · exact (T.MP (m + 1) h1).sem_one
      · exact (T.MP (m + 1) h1).sem_zero
    rw [e2] at h
    rw [← h]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [Function.comp_apply, (T.MP (m + 1) h1).sem_mul, hW, hG, hHs, hM1, MPr_sem, hz,
      T.sem_iterDC m h1]
  funext l
  have hl := l.2
  have e : ((a l : ℤ) : T.F (m + 1)) = 0 := by
    have h1' : ((a l : ℤ) : T.F (m + 1)) = ∑ i : Fin gls.length, (a i : T.F (m + 1)) *
        ∑ p ∈ Finset.range gls.length, W i p * Hs p l := by
      rw [Finset.sum_eq_single l (fun i _ hi ↦ by
          rw [hinv i i.2 l hl, if_neg (fun h ↦ hi (Fin.ext h)), mul_zero])
        (fun h ↦ absurd (Finset.mem_univ l) h), hinv l hl l hl, if_pos rfl, mul_one]
    rw [h1']
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have := hcolD (J.getD p 0) (hJ p (Finset.mem_range.mp hp)) (D.getD p 0)
    rw [show ∑ i : Fin gls.length, (a i : T.F (m + 1)) * (W i p * Hs p l) =
        (∑ i : Fin gls.length, (a i : T.F (m + 1)) * W i p) * Hs p l by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring]
    rw [show (∑ i : Fin gls.length, (a i : T.F (m + 1)) * W i p) = 0 from this, zero_mul]
  exact_mod_cast e

/-- `indepWC_sound1` without `0 < n`. -/
theorem indepWC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (n : ℕ)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0)
    (gls : List (GPoly (LC (m + 1)))) (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ n)
    (u : Fin gls.length → L) (hu : ∀ i, u i ≠ 0)
    (hlog : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (J D : List ℕ) (H : List (List (LC (m + 1)))) (hc : indepWC Fc ks m gls J D H = true) :
    ∀ a : Fin gls.length → ℤ, (∃ c : T.F (m + 1), ∏ i, (u i) ^ (a i) = (c : L)) → a = 0 := by
  rcases Nat.eq_zero_or_pos gls.length with hk0 | hk0
  · intro a _; funext i; exact absurd i.2 (by omega)
  rcases Nat.eq_zero_or_pos n with hn | hn0
  · exfalso
    simp only [indepWC, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
    have h00 := hc.2 0 hk0 0 hk0
    rw [(T.MP (m + 1) h1).isZero_iff, (T.MP (m + 1) h1).sem_add, (T.MP (m + 1) h1).sem_neg,
      sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.sum_eq_zero (fun p _ ↦ by
        simp only [Function.comp_apply]
        rw [(T.MP (m + 1) h1).sem_mul, T.sem_iterDC m h1, List.getD_eq_default (gls.getD 0 [])
          _ (by have := hlen 0 hk0; omega), ← MPr_sem, (T.MPr (m + 1) h1).sem_zero,
          Function.iterate_fixed (Derivation.map_zero _), zero_mul])] at h00
    simp [(T.MP (m + 1) h1).sem_one] at h00
  exact T.indepWC_sound1 m h1 θ n hn0 hind gls hlen u hu hlog J D H hc

/-- **Soundness of the independence certificate**: no product `∏ uᵢ^{aᵢ}` with `a ≠ 0` lies in
`Fₘ`. -/
theorem indepC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (n : ℕ)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0)
    (gls : List (GPoly (LC (m + 1)))) (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ n)
    (u : Fin gls.length → L) (hu : ∀ i, u i ≠ 0)
    (hlog : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (J : List ℕ) (H : List (List (LC (m + 1)))) (hc : indepC Fc ks m gls J H = true) :
    ∀ a : Fin gls.length → ℤ, (∃ c : T.F m, ∏ i, (u i) ^ (a i) = (c : L)) → a = 0 := by
  rintro a ⟨c, hc'⟩
  exact T.indepWC_sound m h1 θ n hind gls hlen u hu hlog J _ H hc a
    ⟨⟨c, T.le_succ m c.2⟩, hc'⟩

set_option maxHeartbeats 4000000 in
/-- **`⇐`** (several places at infinity, any solver). -/
theorem nk_sufficientInf (m : ℕ) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m) (wD bD : T.F m) (S : T.SolverSpec m h1.of_succ wD bD solve)
    (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTL Fc ks m solve (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gls = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind' : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact hind
  have hiff := T.exactTL_correct m h1 htr solve wD bD S (nkPC Fc ks m Pp) _ θ hP hind' Tc Ti gls
    res hres
  obtain ⟨c, Y, hY⟩ := hiff.mp hr
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set u : ℕ → L := fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) with hu
  have hui : ∀ i < gls.length, u i ≠ 0 ∧ T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i := by
    intro i hi
    obtain ⟨huv, hgl, -, -⟩ := unitsC_spec hU i hi
    have huvL := T.unitC_sound m h1 θ Pp _ _ hP huv
    exact ⟨left_ne_zero_of_mul_eq_one huvL, T.logDerChk_sound m h1 θ Pp _ _ _ dθ wθ hP huvL hgl⟩
  have hg : ∑ j ∈ Finset.range Pp.length, (∑ i ∈ Finset.range gls.length, algebraMap Cc L (c i) *
      ((M1.sem ((gls.getD i []).getD j O1.zero) : T.F (m + 1)) : L)) * θ ^ j =
      ∑ i ∈ Finset.range gls.length, algebraMap Cc L (c i) * logDeriv (u i) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [logDeriv, ← (hui i hi').2, T.evθ_list_le m h1 θ _ Pp.length (unitsC_spec hU i hi').2.2.1,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlen] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRest m h1 Pp.length hn0] at hY
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ +
          ((List.range gls.length).map fun i ↦ algebraMap Cc L (c i) * logDeriv (u i)).sum by
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, hY]; ring]
  refine (hq.add_in (hasElementaryIntegralIn_deriv _)).add_in ?_
  exact hasElementaryIntegralIn_logSum (fun i ↦ algebraMap Cc L (c i)) u (List.range gls.length)
    (fun i hi ↦ ⟨by rw [deriv_algebraMap, T.hC, map_zero], (hui i (List.mem_range.mp hi)).1⟩)

end MTower

end Curves.MT
