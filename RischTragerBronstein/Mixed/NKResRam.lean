import RischTragerBronstein.Mixed.NKResCodes

/-!
# Zero residues at ramified places at infinity

A single slope `s/e` at infinity: along `t = T^{−e}` the curve `P(t, θ)` becomes
`P(T^{−e}, θ)`, i.e. the expanded curve `P(xᵉ, θ)` along `x = T⁻¹` (`infSub_comp_expand`). If the
inverted expanded polynomial has `n` distinct simple residual roots in `Fₘ`, the Hensel roots give
a branch system with `N = e` (`zero_res_ram`), and the residues are the coefficients at `T^e`:
`cₖ = ∑ⱼ ∑ᵢ f̃ⱼᵢ [T^{e+i+sj}] Θ̃ₖʲ` with `f̃ⱼ = fⱼ(Tᵉ)` (`splitResRamC`: the certificate
`splitResCkN` on the expanded codes, `expandGC`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section CoeffN

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K]

/-- **The coefficient at `T^N` along a split root**, from a truncation of the inverted root. -/
theorem coeff_eval_inf_splitN (Q : C[X][X]) (N s M : ℕ) (Θ Θt : PowerSeries K)
    (hX : (PowerSeries.X : PowerSeries K) ^ M ∣ Θ - Θt)
    (hM : ∀ j ≤ Q.natDegree, N + (Q.coeff j).natDegree + s * j < M) :
    ((Q.map (infSub (K := K) 1)).eval (ofPowerSeries ℤ K Θ * single (-(s : ℤ)) 1)).coeff (N : ℤ) =
      ∑ j ∈ Finset.range (Q.natDegree + 1), ∑ i ∈ Finset.range ((Q.coeff j).natDegree + 1),
        algebraMap C K ((Q.coeff j).coeff i) * PowerSeries.coeff (N + i + s * j) (Θt ^ j) := by
  rw [eval_map, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [infSub_eq_sum, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ (Q.coeff j).natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : (ofPowerSeries ℤ K Θ * single (-(s : ℤ)) 1) ^ j =
      ofPowerSeries ℤ K (Θ ^ j) * single (-((s * j : ℕ) : ℤ)) 1 := by
    rw [mul_pow, map_pow, HahnSeries.single_pow, one_pow]
    congr 2
    push_cast; ring
  rw [hpow, ← mul_assoc, mul_comm (single _ _), mul_assoc, HahnSeries.single_mul_single, mul_one]
  rw [show (-(((1 : ℕ) : ℤ) * (i : ℤ)) + -(((s * j : ℕ)) : ℤ)) = -((i + s * j : ℕ) : ℤ) by
    push_cast; ring]
  have key := HahnSeries.coeff_mul_single_add (r := algebraMap C K ((Q.coeff j).coeff i))
    (x := ofPowerSeries ℤ K (Θ ^ j)) (a := ((N + i + s * j : ℕ) : ℤ)) (b := -((i + s * j : ℕ) : ℤ))
  rw [show ((N + i + s * j : ℕ) : ℤ) + -((i + s * j : ℕ) : ℤ) = N by push_cast; ring] at key
  rw [key, ofPowerSeries_apply_coeff, mul_comm]
  congr 1
  have hdj : (PowerSeries.X : PowerSeries K) ^ M ∣ Θ ^ j - Θt ^ j :=
    hX.trans (sub_dvd_pow_sub_pow _ _ _)
  have hlt : N + i + s * j < M := lt_of_le_of_lt (by omega) (hM j hj')
  have h0 := (PowerSeries.X_pow_dvd_iff.mp hdj) (N + i + s * j) hlt
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- `x ↦ T^{−e}` is `x ↦ xᵉ` followed by `x ↦ T⁻¹`. -/
lemma infSub_comp_expand (e : ℕ) :
    (infSub (C := C) (K := K) e) = (infSub 1).comp (expand C e : C[X] →+* C[X]) := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · simp [infSub]
  · simp only [RingHom.comp_apply, infSub, coe_eval₂RingHom, eval₂_X]
    rw [show ((expand C e : C[X] →+* C[X]) X) = X ^ e from expand_X e, eval₂_X_pow,
      HahnSeries.single_pow, one_pow]
    congr 1
    push_cast; simp

end CoeffN

section PolyN

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K] [Differential C]
  [Differential K] [IsAlgClosed K]

/-- **Zero residues at `T^N` along the split branch system of `P` above infinity**, certified by
truncations (polynomial form of `zero_res_split`). -/
theorem zero_res_polyN (P : C[X][X]) (hPm : P.Monic) (n N s M : ℕ) (hn : P.natDegree = n)
    (hdeg : ∀ i ≤ n, (P.coeff i).natDegree ≤ (n - i) * s) (γ : Fin n → C)
    (hγi : Function.Injective γ)
    (hγ : ∀ k, (fibreAt (K := K) (invPS n s P) 0).eval (algebraMap C K (γ k)) = 0)
    (hγ' : ∀ k, (fibreAt (K := K) (derivative (invPS n s P)) 0).eval (algebraMap C K (γ k)) ≠ 0)
    (Θt : Fin n → C[X]) (hΘ0 : ∀ k, (Θt k).coeff 0 = γ k)
    (hΘM : ∀ k, (PowerSeries.X : PowerSeries K) ^ M ∣
      (fibrePS (K := K) (invPS n s P) 0).eval (((Θt k).map (algebraMap C K) : K[X]) : PowerSeries K))
    (Q : C[X][X]) (hM : ∀ j ≤ Q.natDegree, N + (Q.coeff j).natDegree + s * j < M)
    (z : Fin n → C)
    (hz : ∀ k, (z k)′ = ∑ j ∈ Finset.range (Q.natDegree + 1),
      ∑ i ∈ Finset.range ((Q.coeff j).natDegree + 1),
        (Q.coeff j).coeff i * ((Θt k) ^ j).coeff (N + i + s * j))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) :
    ∃ li : List (LaurentSeries K), P.map (infSub (K := K) 1) =
      (li.map fun r ↦ X - Polynomial.C r).prod ∧
      ∀ r ∈ li, ∃ β : K, ((Q.map (infSub (K := K) 1)).eval r).coeff (N : ℤ) = β′ := by
  classical
  have hγK : Function.Injective fun k ↦ algebraMap C K (γ k) := fun i j h ↦
    hγi ((algebraMap C K).injective h)
  obtain ⟨Θ, hΘ, hsplit⟩ := split_inf_inv P n s hPm hn hdeg (fun k ↦ algebraMap C K (γ k))
    hγK hγ hγ'
  set r : Fin n → LaurentSeries K := fun k ↦ ofPowerSeries ℤ K (Θ k) * single (-(s : ℤ)) 1 with hr
  refine ⟨List.ofFn r, by rw [hsplit, List.map_ofFn, List.prod_ofFn]; rfl, ?_⟩
  intro r0 hr0
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr0
  refine ⟨algebraMap C K (z k), ?_⟩
  set Θk : PowerSeries K := (((Θt k).map (algebraMap C K) : K[X]) : PowerSeries K) with hΘk
  have hagree : (PowerSeries.X : PowerSeries K) ^ M ∣ Θ k - Θk := by
    refine hensel_trunc _ (Θ k) Θk (hΘ k).1 ?_ ?_ M (hΘM k)
    · rw [(hΘ k).2, hΘk, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        Polynomial.coeff_map, hΘ0]
    · rw [derivative_fibrePS, fibrePS_eval_const', hΘk, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        Polynomial.coeff_coe, Polynomial.coeff_map, hΘ0]
      exact hγ' k
  rw [coeff_eval_inf_splitN Q N s M (Θ k) Θk hagree hM, hK, hz k, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, hΘk, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← Polynomial.map_pow,
    Polynomial.coeff_map]

end PolyN

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Tower.PrimN GTors Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The code of `p(Xᵉ)`. -/
def expandGC (m e : ℕ) (p : GPoly (LC m)) : GPoly (LC m) :=
  if p.isEmpty then [] else
  (List.range ((p.length - 1) * e + 1)).map fun k ↦
    if k % e = 0 then p.getD (k / e) (MO Fc ks m).zero else (MO Fc ks m).zero

/-- The residue value at `T^N`: `∑ⱼ ∑ᵢ fⱼᵢ [T^{N+i+sj}] Θʲ`. -/
def resInfCN (m N s n : ℕ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) : LC m :=
  lsumC (MO Fc ks m) ((List.range n).map fun j ↦
    lsumC (MO Fc ks m) ((List.range (fp.getD j []).length).map fun i ↦
      (MO Fc ks m).mul ((fp.getD j []).getD i (MO Fc ks m).zero)
        ((powG (MO Fc ks m) Θ j).getD (N + i + s * j) (MO Fc ks m).zero)))

/-- The zero-residue certificate with the residue at `T^N`. -/
def splitResCkN (m N s M : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m))
    (Θs : List (GPoly (LC m))) (fp : List (GPoly (LC m))) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  let R := residualC Fc ks m s Pp
  decide (γs.length = n) &&
  (List.range n).all (fun i ↦ decide ((Pp.getD i []).length ≤ (n - i) * s + 1)) &&
  (List.range n).all (fun k ↦ O.isZero (evalLC Fc ks m R (γs.getD k O.zero)) &&
    !O.isZero (evalLC Fc ks m (GPoly.derivX O R) (γs.getD k O.zero))) &&
  (List.range n).all (fun k ↦ (List.range n).all fun l ↦
    decide (k = l) || !O.isZero (O.add (γs.getD k O.zero) (O.neg (γs.getD l O.zero)))) &&
  (List.range n).all (fun k ↦
    O.isZero (O.add ((Θs.getD k []).getD 0 O.zero) (O.neg (γs.getD k O.zero))) &&
    truncOKC Fc ks m M (evalPolyC Fc ks m (invCoeffsC Fc ks m s Pp) (Θs.getD k []))) &&
  (List.range n).all (fun j ↦ decide (N + max 1 (fp.getD j []).length + s * j ≤ M)) &&
  (List.range n).all (fun k ↦ derivTestC Fc ks lv m (resInfCN Fc ks m N s n fp (Θs.getD k [])))

/-- **The ramified zero-residue certificate**: `splitResCkN` at `T^e` on the expanded codes. -/
def splitResRamC (m e s M : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m))
    (Θs : List (GPoly (LC m))) (fp : List (GPoly (LC m))) : Bool :=
  splitResCkN Fc ks lv m e s M (Pp.map (expandGC Fc ks m e)) γs Θs (fp.map (expandGC Fc ks m e))

end Codes

section Sem

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {m : ℕ} {F : Type*} [Field F] [Differential F] (M : CField (LC m) F (MO Fc ks m))

lemma sem_resInfCN (N s n : ℕ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) :
    M.sem (resInfCN Fc ks m N s n fp Θ) = ∑ j ∈ Finset.range n,
      ∑ i ∈ Finset.range (fp.getD j []).length, M.sem ((fp.getD j []).getD i (MO Fc ks m).zero) *
        ((GPoly.toPoly M Θ) ^ j).coeff (N + i + s * j) := by
  unfold resInfCN
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.comp_apply]
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply]
  rw [M.sem_mul]
  congr 1
  rw [← coeff_toPoly_sem, toPoly_powGXP]

lemma toPoly_expandGC (e : ℕ) (he : 0 < e) (p : GPoly (LC m)) :
    GPoly.toPoly M (expandGC Fc ks m e p) = expand F e (GPoly.toPoly M p) := by
  by_cases hp0 : p = []
  · subst hp0; simp [expandGC, GPoly.toPoly_nil]
  have hne : p.isEmpty = false := by simpa using hp0
  have hL : 0 < p.length := List.length_pos_of_ne_nil hp0
  ext k
  rw [coeff_toPoly_sem, coeff_expand he]
  by_cases hk : k < (p.length - 1) * e + 1
  · rw [expandGC, hne, if_neg (by simp), List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk]
    simp only [Option.map_some, Option.getD_some]
    by_cases hd : e ∣ k
    · rw [if_pos (Nat.mod_eq_zero_of_dvd hd), if_pos hd, coeff_toPoly_sem]
    · rw [if_neg (fun h ↦ hd (Nat.dvd_of_mod_eq_zero h)), if_neg hd, M.sem_zero]
  · rw [List.getD_eq_default _ _ (by rw [expandGC, hne, if_neg (by simp)]; simp; omega), M.sem_zero]
    split_ifs with hd
    · rw [coeff_toPoly_sem, List.getD_eq_default _ _ ?_, M.sem_zero]
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ he]
      have h1 : (p.length - 1) * e < c * e := by
        rw [mul_comm c e]; omega
      have := Nat.lt_of_mul_lt_mul_right h1
      omega
    · rfl

lemma length_expandGC (e : ℕ) (p : GPoly (LC m)) (hp : p ≠ []) :
    (expandGC Fc ks m e p).length = (p.length - 1) * e + 1 := by
  rw [expandGC, if_neg (by simpa using hp), List.length_map, List.length_range]

lemma getD_map_expandGC (e : ℕ) (l : List (GPoly (LC m))) (i : ℕ) :
    (l.map (expandGC Fc ks m e)).getD i [] = expandGC Fc ks m e (l.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp [expandGC]

lemma aPoly_expandGC (e : ℕ) (he : 0 < e) (Pp : List (GPoly (LC m))) (i : ℕ) :
    aPoly M (Pp.map (expandGC Fc ks m e)) i = expand F e (aPoly M Pp i) := by
  rw [aPoly, aPoly, getD_map_expandGC, toPoly_expandGC M e he]

end Sem

section Main

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m} {m : ℕ}
variable {F L' K : Type*} [Field F] [Differential F] [CharZero F]
  [Field L'] [CharZero L'] [Algebra F L'] [Differential L'] [DifferentialAlgebra F L']
  [Field K] [CharZero K] [Algebra F K] [Differential K] [IsAlgClosed K]

/-- **A passing certificate `splitResCkN` gives zero residues at `T^N`** (polynomial form). -/
theorem zero_res_codesN (M : CField (LC m) F (MO Fc ks m))
    {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* F)
    (hrde : RdeSpecK ι M (M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    (hK : ∀ c : F, (algebraMap F K c)′ = algebraMap F K c′)
    (Pp : List (GPoly (LC m))) (N s Mn : ℕ) (γs : List (LC m)) (Θs fp : List (GPoly (LC m)))
    (hck : splitResCkN Fc ks lv m N s Mn Pp γs Θs fp = true) (hn0 : 0 < Pp.length) :
    ∃ li : List (LaurentSeries K), (polyF (aPoly M Pp) Pp.length).map (infSub (K := K) 1) =
      (li.map fun r ↦ X - Polynomial.C r).prod ∧
      ∀ r ∈ li, ∃ β : K, (((∑ j ∈ Finset.range Pp.length,
          Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j).map (infSub (K := K) 1)).eval r).coeff
            (N : ℤ) = β′ := by
  classical
  simp only [splitResCkN, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨⟨⟨⟨hγlen, hlen⟩, hroots⟩, hdist⟩, hΘ⟩, hMb⟩, hder⟩ := hck
  have hlen' : ∀ i < Pp.length, (Pp.getD i []).length ≤ (Pp.length - i) * s + 1 := hlen
  set P := polyF (aPoly M Pp) Pp.length with hP
  set γ : Fin Pp.length → F := fun k ↦ M.sem (γs.getD k (MO Fc ks m).zero) with hγ
  set Θt : Fin Pp.length → F[X] := fun k ↦ GPoly.toPoly M (Θs.getD k []) with hΘt
  have hSn : P.natDegree = Pp.length := by rw [hP, polyF_natDegree]
  have hdeg : ∀ i ≤ Pp.length, (P.coeff i).natDegree ≤ (Pp.length - i) * s := by
    intro i hi
    rcases lt_or_eq_of_le hi with hi | rfl
    · rw [hP, polyF_coeff _ _ _ hi]; exact natDegree_aPoly_le M Pp s i (hlen' i hi)
    · have := polyF_monic (aPoly M Pp) Pp.length
      rw [Monic, Polynomial.leadingCoeff, polyF_natDegree] at this
      rw [hP, this]; simp
  have hγi : Function.Injective γ := by
    intro k l hkl
    by_contra hne
    have h := (hdist k k.2 l l.2).resolve_left (fun h ↦ hne (Fin.ext h))
    rw [Bool.eq_false_iff] at h
    apply h
    rw [M.isZero_iff, M.sem_add, M.sem_neg]
    simp only [hγ] at hkl
    rw [hkl, add_neg_cancel]
  have hfib := fibreAt_invPS_polyF (K := K) M Pp s hlen'
  have hγroot : ∀ k : Fin Pp.length,
      (fibreAt (K := K) (invPS Pp.length s P) 0).eval (algebraMap F K (γ k)) = 0 := by
    intro k
    rw [hP, hfib, eval_map, eval₂_hom, hγ, ← sem_evalLC,
      (M.isZero_iff _).mp (hroots k k.2).1, map_zero]
  have hγroot' : ∀ k : Fin Pp.length,
      (fibreAt (K := K) (derivative (invPS Pp.length s P)) 0).eval (algebraMap F K (γ k)) ≠ 0 := by
    intro k
    rw [hP, fibreAt_derivative, hfib, Polynomial.derivative_map,
      eval_map, eval₂_hom, hγ, ← GPoly.toPoly_derivX, ← sem_evalLC]
    intro h0
    have := (map_eq_zero_iff _ (algebraMap F K).injective).mp h0
    have h2 := (hroots k k.2).2
    rw [Bool.eq_false_iff] at h2
    exact h2 ((M.isZero_iff _).mpr this)
  have hΘ0 : ∀ k : Fin Pp.length, (Θt k).coeff 0 = γ k := by
    intro k
    rw [hΘt, coeff_toPoly_sem]
    have := (M.isZero_iff _).mp (hΘ k k.2).1
    rw [M.sem_add, M.sem_neg, add_neg_eq_zero] at this
    exact this
  have hΘM : ∀ k : Fin Pp.length, (PowerSeries.X : PowerSeries K) ^ Mn ∣
      (fibrePS (K := K) (invPS Pp.length s P) 0).eval
        (((Θt k).map (algebraMap F K) : K[X]) : PowerSeries K) := by
    intro k
    rw [fibrePS_eval_coe, hP, hΘt, eval_invPS_polyF M Pp s hlen']
    exact dvd_of_truncOKC M Mn _ (hΘ k k.2).2
  set Q : F[X][X] := ∑ j ∈ Finset.range Pp.length,
    Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j with hQ
  have hQc : ∀ j, Q.coeff j = if j < Pp.length then GPoly.toPoly M (fp.getD j []) else 0 := by
    intro j
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hQd : Q.natDegree < Pp.length := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := Pp.length - 1) fun j hj ↦ ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
  have hM : ∀ j ≤ Q.natDegree, N + (Q.coeff j).natDegree + s * j < Mn := by
    intro j hj
    have hjn : j < Pp.length := lt_of_le_of_lt hj hQd
    rw [hQc, if_pos hjn]
    have h1 := natDegree_toPoly_le M (fp.getD j [])
    have h2 := hMb j hjn
    omega
  have hz : ∀ k : Fin Pp.length, ∃ z : F,
      z′ = M.sem (resInfCN Fc ks m N s Pp.length fp (Θs.getD k [])) :=
    fun k ↦ derivTestC_sound ι M hrde _ (hder k k.2)
  choose z hz using hz
  refine zero_res_polyN P (polyF_monic _ _) Pp.length N s Mn hSn hdeg γ hγi hγroot hγroot' Θt hΘ0
    hΘM Q hM z (fun k ↦ ?_) hK
  rw [hz k, sem_resInfCN]
  simp only [hΘt]
  have hstep : ∀ j ∈ Finset.range Pp.length,
      ∑ i ∈ Finset.range (fp.getD j []).length, M.sem ((fp.getD j []).getD i (MO Fc ks m).zero) *
        ((GPoly.toPoly M (Θs.getD k [])) ^ j).coeff (N + i + s * j) =
      ∑ i ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff i *
        ((GPoly.toPoly M (Θs.getD k [])) ^ j).coeff (N + i + s * j) := by
    intro j hj
    rw [hQc, if_pos (Finset.mem_range.mp hj)]
    exact sum_toPoly_coeff M _ _
  rw [Finset.sum_congr rfl hstep]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (show Q.natDegree + 1 ≤ Pp.length by omega))
    fun j _ hnj ↦ ?_
  rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnj)]
  simp

/-- **Zero residues at a ramified place at infinity**: if the ramified certificate passes, then
along the branch system with `N = e` above infinity every residue of `f = ∑ⱼ fⱼ θʲ` vanishes. -/
theorem zero_res_ram (S : CurveData F L') (M : CField (LC m) F (MO Fc ks m))
    {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* F)
    (hrde : RdeSpecK ι M (M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    (hK : ∀ c : F, (algebraMap F K c)′ = algebraMap F K c′)
    (Pp : List (GPoly (LC m))) (hSF : S.F = polyF (aPoly M Pp) Pp.length)
    (e : ℕ) (he : 0 < e) (s Mn : ℕ) (γs : List (LC m)) (Θs fp : List (GPoly (LC m)))
    (hck : splitResRamC Fc ks lv m e s Mn Pp γs Θs fp = true) (hn0 : 0 < Pp.length) :
    ∃ li : List (LaurentSeries K), ∃ hli : S.F.map (infSub (K := K) e) =
      (li.map fun r ↦ X - Polynomial.C r).prod,
      ∀ r (hr : r ∈ li), ∃ β : K, (S.embG (infSub e) (infSub_injective e he) r
        (S.root_of_mem hli hr) (S.evT (∑ j ∈ Finset.range Pp.length,
          Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j))).coeff (e : ℤ) = β′ := by
  classical
  set Ppe := Pp.map (expandGC Fc ks m e) with hPpe
  set fpe := fp.map (expandGC Fc ks m e) with hfpe
  have hlen : Ppe.length = Pp.length := by rw [hPpe, List.length_map]
  obtain ⟨li, hli, hres⟩ := zero_res_codesN (K := K) M ι hrde hK Ppe e s Mn γs Θs fpe hck
    (by rw [hlen]; exact hn0)
  have hinf := infSub_comp_expand (C := F) (K := K) e
  have hPe : (polyF (aPoly M Ppe) Ppe.length) = S.F.map (expand F e : F[X] →+* F[X]) := by
    rw [hSF, hlen]
    simp only [polyF, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hPpe, aPoly_expandGC M e he]
    rfl
  have hQe : (∑ j ∈ Finset.range Ppe.length,
      Polynomial.C (GPoly.toPoly M (fpe.getD j [])) * X ^ j) =
      (∑ j ∈ Finset.range Pp.length, Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j).map
        (expand F e : F[X] →+* F[X]) := by
    rw [hlen]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, hfpe, getD_map_expandGC, toPoly_expandGC M e he]
    rfl
  have hli' : S.F.map (infSub (K := K) e) = (li.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hinf, ← Polynomial.map_map, ← hPe, hli]
  refine ⟨li, hli', fun r hr ↦ ?_⟩
  obtain ⟨β, hβ⟩ := hres r hr
  refine ⟨β, ?_⟩
  rw [S.embG_evT, hinf, ← Polynomial.map_map, ← hQe]
  exact hβ

end Main

end Curves.MT
