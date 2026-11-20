import RischTragerBronstein.Mixed.KRNorm
import RischTragerBronstein.Mixed.KRIrr

/-!
# The norm of a witness always descends to `Kₘ`

For the cyclotomic code field `Kₘ(ζ)` (`ζ` a root of `Φₙ`, irreducible over `Kₘ`) and a primitive
`n`-th root of unity `ω` in an algebraic closure `L` of `Kₘ`, the embeddings `ψ_v : ζ ↦ ωᵛ`
(`v` a unit modulo `n`) satisfy `ψ_v ∘ τ_u = ψ_{vu}` (`psiZ_tauN`). The coefficients of the norm
`∏_u τ_u W` are therefore fixed by every `ψ_v` (`psiZ_normNF`), and an element fixed by all the
`ψ_v` has a constant representation (`length_le_one_of_fixed`: a polynomial of degree `< φ(n)`
taking one value at the `φ(n)` distinct points `ωᵛ` is constant). Hence `descendNF (normNF W)`
always answers (`descendNF_normNF_isSome`).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
  [Fact (Irreducible (toPoly (cycK Fc m n)))]

/-- The algebraic closure of the code field. -/
abbrev LK : Type := AlgebraicClosure (KF Fc m)

lemma exists_prim_LK (hn : 0 < n) : ∃ ω : LK Fc m, IsPrimitiveRoot ω n := by
  haveI : NeZero (n : LK Fc m) := ⟨by exact_mod_cast hn.ne'⟩
  have hdeg : (cyclotomic n (LK Fc m)).degree ≠ 0 := by
    rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ω, (isRoot_cyclotomic_iff).mp hω⟩

lemma cycK_root_LK (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) :
    (toPoly (cycK Fc m n)).eval₂ (algebraMap (KF Fc m) (LK Fc m)) ω = 0 := by
  rw [← eval_map, toPoly_cycK Fc m n hn, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    map_cyclotomic]
  exact hω.isRoot_cyclotomic hn

/-- **`ψ : Kₘ(ζ) → L`**, `ζ ↦ ω`. -/
noncomputable def psiZ (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) :
    NFz Fc m n →+* LK Fc m :=
  (AdjoinRoot.lift (algebraMap (KF Fc m) (LK Fc m)) ω (cycK_root_LK Fc m n hn ω hω)).comp
    (NFK.toARHom _)

lemma psiZ_val (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) (a : NFz Fc m n) :
    psiZ Fc m n hn ω hω a = (toPoly a.1).eval₂ (algebraMap (KF Fc m) (LK Fc m)) ω := by
  simp only [psiZ, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ (toPoly a.1)) = _
  rw [AdjoinRoot.lift_mk]

lemma psiZ_mk (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) (l : CPoly (KF Fc m)) :
    psiZ Fc m n hn ω hω (NFK.mk _ l) = (toPoly l).eval₂ (algebraMap (KF Fc m) (LK Fc m)) ω := by
  simp only [psiZ, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (NFK.toAR _ (NFK.mk _ l)) = _
  rw [NFK.toAR_mk, AdjoinRoot.lift_mk]

/-- **The Galois action**: `ψ_ω ∘ τ_u = ψ_{ωᵘ}`. -/
lemma psiZ_tauN (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) (u : ℕ)
    (hu : Nat.Coprime u n) (hu0 : 0 < u) (a : NFz Fc m n) :
    psiZ Fc m n hn ω hω (tauN Fc m n u a) = psiZ Fc m n hn (ω ^ u) (hω.pow_of_coprime u hu) a := by
  rw [tauN, psiZ_mk, psiZ_val, toPoly_expandC u hu0, ← eval_map, ← eval_map,
    Polynomial.map_expand, expand_eval]


/-- The units modulo `n` as a finset. -/
def unitsF (n : ℕ) : Finset ℕ := (Finset.range n).filter fun u ↦ Nat.Coprime u n

lemma card_unitsF (n : ℕ) : (unitsF n).card = n.totient := by
  rw [unitsF, Nat.totient]
  congr 1
  ext u; simp [Nat.coprime_comm]

/-- **An element fixed by all the embeddings has a constant representation.** -/
lemma length_le_one_of_fixed (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n)
    (a : NFz Fc m n)
    (hfix : ∀ v (hv : v ∈ unitsF n), psiZ Fc m n hn (ω ^ v) (hω.pow_of_coprime v
      (Finset.mem_filter.mp hv).2) a = psiZ Fc m n hn ω hω a) :
    a.1.length ≤ 1 := by
  classical
  set c := psiZ Fc m n hn ω hω a
  set P : (LK Fc m)[X] := (toPoly a.1).map (algebraMap (KF Fc m) (LK Fc m)) - C c with hP
  have hdeg : (toPoly a.1).natDegree < n.totient ∨ toPoly a.1 = 0 := by
    have h := NFK.degree_val (cycK Fc m n) a
    rw [toPoly_cycK Fc m n hn, degree_map, degree_cyclotomic] at h
    by_cases h0 : toPoly a.1 = 0
    · exact Or.inr h0
    · left; rw [degree_eq_natDegree h0] at h; exact_mod_cast h
  have hP0 : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (ι := unitsF n)
      (f := fun v ↦ ω ^ (v : ℕ)) ?_ (fun v ↦ ?_) ?_
    · intro v w hvw
      have hv := (Finset.mem_filter.mp v.2).1
      have hw := (Finset.mem_filter.mp w.2).1
      exact Subtype.ext (hω.pow_inj (Finset.mem_range.mp hv) (Finset.mem_range.mp hw) hvw)
    · have := hfix v v.2
      simp only [hP, eval_sub, eval_C, eval_map]
      rw [← psiZ_val Fc m n hn (ω ^ (v : ℕ)) (hω.pow_of_coprime _ (Finset.mem_filter.mp v.2).2),
        this, sub_self]
    · rw [Fintype.card_coe, card_unitsF]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      rw [natDegree_C, natDegree_map_eq_of_injective (algebraMap (KF Fc m) (LK Fc m)).injective]
      rcases hdeg with h | h
      · omega
      · rw [h, natDegree_zero]; simpa using hn
  have hc : (toPoly a.1).map (algebraMap (KF Fc m) (LK Fc m)) = C c := sub_eq_zero.mp hP0
  have hnd : (toPoly a.1).natDegree = 0 := by
    rw [← natDegree_map_eq_of_injective (algebraMap (KF Fc m) (LK Fc m)).injective, hc, natDegree_C]
  have htrim : CPoly.trim a.1 = a.1 := by
    have := a.2
    rw [NFK.norm] at this
    rw [← this, CPoly.trim_trim]
  by_cases hne : CPoly.trim a.1 = []
  · rw [htrim] at hne; rw [hne]; simp
  · have := CPoly.length_trim hne
    rw [htrim] at this
    omega


/-- `ψ` at any point (defaulting to `ω` off the primitive roots). -/
noncomputable def psiR (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) (x : LK Fc m) :
    NFz Fc m n →+* LK Fc m :=
  open Classical in
  if h : IsPrimitiveRoot x n then psiZ Fc m n hn x h else psiZ Fc m n hn ω hω

lemma psiR_eq (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) (x : LK Fc m)
    (hx : IsPrimitiveRoot x n) : psiR Fc m n hn ω hω x = psiZ Fc m n hn x hx := by
  rw [psiR, dif_pos hx]

lemma unitsN_toFinset (n : ℕ) : (unitsN n).toFinset = unitsF n := by
  ext u; simp [unitsN, unitsF]

lemma coprime_mod_of (a n : ℕ) (h : Nat.Coprime a n) : Nat.Coprime (a % n) n := by
  rw [Nat.Coprime, ← Nat.gcd_rec n a, Nat.gcd_comm]; exact h

lemma coprime_of_mul_mod_one {a b n : ℕ} (h : a * b % n = 1) : Nat.Coprime b n := by
  rw [Nat.Coprime]
  have hd : Nat.gcd b n ∣ a * b % n := by
    rw [Nat.mod_def]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left b n) a)
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_right b n) _)
  rw [h] at hd
  exact Nat.dvd_one.mp hd

/-- **The norm is fixed by every embedding.** -/
lemma psiZ_normNF (hn : 1 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) (W : BPoly (NFz Fc m n))
    (v : ℕ) (hv : v ∈ unitsF n) :
    (toB (normNF Fc m n W)).map (mapRingHom (psiR Fc m n (by omega) ω hω (ω ^ v))) =
      (toB (normNF Fc m n W)).map (mapRingHom (psiR Fc m n (by omega) ω hω ω)) := by
  classical
  have hn0 : 0 < n := by omega
  have hvc : Nat.Coprime v n := (Finset.mem_filter.mp hv).2
  -- each factor
  have hfac : ∀ (x : LK Fc m) (hx : IsPrimitiveRoot x n) (u : ℕ) (hu : u ∈ unitsN n),
      (toB (W.map fun c ↦ c.map (tauN Fc m n u))).map (mapRingHom (psiR Fc m n hn0 ω hω x)) =
        (toB W).map (mapRingHom (psiR Fc m n hn0 ω hω (x ^ u))) := by
    intro x hx u hu
    have hu' := List.mem_filter.mp hu
    have huc : Nat.Coprime u n := by simpa using hu'.2
    have hu0 : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · rw [h, Nat.coprime_zero_left] at huc; omega
      · exact h
    refine toB_map_fun _ _ _ W fun c _ a _ ↦ ?_
    rw [psiR_eq _ _ _ hn0 ω hω x hx, psiR_eq _ _ _ hn0 ω hω _ (hx.pow_of_coprime u huc),
      psiZ_tauN Fc m n hn0 x hx u huc hu0]
  rw [normNF_eq, toB_foldr_mulB, List.map_map, Polynomial.map_list_prod,
    Polynomial.map_list_prod, List.map_map, List.map_map]
  have e1 : ∀ x (hx : IsPrimitiveRoot x n), ((unitsN n).map ((Polynomial.map
      (mapRingHom (psiR Fc m n hn0 ω hω x))) ∘ (toB ∘ fun u ↦ W.map fun c ↦ c.map (tauN Fc m n u)))) =
      (unitsN n).map fun u ↦ (toB W).map (mapRingHom (psiR Fc m n hn0 ω hω (x ^ u))) :=
    fun x hx ↦ List.map_congr_left fun u hu ↦ hfac x hx u hu
  rw [e1 _ (hω.pow_of_coprime v hvc), e1 _ hω]
  have hnd : (unitsN n).Nodup := (List.nodup_range).filter _
  rw [← List.prod_toFinset _ hnd, ← List.prod_toFinset _ hnd, unitsN_toFinset]
  -- reindex `u ↦ v u mod n`
  refine Finset.prod_nbij (fun u ↦ (v * u) % n) (fun u hu ↦ ?_) (fun u hu w hw h ↦ ?_)
    (fun w hw ↦ ?_) (fun u hu ↦ ?_)
  · have hu := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hn0),
      coprime_mod_of _ _ (Nat.coprime_mul_iff_left.mpr ⟨hvc, hu.2⟩)⟩
  · have hu' := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    have hw' := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
    have h2 : v * u ≡ v * w [MOD n] := h
    have := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hvc) h2
    exact Nat.ModEq.eq_of_lt_of_lt this hu' hw'
  · -- surjectivity: `u = v⁻¹ w`
    have hw' := Finset.mem_filter.mp hw
    obtain ⟨vi, hvi⟩ := Nat.exists_mul_mod_eq_one_of_coprime hvc hn
    refine ⟨(vi * w) % n, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hn0),
        coprime_mod_of _ _ (Nat.coprime_mul_iff_left.mpr ⟨coprime_of_mul_mod_one hvi.2, hw'.2⟩)⟩
    · show (v * ((vi * w) % n)) % n = w
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hvi.2, one_mul,
        Nat.mod_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hw'.1)]
  · show (toB W).map (mapRingHom (psiR Fc m n hn0 ω hω ((ω ^ v) ^ u))) =
      (toB W).map (mapRingHom (psiR Fc m n hn0 ω hω (ω ^ ((v * u) % n))))
    have e : ω ^ ((v * u) % n) = ω ^ (v * u) := by
      rw [hω.eq_orderOf]; exact pow_mod_orderOf ω (v * u)
    rw [← pow_mul, e]


/-- **The norm of any witness descends to `Kₘ`.** -/
theorem descendNF_normNF_isSome (hn : 1 < n) (W : BPoly (NFz Fc m n)) :
    (descendNF Fc m n (normNF Fc m n W)).isSome := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨ω, hω⟩ := exists_prim_LK Fc m n hn0
  set V := normNF Fc m n W with hV
  unfold descendNF
  rw [if_pos]
  · rfl
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro c hc a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hcoef : ((toB V).coeff i).coeff j = V[i][j] := by
    rw [coeff_toB, coeff_toPoly, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  refine length_le_one_of_fixed Fc m n hn0 ω hω _ fun v hv ↦ ?_
  have h := congrArg (fun P : (LK Fc m)[X][X] ↦ (P.coeff i).coeff j)
    (psiZ_normNF Fc m n hn ω hω W v hv)
  simp only [coeff_map, coe_mapRingHom] at h
  rw [hcoef, psiR_eq _ _ _ hn0 ω hω _ (hω.pow_of_coprime v (Finset.mem_filter.mp hv).2),
    psiR_eq _ _ _ hn0 ω hω _ hω] at h
  exact h

end Curves.MT
