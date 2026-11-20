import RischTragerBronstein.Mixed.NKRamGauge
import RischTragerBronstein.Mixed.NKSplitGaugeE

/-!
# The gauge at ramified places at infinity over an exponential level

`ram_gaugeE`: as `ram_gauge` for `x′ = a′ x`. The jets `[T^{N' h}]` acquire the twist
`−(h/e) a′` (`coeff_dS_infSpeedE`), so the diagonal is `(t/e) γₖ′/γₖ − (R/e) a′`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

section RamGaugeE

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

set_option maxHeartbeats 16000000 in
/-- **The gauge at ramified places at infinity** (exponential level, `x′ = a′ x`): a constant gauge
`A` makes the limit matrix `Λ` level-triangular, `A′ = Λ A − A T`, with diagonal
`(t/e) γₖ′/γₖ − (R/e) a′` (`t` the residue of level `R`). -/
theorem ram_gaugeE (bc : C) (hx : S.x′ = aeval S.x (Polynomial.C bc * X))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
    (e sR : ℕ) (he : 0 < e) (hcop : Nat.Coprime sR e) {r' : ℕ} (γ : Fin (r' + 1) → C)
    (hγinj : Function.Injective γ) (hγ0 : ∀ k, γ k ≠ 0)
    (hdegF : ∀ i < S.F.natDegree, e * (S.F.coeff i).natDegree ≤ sR * (S.F.natDegree - i))
    (hlead : leadPolyR e sR S.F = ∏ k, (X ^ e - Polynomial.C (γ k)))
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hrw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C bc * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqE bc r P S0 i j).natDegree ≤ (X ^ r i * S0).natDegree) :
    ∃ (A : Matrix (Fin S.F.natDegree) (Fin e × Fin (r' + 1)) C)
      (Ai : Matrix (Fin e × Fin (r' + 1)) (Fin S.F.natDegree) C)
      (T : Matrix (Fin e × Fin (r' + 1)) (Fin e × Fin (r' + 1)) C),
      A * Ai = 1 ∧ Ai * A = 1 ∧
      (∀ i a, (A i a)′ = ∑ j, (pqE bc r P S0 i j).coeff (X ^ r i * S0).natDegree /
        (X ^ r i * S0).leadingCoeff * A j a - ∑ b, A i b * T b a) ∧
      (∀ a b, b.1 < a.1 → T a b = 0) ∧
      (∀ (R : Fin e) (k k' : Fin (r' + 1)) (t : ℕ), t < e → levR e sR t = R →
        T (R, k) (R, k') = if k = k' then ((t : C) / e) * ((γ k)′ / γ k) - ((R : C) / e) * bc
          else 0) := by
  classical
  set ι := algebraMap C K with hι
  -- `n = e r`
  have hne : S.F.natDegree = e * (r' + 1) := by
    have h1 := (leadPolyR_monic e sR S.F S.monic).2
    rw [hlead, natDegree_prod_of_monic _ _ (fun k _ ↦ monic_X_pow_sub_C _ he.ne')] at h1
    simp only [natDegree_X_pow_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    rw [← h1]; ring
  -- a reparametrized branch system and the leading data
  obtain ⟨Ni, hNi, li, -, hli⟩ := S.hasBranchesInf (K := K)
  have hNi' := Nat.pos_of_ne_zero hNi
  have hNe : 0 < Ni * e := Nat.mul_pos hNi' he
  have hl := branchSys_lsub S.F Ni e he li hli
  obtain ⟨hLB, hnd, -, hex⟩ := S.ram_lead_data e sR he γ hγinj hγ0 hdegF hlead Ni hNi'
    (li.map (lsub e he)) hl
  choose ρk hρkl hρk using hex
  set z : Fin (r' + 1) → LaurentSeries K := fun k ↦ ρk k * single ((Ni * sR : ℕ) : ℤ) 1 with hz
  have hzLB : ∀ k, LowerBd (z k) 0 := fun k ↦ hLB _ (hρkl k)
  set cc : Fin (r' + 1) → K := fun k ↦ (z k).coeff 0 with hcc
  have hcce : ∀ k, cc k ^ e = ι (γ k) := hρk
  have hcc0 : ∀ k, cc k ≠ 0 := fun k h ↦ by
    have := hcce k
    rw [h, zero_pow he.ne'] at this
    exact hγ0 k (ι.injective (by rw [← this, map_zero]))
  -- the expansions of the rescaled basis in the monomials
  have hF1 : S.F ≠ 1 := fun h ↦ S.natDegree_F_ne_zero (by rw [h, natDegree_one])
  choose W Q hQ hWQ hWn using fun i ↦ S.exists_repr_lt (S.wTil w r i) hF1
  obtain ⟨hdegB, hBinv⟩ := S.ram_binf e sR he γ hγinj hγ0 hdegF hlead w r hrw hred W Q hQ hWQ hWn
  set Bm : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := fun i j ↦
    ((W i).coeff j * X ^ gR e sR j).coeff (Q i).natDegree / (Q i).leadingCoeff with hBm
  have hBdet : Bm.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
    exact hv0 (hBinv v fun j ↦ by
      have := congrFun hv j
      simpa [Matrix.vecMul, dotProduct, hBm] using this)
  have hBu : IsUnit Bm.det := isUnit_iff_ne_zero.mpr hBdet
  -- the Vandermonde matrix of the `γₖ`
  set Wv : Matrix (Fin (r' + 1)) (Fin (r' + 1)) C := fun l k ↦ γ k ^ (l : ℕ) with hWv
  have hWdet : Wv.det ≠ 0 := by
    have : Wv = (Matrix.vandermonde γ).transpose := by ext l k; simp [hWv, Matrix.vandermonde]
    rw [this, Matrix.det_transpose]; exact Matrix.det_vandermonde_ne_zero_iff.mpr hγinj
  have hWu : IsUnit Wv.det := isUnit_iff_ne_zero.mpr hWdet
  set Wi := Wv⁻¹ with hWi
  have hWWi : Wv * Wi = 1 := Matrix.mul_nonsing_inv _ hWu
  have hWiW : Wi * Wv = 1 := Matrix.nonsing_inv_mul _ hWu
  set Wi' : Fin (r' + 1) → ℕ → C := fun k l ↦ if h : l < r' + 1 then Wi k ⟨l, h⟩ else 0 with hWi'
  -- the level-graded Vandermonde matrices
  set Qm : Matrix (Fin S.F.natDegree) (Fin e × Fin (r' + 1)) C := fun j a ↦
    if levR e sR j = a.1 then γ a.2 ^ ((j : ℕ) / e) else 0 with hQm
  set Qmi : Matrix (Fin e × Fin (r' + 1)) (Fin S.F.natDegree) C := fun a j ↦
    if levR e sR j = a.1 then Wi' a.2 ((j : ℕ) / e) else 0 with hQmi
  have hjlt : ∀ j : Fin S.F.natDegree, (j : ℕ) / e < r' + 1 := fun j ↦ by
    have h1 : (j : ℕ) < e * (r' + 1) := hne ▸ j.2
    exact Nat.div_lt_of_lt_mul h1
  have hlevlt : ∀ j : ℕ, levR e sR j < e := fun j ↦ (gR_spec e sR j he).2
  have hjeq : ∀ j j' : Fin S.F.natDegree, levR e sR j = levR e sR j' → (j : ℕ) / e = (j' : ℕ) / e →
      j = j' := by
    intro j j' h1 h2
    rw [levR_mod e sR j he, levR_mod e sR j' he] at h1
    have h3 := levR_inj e sR _ _ he hcop (Nat.mod_lt _ he) (Nat.mod_lt _ he) h1
    apply Fin.ext
    rw [← Nat.mod_add_div (j : ℕ) e, ← Nat.mod_add_div (j' : ℕ) e, h3, h2]
  have hWW : ∀ l l' : Fin (r' + 1), ∑ k, γ k ^ (l : ℕ) * Wi k l' = if l = l' then 1 else 0 := by
    intro l l'
    have := congrFun (congrFun hWWi l) l'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hWW' : ∀ k k' : Fin (r' + 1), ∑ l : Fin (r' + 1), Wi k l * γ k' ^ (l : ℕ) =
      if k = k' then 1 else 0 := by
    intro k k'
    have := congrFun (congrFun hWiW k) k'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hQQ : Qm * Qmi = 1 := by
    ext j j'
    rw [Matrix.one_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single (⟨levR e sR j, hlevlt j⟩ : Fin e)]
    · have e1 : ∀ k : Fin (r' + 1), Qm j (⟨levR e sR j, hlevlt j⟩, k) *
          Qmi (⟨levR e sR j, hlevlt j⟩, k) j' =
          if levR e sR j' = levR e sR j then γ k ^ ((j : ℕ) / e) * Wi k ⟨(j' : ℕ) / e, hjlt j'⟩
          else 0 := by
        intro k
        simp only [hQm, hQmi, ↓reduceIte]
        by_cases h : levR e sR (j' : ℕ) = levR e sR j
        · rw [if_pos h, if_pos h]; simp only [hWi', dif_pos (hjlt j')]
        · rw [if_neg h, if_neg h, mul_zero]
      simp only [e1]
      split_ifs with hl hjj hjj
      · rw [hWW ⟨(j : ℕ) / e, hjlt j⟩ ⟨(j' : ℕ) / e, hjlt j'⟩, if_pos (by rw [hjj])]
      · rw [hWW ⟨(j : ℕ) / e, hjlt j⟩ ⟨(j' : ℕ) / e, hjlt j'⟩, if_neg]
        intro h
        exact hjj (hjeq j j' hl.symm (by simpa using congrArg Fin.val h))
      · exact absurd (by rw [hjj]) hl
      · simp
    · intro R _ hR
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      simp only [hQm]
      rw [if_neg (fun h ↦ hR (Fin.ext h.symm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQQ' : Qmi * Qm = 1 := by
    ext a b
    rw [Matrix.one_apply, Matrix.mul_apply]
    by_cases hab1 : (a.1 : ℕ) = b.1
    · have e1 : ∀ j : Fin S.F.natDegree, Qmi a j * Qm j b =
          if levR e sR j = a.1 then Wi' a.2 ((j : ℕ) / e) * γ b.2 ^ ((j : ℕ) / e) else 0 := by
        intro j
        simp only [hQm, hQmi]
        by_cases h : levR e sR (j : ℕ) = a.1
        · rw [if_pos h, if_pos h, if_pos (h.trans hab1)]
        · rw [if_neg h, zero_mul, if_neg h]
      rw [Finset.sum_congr rfl fun j _ ↦ e1 j]
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ if levR e sR j = a.1 then Wi' a.2 (j / e) *
        γ b.2 ^ (j / e) else 0), hne, sum_lev e sR (r' + 1) he hcop a.1 a.1.2
        (fun l ↦ Wi' a.2 l * γ b.2 ^ l), ← Fin.sum_univ_eq_sum_range (fun l ↦ Wi' a.2 l * γ b.2 ^ l)]
      have e2 : ∀ l : Fin (r' + 1), Wi' a.2 l * γ b.2 ^ (l : ℕ) = Wi a.2 l * γ b.2 ^ (l : ℕ) :=
        fun l ↦ by simp only [hWi', dif_pos l.2]
      simp only [e2]
      rw [hWW' a.2 b.2]
      have hab : a = b ↔ a.2 = b.2 :=
        ⟨fun h ↦ by rw [h], fun h ↦ Prod.ext (Fin.ext hab1) h⟩
      by_cases h2 : a.2 = b.2
      · rw [if_pos h2, if_pos (hab.mpr h2)]
      · rw [if_neg h2, if_neg (fun h ↦ h2 (hab.mp h))]
    · have e1 : ∀ j : Fin S.F.natDegree, Qmi a j * Qm j b = 0 := by
        intro j
        simp only [hQm, hQmi]
        by_cases h : levR e sR (j : ℕ) = a.1
        · rw [if_neg (fun h' ↦ hab1 (h.symm.trans h')), mul_zero]
        · rw [if_neg h, zero_mul]
      rw [Finset.sum_congr rfl fun j _ ↦ e1 j, Finset.sum_const_zero,
        if_neg (fun h ↦ hab1 (by rw [h]))]
  -- the gauge `A = B∞ Q` and `T`
  set Bmi := Bm⁻¹ with hBmi
  have hBB : Bm * Bmi = 1 := Matrix.mul_nonsing_inv _ hBu
  have hBB' : Bmi * Bm = 1 := Matrix.nonsing_inv_mul _ hBu
  set A := Bm * Qm with hA
  set Ai := Qmi * Bmi with hAi
  have hAAi : A * Ai = 1 := by
    rw [hA, hAi, Matrix.mul_assoc, ← Matrix.mul_assoc Qm, hQQ, Matrix.one_mul, hBB]
  have hAiA : Ai * A = 1 := by
    rw [hA, hAi, Matrix.mul_assoc, ← Matrix.mul_assoc Bmi, hBB', Matrix.one_mul, hQQ']
  set Λm : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := fun i j ↦
    (pqE bc r P S0 i j).coeff (X ^ r i * S0).natDegree / (X ^ r i * S0).leadingCoeff
    with hΛm
  set T := Ai * (Λm * A - A.map fun z ↦ z′) with hT
  have hAT : A * T = Λm * A - A.map fun z ↦ z′ := by
    rw [hT, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  have hderA : ∀ i a, (A i a)′ = ∑ j, Λm i j * A j a - ∑ b, A i b * T b a := by
    intro i a
    have := congrFun (congrFun hAT i) a
    rw [Matrix.mul_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply] at this
    rw [this]; ring
  -- the jets along one root per place
  have hroot : ∀ k, (S.F.map (infSub (Ni * e))).eval (ρk k) = 0 := fun k ↦ S.root_of_mem hl (hρkl k)
  set φ : Fin (r' + 1) → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) := fun k ↦
    S.embG (infSub (Ni * e)) (infSub_injective (Ni * e) hNe) (ρk k) (hroot k) with hφ
  have hwLB : ∀ i k, LowerBd (φ k (S.wTil w r i)) 0 := fun i k ↦ by
    have := S.infOrd_wTil w r i (hrw i) (Ni * e) hNe.ne' _ hl (ρk k) (hρkl k)
    simpa using this
  set Jt : Fin S.F.natDegree → (Fin e × Fin (r' + 1)) → K := fun i b ↦
    (φ b.2 (S.wTil w r i)).coeff ((Ni * b.1 : ℕ) : ℤ) with hJt
  set Jμ : Fin S.F.natDegree → (Fin e × Fin (r' + 1)) → K := fun j b ↦
    ((z b.2) ^ (j : ℕ)).coeff (((Ni * b.1 : ℕ) : ℤ) - ((Ni * levR e sR j : ℕ) : ℤ)) with hJμ
  have hkN : ∀ b : Fin e × Fin (r' + 1), ((Ni * b.1 : ℕ) : ℤ) < ((Ni * e : ℕ) : ℤ) := fun b ↦ by
    have : Ni * b.1 < Ni * e := Nat.mul_lt_mul_of_pos_left b.1.2 hNi'
    exact_mod_cast this
  have hJexp : ∀ i b, Jt i b = ∑ j, ι (Bm i j) * Jμ j b := by
    intro i b
    have h1 := S.expand_ram e sR Ni he hNi' (ρk b.2) (hroot b.2) (S.wTil w r i) (W i) (Q i) (hQ i)
      (hWQ i) (hWn i)
    simp only [hJt]
    change (φ b.2 (S.wTil w r i)).coeff _ = _
    rw [show φ b.2 (S.wTil w r i) = _ from h1, HahnSeries.coeff_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hE := lowerBd_infSub_div (K := K) (Ni * e) hNe ((W i).coeff t * X ^ gR e sR t) (Q i) (hQ i)
      (hdegB i t t.2)
    set E := infSub (K := K) (Ni * e) ((W i).coeff t * X ^ gR e sR t) *
      (infSub (K := K) (Ni * e) (Q i))⁻¹ - HahnSeries.C (ι (Bm i t)) with hEdef
    have hsplit : infSub (K := K) (Ni * e) ((W i).coeff t * X ^ gR e sR t) *
        (infSub (K := K) (Ni * e) (Q i))⁻¹ = HahnSeries.C (ι (Bm i t)) + E := by
      rw [hEdef]; ring
    have hF : LowerBd (single ((Ni * levR e sR t : ℕ) : ℤ) (1 : K) * z b.2 ^ (t : ℕ)) 0 := by
      have := (lowerBd_single ((Ni * levR e sR t : ℕ) : ℤ) (1 : K)).mul (lowerBd_pow0 (hzLB b.2) t)
      exact this.mono (by positivity)
    rw [hsplit, mul_assoc, coeff_add_mul_of_lowerBd _ E _ _ hE hF _ (hkN b), coeff_single_mul',
      one_mul]
  set Dv : Fin e → K := fun h ↦ ι (((h : ℕ) : C) / e * bc) with hDv
  have hJder : ∀ i b, (Jt i b)′ = ∑ j, ι (Λm i j) * Jt j b + Jt i b * Dv b.1 := by
    intro i b
    set q : C[X] := X ^ r i * S0 with hq
    have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hqK := infSub_ne_zero (K := K) (Ni * e) hNe q hq0
    have hmem := S.derivClosedXYW' (Polynomial.C bc * X) hx (S.wTil w r i) (S.wTil w r i).2
    have hdw := S.deriv_wTilE bc hx w r S0 P hP i
    have hid : (⟨(S.wTil w r i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE q =
        ∑ j, S.polyE (pqE bc r P S0 i j) * S.wTil w r j := Subtype.ext (by
      push_cast
      exact hdw)
    have hemb := congrArg (φ b.2) hid
    rw [map_mul, map_sum] at hemb
    simp only [map_mul] at hemb
    rw [show φ b.2 (S.polyE q) = infSub (Ni * e) q from S.embG_polyX _ _ _ _ _ _] at hemb
    have hpoly : ∀ j, φ b.2 (S.polyE (pqE bc r P S0 i j)) = infSub (Ni * e) (pqE bc r P S0 i j) :=
      fun j ↦ S.embG_polyX _ _ _ _ _ _
    simp only [hpoly] at hemb
    have hder : φ b.2 ⟨(S.wTil w r i : L)′, hmem⟩ =
        ∑ j, (infSub (K := K) (Ni * e) (pqE bc r P S0 i j) * (infSub (K := K) (Ni * e) q)⁻¹) *
          φ b.2 (S.wTil w r j) := by
      have : φ b.2 ⟨(S.wTil w r i : L)′, hmem⟩ =
          (∑ j, infSub (K := K) (Ni * e) (pqE bc r P S0 i j) * φ b.2 (S.wTil w r j)) *
            (infSub (K := K) (Ni * e) q)⁻¹ := by
        rw [← hemb, mul_assoc, mul_inv_cancel₀ hqK, mul_one]
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hL : (φ b.2 ⟨(S.wTil w r i : L)′, hmem⟩).coeff ((Ni * b.1 : ℕ) : ℤ) =
        (Jt i b)′ - Jt i b * Dv b.1 := by
      change (S.embG (infSub (Ni * e)) (infSub_injective (Ni * e) hNe) (ρk b.2) (hroot b.2)
        ⟨(S.wTil w r i : L)′, S.derivClosedXYW' (Polynomial.C bc * X) hx _ (S.wTil w r i).2⟩).coeff _ = _
      rw [S.embG_deriv_infE bc hx hK (Ni * e) hNe (ρk b.2) (hroot b.2) (S.wTil w r i),
        coeff_dS_infSpeedE]
      simp only [hJt, hDv]
      have hNi0 : (Ni : K) ≠ 0 := by exact_mod_cast hNi'.ne'
      have he0 : (e : K) ≠ 0 := by exact_mod_cast he.ne'
      rw [map_mul, map_div₀, map_natCast, map_natCast]
      push_cast
      field_simp
      ring
    have hsum : (φ b.2 ⟨(S.wTil w r i : L)′, hmem⟩).coeff ((Ni * b.1 : ℕ) : ℤ) =
        ∑ j, ι (Λm i j) * Jt j b := by
      rw [hder, HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hlim := lowerBd_infSub_div (K := K) (Ni * e) hNe (pqE bc r P S0 i j) q hq0 (hdeg i j)
      rw [show infSub (K := K) (Ni * e) (pqE bc r P S0 i j) * (infSub (K := K) (Ni * e) q)⁻¹ =
        HahnSeries.C (ι (Λm i j)) + (infSub (K := K) (Ni * e) (pqE bc r P S0 i j) *
          (infSub (K := K) (Ni * e) q)⁻¹ - HahnSeries.C (ι (Λm i j))) by ring,
        coeff_add_mul_of_lowerBd _ _ _ _ hlim (hwLB j b.2) _ (hkN b)]
    rw [← hsum, hL]; ring
  -- the jets through the gauge: `Jt = A Z`
  set AK : Matrix (Fin S.F.natDegree) (Fin e × Fin (r' + 1)) K := A.map ι with hAK
  set AiK : Matrix (Fin e × Fin (r' + 1)) (Fin S.F.natDegree) K := Ai.map ι with hAiK
  set TK : Matrix (Fin e × Fin (r' + 1)) (Fin e × Fin (r' + 1)) K := T.map ι with hTK
  set Z : Matrix (Fin e × Fin (r' + 1)) (Fin e × Fin (r' + 1)) K := fun a b ↦
    ∑ j, ι (Qmi a j) * Jμ j b with hZ
  have hAKi : AK * AiK = 1 := by
    rw [hAK, hAiK, ← Matrix.map_mul, hAAi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAQ : A * Qmi = Bm := by rw [hA, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hJAZ : ∀ i b, Jt i b = ∑ a, AK i a * Z a b := by
    intro i b
    rw [hJexp]
    simp only [hZ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    rw [← hAQ, Matrix.mul_apply, map_sum]
    simp only [hAK, Matrix.map_apply, map_mul]
  -- `T Z = Z′`
  have hkey : ∀ i b, ∑ c, AK i c * (∑ a, TK c a * Z a b - ((Z c b)′ - Z c b * Dv b.1)) = 0 := by
    intro i b
    have h1 := hJder i b
    simp only [hJAZ] at h1
    rw [map_sum] at h1
    simp only [Derivation.leibniz, smul_eq_mul] at h1
    have hAd : ∀ a, (AK i a)′ = ∑ j, ι (Λm i j) * AK j a - ∑ c, AK i c * TK c a := by
      intro a
      simp only [hAK, hTK, Matrix.map_apply]
      rw [hK, hderA i a, map_sub, map_sum, map_sum]
      simp only [map_mul]
    simp only [hAd] at h1
    have e1 : ∑ a, (AK i a * (Z a b)′ + Z a b * (∑ j, ι (Λm i j) * AK j a -
        ∑ c, AK i c * TK c a)) = ∑ j, ι (Λm i j) * ∑ a, AK j a * Z a b -
          ∑ c, AK i c * ∑ a, TK c a * Z a b + ∑ c, AK i c * (Z c b)′ := by
      simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [add_comm]
      congr 1
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
    rw [e1, Finset.sum_mul] at h1
    simp only [mul_sub, Finset.sum_sub_distrib]
    have e3 : ∑ c, AK i c * (Z c b * Dv b.1) = ∑ a, AK i a * Z a b * Dv b.1 :=
      Finset.sum_congr rfl fun c _ ↦ by ring
    rw [e3]
    linear_combination -h1
  have hTZ : ∀ a b, ∑ c, TK a c * Z c b = (Z a b)′ - Z a b * Dv b.1 := by
    intro a b
    have h2 : ∑ i, AiK a i * ∑ c, AK i c * (∑ a', TK c a' * Z a' b - ((Z c b)′ - Z c b * Dv b.1)) = 0 := by
      simp only [hkey, mul_zero, Finset.sum_const_zero]
    simp only [Finset.mul_sum] at h2
    rw [Finset.sum_comm] at h2
    have h3 : ∀ c, ∑ i, AiK a i * (AK i c * (∑ a', TK c a' * Z a' b - ((Z c b)′ - Z c b * Dv b.1))) =
        (AiK * AK) a c * (∑ a', TK c a' * Z a' b - ((Z c b)′ - Z c b * Dv b.1)) := fun c ↦ by
      rw [Matrix.mul_apply]
      generalize (∑ a', TK c a' * Z a' b - ((Z c b)′ - Z c b * Dv b.1)) = X
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hAiAK : AiK * AK = 1 := by
      rw [hAK, hAiK, ← Matrix.map_mul, hAiA, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [h3, hAiAK, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    exact sub_eq_zero.mp h2
  -- the level structure of `Z`
  choose t0 ht0 hlt0 using fun R : Fin e ↦ exists_levR e sR he hcop R R.2
  have hZlow : ∀ (R h : Fin e) (k k' : Fin (r' + 1)), h < R → Z (R, k) (h, k') = 0 := by
    intro R h k k' hhR
    simp only [hZ]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hj : levR e sR (j : ℕ) = R
    · have hneg : ((Ni * (h : ℕ) : ℕ) : ℤ) - ((Ni * levR e sR j : ℕ) : ℤ) < 0 := by
        rw [hj]
        have : Ni * (h : ℕ) < Ni * (R : ℕ) := Nat.mul_lt_mul_of_pos_left hhR hNi'
        push_cast at this ⊢; linarith
      simp only [hJμ]
      rw [lowerBd_pow0 (hzLB k') _ _ hneg, mul_zero]
    · simp only [hQmi, if_neg hj, map_zero, zero_mul]
  have hcpow : ∀ (k' : Fin (r' + 1)) (j : ℕ) (R : Fin e), levR e sR j = R →
      cc k' ^ j = cc k' ^ t0 R * ι (γ k') ^ (j / e) := by
    intro k' j R hj
    have hmod : j % e = t0 R := levR_inj e sR _ _ he hcop (Nat.mod_lt _ he) (ht0 R)
      (by rw [← levR_mod e sR j he, hj, hlt0])
    conv_lhs => rw [← Nat.mod_add_div j e, hmod, pow_add, pow_mul, hcce]
  have hZdiag : ∀ (R : Fin e) (k k' : Fin (r' + 1)),
      Z (R, k) (R, k') = if k = k' then cc k ^ t0 R else 0 := by
    intro R k k'
    have hterm : ∀ j : Fin S.F.natDegree, ι (Qmi (R, k) j) * Jμ j (R, k') =
        cc k' ^ t0 R * ι (if levR e sR j = R then Wi' k ((j : ℕ) / e) * γ k' ^ ((j : ℕ) / e)
          else 0) := by
      intro j
      by_cases hj : levR e sR (j : ℕ) = R
      · simp only [hQmi, hJμ, hj, sub_self, ↓reduceIte]
        rw [coeff_zero_pow_of_lowerBd (hzLB k'), hcpow k' j R hj, map_mul, map_pow]
        ring
      · simp only [hQmi, if_neg hj, map_zero, zero_mul, mul_zero]
    simp only [hZ, hterm, ← Finset.mul_sum, ← map_sum]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ if levR e sR j = R then Wi' k (j / e) *
      γ k' ^ (j / e) else 0), hne, sum_lev e sR (r' + 1) he hcop R R.2
      (fun l ↦ Wi' k l * γ k' ^ l), ← Fin.sum_univ_eq_sum_range (fun l ↦ Wi' k l * γ k' ^ l)]
    have e2 : ∀ l : Fin (r' + 1), Wi' k l * γ k' ^ (l : ℕ) = Wi k l * γ k' ^ (l : ℕ) :=
      fun l ↦ by simp only [hWi', dif_pos l.2]
    simp only [e2]
    rw [hWW' k k']
    split_ifs with hkk
    · subst hkk; simp
    · simp
  have hd0 : ∀ (R : Fin e) (k : Fin (r' + 1)), cc k ^ t0 R ≠ 0 := fun R k ↦ pow_ne_zero _ (hcc0 k)
  obtain ⟨hlowK, hdiagK⟩ := tri_of_TZ TK Z Dv (fun R k ↦ cc k ^ t0 R) hd0 hZlow hZdiag hTZ
  -- back to `C`
  have hlow : ∀ a b, b.1 < a.1 → T a b = 0 := fun a b hab ↦
    ι.injective (by have := hlowK a b hab; simpa [hTK] using this)
  have hlog : ∀ (k : Fin (r' + 1)) (t : ℕ), (cc k ^ t)′ / cc k ^ t =
      ι (((t : C) / e) * ((γ k)′ / γ k)) := by
    intro k t
    have hde : (e : K) * cc k ^ (e - 1) * (cc k)′ = ι ((γ k)′) := by
      have := congrArg (fun x : K ↦ x′) (hcce k)
      simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, hK] at this
      rw [← this]; ring
    have hc := hcc0 k
    have he' : (e : K) ≠ 0 := by exact_mod_cast he.ne'
    have hγk : ι (γ k) = cc k ^ e := (hcce k).symm
    simp only [map_mul, map_div₀, map_natCast, hγk, ← hde, Derivation.leibniz_pow, nsmul_eq_mul,
      smul_eq_mul]
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    have h1 : cc k ^ t = cc k ^ (t - 1) * cc k := by rw [← pow_succ]; congr 1; omega
    have h2 : cc k ^ e = cc k ^ (e - 1) * cc k := by rw [← pow_succ]; congr 1; omega
    rw [h1, h2]
    field_simp
  have hdiag : ∀ (R : Fin e) (k k' : Fin (r' + 1)) (t : ℕ), t < e → levR e sR t = R →
      T (R, k) (R, k') = if k = k' then ((t : C) / e) * ((γ k)′ / γ k) - ((R : C) / e) * bc
        else 0 := by
    intro R k k' t ht htR
    have htt : t = t0 R := levR_inj e sR _ _ he hcop ht (ht0 R) (by rw [htR, hlt0])
    have h1 := hdiagK R k k'
    apply ι.injective
    rw [show ι (T (R, k) (R, k')) = TK (R, k) (R, k') from rfl, h1]
    split_ifs with hkk
    · rw [hlog k (t0 R), htt, hDv, ← map_sub]
    · simp
  exact ⟨A, Ai, T, hAAi, hAiA, hderA, hlow, hdiag⟩


end RamGaugeE

end CurveData

end Curves
