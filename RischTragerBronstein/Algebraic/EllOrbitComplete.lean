import RischTragerBronstein.Algebraic.EllOrbit
import RischTragerBronstein.Computable.KronComplete
import RischTragerBronstein.Computable.SquarefreePart

/-!
# Completeness of the orbit reduction for quadratic orbits

The class `OrbCls`: every irreducible factor `P` of `D` of degree `≥ 2` is a quadratic, simple in
`D`, prime to `p` and to `A`, with a rational residue (`P ∣ A² − z² D′² p` for some `z ∈ ℚ`).
Then every Cantor step of `orbitSearch` succeeds (`orbitStep_spec`), the class is preserved with
one quadratic factor fewer (`orbCls_step`), and the reduction ends with a split denominator; so
`ellDecideOrbitAuto` always answers, correctly (`ellDecideOrbitAuto_decides`).
-/

open Polynomial Differential

namespace EllAlgo

open CPoly

/-! ### Helpers -/

lemma trim_eq_singleton {w : CPoly ℚ} {c : ℚ} (hc : c ≠ 0) (h : toPoly w = C c) :
    trim w = [c] := by
  have hne : trim w ≠ [] := fun h0 ↦ by
    have := (trim_eq_nil_iff w).mp h0
    rw [h] at this; exact hc (C_eq_zero.mp this)
  have hlen : (trim w).length = 1 := by rw [length_trim hne, h, natDegree_C]
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨-, hγ'⟩ := trim_singleton hγ
  rw [hγ, ← C_inj.mp (hγ'.symm.trans h)]

/-- **The modular inverse.** -/
lemma modInv_spec (u f : CPoly ℚ) (hf : toPoly f ≠ 0) (hcop : IsCoprime (toPoly u) (toPoly f)) :
    toPoly f ∣ toPoly u * toPoly (modInv u f) - 1 := by
  obtain ⟨hg1, hg2⟩ := egcd_dvd u f
  have hbez := egcd_spec u f
  set e := egcd u f with he
  have hunit : IsUnit (toPoly e.1) := by
    obtain ⟨s, t, hst⟩ := hcop
    exact isUnit_of_dvd_one (hst ▸ dvd_add (Dvd.dvd.mul_left hg1 s) (Dvd.dvd.mul_left hg2 t))
  have hne : trim e.1 ≠ [] := fun h ↦ hunit.ne_zero ((trim_eq_nil_iff _).mp h)
  have hlen : (trim e.1).length = 1 := by
    rw [length_trim hne, natDegree_eq_zero_of_isUnit hunit]
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨hγ0, hg⟩ := trim_singleton hγ
  have hlead : lead (trim e.1) = γ := by rw [hγ]; rfl
  unfold modInv
  dsimp only
  rw [← he, hlead]
  have hsp := divMod_spec (smul γ⁻¹ e.2.1) f
  rw [toPoly_smul] at hsp
  have hinv : C γ⁻¹ * C γ = (1 : ℚ[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  refine ⟨-(C γ⁻¹ * toPoly e.2.2) - toPoly u * toPoly (divMod (smul γ⁻¹ e.2.1) f).1, ?_⟩
  have : toPoly (divMod (smul γ⁻¹ e.2.1) f).2 =
      C γ⁻¹ * toPoly e.2.1 - toPoly (divMod (smul γ⁻¹ e.2.1) f).1 * toPoly f := by
    rw [hsp]; ring
  rw [this]
  rw [hg] at hbez
  linear_combination (C γ⁻¹) * hbez + hinv

lemma not_dvd_derivative_irr {P : ℚ[X]} (hP : Irreducible P) : ¬P ∣ derivative P :=
  fun hd ↦ hP.not_isUnit ((PerfectField.separable_of_irreducible hP).isUnit_of_dvd' dvd_rfl hd)

lemma rem_dvd (q d : CPoly ℚ) : toPoly d ∣ toPoly (divMod q d).2 - toPoly q :=
  ⟨-toPoly (divMod q d).1, by rw [divMod_spec q d]; ring⟩

lemma rem_zero_of_dvd {q d : CPoly ℚ} (hd : toPoly d ≠ 0) (h : toPoly d ∣ toPoly q) :
    toPoly q = toPoly (divMod q d).1 * toPoly d := by
  rw [divMod_spec q d, CPoly.divMod_exact q d hd h, add_zero]

lemma dvd_of_dvd_mul_unit {F Y : ℚ[X]} (hF : Irreducible F) {u : ℚ[X]} (hu : ¬F ∣ u)
    (h : F ∣ u * Y) : F ∣ Y := (hF.prime.dvd_or_dvd h).resolve_left hu

set_option maxHeartbeats 1600000 in
/-- **One Cantor step succeeds** at a simple quadratic factor with rational residue. -/
lemma orbitStep_spec (p A D f : CPoly ℚ) (hP3 : (toPoly p).natDegree = 3)
    (hfi : Irreducible (toPoly f)) (hf2 : (toPoly f).natDegree = 2 ∨ (toPoly f).natDegree = 3)
    (hD0 : toPoly D ≠ 0) (hfD : toPoly f ∣ toPoly D)
    (hsimple : ¬toPoly f * toPoly f ∣ toPoly D) (hfp : ¬toPoly f ∣ toPoly p)
    (hfA : ¬toPoly f ∣ toPoly A) (z : ℚ)
    (hz : toPoly f ∣ toPoly A ^ 2 - C z ^ 2 * derivative (toPoly D) ^ 2 * toPoly p) :
    ∃ st : OStep, orbitStep p A D f = some st ∧ stepOk p A D st = true ∧
      toPoly D = toPoly f * toPoly (divMod D f).1 ∧
      ∃ H : ℚ[X], (H ≠ 0 ∧ H.natDegree ≤ 1) ∧ toPoly st.2.2.2 = toPoly (divMod D f).1 * H ∧
        toPoly (orbQ p st.2.1) = toPoly f * H := by
  classical
  set F := toPoly f with hFd
  set P := toPoly p with hPd
  have hF0 : F ≠ 0 := hfi.ne_zero
  have hFpr := hfi.prime
  set Rc := (divMod D f).1 with hRc
  set R := toPoly Rc with hRd
  have hDR : toPoly D = R * F := rem_zero_of_dvd hF0 hfD
  have hR0 : R ≠ 0 := fun h0 ↦ hD0 (by rw [hDR, h0, zero_mul])
  have hFR : ¬F ∣ R := fun h ↦ hsimple (by rw [hDR]; exact mul_dvd_mul h (dvd_refl F))
  have hcopR : IsCoprime R F := ((hfi.coprime_iff_not_dvd).mpr hFR).symm
  set RI := modInv Rc f with hRI
  have hRIs : F ∣ R * toPoly RI - 1 := modInv_spec Rc f hF0 hcopR
  set Tc := (divMod (mul A RI) f).2 with hTc
  set T := toPoly Tc with hTd
  have hT : F ∣ T - toPoly A * toPoly RI := by
    have := rem_dvd (mul A RI) f
    rwa [toPoly_mul] at this
  set F' := derivative F with hF'd
  have hDd : derivative (toPoly D) = derivative R * F + R * F' := by
    rw [hDR, derivative_mul]
  -- `T² ≡ z² F′² p`
  have hT2 : F ∣ T ^ 2 - C z ^ 2 * F' ^ 2 * P := by
    have h1 : F ∣ toPoly RI * derivative (toPoly D) - F' := by
      have : toPoly RI * derivative (toPoly D) - F' =
          F * (toPoly RI * derivative R) + F' * (R * toPoly RI - 1) := by rw [hDd]; ring
      rw [this]; exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hRIs _)
    have e : T ^ 2 - C z ^ 2 * F' ^ 2 * P =
        (T - toPoly A * toPoly RI) * (T + toPoly A * toPoly RI) +
          toPoly RI ^ 2 * (toPoly A ^ 2 - C z ^ 2 * derivative (toPoly D) ^ 2 * P) +
          C z ^ 2 * P * (toPoly RI * derivative (toPoly D) - F') *
            (toPoly RI * derivative (toPoly D) + F') := by ring
    rw [e]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left hT _) (dvd_mul_of_dvd_right hz _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _)
  have hFF' : ¬F ∣ F' := not_dvd_derivative_irr hfi
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hfA
    have : F ∣ toPoly A ^ 2 := by simpa using hz
    exact hFpr.dvd_of_dvd_pow this
  -- the constant `w = z²`
  have hcopM : IsCoprime (toPoly (mul (mul (deriv f) (deriv f)) p)) F := by
    rw [toPoly_mul, toPoly_mul, toPoly_deriv]
    refine ((hfi.coprime_iff_not_dvd).mpr ?_).symm
    intro h
    rcases hFpr.dvd_or_dvd h with h | h
    · rcases hFpr.dvd_or_dvd h with h | h <;> exact hFF' h
    · exact hfp h
  set MI := modInv (mul (mul (deriv f) (deriv f)) p) f with hMI
  have hMIs := modInv_spec (mul (mul (deriv f) (deriv f)) p) f hF0 hcopM
  rw [toPoly_mul, toPoly_mul, toPoly_deriv] at hMIs
  set wc := (divMod (mul (mul Tc Tc) MI) f).2 with hwc
  have hw : F ∣ toPoly wc - C (z ^ 2) := by
    have h1 := rem_dvd (mul (mul Tc Tc) MI) f
    rw [toPoly_mul, toPoly_mul] at h1
    have e : toPoly wc - C (z ^ 2) = (toPoly wc - T * T * toPoly MI) +
        toPoly MI * (T ^ 2 - C z ^ 2 * F' ^ 2 * P) +
        C z ^ 2 * (F' * F' * P * toPoly MI - 1) := by rw [C_pow]; ring
    rw [e]
    exact dvd_add (dvd_add h1 (dvd_mul_of_dvd_right hT2 _)) (dvd_mul_of_dvd_right hMIs _)
  have hwC : toPoly wc = C (z ^ 2) := by
    have hdeg : (toPoly wc - C (z ^ 2)).degree < F.degree := by
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt (divMod_degree_lt _ f hF0) ?_)
      have hFpos : 0 < F.natDegree := by rcases hf2 with h | h <;> omega
      rw [degree_eq_natDegree hF0]
      exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hFpos)
    exact sub_eq_zero.mp (Kron.toPoly_eq_zero_of_dvd_of_degree_lt hw hdeg)
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  have htrim : trim wc = [z ^ 2] := trim_eq_singleton hz2 hwC
  obtain ⟨z', hq⟩ := Option.isSome_iff_exists.mp (qsqrt_sq z)
  have hz' : z' ^ 2 = z ^ 2 := qsqrt_spec hq
  have hz'0 : z' ≠ 0 := fun h0 ↦ hz2 (by rw [← hz', h0]; ring)
  -- the `y`-values `g`
  have hcopZ : IsCoprime (toPoly (smul z' (deriv f))) F := by
    rw [toPoly_smul, toPoly_deriv]
    refine ((hfi.coprime_iff_not_dvd).mpr fun h ↦ hFF' ?_).symm
    exact dvd_of_dvd_mul_unit hfi (u := C z') (fun hd ↦ hfi.not_isUnit
      (isUnit_of_dvd_unit hd (isUnit_C.mpr (Ne.isUnit hz'0)))) h
  set ZI := modInv (smul z' (deriv f)) f with hZI
  have hZIs := modInv_spec (smul z' (deriv f)) f hF0 hcopZ
  rw [toPoly_smul, toPoly_deriv] at hZIs
  set gc := (divMod (mul Tc ZI) f).2 with hgc
  set G := toPoly gc with hGd
  have hG : F ∣ G - T * toPoly ZI := by
    have := rem_dvd (mul Tc ZI) f
    rwa [toPoly_mul] at this
  have hG1 : F ∣ C z' * F' * G - T := by
    have e : C z' * F' * G - T = C z' * F' * (G - T * toPoly ZI) + T * (C z' * F' * toPoly ZI - 1) := by
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hG _) (dvd_mul_of_dvd_right hZIs _)
  have hG2 : F ∣ G * G - P := by
    have hzC : C z' ^ 2 = C z ^ 2 := by rw [← C_pow, ← C_pow, hz']
    have e : C z' ^ 2 * F' ^ 2 * (G * G - P) =
        (C z' * F' * G - T) * (C z' * F' * G + T) + (T ^ 2 - C z ^ 2 * F' ^ 2 * P) := by
      linear_combination (-(F' ^ 2 * P)) * hzC
    have h3 : F ∣ C z' ^ 2 * F' ^ 2 * (G * G - P) := by
      rw [e]; exact dvd_add (dvd_mul_of_dvd_left hG1 _) hT2
    refine dvd_of_dvd_mul_unit hfi ?_ h3
    intro h
    rcases hFpr.dvd_or_dvd h with h | h
    · exact hfi.not_isUnit (isUnit_of_dvd_unit h ((isUnit_C.mpr (Ne.isUnit hz'0)).pow 2))
    · exact hFF' (hFpr.dvd_of_dvd_pow h)
  -- `Q = p − g² = f H`
  have hQd : toPoly (orbQ p gc) = P - G * G := by rw [orbQ, toPoly_sub, toPoly_mul]
  have hFQ : F ∣ toPoly (orbQ p gc) := by
    rw [hQd]; have := (dvd_neg).mpr hG2; rwa [neg_sub] at this
  set hc := (divMod (orbQ p gc) f).1 with hhc
  set H := toPoly hc with hHd
  have hQ : toPoly (orbQ p gc) = H * F := rem_zero_of_dvd hF0 hFQ
  have hGdeg : G.natDegree + 1 ≤ F.natDegree := by
    by_cases hG0 : G = 0
    · rw [hG0, natDegree_zero]; rcases hf2 with h | h <;> omega
    · have := natDegree_lt_natDegree hG0 (divMod_degree_lt (mul Tc ZI) f hF0)
      have h1 : (toPoly f).natDegree = F.natDegree := rfl
      omega
  have hPG : P - G * G ≠ 0 := by
    intro h
    have e : P = G * G := sub_eq_zero.mp h
    by_cases hG0 : G = 0
    · rw [e, hG0, mul_zero, natDegree_zero] at hP3; omega
    · rw [e, natDegree_mul hG0 hG0] at hP3; omega
  have hQle : (P - G * G).natDegree ≤ max 3 (G.natDegree + G.natDegree) := by
    refine (natDegree_sub_le _ _).trans (max_le_max (le_of_eq hP3) natDegree_mul_le)
  have hH0 : H ≠ 0 := fun h0 ↦ hPG (by rw [← hQd, hQ, h0, zero_mul])
  have hH1 : H.natDegree ≤ 1 := by
    have := hQle
    rw [← hQd, hQ, natDegree_mul hH0 hF0] at this
    have h1 : (toPoly f).natDegree = F.natDegree := rfl
    rcases hf2 with h | h <;> omega
  -- the new numerator
  set N := toPoly (orbN p gc) with hNd
  have hNe : N = derivative P * G - 2 * (derivative G * P) := by
    rw [hNd, orbN, toPoly_sub, toPoly_mul, toPoly_smul, toPoly_mul, toPoly_deriv, toPoly_deriv]
    simp only [C_ofNat]
    rfl
  set Xc := sub (mul A hc) (smul z' (mul (orbN p gc) Rc)) with hXc
  have hXd : toPoly Xc = toPoly A * H - C z' * (N * R) := by
    rw [hXc, toPoly_sub, toPoly_mul, toPoly_smul, toPoly_mul]
  have hFX : F ∣ toPoly Xc := by
    rw [hXd]
    have hQ' : derivative P - 2 * G * derivative G = derivative H * F + H * F' := by
      have := congrArg derivative (hQ.symm.trans hQd)
      rw [derivative_mul, derivative_sub, derivative_mul] at this
      linear_combination -this
    have e : toPoly A * H - C z' * (N * R) =
        H * ((toPoly A - T * R) + R * (T - C z' * F' * G)) -
          C z' * R * (G * derivative H * F - 2 * derivative G * (H * F)) := by
      rw [hNe]
      linear_combination (-(C z' * R * G)) * hQ' + (-(2 * C z' * R * derivative G)) *
        (hQ.symm.trans hQd)
    rw [e]
    have hAT : F ∣ toPoly A - T * R := by
      have e2 : toPoly A - T * R = -(R * (T - toPoly A * toPoly RI)) -
          toPoly A * (R * toPoly RI - 1) := by ring
      rw [e2]
      exact dvd_sub (dvd_neg.mpr (dvd_mul_of_dvd_right hT _)) (dvd_mul_of_dvd_right hRIs _)
    have hTG : F ∣ T - C z' * F' * G := by
      have := (dvd_neg).mpr hG1; rwa [neg_sub] at this
    refine dvd_sub (dvd_mul_of_dvd_right (dvd_add hAT (dvd_mul_of_dvd_right hTG _)) _)
      (dvd_mul_of_dvd_right ?_ _)
    exact ⟨G * derivative H - 2 * derivative G * H, by ring⟩
  set A1c := (divMod Xc f).1 with hA1c
  have hX : toPoly Xc = toPoly A1c * F := rem_zero_of_dvd hF0 hFX
  -- the step
  have hstep : orbitStep p A D f = some (z', gc, A1c, mul Rc hc) := by
    unfold orbitStep
    dsimp only
    rw [htrim]
    simp only [hq, if_neg hz'0]
    rfl
  refine ⟨_, hstep, ?_, by rw [hDR, mul_comm], H, ⟨hH0, hH1⟩, by rw [toPoly_mul], by rw [hQ, mul_comm]⟩
  simp only [stepOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · cases hzz : isZero (mul Rc hc)
    · rfl
    · exact absurd ((isZero_iff _).mp hzz) (by rw [toPoly_mul]; exact mul_ne_zero hR0 hH0)
  · cases hzz : isZero (orbQ p gc)
    · rfl
    · exact absurd ((isZero_iff _).mp hzz) (by rw [hQ]; exact mul_ne_zero hH0 hF0)
  · simp only [toPoly_mul, toPoly_add, toPoly_smul]
    rw [hQ, hDR, ← hNd]
    rw [hXd] at hX
    linear_combination (R * F * H) * hX

/-! ### The class and its preservation -/

/-- **The class**: every non-linear irreducible factor of `D` is a simple quadratic, prime to `p`
and `A`, with a rational residue. -/
def OrbCls (P A D : ℚ[X]) : Prop :=
  ∀ Q : ℚ[X], Irreducible Q → Q ∣ D → 2 ≤ Q.natDegree →
    (Q.natDegree = 2 ∨ Q.natDegree = 3) ∧ ¬Q * Q ∣ D ∧ ¬Q ∣ P ∧ ¬Q ∣ A ∧
      ∃ z : ℚ, Q ∣ A ^ 2 - C z ^ 2 * derivative D ^ 2 * P

/-- **One step preserves the class.** -/
lemma orbCls_step {P A D A₁ D₁ F R H Qp N : ℚ[X]} {z : ℚ} (hcls : OrbCls P A D)
    (hFirr : Irreducible F) (hFs : ¬F * F ∣ D) (hD : D = F * R) (hD₁ : D₁ = R * H)
    (hH0 : H ≠ 0) (hH1 : H.natDegree ≤ 1) (hQ : Qp = F * H)
    (hid : A * D₁ * Qp = D * (A₁ * Qp + C z * (N * D₁))) : OrbCls P A₁ D₁ := by
  intro Q2 hQi hQD1 hdeg
  have hpr := hQi.prime
  have hQH : ¬Q2 ∣ H := fun h ↦ by
    have := natDegree_le_of_dvd h hH0; omega
  have hQR : Q2 ∣ R := (hpr.dvd_or_dvd (hD₁ ▸ hQD1)).resolve_right hQH
  have hQD : Q2 ∣ D := by rw [hD]; exact dvd_mul_of_dvd_right hQR _
  obtain ⟨h2, hsq, hp, hA, z2, hz2⟩ := hcls Q2 hQi hQD hdeg
  have hQF : ¬Q2 ∣ F := fun h ↦ hFs (by
    rw [hD]; exact mul_dvd_mul_left F ((hQi.dvd_symm hFirr h).trans hQR))
  obtain ⟨R2, hR2⟩ := hQR
  have hQR2 : ¬Q2 ∣ R2 := fun ⟨r, hr⟩ ↦ hsq ⟨F * r, by rw [hD, hR2, hr]; ring⟩
  set S := F * R2 with hS
  set S₁ := R2 * H with hS₁
  have hDS : D = Q2 * S := by rw [hD, hR2]; ring
  have hD₁S : D₁ = Q2 * S₁ := by rw [hD₁, hR2]; ring
  have hQS : ¬Q2 ∣ S := fun h ↦ by
    rcases hpr.dvd_or_dvd h with h | h
    · exact hQF h
    · exact hQR2 h
  have hQS₁ : ¬Q2 ∣ S₁ := fun h ↦ by
    rcases hpr.dvd_or_dvd h with h | h
    · exact hQR2 h
    · exact hQH h
  have hQQp : ¬Q2 ∣ Qp := fun h ↦ by
    rw [hQ] at h
    rcases hpr.dvd_or_dvd h with h | h
    · exact hQF h
    · exact hQH h
  have hQ0 : Q2 ≠ 0 := hQi.ne_zero
  -- the congruence `A S₁ ≡ S A₁`
  have hcong : Q2 ∣ A * S₁ - S * A₁ := by
    have e : Qp * (A * S₁ - S * A₁) = Q2 * (S * C z * N * S₁) := by
      refine mul_left_cancel₀ hQ0 ?_
      rw [hDS, hD₁S] at hid
      linear_combination hid
    have : Q2 ∣ Qp * (A * S₁ - S * A₁) := ⟨_, e⟩
    exact (hpr.dvd_or_dvd this).resolve_left hQQp
  refine ⟨h2, fun h ↦ ?_, hp, fun h ↦ ?_, z2, ?_⟩
  · rw [hD₁S] at h
    exact hQS₁ ((mul_dvd_mul_iff_left hQ0).mp h)
  · have : Q2 ∣ A * S₁ := by
      have := dvd_add hcong (dvd_mul_of_dvd_right h S)
      rwa [sub_add_cancel] at this
    rcases hpr.dvd_or_dvd this with h' | h'
    · exact hA h'
    · exact hQS₁ h'
  · -- `S² X₁ ≡ S₁² X₀`
    have hkey : Q2 ∣ S ^ 2 * (A₁ ^ 2 - C z2 ^ 2 * derivative D₁ ^ 2 * P) := by
      have hDd : derivative D = derivative Q2 * S + Q2 * derivative S := by
        rw [hDS, derivative_mul]
      have hD₁d : derivative D₁ = derivative Q2 * S₁ + Q2 * derivative S₁ := by
        rw [hD₁S, derivative_mul]
      have e : S ^ 2 * (A₁ ^ 2 - C z2 ^ 2 * derivative D₁ ^ 2 * P) =
          S₁ ^ 2 * (A ^ 2 - C z2 ^ 2 * derivative D ^ 2 * P) -
            (A * S₁ - S * A₁) * (A * S₁ + S * A₁) -
            C z2 ^ 2 * P * Q2 * (2 * derivative Q2 * S ^ 2 * S₁ * derivative S₁ +
              Q2 * S ^ 2 * derivative S₁ ^ 2 - 2 * derivative Q2 * S₁ ^ 2 * S * derivative S -
              Q2 * S₁ ^ 2 * derivative S ^ 2) := by
        rw [hDd, hD₁d]; ring
      rw [e]
      exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right hz2 (S₁ ^ 2))
        (dvd_mul_of_dvd_left hcong (A * S₁ + S * A₁)))
        (dvd_mul_of_dvd_left (dvd_mul_left Q2 (C z2 ^ 2 * P)) _)
    exact (hpr.dvd_or_dvd hkey).resolve_left fun h ↦ hQS (hpr.dvd_of_dvd_pow h)

/-! ### `factorQ` does not increase degrees -/

lemma factorQ_natDegree_le : ∀ (n : ℕ) (F : CPoly ℚ), toPoly F ≠ 0 →
    ∀ q ∈ Kron.factorQ n F, toPoly q ≠ 0 ∧ (toPoly q).natDegree ≤ (toPoly F).natDegree
  | 0, F, hF, q, hq => by
    simp only [Kron.factorQ, List.mem_singleton] at hq
    subst hq
    obtain ⟨-, -, k, hk0, hk⟩ := Kron.primInt_spec F hF
    rw [hk, natDegree_C_mul hk0]
    exact ⟨mul_ne_zero (by simpa using hk0) hF, le_rfl⟩
  | n + 1, F, hF, q, hq => by
    obtain ⟨-, -, k, hk0, hk⟩ := Kron.primInt_spec F hF
    have hP0 : toPoly (Kron.primInt F) ≠ 0 := by rw [hk]; exact mul_ne_zero (by simpa using hk0) hF
    have hPd : (toPoly (Kron.primInt F)).natDegree = (toPoly F).natDegree := by
      rw [hk, natDegree_C_mul hk0]
    rcases hf : Kron.findFactor (Kron.primInt F) with _ | g
    · simp only [Kron.factorQ, hf, List.mem_singleton] at hq
      subst hq
      exact ⟨hP0, hPd.le⟩
    · simp only [Kron.factorQ, hf, List.mem_append] at hq
      obtain ⟨e, -, hgl, hz⟩ := Kron.findFactor_spec _ _ hf
      have hPq := Kron.rem_zero_spec _ _ hz
      have hgtr : trim g ≠ [] := fun h0 ↦ by rw [h0] at hgl; simp at hgl
      have hg0 : toPoly g ≠ 0 := fun h0 ↦ hgtr ((trim_eq_nil_iff g).mpr h0)
      have hq0 : toPoly (divMod (Kron.primInt F) g).1 ≠ 0 := fun h0 ↦ hP0 (by rw [hPq, h0, zero_mul])
      have hsum := congrArg natDegree hPq
      rw [natDegree_mul hq0 hg0] at hsum
      rcases hq with hq | hq
      · obtain ⟨h1, h2⟩ := factorQ_natDegree_le n g hg0 q hq
        exact ⟨h1, by omega⟩
      · obtain ⟨h1, h2⟩ := factorQ_natDegree_le n _ hq0 q hq
        exact ⟨h1, by omega⟩

/-! ### The whole reduction -/

lemma splits_of_factorQ (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (h : ∀ q ∈ Kron.factorQ (Kron.degC D + 1) D, ¬(decide (2 ≤ Kron.degC q)) = true) :
    (toPoly D).Splits := by
  by_cases h0 : (toPoly D).natDegree = 0
  · exact Splits.of_natDegree_le_one (by omega)
  obtain ⟨-, k, -, hk⟩ := Kron.factorQ_spec (Kron.degC D + 1) D (Nat.pos_of_ne_zero h0)
    (by rw [Kron.degC_eq D hD]; omega)
  rw [hk]
  refine Splits.mul (Splits.of_natDegree_le_one (by rw [natDegree_C]; omega)) ?_
  rw [← Multiset.prod_coe]
  refine Splits.multisetProd fun q hq ↦ ?_
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hq)
  have := h q' hq'
  simp only [decide_eq_true_eq, not_le] at this
  obtain ⟨hq0, -⟩ := factorQ_natDegree_le _ D hD q' hq'
  rw [Kron.degC_eq q' hq0] at this
  exact Splits.of_natDegree_le_one (by omega)

/-- **The reduction always succeeds on the class**, ending with a split denominator. -/
theorem orbitSearch_complete (p : CPoly ℚ) (hP3 : (toPoly p).natDegree = 3) :
    ∀ (n : ℕ) (A D : CPoly ℚ), toPoly D ≠ 0 → (toPoly D).natDegree < n →
      OrbCls (toPoly p) (toPoly A) (toPoly D) →
      ∃ A' D', chainOk p A D (orbitSearch p n A D) = some (A', D') ∧ toPoly D' ≠ 0 ∧
        (toPoly D').Splits
  | 0, _, _, _, hn, _ => by omega
  | n + 1, A, D, hD, hn, hcls => by
    classical
    rcases hfind : (Kron.factorQ (Kron.degC D + 1) D).find?
        (fun f ↦ decide (2 ≤ Kron.degC f)) with _ | f
    · refine ⟨A, D, by simp [orbitSearch, hfind, chainOk], hD, ?_⟩
      exact splits_of_factorQ D hD (List.find?_eq_none.mp hfind)
    have hfm := List.mem_of_find?_eq_some hfind
    have hf2 : 2 ≤ Kron.degC f := by simpa using List.find?_some hfind
    obtain ⟨hf0, hfdeg⟩ := factorQ_natDegree_le _ D hD f hfm
    rw [Kron.degC_eq f hf0] at hf2
    obtain ⟨hirr, k, hk0, hk⟩ := Kron.factorQ_spec (Kron.degC D + 1) D (by omega)
      (by rw [Kron.degC_eq D hD]; omega)
    have hfi := Kron.irredQ_sound f (hirr f hfm)
    have hfD : toPoly f ∣ toPoly D := by
      rw [hk]; exact dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map_of_mem hfm)) _
    obtain ⟨h2, hsq, hp, hA, z, hz⟩ := hcls _ hfi hfD hf2
    obtain ⟨st, hst, hok, hDR, H, ⟨hH0, hH1⟩, hD1, hQ⟩ :=
      orbitStep_spec p A D f hP3 hfi h2 hD hfD hsq hp hA z hz
    have hok' := hok
    simp only [stepOk, Bool.and_eq_true, beq_iff] at hok'
    have hid := hok'.2
    simp only [toPoly_mul, toPoly_add, toPoly_smul] at hid
    set R := toPoly (divMod D f).1
    have hR0 : R ≠ 0 := fun h0 ↦ hD (by rw [hDR, h0, mul_zero])
    have hD10 : toPoly st.2.2.2 ≠ 0 := by rw [hD1]; exact mul_ne_zero hR0 hH0
    have hdeg1 : (toPoly st.2.2.2).natDegree < n := by
      have e1 := congrArg natDegree hDR
      rw [natDegree_mul hfi.ne_zero hR0] at e1
      rw [hD1, natDegree_mul hR0 hH0]
      rcases h2 with h2 | h2 <;> omega
    have hcls' := orbCls_step hcls hfi hsq hDR hD1 hH0 hH1 hQ hid
    obtain ⟨A', D', hch, hD'0, hsp⟩ := orbitSearch_complete p hP3 n _ _ hD10 hdeg1 hcls'
    refine ⟨A', D', ?_, hD'0, hsp⟩
    simp only [orbitSearch, hfind, hst, chainOk, hok, if_true]
    exact hch

/-- The decision with the automatic fuel bound of the final (split) denominator. -/
def ellDecideOrbitAuto (a b c : ℤ) (A D : CPoly ℚ) : Option Bool :=
  let p := pOf a b c
  if isZero D then none else
    match chainOk p A D (orbitSearch p (Kron.degC D + 1) A D) with
    | some (A', D') => ellDecideEll a b c A' D' (fuelAny a b c D')
    | none => none

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for quadratic Galois orbits with rational residues**: for
`y² = x³ + ax² + bx + c` squarefree and `A/D` in the class `OrbCls` (every non-linear irreducible
factor of `D` a simple quadratic, prime to `p` and `A`, with rational residue),
`ellDecideOrbitAuto` answers, and its answer is the truth. -/
theorem ellDecideOrbitAuto_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hcls : OrbCls (toPoly (pOf a b c)) (toPoly A) (toPoly D)) :
    ∃ ans : Bool, ellDecideOrbitAuto a b c A D = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  have hP3 : (toPoly (pOf a b c)).natDegree = 3 := by rw [toPoly_pOf]; compute_degree!
  obtain ⟨A', D', hch, hD'0, hsp⟩ := orbitSearch_complete (pOf a b c) hP3 (Kron.degC D + 1) A D hD
    (by rw [Kron.degC_eq D hD]; omega) hcls
  obtain ⟨ans, hans, hcorr⟩ := ellDecideEll_decides hC hCall x y hx a b c hsq hy hgen A' D' hD'0 hsp
  refine ⟨ans, ?_, ?_⟩
  · have hz : isZero D = false := by
      cases hz : isZero D
      · rfl
      · exact absurd ((isZero_iff _).mp hz) hD
    simp only [ellDecideOrbitAuto, hz, Bool.false_eq_true, ↓reduceIte, hch]
    exact hans
  · have hyp : y ^ 2 = aeval x (toPoly (pOf a b c)) := by rw [hy, toPoly_pOf]; simp
    have htrK : Transcendental Kc x :=
      transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have hne := aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
        (algebraMap ℚ Kc).injective).mpr hsq.ne_zero)
      apply hne
      rw [aeval_map_algebraMap]
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_intCast]
      linear_combination -hy
    obtain ⟨-, hiff⟩ := chainOk_spec hC x y hx (pOf a b c) hyp hy0 _ A D A' D' hD hch
    rw [hiff]; exact hcorr

end EllAlgo
