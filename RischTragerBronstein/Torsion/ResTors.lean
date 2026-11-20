import RischTragerBronstein.Torsion.NonTorsionMap
import RischTragerBronstein.Curves.ProcLogDecide

/-!
# Non-elementary integrals from non-torsion residue divisors

For an integrand `f = A(x, y)/D(x)` (a `CurveProb`), a coordinate `coord j₀` of the residues
and a scale `s > 0`, `torsResCheck P T eL s j₀` checks that `s` times the `j₀`-component of the
residue divisor of `f dx` is `∑ (Γ_{jk} − e_j) P_{jk}` at the points `P_{jk} = (α_j, y_{jk})` of
the global certificate `T` (each `α_j` a certified unramified point of `P`), and is uniform along
the certified branches at every other special point `a` (with `s ρ_a / N_a = −f_a` integral) and
above infinity. Then `f dx` having an elementary integral would make `Γ − c ∞ₓ`
(`c = ∑ e_j + ∑ f_a − s ρ_∞ / N_∞`) torsion (Abel: `curve_abel`, multiplied by
`∏ (x − α_j)^{m e_j} ∏ (x − a)^{m f_a}`), which the certificates of `not_torsion_of_cert_map`
exclude. This covers residues at totally ramified points and above a single place at infinity.
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries GTors

section Defs

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- `x − a`. -/
def xSubC (a : F) : CPoly F := [-a, 1]

/-- The `j₀`-residue along the first certified branch at a point. -/
def rho0 (P : CurveProb F) (j₀ : Fin (dim F)) (ac : F × BranchCert F) : ℚ :=
  coord j₀ (P.resFin ac.1 ac.2 (ac.2.ys.getD 0 []))

/-- The exponent of `x − a` at a special point outside `Γ` (`−s ρ / N`, an integer). -/
def fexp (P : CurveProb F) (T : GlobalCert F) (s : ℕ) (j₀ : Fin (dim F)) (ac : F × BranchCert F) :
    ℤ :=
  if ac.1 ∈ T.αL then 0 else (-(s * rho0 P j₀ ac / ac.2.N)).num

/-- **The residue check** for the component `j₀` (scaled by `s`): at the points of `Γ` the
scaled residues are `Γ_{jk} − e_j`; at the other special points and above infinity the residues
are uniform along the certified branches, with `s ρ / N` integral at the finite points; the
degree `c` of `Γ − c ∞ₓ` is `∑ eⱼ + ∑ f_a − s ρ_∞ / N_∞`. -/
def torsResCheck (P : CurveProb F) (T : GlobalCert F) (eL : List ℤ) (s : ℕ)
    (j₀ : Fin (dim F)) : Bool :=
  decide (T.Fc = P.Fc) && decide (T.n = P.n) && decide (0 < s) &&
  decide (P.pts.map Prod.fst).Nodup &&
  (List.range T.αL.length).all (fun j ↦
    match P.pts.find? (fun ac ↦ decide (ac.1 = T.αL.getD j 0)) with
    | none => false
    | some ac => decide (ac.2.N = 1) && decide (1 ≤ ac.2.prec) &&
      (List.range T.n).all fun k ↦
        decide ((ac.2.ys.getD k []).getD 0 0 = (T.yL.getD j []).getD k 0) &&
        decide ((s : ℚ) * coord j₀ (P.resFin ac.1 ac.2 (ac.2.ys.getD k [])) =
          (((T.ΓL.getD j []).getD k 0 : ℤ) - eL.getD j 0 : ℤ))) &&
  P.pts.all (fun ac ↦ decide (ac.1 ∈ T.αL) ||
    (ac.2.ys.all (fun yt ↦ decide (coord j₀ (P.resFin ac.1 ac.2 yt) = rho0 P j₀ ac)) &&
      decide ((s * rho0 P j₀ ac / ac.2.N).den = 1))) &&
  P.inf.ys.all (fun wt ↦ decide (coord j₀ (P.resInf wt) = coord j₀ (P.resInf (P.inf.ys.getD 0 [])))) &&
  decide (((∑ j ∈ Finset.range T.αL.length, eL.getD j 0 : ℤ) : ℚ) +
      ((P.pts.map (fexp P T s j₀)).sum : ℚ) -
      s * coord j₀ (P.resInf (P.inf.ys.getD 0 [])) / P.inf.N = T.cdeg)

/-- The content of `torsResCheck`. -/
structure TorsResFacts (P : CurveProb F) (T : GlobalCert F) (eL : List ℤ) (s : ℕ)
    (j₀ : Fin (dim F)) : Prop where
  Fc : T.Fc = P.Fc
  n : T.n = P.n
  s_pos : 0 < s
  nd : (P.pts.map Prod.fst).Nodup
  Γpt : ∀ j < T.αL.length, ∃ c : BranchCert F, (T.αL.getD j 0, c) ∈ P.pts ∧ c.N = 1 ∧
    1 ≤ c.prec ∧ ∀ k < T.n, (c.ys.getD k []).getD 0 0 = (T.yL.getD j []).getD k 0 ∧
      (s : ℚ) * coord j₀ (P.resFin (T.αL.getD j 0) c (c.ys.getD k [])) =
        (((T.ΓL.getD j []).getD k 0 : ℤ) - eL.getD j 0 : ℤ)
  other : ∀ ac ∈ P.pts, ac.1 ∉ T.αL → (∀ yt ∈ ac.2.ys, coord j₀ (P.resFin ac.1 ac.2 yt) =
    rho0 P j₀ ac) ∧ (s * rho0 P j₀ ac / ac.2.N).den = 1
  inf : ∀ wt ∈ P.inf.ys, coord j₀ (P.resInf wt) = coord j₀ (P.resInf (P.inf.ys.getD 0 []))
  csum : (((∑ j ∈ Finset.range T.αL.length, eL.getD j 0 : ℤ) : ℚ) +
      ((P.pts.map (fexp P T s j₀)).sum : ℚ) -
      s * coord j₀ (P.resInf (P.inf.ys.getD 0 [])) / P.inf.N = T.cdeg)

lemma torsResCheck_spec {P : CurveProb F} {T : GlobalCert F} {eL : List ℤ} {s : ℕ}
    {j₀ : Fin (dim F)} (h : torsResCheck P T eL s j₀ = true) : TorsResFacts P T eL s j₀ := by
  simp only [torsResCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, and_assoc] at h
  obtain ⟨hFc, hn, hs, hnd, hΓ, hoth, hinf, hsum⟩ := h
  refine ⟨hFc, hn, hs, hnd, fun j hj ↦ ?_, fun ac hac hna ↦ ?_, fun wt hwt ↦ hinf wt hwt, hsum⟩
  · have hj' := hΓ j hj
    cases hf : P.pts.find? (fun ac ↦ decide (ac.1 = T.αL.getD j 0)) with
    | none => rw [hf] at hj'; exact absurd hj' (by simp)
    | some ac =>
      rw [hf] at hj'
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hj'
      obtain ⟨⟨hN, hprec⟩, hk⟩ := hj'
      have hmem := List.mem_of_find?_eq_some hf
      have heq : ac.1 = T.αL.getD j 0 := by simpa using List.find?_some hf
      refine ⟨ac.2, ?_, hN, hprec, fun k hk' ↦ ?_⟩
      · rw [← heq]; exact hmem
      · obtain ⟨h1, h2⟩ := hk k hk'
        exact ⟨h1, by rw [← heq]; exact_mod_cast h2⟩
  · rcases hoth ac hac with h1 | ⟨h1, h2⟩
    · exact absurd h1 hna
    · exact ⟨h1, h2⟩

end Defs

section Link

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L] [Field K]
  [CharZero K] [Algebra C K]

lemma toPoly_xSubC (a : F) : toPoly (xSubC a) = X - Polynomial.C a := by
  simp [xSubC, toPoly]; ring

lemma ratSmul_eq (Λ : K →ₗ[ℚ] ℚ) (N : ℕ) (z : K) : Λ ((N : K) * z) = N * Λ z := by
  rw [show (N : K) * z = (N : ℚ) • z by rw [Rat.smul_def]; push_cast; rfl, map_smul, smul_eq_mul]

namespace CurveData

variable (S : CurveData C L)

open Classical in
/-- The order of `x − a` along a finite branch. -/
lemma order_qE_xSubC_fin (ψ : F →+* C) (a : F) (N : ℕ) (hN : 0 < N) (b : K)
    (Y : LaurentSeries K) (hY : (S.F.map (branchSub N b)).eval Y = 0) :
    (S.embG (branchSub N b) (branchSub_injective N hN b) Y hY (S.qE ψ (xSubC a))).order =
      if b = algebraMap C K (ψ a) then (N : ℤ) else 0 := by
  rw [S.embG_qE, toPoly_xSubC, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    order_branchSub N hN b _ (X_sub_C_ne_zero _), Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, rootMultiplicity_X_sub_C]
  split_ifs <;> simp

/-- The order of `x − a` along a branch above infinity. -/
lemma order_qE_xSubC_inf (ψ : F →+* C) (a : F) (N : ℕ) (hN : 0 < N)
    (Y : LaurentSeries K) (hY : (S.F.map (infSub N)).eval Y = 0) :
    (S.embG (infSub N) (infSub_injective N hN) Y hY (S.qE ψ (xSubC a))).order = -(N : ℤ) := by
  rw [S.embG_qE, toPoly_xSubC, order_Q_inf ψ _ (X_sub_C_ne_zero a) N hN, natDegree_X_sub_C,
    mul_one]

variable (P : CurveProb F) (ψ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ))
  (hV : P.ValidFacts)

include hSF hV in
/-- **Residues at a certified point outside `Γ`**: uniform along the certified branches, hence
`N_c Λ(res) = N ρ` along every branch. -/
lemma lam_res_fin_special (Λ : K →ₗ[ℚ] ℚ) {j₀ : Fin (dim F)}
    (hΛ : ∀ r : F, Λ (algebraMap C K (ψ r)) = coord j₀ r) (a1 : F) (c : BranchCert F)
    (hac : (a1, c) ∈ P.pts) (ρ : ℚ) (hρ : ∀ yt ∈ c.ys, coord j₀ (P.resFin a1 c yt) = ρ)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N (algebraMap C K (ψ a1))) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    (c.N : ℚ) * Λ (LaurentSeries.res (S.embG (branchSub N (algebraMap C K (ψ a1)))
      (branchSub_injective N (Nat.pos_of_ne_zero hN) _) x (S.root_of_mem hl hx) (S.fE P ψ) *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ a1)) + single (N : ℤ) (1 : K)))) =
      N * ρ := by
  classical
  have hf := S.fE_spec P ψ hV
  obtain ⟨hl0, hN0⟩ := CurveProb.length_ys_of_cert (hV.certs _ hac)
  obtain ⟨y, hy, hs0⟩ := S.certFinSys (K := K) P ψ hSF hV a1 c hac
  obtain ⟨k, hk⟩ := S.fin_rel_list _ c.N hN0 _ hs0 N hN l hl x hx
  have htr := transfer_res c.N N hN0 (Nat.pos_of_ne_zero hN) _ _
    (HahnSeries.C (algebraMap C K (ψ a1)) + single (c.N : ℤ) (1 : K))
    (HahnSeries.C (algebraMap C K (ψ a1)) + single (N : ℤ) (1 : K)) (hk (S.fE P ψ))
    (by rw [lsub_Xfin, lsub_Xfin, mul_comm])
  obtain ⟨-, hμf, -, hQfl⟩ := hV.prec _ hac
  rw [S.resFin_sem P ψ hSF a1 c hN0 (y k) (S.root_of_split _ _ hs0 k) _ (hy k) hμf hQfl _ hf,
    RingHom.comp_apply] at htr
  have h0 := congrArg Λ htr
  rw [ratSmul_eq, ratSmul_eq, hΛ, hρ _ (S.getD_mem_ys P ψ hSF hV c.ys hl0 k)] at h0
  exact h0

include hSF hV in
/-- **No residue at a point outside the certified ones.** -/
lemma res_fin_regular (b : K)
    (hb : ∀ ac ∈ P.pts, b ≠ algebraMap C K (ψ ac.1))
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    LaurentSeries.res (S.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b)
      x (S.root_of_mem hl hx) (S.fE P ψ) *
        LaurentSeries.derivation (HahnSeries.C b + single (N : ℤ) (1 : K))) = 0 := by
  classical
  have hf := S.fE_spec P ψ hV
  have hsp : ((toPoly (mul P.D (discRC P.Fc P.n P.k))).map ((algebraMap C K).comp ψ)).eval b ≠ 0 := by
    intro h0
    obtain ⟨a0, ha0, hae⟩ := coverCheck_spec _ _ hV.cover ((algebraMap C K).comp ψ) b h0
    obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp ha0
    exact hb ac hac hae
  have hN' := Nat.pos_of_ne_zero hN
  have hDd : toPoly P.D ∣ toPoly (mul P.D (discRC P.Fc P.n P.k)) := ⟨_, toPoly_mul _ _⟩
  have h1 := (S.lb_regular P ψ hSF hV P.D hDd hV.D0 _ P.A hf b hsp N hN' x
    (S.root_of_mem hl hx)).mul (lowerBd_single ((N : ℤ) - 1) (N : K))
  rw [SuperData.derivation_branchX N hN', LaurentSeries.res]
  exact h1 (-1) (by omega)

include hSF hV in
/-- **Residues above infinity**: uniform along the certified branches, hence
`N_∞ Λ(res) = N ρ_∞` along every branch. -/
lemma lam_res_inf (Λ : K →ₗ[ℚ] ℚ) {j₀ : Fin (dim F)}
    (hΛ : ∀ r : F, Λ (algebraMap C K (ψ r)) = coord j₀ r) (ρ : ℚ)
    (hρ : ∀ wt ∈ P.inf.ys, coord j₀ (P.resInf wt) = ρ) (N : ℕ) (hN : N ≠ 0)
    (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    (P.inf.N : ℚ) * Λ (LaurentSeries.res (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) x
      (S.root_of_mem hl hx) (S.fE P ψ) * LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)))) =
      N * ρ := by
  have hf := S.fE_spec P ψ hV
  obtain ⟨hl0, -⟩ := CurveProb.length_ys_of_cert hV.certInf
  obtain ⟨w, hw, hs0⟩ := S.certInfSys (K := K) P ψ hSF hV
  obtain ⟨k, hk⟩ := S.inf_rel_list P.inf.N hV.infN _ hs0 N hN l hl x hx
  have htr := transfer_res P.inf.N N hV.infN (Nat.pos_of_ne_zero hN) _ _
    (single (-(P.inf.N : ℤ)) (1 : K)) (single (-(N : ℤ)) (1 : K)) (hk (S.fE P ψ))
    (by rw [lsub_Xinf, lsub_Xinf, mul_comm])
  rw [S.resInf_sem P ψ hSF hV.infN (w k) (S.root_of_split _ _ hs0 k) _ (hw k) hV.sf hV.Dl hV.okA _
    hf, RingHom.comp_apply] at htr
  have h0 := congrArg Λ htr
  rw [ratSmul_eq, ratSmul_eq, hΛ, hρ _ (S.getD_mem_ys P ψ hSF hV P.inf.ys hl0 k)] at h0
  exact h0

include hSF hV in
/-- **The `j₀`-residues at the points of `Γ`.** -/
lemma lam_res_Γ (Λ : K →ₗ[ℚ] ℚ) {j₀ : Fin (dim F)}
    (hΛ : ∀ r : F, Λ (algebraMap C K (ψ r)) = coord j₀ r) {T : GlobalCert F} {eL : List ℤ}
    {s : ℕ} (hTR : TorsResFacts P T eL s j₀)
    (hy : ∀ j < T.αL.length, (T.yL.getD j []).Nodup ∧ (T.yL.getD j []).length = T.n)
    (j : ℕ) (hj : j < T.αL.length) (k : Fin S.F.natDegree) (Yp : PowerSeries K)
    (hY : (S.F.map (branchSub 1 (algebraMap C K (ψ (T.αL.getD j 0))))).eval
      (ofPowerSeries ℤ K Yp) = 0)
    (hYc : PowerSeries.constantCoeff Yp = algebraMap C K (ψ ((T.yL.getD j []).getD k 0))) :
    (s : ℚ) * Λ (LaurentSeries.res (S.embG (branchSub 1 (algebraMap C K (ψ (T.αL.getD j 0))))
      (branchSub_injective 1 one_pos _) (ofPowerSeries ℤ K Yp) hY (S.fE P ψ) *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ (T.αL.getD j 0))) +
          single ((1 : ℕ) : ℤ) (1 : K)))) =
      (((T.ΓL.getD j []).getD k 0 : ℤ) - eL.getD j 0 : ℤ) := by
  classical
  have hf := S.fE_spec P ψ hV
  have hnS : S.F.natDegree = T.n := by rw [S.natDegree_F_eq P ψ hSF hV, hTR.n]
  obtain ⟨c, hac, hN1, hprec, hck⟩ := hTR.Γpt j hj
  obtain ⟨N, ys, prec⟩ := c
  simp only at hN1 hprec hck
  subst hN1
  obtain ⟨y, hy', hs0⟩ := S.certFinSys (K := K) P ψ hSF hV _ ⟨1, ys, prec⟩ hac
  -- the branch is a certified one
  have hk' : ∃ k', Yp = y k' := by
    have h0 := hY
    rw [hs0, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨k', -, hk'⟩ := h0
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk'
    exact ⟨k', HahnSeries.ofPowerSeries_injective hk'⟩
  obtain ⟨k', rfl⟩ := hk'
  have hc0 : PowerSeries.constantCoeff (y k') =
      algebraMap C K (ψ ((ys.getD k' []).getD 0 0)) := by
    have := (PowerSeries.X_pow_dvd_iff.mp (hy' k')) 0 hprec
    rw [map_sub, sub_eq_zero, coeff_thetaT, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    exact this
  have hkk : k' = k := by
    rw [hc0, (hck k' (by rw [← hnS]; exact k'.2)).1] at hYc
    have h1 := ψ.injective ((algebraMap C K).injective hYc)
    by_contra hne
    exact nodup_getD_ne (hy j hj).1 (by rw [(hy j hj).2, ← hnS]; exact k'.2)
      (by rw [(hy j hj).2, ← hnS]; exact k.2) (Fin.val_ne_of_ne hne) 0 h1
  subst hkk
  obtain ⟨-, hμf, -, hQfl⟩ := hV.prec _ hac
  have hres := S.resFin_sem P ψ hSF (T.αL.getD j 0) ⟨1, ys, prec⟩ one_pos (y k') hY _ (hy' k')
    hμf hQfl _ hf
  simp only at hres
  rw [hres, RingHom.comp_apply, hΛ, (hck k' (by rw [← hnS]; exact k'.2)).2]

end CurveData

end Link

section Main

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L)

lemma fexp_eq {P : CurveProb F} {T : GlobalCert F} {s : ℕ} {j₀ : Fin (dim F)}
    {ac : F × BranchCert F} (hna : ac.1 ∉ T.αL) (hden : (s * rho0 P j₀ ac / ac.2.N).den = 1) :
    (fexp P T s j₀ ac : ℚ) = -(s * rho0 P j₀ ac / ac.2.N) := by
  rw [fexp, if_neg hna]
  exact Rat.coe_int_num_of_den_eq_one (by rw [Rat.den_neg_eq_den]; exact hden)

lemma fexp_mem {P : CurveProb F} {T : GlobalCert F} {s : ℕ} {j₀ : Fin (dim F)}
    {ac : F × BranchCert F} (ha : ac.1 ∈ T.αL) : fexp P T s j₀ ac = 0 := by
  rw [fexp, if_pos ha]

set_option maxHeartbeats 8000000 in
/-- **A Liouville form contradicts the non-torsion certificate.** If `f dx` (the integrand of
`P`) had a Liouville form, the scaled `j₀`-component of its residue divisor would be torsion
(`curve_abel`), which the certificates exclude. -/
theorem false_of_torsRes (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (P : CurveProb F) (ψ : F →+* C)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts) (T : GlobalCert F)
    (hT : T.globalCheck = true) (eL : List ℤ) (s : ℕ) (j₀ : Fin (dim F))
    (hTR : torsResCheck P T eL s j₀ = true) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincCheck T.n ((Pp.mp * Pq.mp) * T.cdeg) Pb T.I.δL T.I.Bc T.I.Dc T.αL T.cΓ
      (T.ΓL.map (·.map ((Pp.mp * Pq.mp) * ·))) Lm = true)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ιI : Type*} [DecidableEq ιI] (sI : Finset ιI) (c : ιI → C)
    (u : ιI → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (heq : (S.fE P ψ : L) = v′ + ∑ i ∈ sI, algebraMap C L (c i) * ((u i)′ / u i)) : False := by
  classical
  set Kb := AlgebraicClosure C
  haveI : CharZero Kb := charZero_of_injective_algebraMap (algebraMap C Kb).injective
  have hTR' := torsResCheck_spec hTR
  have hTf := globalCheck_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  -- the functional `Λ` extending `coord j₀`, and its multiple `s Λ`
  have hinj : Function.Injective ((algebraMap C Kb).comp ψ) :=
    (algebraMap C Kb).injective.comp ψ.injective
  set ιF : F →ₗ[ℚ] Kb := ((algebraMap C Kb).comp ψ).toRatAlgHom.toLinearMap with hιF
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ιF (LinearMap.ker_eq_bot.mpr hinj)
  set Λ : Kb →ₗ[ℚ] ℚ := (coord j₀).comp g with hΛdef
  have hΛ : ∀ r : F, Λ (algebraMap C Kb (ψ r)) = coord j₀ r := fun r ↦ by
    have : g (ιF r) = r := by rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
    rw [hΛdef, LinearMap.comp_apply]
    exact congrArg (coord j₀) this
  set Λs : Kb →ₗ[ℚ] ℚ := (s : ℚ) • Λ with hΛs
  have hΛs' : ∀ z, Λs z = s * Λ z := fun z ↦ by rw [hΛs, LinearMap.smul_apply, smul_eq_mul]
  -- Abel
  obtain ⟨m, hm, w, hw0, hord⟩ := S.curve_abel (K := Kb) hC hx _ v (S.fE P ψ).2 hv sI c u hu hu0
    heq Λs
  -- the points of `Γ`
  obtain ⟨-, hαnd, hptK⟩ := ptCheck_spec (RingHom.id F) (n := T.n) hmon hdeg hTf.pt
  have hy : ∀ j < T.αL.length, (T.yL.getD j []).Nodup ∧ (T.yL.getD j []).length = T.n :=
    fun j hj ↦ ⟨(hptK j hj).1.2, (hptK j hj).1.1⟩
  set α : Fin T.αL.length → F := fun j ↦ T.αL.getD j 0 with hα
  set pt : Fin P.pts.length → F × BranchCert F := fun i ↦ P.pts[i.1] with hpt
  set fe : Fin P.pts.length → ℤ := fun i ↦ fexp P T s j₀ (pt i) with hfe
  set U1 : C⟮S.x⟯⟮S.y⟯ := ∏ j ∈ Finset.univ, (S.qE ψ (xSubC (α j))) ^ ((m : ℤ) * eL.getD j 0)
    with hU1
  set U2 : C⟮S.x⟯⟮S.y⟯ := ∏ i ∈ Finset.univ, (S.qE ψ (xSubC (pt i).1)) ^ ((m : ℤ) * fe i)
    with hU2
  have hq0 : ∀ a : F, S.qE ψ (xSubC a) ≠ 0 := fun a h ↦
    S.qE_ne_zero (ψ₀ := ψ) _ (by rw [toPoly_xSubC]; exact X_sub_C_ne_zero _) (congrArg Subtype.val h)
  have hU10 : U1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hq0 _)
  have hU20 : U2 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hq0 _)
  have hSF' : S.F = (toB T.Fc).map (mapRingHom ψ) := by rw [hSF, hTR'.Fc]
  have hptmem : ∀ i, pt i ∈ P.pts := fun i ↦ List.getElem_mem _
  have hptinj : ∀ i i', (pt i).1 = (pt i').1 → i = i' := fun i i' h ↦ by
    have := (List.Nodup.getElem_inj_iff hTR'.nd (i := i.1) (j := i'.1)
      (hi := by simpa using i.2) (hj := by simpa using i'.2)).mp (by simpa [hpt] using h)
    exact Fin.ext this
  -- orders of the correction factors along finite branches
  have hordU : ∀ (N' : ℕ) (hN' : 0 < N') (b : Kb) (Y : LaurentSeries Kb)
      (hY : (S.F.map (branchSub N' b)).eval Y = 0),
      (S.embG (branchSub N' b) (branchSub_injective N' hN' b) Y hY (U1 * U2)).order =
        (∑ j : Fin T.αL.length, (m : ℤ) * eL.getD j 0 *
          (if b = algebraMap C Kb (ψ (α j)) then (N' : ℤ) else 0)) +
        ∑ i : Fin P.pts.length, (m : ℤ) * fe i *
          (if b = algebraMap C Kb (ψ (pt i).1) then (N' : ℤ) else 0) := by
    intro N' hN' b Y hY
    rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU10)
      ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU20), hU1, hU2,
      S.order_prod_zpow _ _ _ (fun j _ ↦ hq0 _), S.order_prod_zpow _ _ _ (fun i _ ↦ hq0 _)]
    simp only [S.order_qE_xSubC_fin ψ _ N' hN']
  have hordUi : ∀ (N' : ℕ) (hN' : 0 < N') (Y : LaurentSeries Kb)
      (hY : (S.F.map (infSub N')).eval Y = 0),
      (S.embG (infSub N') (infSub_injective N' hN') Y hY (U1 * U2)).order =
        -(N' : ℤ) * m * ((∑ j : Fin T.αL.length, eL.getD j 0) + ∑ i, fe i) := by
    intro N' hN' Y hY
    rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU10)
      ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU20), hU1, hU2,
      S.order_prod_zpow _ _ _ (fun j _ ↦ hq0 _), S.order_prod_zpow _ _ _ (fun i _ ↦ hq0 _)]
    simp only [S.order_qE_xSubC_inf ψ _ N' hN']
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ ↦ by ring
  have hwne : ∀ (g' : C[X] →+* LaurentSeries Kb) (hg' : Function.Injective g') (Y : LaurentSeries Kb)
      (hY : (S.F.map g').eval Y = 0), S.embG g' hg' Y hY w ≠ 0 :=
    fun g' hg' Y hY ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr hw0
  have hUne : ∀ (g' : C[X] →+* LaurentSeries Kb) (hg' : Function.Injective g') (Y : LaurentSeries Kb)
      (hY : (S.F.map g').eval Y = 0), S.embG g' hg' Y hY (U1 * U2) ≠ 0 :=
    fun g' hg' Y hY ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr (mul_ne_zero hU10 hU20)
  refine not_torsion_of_cert_map (Kb := Kb) S ψ T hSF' hT hpq Rp φp hRp Pp hPp Rq φq hRq Pq hPq
    Pb Lm htest m hm ⟨w * (U1 * U2), mul_ne_zero hw0 (mul_ne_zero hU10 hU20), ?_, ?_, ?_⟩
  · -- the points of `Γ`
    intro j k Yp hY hYc
    set a := algebraMap C Kb (ψ (T.αL.getD j 0)) with ha
    have h1 := hord (HahnSeries.C a + single ((1 : ℕ) : ℤ) (1 : Kb)) (hX_fin 1 one_pos a)
      (branchSub 1 a) (branchSub_injective 1 one_pos a)
      (fun Q ↦ by rw [SuperData.branchSub_eq_subst]) (ofPowerSeries ℤ Kb Yp) hY
    simp only [Subtype.coe_eta] at h1
    rw [hΛs', S.lam_res_Γ P ψ hSF hV Λ hΛ hTR' hy j j.2 k Yp hY hYc] at h1
    have h3 : (S.embG (branchSub 1 a) (branchSub_injective 1 one_pos a) (ofPowerSeries ℤ Kb Yp)
        hY w).order = m * (((T.ΓL.getD j []).getD k 0 : ℤ) - eL.getD j 0) := by
      exact_mod_cast h1
    have hs1 : (∑ j' : Fin T.αL.length, (m : ℤ) * eL.getD j' 0 *
        (if a = algebraMap C Kb (ψ (α j')) then ((1 : ℕ) : ℤ) else 0)) = m * eL.getD j 0 := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]; push_cast; ring
      · intro j' _ hj'
        rw [if_neg, mul_zero]
        intro he
        exact nodup_getD_ne hαnd j.2 j'.2 (Fin.val_ne_of_ne (Ne.symm hj')) 0
          (ψ.injective ((algebraMap C Kb).injective he))
      · simp
    have hs2 : (∑ i : Fin P.pts.length, (m : ℤ) * fe i *
        (if a = algebraMap C Kb (ψ (pt i).1) then ((1 : ℕ) : ℤ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs with he
      · have hmem : (pt i).1 ∈ T.αL := by
          rw [ψ.injective ((algebraMap C Kb).injective he).symm, List.getD_eq_getElem _ _ j.2]
          exact List.getElem_mem _
        rw [hfe]; dsimp only; rw [fexp_mem hmem]; ring
      · ring
    rw [map_mul, HahnSeries.order_mul (hwne _ _ _ _) (hUne _ _ _ _), hordU 1 one_pos a _ hY,
      hs1, hs2, h3]
    push_cast; ring_nf; exact le_refl _
  · -- the other finite points
    intro b hb N' hN' l hl r hr
    have hb' : ∀ j : Fin T.αL.length, b ≠ algebraMap C Kb (ψ (α j)) := fun j he ↦ hb ⟨j, he.symm⟩
    have hN0 := Nat.pos_of_ne_zero hN'
    have h1 := hord (HahnSeries.C b + single (N' : ℤ) (1 : Kb)) (hX_fin N' hN0 b)
      (branchSub N' b) (branchSub_injective N' hN0 b)
      (fun Q ↦ by rw [SuperData.branchSub_eq_subst]) r (S.root_of_mem hl hr)
    simp only [Subtype.coe_eta] at h1
    rw [hΛs'] at h1
    have hs1 : (∑ j' : Fin T.αL.length, (m : ℤ) * eL.getD j' 0 *
        (if b = algebraMap C Kb (ψ (α j')) then (N' : ℤ) else 0)) = 0 :=
      Finset.sum_eq_zero fun j' _ ↦ by rw [if_neg (hb' j'), mul_zero]
    rw [map_mul, HahnSeries.order_mul (hwne _ _ _ _) (hUne _ _ _ _), hordU N' hN0 b _ _, hs1,
      zero_add]
    by_cases hsp : ∃ i, b = algebraMap C Kb (ψ (pt i).1)
    · obtain ⟨i, rfl⟩ := hsp
      have hna : (pt i).1 ∉ T.αL := by
        intro hm'
        obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hm'
        exact hb' ⟨j, hj⟩ (by simp only [hα]; rw [List.getD_eq_getElem _ _ hj, hje])
      obtain ⟨hρ, hden⟩ := hTR'.other (pt i) (hptmem i) hna
      have h2 := S.lam_res_fin_special P ψ hSF hV Λ hΛ (pt i).1 (pt i).2 (hptmem i) _ hρ N' hN' l
        hl r hr
      obtain ⟨-, hNc⟩ := CurveProb.length_ys_of_cert (hV.certs _ (hptmem i))
      have hs2 : (∑ i' : Fin P.pts.length, (m : ℤ) * fe i' *
          (if algebraMap C Kb (ψ (pt i).1) = algebraMap C Kb (ψ (pt i').1) then (N' : ℤ)
            else 0)) = m * fe i * N' := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro i' _ hi'
          rw [if_neg, mul_zero]
          intro he
          exact hi' (hptinj i' i (ψ.injective ((algebraMap C Kb).injective he)).symm)
        · simp
      rw [hs2]
      have hfe' : (fe i : ℚ) = -(s * rho0 P j₀ (pt i) / (pt i).2.N) := fexp_eq hna hden
      have hNq : ((pt i).2.N : ℚ) ≠ 0 := by exact_mod_cast hNc.ne'
      have hΛv : Λ (LaurentSeries.res (S.embG (branchSub N' (algebraMap C Kb (ψ (pt i).1)))
          (branchSub_injective N' hN0 _) r (S.root_of_mem hl hr) (S.fE P ψ) *
          LaurentSeries.derivation (HahnSeries.C (algebraMap C Kb (ψ (pt i).1)) +
            single (N' : ℤ) (1 : Kb)))) = N' * rho0 P j₀ (pt i) / (pt i).2.N := by
        field_simp; linarith [h2]
      rw [hΛv] at h1
      have h4 : ((S.embG (branchSub N' (algebraMap C Kb (ψ (pt i).1)))
          (branchSub_injective N' hN0 _) r (S.root_of_mem hl hr) w).order + m * fe i * N' : ℤ) =
          (0 : ℚ) := by
        push_cast; rw [h1, hfe']; field_simp; ring
      exact_mod_cast h4.ge
    · push Not at hsp
      have hreg := S.res_fin_regular P ψ hSF hV b (fun ac hac h ↦ by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hac
        exact hsp ⟨i, hi⟩ h) N' hN' l hl r hr
      rw [hreg, map_zero, mul_zero, mul_zero] at h1
      have hs2 : (∑ i : Fin P.pts.length, (m : ℤ) * fe i *
          (if b = algebraMap C Kb (ψ (pt i).1) then (N' : ℤ) else 0)) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by rw [if_neg (hsp i), mul_zero]
      rw [hs2, add_zero]
      exact_mod_cast h1.ge
  · -- infinity
    intro N' hN' l hl r hr
    have hN0 := Nat.pos_of_ne_zero hN'
    have h1 := hord (single (-(N' : ℤ)) (1 : Kb)) (hX_inf N' hN0)
      (infSub N') (infSub_injective N' hN0)
      (fun Q ↦ by rw [SuperData.infSub_eq_subst]) r (S.root_of_mem hl hr)
    simp only [Subtype.coe_eta] at h1
    rw [hΛs'] at h1
    have h2 := S.lam_res_inf P ψ hSF hV Λ hΛ _ hTR'.inf N' hN' l hl r hr
    have hNq : (P.inf.N : ℚ) ≠ 0 := by exact_mod_cast hV.infN.ne'
    rw [map_mul, HahnSeries.order_mul (hwne _ _ _ _) (hUne _ _ _ _), hordUi N' hN0 _ _]
    have hfs : (∑ i : Fin P.pts.length, (fe i : ℚ)) = ((P.pts.map (fexp P T s j₀)).sum : ℚ) := by
      rw [← Int.cast_sum]
      congr 1
      rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
    have hes : (∑ j : Fin T.αL.length, (eL.getD j 0 : ℚ)) =
        ((∑ j ∈ Finset.range T.αL.length, eL.getD j 0 : ℤ) : ℚ) := by
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ (eL.getD j 0 : ℚ)), Int.cast_sum]
    have hcs := hTR'.csum
    have hΛv : Λ (LaurentSeries.res (S.embG (infSub N') (infSub_injective N' hN0) r
        (S.root_of_mem hl hr) (S.fE P ψ) * LaurentSeries.derivation (single (-(N' : ℤ)) (1 : Kb)))) =
        N' * coord j₀ (P.resInf (P.inf.ys.getD 0 [])) / P.inf.N := by
      field_simp; linarith [h2]
    rw [hΛv] at h1
    have h4 : ((S.embG (infSub N') (infSub_injective N' hN0) r (S.root_of_mem hl hr) w).order +
        -(N' : ℤ) * m * ((∑ j : Fin T.αL.length, eL.getD j 0) + ∑ i, fe i) : ℤ) =
        ((-((N' * (m * T.cdeg) : ℕ) : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [h1, hfs, hes, ← hcs]
      field_simp; ring
    exact_mod_cast h4.ge

end CurveData

end Main

end Curves
