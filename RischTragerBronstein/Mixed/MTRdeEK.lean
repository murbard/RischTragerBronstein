import RischTragerBronstein.Mixed.MTRdeED
import RischTragerBronstein.Computable.NestXRdeEK

/-!
# Mixed towers over a curve (`RdeEK`)

Ported from `Tower.NestX` (`NestXRdeEK`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u


namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


set_option maxHeartbeats 6400000 in
/-- **The denominator bound**: every solution of `y′ + f y = ∑ cᵢ wᵢ` is `Y / Q`. -/
theorem pe_denominatorXE (m : ℕ) (hM : T.MixHyp (m + 1)) {a : LC m}
    (hk : ks m = .exp a)
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (hc : PrXEC m) (hhc : GPoly.toPoly (T.MX m hM.tr) hc.2 ≠ 0)
    (logs : List (LgXEC m)) (hok : ∀ cw ∈ logs, ((T.M1X m hM.tr).sem cw.1)′ = 0)
    (Wc : List (PrXEC m)) (hWc : ∀ q ∈ Wc, GPoly.toPoly (T.MX m hM.tr) q.2 ≠ 0) (c : ℕ → Cc)
    (y : T.F (m + 1))
    (hy : y′ + (((T.M1X m hM.tr).sem hc)′ + logSumV (T.M1X m hM.tr) logs) * y =
      ∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c i) *
        (T.M1X m hM.tr).sem (Wc.getD i ([], []))) :
    ∃ Yv : (T.F m)[X], y * T.σX m hM.tr (peQ (MO Fc ks m)
      (kapXEC Fc ks m a hc (peEps (MO Fc ks m) Wc) (sumOrdXEC Fc ks m (logsCXE (MO Fc ks m) logs)))
      (DXEC Fc ks m Wc logs)) = T.phi m Yv := by
  classical
  set h := hM.tr with hh
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  set O := MO Fc ks m with hO
  set d : LgXEC m := (([], [O.one]), ([], [O.one])) with hd
  obtain ⟨κ, hκ⟩ := T.exists_consts_XE m h logs hok d
  set len := logs.length with hlen
  set cK : ℕ → T.F m := fun i ↦ algebraMap Cc (T.F m) (κ i) with hcK
  set Nw : ℕ → (T.F m)[X] := fun i ↦ T.NwXE m h (logs.getD i d) with hNw
  set Dw : ℕ → (T.F m)[X] := fun i ↦ T.DwXE m h (logs.getD i d) with hDw
  -- the normal part of the denominators
  obtain ⟨e, he⟩ : ∃ e, e = peE O Wc := ⟨_, rfl⟩
  obtain ⟨he0, hediv⟩ := T.peE_specXE m h Wc hWc
  rw [← he] at he0 hediv
  obtain ⟨uD, hDu, hDm⟩ := T.DXE_spec m h Wc logs (he ▸ he0)
  rw [← he] at hDu
  set G := (GPoly.egcd O e (GPoly.derivT O (wKC O (ks m)) e)).1 with hG
  have hGbez : GPoly.toPoly (T.MX m h) (GPoly.egcd O e (GPoly.derivT O (wKC O (ks m)) e)).2.1 *
      GPoly.toPoly (T.MX m h) e + GPoly.toPoly (T.MX m h)
        (GPoly.egcd O e (GPoly.derivT O (wKC O (ks m)) e)).2.2 *
      implicitDeriv (T.wPoly m) (GPoly.toPoly (T.MX m h) e) = GPoly.toPoly (T.MX m h) G := by
    have := GPoly.egcd_spec (T.MX m h) e (GPoly.derivT O (wKC O (ks m)) e)
    rwa [GPoly.toPoly_derivT, T.toPoly_wKX] at this
  obtain ⟨eps, heps⟩ : ∃ eps, eps = peEps O Wc := ⟨_, rfl⟩
  obtain ⟨kap, hkap⟩ : ∃ kap, kap = kapXEC Fc ks m a hc eps (sumOrdXEC Fc ks m (logsCXE O logs)) :=
    ⟨_, rfl⟩
  rw [← heps, ← hkap]
  obtain ⟨D, hDd⟩ : ∃ D, D = DXEC Fc ks m Wc logs := ⟨_, rfl⟩
  rw [← hDd] at hDu hDm ⊢
  -- the setting `K = F m (t)`
  set t := T.ts m with ht
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : L) = aeval t P :=
    algebraMap_adjoinSimple _
  have hDe : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.bX m h a) * X) P := fun P ↦ by
    change implicitDeriv (T.wPoly m) P = _
    rw [T.wPoly_eq_bX m h hk]
  set φK := algebraMap (T.F m)[X] (T.F m)⟮t⟯ with hφK
  have hinj : Function.Injective φK := IsFractionRing.injective _ _
  -- the transfer `F (m + 1) → K`
  let toK : T.F (m + 1) →+* (T.F m)⟮t⟯ :=
    { toFun := fun z ↦ ⟨(z : L), (T.mem_F_succ).mp z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have htoK_phi : ∀ P, toK (T.phi m P) = φK P := fun P ↦ Subtype.ext (by
    change ((T.phi m P : T.F (m + 1)) : L) = _
    rw [T.coe_phi, hφK, hcoe])
  have htoK_inj : Function.Injective toK := fun a b hab ↦
    Subtype.ext (congrArg Subtype.val hab)
  have htoK_der : ∀ z, toK z′ = (toK z)′ := fun z ↦ rfl
  have htoK_ld : ∀ z, toK (logDeriv z) = logDeriv (toK z) := by
    intro z; unfold logDeriv; rw [map_div₀, htoK_der]
  have hsemK : ∀ q : PrXEC m, toK ((T.M1X m h).sem q) =
      φK (GPoly.toPoly (T.MX m h) q.1) / φK (GPoly.toPoly (T.MX m h) q.2) := fun q ↦ by
    rw [T.semX, map_div₀, htoK_phi, htoK_phi]
  -- the equation in `K`
  set yK := toK y with hyK
  set hK := toK ((T.M1X m h).sem hc) with hhK
  set gK := toK (∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c i) *
    (T.M1X m h).sem (Wc.getD i ([], []))) with hgK
  set R := ∑ i ∈ Finset.range len, φK (C (cK i)) * logDeriv (φK (Nw i) / φK (Dw i)) with hR
  have hrde : yK′ + (hK′ + R) * yK = gK := by
    have := congrArg toK hy
    rw [T.logSumV_eqXE m h logs d κ hκ] at this
    simp only [map_add, map_mul, map_sum, htoK_der, htoK_ld, map_div₀, htoK_phi] at this
    exact this
  have hgK' : gK = ∑ i ∈ Finset.range Wc.length, φK (C (algebraMap Cc (T.F m) (c i))) *
      (φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).1) /
        φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).2)) := by
    rw [hgK, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, T.algebraMap_succ, htoK_phi, hsemK]
  -- the weights
  have hWi : ∀ i < Wc.length, ∃ (dd qq : (T.F m)[X]) (s : ℕ),
      GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).2 = X ^ s * dd ∧ dd ≠ 0 ∧ ¬X ∣ dd ∧
      GPoly.toPoly (T.MX m h) e = dd * qq := by
    intro i hi
    have hmem : Wc.getD i ([], []) ∈ Wc := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    have hq0 := hWc _ hmem
    obtain ⟨qq, hqq⟩ := hediv _ hmem
    refine ⟨_, qq, _, toPoly_lowZ (T.MX m h) _, fun h0 ↦ hq0 ?_,
      not_X_dvd_drop_lowZ (T.MX m h) _ hq0, hqq⟩
    rw [toPoly_lowZ (T.MX m h), h0, mul_zero]
  -- normal primes
  have hnormal : ∀ (p : (T.F m)[X]) (_ : p.Monic) (hp : Irreducible p), ¬X ∣ p →
      yK * φK (GPoly.toPoly (T.MX m h) D) ∈ regularAt (T.F m)⟮t⟯ p hp.prime := by
    intro p _ hp hXp
    have hnorm : ¬p ∣ p′ := T.normal_exp m htr hk p hp hXp
    have hpX : ¬p ∣ X := fun hdvd ↦ hXp (hp.dvd_symm irreducible_X hdvd)
    have hgreg : gK * φK (GPoly.toPoly (T.MX m h) e) ∈ regularAt (T.F m)⟮t⟯ p hp.prime := by
      rw [hgK', Finset.sum_mul]
      refine Subring.sum_mem _ fun i hi ↦ ?_
      obtain ⟨dd, qq, s, hds, hdd0, -, heq⟩ := hWi i (Finset.mem_range.mp hi)
      rw [mul_assoc]
      refine mul_mem (algebraMap_mem_regularAt _ _) ?_
      have hφX : φK (X ^ s) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
      have hφd : φK dd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hdd0
      have e1 : φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).1) /
          φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).2) * φK (GPoly.toPoly (T.MX m h) e) =
          φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).1 * qq) / φK (X ^ s) := by
        rw [hds, heq, map_mul, map_mul, map_mul]
        field_simp
      rw [e1]
      exact ⟨GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).1 * qq, X ^ s,
        fun hdvd ↦ hpX (hp.prime.dvd_of_dvd_pow hdvd), div_mul_cancel₀ _ hφX⟩
    have hmain := rde_log_denominator (K := (T.F m)⟮t⟯) hp hnorm hK yK gK (Finset.range len) cK
      Nw Dw (fun i _ ↦ T.NwD_ne_XE m h _) (GPoly.toPoly (T.MX m h) e) he0 hgreg
      (GPoly.toPoly (T.MX m h) G) _ _ hGbez (GPoly.toPoly (T.MX m h) (logPoly O true logs))
      (fun i hi hdvd ↦ T.dvd_logPolyXE m h logs _ (by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]; exact List.getElem_mem _)
        p hp hXp hdvd) (logBoundC Fc ks m logs)
      (fun k n _ hn hkn ↦ T.logBound_geXE m h logs d κ hκ k n hn hkn) hrde
    rw [hDu, map_mul, mul_comm (φK (C uD)), ← mul_assoc]
    exact mul_mem hmain (algebraMap_mem_regularAt _ _)
  -- the special prime `t`: the right-hand side
  have hgX : gK * φK (X ^ eps) ∈ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X := by
    rw [hgK', Finset.sum_mul]
    refine Subring.sum_mem _ fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [mul_assoc]
    refine mul_mem (algebraMap_mem_regularAt _ _) ?_
    have hmem : Wc.getD i ([], []) ∈ Wc := by
      rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem _
    set q := Wc.getD i ([], []) with hqd
    by_cases hz : GPoly.isZero O q.1 = true
    · rw [(GPoly.isZero_iff (T.MX m h) _).mp hz, map_zero, zero_div, zero_mul]; exact zero_mem _
    · have hle := peEps_ge O Wc q hmem (by simpa using hz)
      rw [← heps] at hle
      have hq2 := hWc q hmem
      have hu := toPoly_lowZ (T.MX m h) q.1
      have hs := toPoly_lowZ (T.MX m h) q.2
      have hXd := not_X_dvd_drop_lowZ (T.MX m h) q.2 hq2
      set u := lowZ O q.1
      set v := lowZ O q.2
      set n' := GPoly.toPoly (T.MX m h) (q.1.drop u)
      set dq := GPoly.toPoly (T.MX m h) (q.2.drop v)
      have hd0 : dq ≠ 0 := fun h0 ↦ hq2 (by rw [hs, h0, mul_zero])
      have hφd : φK dq ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
      have hφX : ∀ k, φK (X ^ k) ≠ 0 := fun k ↦
        (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
      refine ⟨X ^ (u + eps - v) * n', dq, hXd, ?_⟩
      rw [hu, hs, map_mul, map_mul, map_mul]
      have hpow : (X : (T.F m)[X]) ^ (u + eps) = X ^ (u + eps - v) * X ^ v := by
        rw [← pow_add]; congr 1; omega
      have h1 : φK (X ^ u) * φK (X ^ eps) = φK (X ^ (u + eps - v)) * φK (X ^ v) := by
        rw [← map_mul, ← map_mul, ← pow_add, hpow]
      have hv0 := hφX v
      simp only [← hφK]
      field_simp
      linear_combination φK n' * h1
  -- the logarithmic part at `t`
  obtain ⟨rL, hrL, hLv⟩ := logSum_val_X hDe (K := (T.F m)⟮t⟯) (Finset.range len) cK Nw Dw
    (fun i ↦ T.N1XE m h (logs.getD i d)) (fun i ↦ T.D1XE m h (logs.getD i d))
    (fun i ↦ aNXE O (logs.getD i d)) (fun i ↦ aDXE O (logs.getD i d))
    (fun i _ ↦ T.Nw_splitXE m h _) (fun i _ ↦ T.Dw_splitXE m h _)
  rw [← hR] at hLv
  have hRX : R ∈ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X := by
    rw [hLv]
    exact add_mem (algebraMap_mem_regularAt _ _)
      (mul_mem (algebraMap_mem_regularAt _ _) hrL)
  -- the data of `h`
  have hhn := toPoly_lowZ (T.MX m h) hc.1
  have hhd := toPoly_lowZ (T.MX m h) hc.2
  have hXd := not_X_dvd_drop_lowZ (T.MX m h) hc.2 hhc
  obtain ⟨u, hu⟩ : ∃ u, u = lowZ O hc.1 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = lowZ O hc.2 := ⟨_, rfl⟩
  obtain ⟨n', hn'⟩ : ∃ n', n' = GPoly.toPoly (T.MX m h) (hc.1.drop u) := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d', d' = GPoly.toPoly (T.MX m h) (hc.2.drop v) := ⟨_, rfl⟩
  rw [← hu, ← hn'] at hhn
  rw [← hv, ← hd'] at hhd hXd
  have hd'0 : d' ≠ 0 := fun h0 ↦ hhc (by rw [hhd, h0, mul_zero])
  have hφd' : φK d' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd'0
  have hφXk : ∀ k, φK (X ^ k) ≠ 0 := fun k ↦
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hKv : hK = φK (X ^ u * n') / φK (X ^ v * d') := by rw [hhK, hsemK, ← hhn, ← hhd]
  have hhomE := hM.homX T (Nat.lt_succ_self m) hk h
  have hspecial : yK * φK (X ^ kap) ∈ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X := by
    by_cases hcase : (!GPoly.isZero O hc.1 && decide (lowZ O hc.1 < lowZ O hc.2)) = true
    · -- `h` has a pole at `t`
      have hkap' : kap = eps := by rw [hkap]; unfold kapXEC; rw [if_pos hcase]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcase
      obtain ⟨hz, hlt⟩ := hcase
      rw [← hu, ← hv] at hlt
      have hn'0 : ¬X ∣ n' := by
        rw [hn', hu]
        refine not_X_dvd_drop_lowZ (T.MX m h) hc.1 fun h0 ↦ ?_
        rw [(GPoly.isZero_iff (T.MX m h) _).mpr h0] at hz; exact Bool.noConfusion hz
      have hKnot : hK ∉ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X := by
        rintro ⟨a', b', hb', heq⟩
        rw [hKv] at heq
        have hx : X ^ u * n' * b' = a' * (X ^ v * d') := by
          apply hinj
          simp only [map_mul] at heq ⊢
          have := hφXk v
          field_simp at heq
          linear_combination heq
        obtain ⟨w, rfl⟩ : ∃ w, v = u + (w + 1) := ⟨v - u - 1, by omega⟩
        have hx' : n' * b' = X * (X ^ w * a' * d') := by
          apply mul_left_cancel₀ (pow_ne_zero u (X_ne_zero : (X : (T.F m)[X]) ≠ 0))
          rw [← mul_assoc, hx]
          ring
        rcases (prime_X (R := T.F m)).dvd_or_dvd ⟨_, hx'⟩ with h1 | h1
        · exact hn'0 h1
        · exact hb' h1
      rw [hkap']
      refine rde_special_bound_pole_R hDe (fun l hl e' he' h0 ↦ ?_) hK yK gK R eps hgX hKnot hRX
        hrde
      have := hhomE (-(l : ℤ)) (by omega) e' he'
      apply this
      push_cast
      linear_combination h0
    · -- `h` is regular at `t`
      set h0 := (T.MX m h).sem (peH0 O hc) with hh0
      have hKr : ∃ rh, rh ∈ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X ∧
          hK = φK (C h0) + φK X * rh := by
        by_cases hz : GPoly.isZero O hc.1 = true
        · have hz' := (GPoly.isZero_iff (T.MX m h) _).mp hz
          have h00 : h0 = 0 := by
            rw [hh0, peH0, (T.MX m h).sem_mul, ← coeff_toPoly_getD', hz', coeff_zero, zero_mul]
          refine ⟨0, zero_mem _, ?_⟩
          rw [h00, hhK, hsemK, hz']
          simp
        · have hlt : ¬lowZ O hc.1 < lowZ O hc.2 := by
            intro hlt; apply hcase; simp [hz, hlt]
          rw [← hu, ← hv] at hlt
          push_neg at hlt
          obtain ⟨w, rfl⟩ : ∃ w, u = v + w := ⟨u - v, by omega⟩
          have hcn : (GPoly.toPoly (T.MX m h) hc.1).coeff v =
              (T.MX m h).sem (hc.1.getD v O.zero) := coeff_toPoly_getD' _ _ _
          have hcd : (GPoly.toPoly (T.MX m h) hc.2).coeff v =
              (T.MX m h).sem (hc.2.getD v O.zero) := coeff_toPoly_getD' _ _ _
          rw [hhn] at hcn
          rw [hhd] at hcd
          have hd0' : d'.coeff 0 ≠ 0 := fun h0 ↦ hXd (X_dvd_iff.mpr h0)
          have c1 : (X ^ (v + w) * n').coeff v = (X ^ w * n').coeff 0 := by
            rw [pow_add, mul_assoc, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
          have c2 : (X ^ v * d').coeff v = d'.coeff 0 := by
            rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
          have hh0v : h0 * d'.coeff 0 = (X ^ w * n').coeff 0 := by
            rw [hh0, peH0, (T.MX m h).sem_mul, (T.MX m h).sem_inv, ← hv, ← hcn, ← hcd, c1, c2]
            field_simp
          obtain ⟨q, hq⟩ : X ∣ X ^ w * n' - C h0 * d' := by
            rw [X_dvd_iff, coeff_sub, coeff_C_mul, hh0v, sub_self]
          refine ⟨φK q / φK d', ⟨q, d', hXd, div_mul_cancel₀ _ hφd'⟩, ?_⟩
          rw [hKv]
          have e1 : X ^ (v + w) * n' = X ^ v * (C h0 * d' + X * q) := by
            rw [← hq, pow_add]; ring
          rw [e1, map_mul, map_mul, map_add, map_mul, map_mul]
          have := hφXk v
          field_simp
      obtain ⟨rh, hrh, hKr⟩ := hKr
      refine rde_special_bound_reg_R hDe hK yK gK R eps kap
        (by rw [hkap]; exact eps_le_kapXEC _ _ _ _ _ _ _) hgX h0 rh hrh hKr _ rL hrL hLv
        (fun k hk' e' he' ↦ T.hno_XE m hM hk hc2 logs d κ hκ hc eps hcase k (hkap ▸ hk') e' he')
        hrde
  -- the combination
  have hreg : ∀ (p : (T.F m)[X]) (_ : p.Monic) (hp : Irreducible p),
      yK * φK (GPoly.toPoly (T.MX m h) (peQ O kap D)) ∈ regularAt (T.F m)⟮t⟯ p hp.prime := by
    intro p hpm hp
    rw [T.toPoly_peQX, map_mul]
    by_cases hXp : X ∣ p
    · have hpX : p = X := eq_of_monic_of_associated hpm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp)
      subst hpX
      rw [← mul_assoc]
      exact mul_mem hspecial (algebraMap_mem_regularAt _ _)
    · rw [mul_comm (φK _), ← mul_assoc]
      exact mul_mem (hnormal p hpm hp hXp) (algebraMap_mem_regularAt _ _)
  obtain ⟨Yv, hYv⟩ := exists_polynomial_of_regularAt _ hreg
  refine ⟨Yv, htoK_inj ?_⟩
  rw [map_mul, htoK_phi, htoK_phi]
  exact hYv


end MTower

end Curves.MT
