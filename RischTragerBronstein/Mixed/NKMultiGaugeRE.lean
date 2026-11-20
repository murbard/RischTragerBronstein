import RischTragerBronstein.Mixed.NKMultiGaugeR
import RischTragerBronstein.Mixed.NKExpCurve

/-!
# The gauge at infinity for rational places of any slopes over an exponential level

`multi_gauge_ramE`: as `multi_gauge_ram` for `t′ = b t`: the expansion of `w′` at the window
`T^{h N/e}` is the derivative of the jet minus `(h/e) b` times it (`coeff_dS_infSpeedE`), so the
twisted jets satisfy `A′ = Λ A − A T` with `T` diagonal, `(t/e) γ′/γ − (h/e) b`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

section TwistB

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- `twist_deriv` with an extra diagonal term `β`. -/
lemma twist_derivB {n : ℕ} (J : Fin n → K) (lam : Fin n → Fin n → K) (β : K)
    (hJ : ∀ i, (J i)′ = ∑ j, lam i j * J j + β * J i) (c Γ : K) (hc : c ≠ 0) (e t : ℕ) (he : 0 < e)
    (hcΓ : c ^ e = Γ) (i : Fin n) :
    (J i / c ^ t)′ = ∑ j, lam i j * (J j / c ^ t) + β * (J i / c ^ t) -
      (J i / c ^ t) * (((t : K) / e) * (Γ′ / Γ)) := by
  have hct0 : c ^ t ≠ 0 := pow_ne_zero _ hc
  have he' : (e : K) ≠ 0 := by exact_mod_cast he.ne'
  have key : ∀ m : ℕ, (c ^ m)′ = (m : K) * c ^ m * (c′ / c) := by
    intro m
    rcases m with _ | m
    · simp
    · rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, pow_succ]
      field_simp
  have hΓ : Γ′ / Γ = (e : K) * (c′ / c) := by
    rw [← hcΓ, key e]; field_simp
  have hs : ∑ j, lam i j * (J j / c ^ t) = (∑ j, lam i j * J j) / c ^ t := by
    rw [Finset.sum_div]; simp only [mul_div_assoc]
  rw [hs, hΓ, Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, key t, hJ i]
  generalize ∑ j, lam i j * J j = s
  field_simp
  have : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  linear_combination (-(c ^ t * ↑t * c′ * J i)) * this

end TwistB

section RamGaugeE

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

set_option maxHeartbeats 8000000 in
/-- **The gauge at infinity for rational places of any slopes, ramified or not**: the twisted
window values `A` of the rescaled basis along representatives of the places form an invertible
matrix over `C` with `A′ = Λ A − A T`, `T` diagonal with entries `(t/e) γ′/γ`, `γ = cᵉ` the
`e`-th power of a leading coefficient. -/
theorem multi_gauge_ramE [IsGalois C K] (bc : C) (hx : S.x′ = aeval S.x (Polynomial.C bc * X))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) (N : ℕ) (hN : 0 < N)
    (l : List (LaurentSeries K)) (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hl0 : ∀ r ∈ l, r ≠ 0) (e : ℤ → ℕ) (sp : ℤ → ℤ)
    (hdata : ∀ r ∈ l, 0 < e r.order ∧ e r.order ∣ N ∧ Int.gcd (sp r.order) (e r.order) = 1 ∧
      r.order = -((N / e r.order : ℕ) * sp r.order))
    (hce : ∀ r ∈ l, (r.coeff r.order) ^ e r.order ∈ Set.range (algebraMap C K))
    (huniq : ∀ r₁ ∈ l, ∀ r₂ ∈ l, r₁.order = r₂.order → r₁.coeff r₁.order = r₂.coeff r₂.order →
      r₁ = r₂)
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hrw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C bc * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqE bc r P S0 i j).natDegree ≤ (X ^ r i * S0).natDegree) :
    ∃ (A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C) (Td : Fin S.F.natDegree → C),
      A.det ≠ 0 ∧
      (∀ i a, (A i a)′ = ∑ j, (pqE bc r P S0 i j).coeff (X ^ r i * S0).natDegree /
        (X ^ r i * S0).leadingCoeff * A j a - A i a * Td a) ∧
      ∀ a, ∃ (q1 q : ℚ) (γ : C), γ ≠ 0 ∧ Td a = q * (γ′ / γ) + q1 * bc := by
  classical
  have hlen : l.length = S.F.natDegree := S.length_of_split hl
  set ρ : Fin l.length → LaurentSeries K := fun a ↦ l[(a : ℕ)] with hρdef
  have hρl : ∀ a, ρ a ∈ l := fun a ↦ List.getElem_mem _
  have hρr : ∀ a, (S.F.map (infSub N)).eval (ρ a) = 0 := fun a ↦ S.root_of_mem hl (hρl a)
  set φ : Fin l.length → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) := fun a ↦
    S.embG (infSub N) (infSub_injective N hN) (ρ a) (hρr a) with hφ
  have : NeZero ((N : ℕ) : K) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  obtain ⟨rep, hh, hhr, hsurj⟩ := S.orbit_data N hN hζ l hl hl0 e sp hdata huniq
  have hrepord : ∀ a, (ρ (rep a)).order = (ρ a).order := fun a ↦ by
    have := (hhr a).2
    rw [show l[(a : ℕ)] = ρ a from rfl, show l[((rep a) : ℕ)] = ρ (rep a) from rfl] at this
    rw [this, rot_order]
  -- the twists
  have htw : ∀ a, ∃ t : ℕ, ((e (ρ a).order : ℕ) : ℤ) ∣ hh a + sp (ρ a).order * t := fun a ↦
    exists_twist _ (hdata _ (hρl a)).1 _ (hdata _ (hρl a)).2.2.1 _
  choose tt htt using htw
  -- the columns are rational
  have hcol : ∀ (i : Fin S.F.natDegree) (a : Fin l.length), ∃ b : C, algebraMap C K b =
      (φ (rep a) (S.wTil w r i)).coeff ((hh a * (N / e (ρ a).order) : ℕ) : ℤ) /
        ((ρ (rep a)).coeff (ρ (rep a)).order) ^ tt a := by
    intro i a
    obtain ⟨he, hed, hcop, hor⟩ := hdata _ (hρl (rep a))
    rw [hrepord] at he hed hcop hor
    have hce' : ((ρ (rep a)).coeff (ρ (rep a)).order) ^ e (ρ a).order ∈
        Set.range (algebraMap C K) := by
      have := hce _ (hρl (rep a))
      rwa [show e (ρ (rep a)).order = e (ρ a).order by rw [hrepord]] at this
    exact S.jet_eigen N hN hζ l hl (hρl (rep a)) (hl0 _ (hρl _)) (e (ρ a).order) he hed
      (sp (ρ a).order) hcop (by rw [hrepord]; exact hor) hce'
      (fun r₁ h₁ r₂ h₂ ho hc ↦ huniq r₁ h₁ r₂ h₂ ho hc) _ (hh a) (tt a) (htt a)
  choose A0 hA0 using hcol
  -- the leading coefficients of the representatives and their `e`-th powers
  set cst : Fin l.length → K := fun a ↦ (ρ (rep a)).coeff (ρ (rep a)).order with hcst
  have hcst0 : ∀ a, cst a ≠ 0 := fun a h0 ↦
    hl0 _ (hρl (rep a)) (HahnSeries.coeff_order_eq_zero.mp h0)
  have hγex : ∀ a, ∃ γ : C, algebraMap C K γ = cst a ^ e (ρ a).order := fun a ↦ by
    have := hce _ (hρl (rep a))
    rw [show e (ρ (rep a)).order = e (ρ a).order by rw [hrepord]] at this
    obtain ⟨γ, hγ⟩ := this
    exact ⟨γ, hγ⟩
  choose γ hγ using hγex
  have hγ0 : ∀ a, γ a ≠ 0 := fun a h0 ↦ by
    have := hγ a
    rw [h0, map_zero] at this
    exact pow_ne_zero _ (hcst0 a) this.symm
  -- the matrix and the diagonal
  set cs : Fin S.F.natDegree → Fin l.length := fun a ↦ Fin.cast hlen.symm a with hcs
  set A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := Matrix.of fun i a ↦ A0 i (cs a)
    with hA
  set Td : Fin S.F.natDegree → C := fun a ↦
    ((((tt (cs a) : ℚ) / (e (ρ (cs a)).order : ℚ) : ℚ) : C)) * ((γ (cs a))′ / γ (cs a)) +
      (((-(hh (cs a) : ℚ) / (e (ρ (cs a)).order : ℚ) : ℚ) : C)) * bc with hTd
  -- the jets and their derivatives
  have hWLB : ∀ i m, LowerBd (φ m (S.wTil w r i)) 0 := fun i m ↦ by
    have := S.infOrd_wTil w r i (hrw i) N hN.ne' l hl (ρ m) (hρl m)
    simpa using this
  set lamK : Fin S.F.natDegree → Fin S.F.natDegree → K := fun i j ↦
    algebraMap C K ((pqE bc r P S0 i j).coeff (X ^ r i * S0).natDegree /
      (X ^ r i * S0).leadingCoeff) with hlamK
  set Jv : Fin l.length → Fin S.F.natDegree → K := fun m i ↦
    (φ (rep m) (S.wTil w r i)).coeff ((hh m * (N / e (ρ m).order) : ℕ) : ℤ) with hJv
  have hJd : ∀ m i, (Jv m i)′ = ∑ j, lamK i j * Jv m j +
      ((hh m : K) / (e (ρ m).order : K) * algebraMap C K bc) * Jv m i := by
    intro m i
    set kk : ℤ := ((hh m * (N / e (ρ m).order) : ℕ) : ℤ) with hkk
    obtain ⟨he, hed, -, -⟩ := hdata _ (hρl m)
    have hkN : kk < N := by
      have h1 : hh m * (N / e (ρ m).order) < e (ρ m).order * (N / e (ρ m).order) :=
        Nat.mul_lt_mul_of_pos_right (hhr m).1 (Nat.div_pos (Nat.le_of_dvd hN hed) he)
      rw [Nat.mul_div_cancel' hed] at h1
      rw [hkk]; exact_mod_cast h1
    set q : C[X] := X ^ r i * S0 with hq
    have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hqK := infSub_ne_zero (K := K) N hN q hq0
    have hmem := S.derivClosedXYW' (Polynomial.C bc * X) hx (S.wTil w r i) (S.wTil w r i).2
    have hdw := S.deriv_wTilE bc hx w r S0 P hP i
    have hid : (⟨(S.wTil w r i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE q =
        ∑ j, S.polyE (pqE bc r P S0 i j) * S.wTil w r j := Subtype.ext (by
      push_cast
      exact hdw)
    have hemb := congrArg (φ (rep m)) hid
    rw [map_mul, map_sum] at hemb
    simp only [map_mul] at hemb
    rw [show φ (rep m) (S.polyE q) = infSub N q from S.embG_polyX _ _ _ _ _ _] at hemb
    have hpoly : ∀ j, φ (rep m) (S.polyE (pqE bc r P S0 i j)) = infSub N (pqE bc r P S0 i j) :=
      fun j ↦ S.embG_polyX _ _ _ _ _ _
    simp only [hpoly] at hemb
    have hder : φ (rep m) ⟨(S.wTil w r i : L)′, hmem⟩ =
        ∑ j, (infSub (K := K) N (pqE bc r P S0 i j) * (infSub (K := K) N q)⁻¹) *
          φ (rep m) (S.wTil w r j) := by
      have : φ (rep m) ⟨(S.wTil w r i : L)′, hmem⟩ =
          (∑ j, infSub (K := K) N (pqE bc r P S0 i j) * φ (rep m) (S.wTil w r j)) *
            (infSub (K := K) N q)⁻¹ := by
        rw [← hemb, mul_assoc, mul_inv_cancel₀ hqK, mul_one]
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hL : (φ (rep m) ⟨(S.wTil w r i : L)′, hmem⟩).coeff kk =
        (Jv m i)′ - algebraMap C K bc * ((kk : K) / (N : K)) * Jv m i := by
      change (S.embG (infSub N) (infSub_injective N hN) (ρ (rep m)) (hρr (rep m))
        ⟨(S.wTil w r i : L)′, S.derivClosedXYW' (Polynomial.C bc * X) hx _ (S.wTil w r i).2⟩).coeff kk = _
      rw [S.embG_deriv_infE bc hx hK N hN (ρ (rep m)) (hρr (rep m)) (S.wTil w r i), coeff_dS_infSpeedE]
    have hsum : (φ (rep m) ⟨(S.wTil w r i : L)′, hmem⟩).coeff kk = ∑ j, lamK i j * Jv m j := by
      rw [hder, HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      exact coeff_mul_of_sub_lowerBd _
        (lowerBd_infSub_div (K := K) N hN (pqE bc r P S0 i j) q hq0 (hdeg i j)) (hWLB j (rep m))
        kk hkN
    have hkK : (kk : K) / (N : K) = (hh m : K) / (e (ρ m).order : K) := by
      have hNe : ((N / e (ρ m).order : ℕ) : K) * (e (ρ m).order : K) = (N : K) := by
        exact_mod_cast Nat.div_mul_cancel hed
      have he0 : (e (ρ m).order : K) ≠ 0 := by exact_mod_cast he.ne'
      have hN0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
      rw [hkk, div_eq_div_iff hN0 he0, ← hNe]
      generalize N / e (ρ m).order = d
      push_cast
      ring
    rw [hL, hkK] at hsum
    linear_combination hsum

  have hAJ : ∀ i a, algebraMap C K (A i a) = Jv (cs a) i / cst (cs a) ^ tt (cs a) := fun i a ↦ by
    rw [hA, Matrix.of_apply, hA0]
  -- invertibility (normality at infinity)
  have hA0' : A.det ≠ 0 := by
    intro hdet0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet0
    apply hv0
    funext i
    refine hred v ?_ i
    set z : C⟮S.x⟯⟮S.y⟯ := ∑ j, S.polyE (Polynomial.C (v j)) * ((S.polyE (X ^ r j))⁻¹ * w j)
      with hz
    have hφz : ∀ m, φ m z = ∑ j, HahnSeries.C (algebraMap C K (v j)) * φ m (S.wTil w r j) := by
      intro m
      rw [hz, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul]
      congr 1
      rw [show S.polyE (Polynomial.C (v j)) = ⟨aeval S.x (Polynomial.C (v j)), S.aeval_mem _⟩ from rfl,
        S.embG_polyX, infSub_C]
    have hWLB : ∀ i m, LowerBd (φ m (S.wTil w r i)) 0 := fun i m ↦ by
      have := S.infOrd_wTil w r i (hrw i) N hN.ne' l hl (ρ m) (hρl m)
      simpa using this
    have hLB0 : ∀ m, LowerBd (φ m z) 0 := fun m ↦ by
      rw [hφz]
      exact lowerBd_sum _ _ fun j _ ↦ by
        have := (lowerBd_C (algebraMap C K (v j))).mul (hWLB j m)
        rwa [zero_add] at this
    have hjet : ∀ a, (φ (rep a) z).coeff ((hh a * (N / e (ρ a).order) : ℕ) : ℤ) = 0 := by
      intro a
      rw [hφz, HahnSeries.coeff_sum]
      have h1 : ∀ j, (HahnSeries.C (algebraMap C K (v j)) * φ (rep a) (S.wTil w r j)).coeff
          ((hh a * (N / e (ρ a).order) : ℕ) : ℤ) = algebraMap C K (v j * A0 j a) * cst a ^ tt a :=
        fun j ↦ by
          rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, map_mul, hA0,
            mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ (hcst0 a))]
      simp only [h1, ← Finset.sum_mul, ← map_sum]
      have := congrFun hv (Fin.cast hlen a)
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, hA, Matrix.of_apply] at this
      rw [show ∑ j, v j * A0 j a = 0 from this, map_zero, zero_mul]
    have hrepLB : ∀ a, LowerBd (φ (rep a) z) N := by
      intro a k hk
      rcases lt_or_ge k 0 with h | h
      · exact hLB0 _ k h
      obtain ⟨he, hed, hcop, hor⟩ := hdata _ (hρl (rep a))
      rw [hrepord] at he hed hcop hor
      by_cases hdk : ((N / e (ρ a).order : ℕ) : ℤ) ∣ k
      · obtain ⟨j, rfl⟩ := hdk
        have hNe0 : 0 < N / e (ρ a).order := Nat.div_pos (Nat.le_of_dvd hN hed) he
        have hj0 : 0 ≤ j := by
          by_contra hc; push Not at hc
          have : ((N / e (ρ a).order : ℕ) : ℤ) * j < 0 :=
            mul_neg_of_pos_of_neg (by exact_mod_cast hNe0) hc
          omega
        lift j to ℕ using hj0
        have hjlt : j < e (ρ a).order := by
          by_contra hc; push Not at hc
          have h1 : N ≤ N / e (ρ a).order * j := by
            calc N = N / e (ρ a).order * e (ρ a).order := (Nat.div_mul_cancel hed).symm
              _ ≤ N / e (ρ a).order * j := Nat.mul_le_mul_left _ hc
          have : ((N : ℕ) : ℤ) ≤ ((N / e (ρ a).order * j : ℕ) : ℤ) := by exact_mod_cast h1
          push_cast at this
          omega
        obtain ⟨b, hb1, hb2⟩ := hsurj a j hjlt
        have hbo : (ρ b).order = (ρ a).order := by rw [← hrepord b, hb1, hrepord a]
        have := hjet b
        rw [hb1, hb2, hbo, mul_comm] at this
        exact_mod_cast this
      · have hfix : rot (ζ ^ e (ρ a).order) (pow_ne_zero _ hζ0) (ρ (rep a)) = ρ (rep a) := by
          refine S.root_rot_fixed_gen N (pow_ne_zero _ hζ0)
            (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) l hl (hρl _) ?_
            (fun r' hr' ho hc ↦ huniq r' hr' _ (hρl _) ho hc)
          have : ((N / e (ρ a).order : ℕ) : ℤ) * (e (ρ a).order : ℤ) = N := by
            exact_mod_cast Nat.div_mul_cancel hed
          have key : (ρ a).order * (e (ρ a).order : ℤ) = -(N * sp (ρ a).order) := by
            calc (ρ a).order * (e (ρ a).order : ℤ)
                = -(((N / e (ρ a).order : ℕ) : ℤ) * sp (ρ a).order) * e (ρ a).order := by
                  rw [← hor]
              _ = _ := by linear_combination (-sp (ρ a).order) * this
          rw [hrepord, ← zpow_natCast, ← zpow_mul, hζ.zpow_eq_one_iff_dvd]
          exact ⟨-sp (ρ a).order, by rw [mul_comm, key]; ring⟩
        exact S.embG_coeff_eq_zero_of_rot N hN (hζ.pow_of_dvd he.ne' hed) (pow_ne_zero _ hζ0)
          (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) _ _ hfix z k hdk
    apply S.infOrd_of_sys N hN l hl
    intro ρ' hρ'
    obtain ⟨i', hi', hρi'⟩ := List.getElem_of_mem hρ'
    set b : Fin l.length := ⟨i', hi'⟩ with hb
    have hρb : ρ' = rot (ζ ^ hh b) (pow_ne_zero _ hζ0) (ρ (rep b)) := hρi'.symm.trans (hhr b).2
    have hζN : (ζ ^ hh b) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hr' : (S.F.map (infSub N)).eval (rot (ζ ^ hh b) (pow_ne_zero _ hζ0) (ρ (rep b))) = 0 :=
      rot_root_inf _ _ N hζN S.F _ (hρr _)
    intro k hk
    rw [S.embG_eq_of_eq _ _ hρb _ hr',
      S.embG_rot_coeff N hN (pow_ne_zero _ hζ0) hζN (ρ (rep b)) (hρr _) hr' z k]
    have := hrepLB b k (by linarith)
    simp only [hφ] at this
    rw [this, mul_zero]
  refine ⟨A, Td, ?_, ?_, fun a ↦ ⟨-(hh (cs a) : ℚ) / (e (ρ (cs a)).order : ℚ),
    (tt (cs a) : ℚ) / (e (ρ (cs a)).order : ℚ), γ (cs a), hγ0 _, rfl⟩⟩
  · exact hA0'
  · -- the derivative: `A′ = Λ A − A T`
    intro i a
    apply (algebraMap C K).injective
    set m : Fin l.length := cs a with hm
    obtain ⟨he, -, -, -⟩ := hdata _ (hρl m)
    have hγe : cst m ^ e (ρ m).order = algebraMap C K (γ m) := (hγ m).symm
    have htw := twist_derivB (Jv m) lamK _ (hJd m) (cst m) (algebraMap C K (γ m)) (hcst0 m)
      (e (ρ m).order) (tt m) he hγe i
    rw [← hK, hAJ, htw]
    simp only [hlamK, hTd, map_sub, map_sum, map_mul, map_add, hAJ, map_ratCast]
    rw [map_div₀ (algebraMap C K) ((γ m)′), hK]
    push_cast
    ring

end RamGaugeE

end CurveData

end Curves
