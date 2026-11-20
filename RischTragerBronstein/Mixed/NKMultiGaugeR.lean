import RischTragerBronstein.Mixed.NKMultiRam
import RischTragerBronstein.Torsion.PlaceExist1

/-!
# The gauge at infinity for rational places of any slopes (ramified or not)

The roots above infinity (`x = T^{−N}`) of a ramified place are the rotations `rot ζʲ ρ`
(`ζ` a primitive `N`-th root of unity, `j < e`) of one of them. `orbit_data` chooses a
representative per place and the exponent `h < e` of each root, bijectively.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

section Orbits

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

lemma rot_pow_add {ζ : K} (hζ0 : ζ ≠ 0) (j j' : ℕ) (r : LaurentSeries K) :
    rot (ζ ^ j) (pow_ne_zero _ hζ0) (rot (ζ ^ j') (pow_ne_zero _ hζ0) r) =
      rot (ζ ^ (j + j')) (pow_ne_zero _ hζ0) r := by
  rw [rot_rot]
  ext k
  simp only [rot_coeff, pow_add]

lemma rot_pow_eq_of_eq_one {ζ : K} (hζ0 : ζ ≠ 0) (j : ℕ) (h1 : ζ ^ j = 1) (r : LaurentSeries K) :
    rot (ζ ^ j) (pow_ne_zero _ hζ0) r = r := by
  ext k
  simp [rot_coeff, h1]

/-- **Distinct exponents `< e` give distinct rotations.** -/
lemma rot_inj_of_lt (N : ℕ) (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    {r : LaurentSeries K} (hr0 : r ≠ 0) (e : ℕ) (he : 0 < e) (hdvd : e ∣ N) (sp : ℤ)
    (hcop : Int.gcd sp e = 1) (hord : r.order = -((N / e : ℕ) * sp)) {j j' : ℕ} (hj : j < e)
    (hj' : j' < e)
    (h : rot (ζ ^ j) (pow_ne_zero _ (hζ.ne_zero hN.ne')) r =
      rot (ζ ^ j') (pow_ne_zero _ (hζ.ne_zero hN.ne')) r) : j = j' := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  have hc0 : r.coeff r.order ≠ 0 := fun h0 ↦ hr0 (HahnSeries.coeff_order_eq_zero.mp h0)
  have h1 := congrArg (fun y ↦ y.coeff y.order) h
  simp only [rot_lc] at h1
  have h2 := mul_right_cancel₀ hc0 h1
  obtain ⟨d, hd⟩ := hdvd
  have hNe : N / e = d := by rw [hd, Nat.mul_div_cancel_left _ he]
  have h3 : ζ ^ (((j : ℤ) - j') * r.order) = 1 := by
    rw [sub_mul, zpow_sub₀ hζ0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, h2,
      div_self (zpow_ne_zero _ (pow_ne_zero _ hζ0))]
  rw [hζ.zpow_eq_one_iff_dvd, hord, hNe, hd] at h3
  -- `e d ∣ (j − j') (−d sp)` ⇒ `e ∣ (j − j') sp` ⇒ `e ∣ j − j'`
  have hd0 : (d : ℤ) ≠ 0 := by
    intro h0
    have : d = 0 := by exact_mod_cast h0
    subst this; simp at hd; omega
  obtain ⟨w, hw⟩ := h3
  have h4 : (e : ℤ) ∣ ((j : ℤ) - j') * sp := ⟨-w, by
    apply mul_left_cancel₀ hd0
    push_cast at hw
    linear_combination -hw⟩
  have h5 : (e : ℤ) ∣ (j : ℤ) - j' :=
    Int.dvd_of_dvd_mul_left_of_gcd_one h4 (by rw [Int.gcd_comm]; exact hcop)
  have h6 : (j : ℤ) - j' = 0 := by
    obtain ⟨u, hu⟩ := h5
    have hlt : |(j : ℤ) - j'| < e := by
      rw [abs_lt]; constructor <;> omega
    rw [hu, abs_mul] at hlt
    have : |u| < 1 := by
      by_contra hc
      push Not at hc
      have : (e : ℤ) ≤ |(e : ℤ)| * |u| := by
        rw [abs_of_pos (by exact_mod_cast he)]; nlinarith
      linarith
    have hu0 : u = 0 := by
      rcases abs_lt.mp this with ⟨h1, h2⟩; omega
    rw [hu, hu0, mul_zero]
  omega

/-- **Representatives of the places and exponents of the roots.** -/
lemma orbit_data (N : ℕ) (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (l : List (LaurentSeries K)) (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hl0 : ∀ r ∈ l, r ≠ 0) (e : ℤ → ℕ) (sp : ℤ → ℤ)
    (hdata : ∀ r ∈ l, 0 < e r.order ∧ e r.order ∣ N ∧ Int.gcd (sp r.order) (e r.order) = 1 ∧
      r.order = -((N / e r.order : ℕ) * sp r.order))
    (huniq : ∀ r₁ ∈ l, ∀ r₂ ∈ l, r₁.order = r₂.order → r₁.coeff r₁.order = r₂.coeff r₂.order →
      r₁ = r₂) :
    ∃ (rep : Fin l.length → Fin l.length) (hh : Fin l.length → ℕ),
      (∀ a : Fin l.length, hh a < e (l[(a : ℕ)]).order ∧
        l[(a : ℕ)] = rot (ζ ^ hh a) (pow_ne_zero _ (hζ.ne_zero hN.ne')) l[((rep a) : ℕ)]) ∧
      (∀ a : Fin l.length, ∀ j < e (l[(a : ℕ)]).order, ∃ b, rep b = rep a ∧ hh b = j) := by
  classical
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  set ρ : Fin l.length → LaurentSeries K := fun a ↦ l[(a : ℕ)] with hρ
  have hρl : ∀ a, ρ a ∈ l := fun a ↦ List.getElem_mem _
  set R : Fin l.length → Fin l.length → Prop := fun a b ↦
    ∃ j : ℕ, ρ b = rot (ζ ^ j) (pow_ne_zero _ hζ0) (ρ a) with hR
  have Rrefl : ∀ a, R a a := fun a ↦ ⟨0, (rot_pow_eq_of_eq_one hζ0 0 (pow_zero ζ) _).symm⟩
  have Rtrans : ∀ a b c, R a b → R b c → R a c := by
    rintro a b c ⟨j, hj⟩ ⟨j', hj'⟩
    exact ⟨j' + j, by rw [hj', hj, rot_pow_add hζ0]⟩
  have Rsymm : ∀ a b, R a b → R b a := by
    rintro a b ⟨j, hj⟩
    refine ⟨(N - 1) * j, ?_⟩
    rw [hj, rot_pow_add hζ0, rot_pow_eq_of_eq_one hζ0]
    rw [show (N - 1) * j + j = N * j by
      rcases N with _ | N
      · omega
      · simp; ring, pow_mul, hζ.pow_eq_one, one_pow]
  have Rord : ∀ a b, R a b → (ρ b).order = (ρ a).order := by
    rintro a b ⟨j, hj⟩
    rw [hj, rot_order]
  -- the representatives
  set rep : Fin l.length → Fin l.length := fun a ↦
    (Finset.univ.filter fun b ↦ R b a).min' ⟨a, by simp [Rrefl a]⟩ with hrep
  have hrepR : ∀ a, R (rep a) a := fun a ↦ by
    have := Finset.min'_mem (Finset.univ.filter fun b ↦ R b a) ⟨a, by simp [Rrefl a]⟩
    simpa using this
  have hrepc : ∀ a b, R a b → rep a = rep b := by
    intro a b hab
    simp only [hrep]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ Rtrans _ _ _ h hab, fun h ↦ Rtrans _ _ _ h (Rsymm _ _ hab)⟩
  -- the exponents
  have hex : ∀ a, ∃ j, j < e (ρ a).order ∧ ρ a = rot (ζ ^ j) (pow_ne_zero _ hζ0) (ρ (rep a)) := by
    intro a
    obtain ⟨J, hJ⟩ := hrepR a
    have hord : (ρ (rep a)).order = (ρ a).order := (Rord _ _ (hrepR a)).symm
    obtain ⟨he, hed, hcop, hor⟩ := hdata _ (hρl (rep a))
    rw [hord] at he hed hcop hor
    set ee := e (ρ a).order
    refine ⟨J % ee, Nat.mod_lt _ he, ?_⟩
    have hfix : rot (ζ ^ (ee * (J / ee))) (pow_ne_zero _ hζ0) (ρ (rep a)) = ρ (rep a) := by
      refine S.root_rot_fixed_gen N (pow_ne_zero _ hζ0)
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) l hl (hρl _) ?_
        (fun r' hr' ho hc ↦ huniq r' hr' _ (hρl _) ho hc)
      rw [hord, hor, ← zpow_natCast, ← zpow_mul, hζ.zpow_eq_one_iff_dvd]
      obtain ⟨d, hd⟩ := hed
      have hNe : N / ee = d := by rw [hd, Nat.mul_div_cancel_left _ he]
      refine ⟨-(J / ee : ℕ) * sp (ρ a).order, ?_⟩
      rw [hNe, hd]
      push_cast
      ring
    calc ρ a = rot (ζ ^ J) (pow_ne_zero _ hζ0) (ρ (rep a)) := hJ
      _ = rot (ζ ^ (J % ee + ee * (J / ee))) (pow_ne_zero _ hζ0) (ρ (rep a)) := by
          rw [Nat.mod_add_div]
      _ = rot (ζ ^ (J % ee)) (pow_ne_zero _ hζ0)
            (rot (ζ ^ (ee * (J / ee))) (pow_ne_zero _ hζ0) (ρ (rep a))) :=
          (rot_pow_add hζ0 _ _ _).symm
      _ = _ := by rw [hfix]
  choose hh hhlt hhrot using hex
  refine ⟨rep, hh, fun a ↦ ⟨hhlt a, hhrot a⟩, fun a j hj ↦ ?_⟩
  -- the root `rot ζʲ ρ(rep a)`
  have hord : (ρ (rep a)).order = (ρ a).order := (Rord _ _ (hrepR a)).symm
  have hmem : rot (ζ ^ j) (pow_ne_zero _ hζ0) (ρ (rep a)) ∈ l :=
    S.rot_mem N (pow_ne_zero _ hζ0) (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
      l hl (hρl _)
  obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hmem
  set b : Fin l.length := ⟨i, hi⟩ with hb
  have hρb : ρ b = rot (ζ ^ j) (pow_ne_zero _ hζ0) (ρ (rep a)) := hib
  have hRb : R (rep a) b := ⟨j, hρb⟩
  have hrepb : rep b = rep a := (hrepc _ _ (Rtrans _ _ _ (Rsymm _ _ (hrepR a)) hRb)).symm
  refine ⟨b, hrepb, ?_⟩
  obtain ⟨he, hed, hcop, hor⟩ := hdata _ (hρl (rep a))
  rw [hord] at he hed hcop hor
  have hbord : (ρ b).order = (ρ a).order := by rw [hρb, rot_order, hord]
  have h1 := hhrot b
  rw [hrepb, hρb] at h1
  refine (rot_inj_of_lt N hN hζ (hl0 _ (hρl (rep a))) (e (ρ a).order) he hed (sp (ρ a).order)
    hcop (by rw [hord]; exact hor) (j := hh b) (j' := j) (by rw [← hbord]; exact hhlt b) hj
    h1.symm)

end Orbits

section Twist

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- **Twisting by a power of an `e`-th root**: `(J/cᵗ)′ = Λ (J/cᵗ) − (t/e) (Γ′/Γ) (J/cᵗ)` when
`J′ = Λ J` and `cᵉ = Γ`. -/
lemma twist_deriv {n : ℕ} (J : Fin n → K) (lam : Fin n → Fin n → K)
    (hJ : ∀ i, (J i)′ = ∑ j, lam i j * J j) (c Γ : K) (hc : c ≠ 0) (e t : ℕ) (he : 0 < e)
    (hcΓ : c ^ e = Γ) (i : Fin n) :
    (J i / c ^ t)′ = ∑ j, lam i j * (J j / c ^ t) - (J i / c ^ t) * (((t : K) / e) * (Γ′ / Γ)) := by
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

lemma coeff_mul_of_sub_lowerBd {a b : LaurentSeries K} (lam : K) {M : ℤ}
    (ha : LowerBd (a - HahnSeries.C lam) M) (hb : LowerBd b 0) (k : ℤ) (hk : k < M) :
    (a * b).coeff k = lam * b.coeff k := by
  have h1 : a * b = HahnSeries.C lam * b + (a - HahnSeries.C lam) * b := by ring
  have h2 := ha.mul hb
  rw [add_zero] at h2
  rw [h1, HahnSeries.coeff_add, h2 k hk, add_zero, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul]

end Twist

section RamGauge

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

set_option maxHeartbeats 8000000 in
/-- **The gauge at infinity for rational places of any slopes, ramified or not**: the twisted
window values `A` of the rescaled basis along representatives of the places form an invertible
matrix over `C` with `A′ = Λ A − A T`, `T` diagonal with entries `(t/e) γ′/γ`, `γ = cᵉ` the
`e`-th power of a leading coefficient. -/
theorem multi_gauge_ram [IsGalois C K] (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
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
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree) :
    ∃ (A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C) (Td : Fin S.F.natDegree → C),
      A.det ≠ 0 ∧
      (∀ i a, (A i a)′ = ∑ j, (pqV η r P S0 i j).coeff (X ^ (r i + 1) * S0).natDegree /
        (X ^ (r i + 1) * S0).leadingCoeff * A j a - A i a * Td a) ∧
      (∀ a, ∃ (q : ℚ) (γ : C), γ ≠ 0 ∧ (∃ ρ ∈ l, algebraMap C K γ = (ρ.coeff ρ.order) ^ e ρ.order) ∧
        Td a = q * (γ′ / γ)) ∧
      ∃ Jt : Fin S.F.natDegree → Fin S.F.natDegree → K,
        (∀ c : Fin S.F.natDegree → K, (∀ b, ∑ i, c i * Jt i b = 0) → c = 0) ∧
        ∀ i b, (Jt i b)′ = ∑ j, algebraMap C K ((pqV η r P S0 i j).coeff
          (X ^ (r i + 1) * S0).natDegree / (X ^ (r i + 1) * S0).leadingCoeff) * Jt j b := by
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
    ((((tt (cs a) : ℚ) / (e (ρ (cs a)).order : ℚ) : ℚ) : C)) * ((γ (cs a))′ / γ (cs a)) with hTd
  -- the jets and their derivatives
  have hWLB : ∀ i m, LowerBd (φ m (S.wTil w r i)) 0 := fun i m ↦ by
    have := S.infOrd_wTil w r i (hrw i) N hN.ne' l hl (ρ m) (hρl m)
    simpa using this
  set lamK : Fin S.F.natDegree → Fin S.F.natDegree → K := fun i j ↦
    algebraMap C K ((pqV η r P S0 i j).coeff (X ^ (r i + 1) * S0).natDegree /
      (X ^ (r i + 1) * S0).leadingCoeff) with hlamK
  set Jv : Fin l.length → Fin S.F.natDegree → K := fun m i ↦
    (φ (rep m) (S.wTil w r i)).coeff ((hh m * (N / e (ρ m).order) : ℕ) : ℤ) with hJv
  have hJd : ∀ m i, (Jv m i)′ = ∑ j, lamK i j * Jv m j := by
    intro m i
    set kk : ℤ := ((hh m * (N / e (ρ m).order) : ℕ) : ℤ) with hkk
    obtain ⟨he, hed, -, -⟩ := hdata _ (hρl m)
    have hkN : kk < N := by
      have h1 : hh m * (N / e (ρ m).order) < e (ρ m).order * (N / e (ρ m).order) :=
        Nat.mul_lt_mul_of_pos_right (hhr m).1 (Nat.div_pos (Nat.le_of_dvd hN hed) he)
      rw [Nat.mul_div_cancel' hed] at h1
      rw [hkk]; exact_mod_cast h1
    set q : C[X] := X ^ (r i + 1) * S0 with hq
    have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hqK := infSub_ne_zero (K := K) N hN q hq0
    have hmem := S.derivClosedXYW' (Polynomial.C η) hx (S.wTil w r i) (S.wTil w r i).2
    have hdw := S.deriv_wTil η hx w r S0 P hP i
    have hid : (⟨(S.wTil w r i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE q =
        ∑ j, S.polyE (pqV η r P S0 i j) * S.wTil w r j := Subtype.ext (by
      push_cast
      exact hdw)
    have hemb := congrArg (φ (rep m)) hid
    rw [map_mul, map_sum] at hemb
    simp only [map_mul] at hemb
    rw [show φ (rep m) (S.polyE q) = infSub N q from S.embG_polyX _ _ _ _ _ _] at hemb
    have hpoly : ∀ j, φ (rep m) (S.polyE (pqV η r P S0 i j)) = infSub N (pqV η r P S0 i j) :=
      fun j ↦ S.embG_polyX _ _ _ _ _ _
    simp only [hpoly] at hemb
    have hder : φ (rep m) ⟨(S.wTil w r i : L)′, hmem⟩ =
        ∑ j, (infSub (K := K) N (pqV η r P S0 i j) * (infSub (K := K) N q)⁻¹) *
          φ (rep m) (S.wTil w r j) := by
      have : φ (rep m) ⟨(S.wTil w r i : L)′, hmem⟩ =
          (∑ j, infSub (K := K) N (pqV η r P S0 i j) * φ (rep m) (S.wTil w r j)) *
            (infSub (K := K) N q)⁻¹ := by
        rw [← hemb, mul_assoc, mul_inv_cancel₀ hqK, mul_one]
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hL := S.coeff_embG_deriv_inf η hx hK N hN (ρ (rep m)) (hρr (rep m)) (S.wTil w r i)
      (hWLB i (rep m)) kk hkN
    simp only [hJv]
    rw [← hL]
    change (φ (rep m) ⟨(S.wTil w r i : L)′, hmem⟩).coeff kk = _
    rw [hder, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact coeff_mul_of_sub_lowerBd _
      (lowerBd_infSub_div (K := K) N hN (pqV η r P S0 i j) q hq0 (hdeg i j)) (hWLB j (rep m))
      kk hkN
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
  refine ⟨A, Td, ?_, ?_, fun a ↦ ⟨(tt (cs a) : ℚ) / (e (ρ (cs a)).order : ℚ), γ (cs a),
    hγ0 _, ⟨ρ (rep (cs a)), hρl _, by
      rw [hγ, show e (ρ (rep (cs a))).order = e (ρ (cs a)).order by rw [hrepord]]⟩, rfl⟩,
    fun i b ↦ Jv (cs b) i, ?_, fun i b ↦ by rw [hJd]⟩
  · exact hA0'
  · -- the derivative: `A′ = Λ A − A T`
    intro i a
    apply (algebraMap C K).injective
    set m : Fin l.length := cs a with hm
    obtain ⟨he, -, -, -⟩ := hdata _ (hρl m)
    have hγe : cst m ^ e (ρ m).order = algebraMap C K (γ m) := (hγ m).symm
    have htw := twist_deriv (Jv m) lamK (hJd m) (cst m) (algebraMap C K (γ m)) (hcst0 m)
      (e (ρ m).order) (tt m) he hγe i
    rw [← hK, hAJ, htw, map_sub, map_sum, map_mul, hAJ, hTd]
    simp only [map_mul, hAJ, map_div₀, ← hK, map_ratCast]
    congr 1
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hlamK, map_div₀]
      rfl
    · push_cast
      ring
  · -- the jets are independent
    intro c hc
    by_contra hc0
    have hdetK : (A.map (algebraMap C K)).det ≠ 0 := by
      rw [show (A.map (algebraMap C K)).det = algebraMap C K A.det from (RingHom.map_det _ _).symm]
      exact (_root_.map_ne_zero _).mpr hA0'
    apply hdetK
    refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc0, funext fun b ↦ ?_⟩
    have h1 := hc b
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply]
    have h2 : ∑ i, c i * algebraMap C K (A i b) =
        (∑ i, c i * Jv (cs b) i) / cst (cs b) ^ tt (cs b) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hAJ, mul_div_assoc]
    rw [h2, h1, zero_div]

end RamGauge

end CurveData

end Curves
