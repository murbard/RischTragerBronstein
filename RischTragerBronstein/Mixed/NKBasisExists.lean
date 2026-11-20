import RischTragerBronstein.Mixed.NKEchelon

/-!
# Integral bases of non-constant curves with a single place at infinity

`S : CurveData C L` of weighted shape over a differential field `C` (coefficients not constant)
with `x′ = η ∈ C`. `exists_nkBasis` gives an integral basis `w` with shifts `r` such that

* `S₀ wᵢ′ = ∑ Pᵢⱼ wⱼ` with `S₀` squarefree (finite places: `regularFinite_rad_derivW`);
* the rescaled basis `w̃ᵢ = x^{−rᵢ} wᵢ` has a bounded derivation matrix at infinity
  (`InfOrd` is stable under the derivation, `infOrd_derivW`, and the basis is reduced);
* the `w̃ᵢ = Wᵢ(x, y)/Qᵢ(x)` have pairwise distinct weights in `(−n, 0]` (echelon at infinity,
  `exists_echelon`) and leading coefficients `1` (scaling by constants).

With `nk_inf_struct` this makes the limit matrix triangular with diagonal `(j₀/n) c′/c`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

section Scale

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

variable (S : CurveData C L)

lemma polyE_C_ne_zero (u : C) (hu : u ≠ 0) : S.polyE (Polynomial.C u) ≠ 0 :=
  S.polyE_ne_zero _ (Polynomial.C_ne_zero.mpr hu)

lemma polyE_C_mul_inv (u : C) (hu : u ≠ 0) :
    S.polyE (Polynomial.C u⁻¹) * S.polyE (Polynomial.C u) = 1 := by
  rw [← S.polyE_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hu, Polynomial.C_1, S.polyE_one]

/-- Scaling by non-zero constants keeps an integral basis. -/
lemma IBasis.scale {m : ℕ} {w : Fin m → C⟮S.x⟯⟮S.y⟯} (hw : S.IBasis K w) (u : Fin m → C)
    (hu : ∀ j, u j ≠ 0) : S.IBasis K (fun j ↦ S.polyE (Polynomial.C (u j)) * w j) := by
  refine ⟨fun j ↦ S.regularFinite_polyE_mul _ (hw.1 j), fun z hz ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hw.2.1 z hz
    refine ⟨fun j ↦ c j * Polynomial.C (u j)⁻¹, ?_⟩
    rw [hc]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    show _ = S.polyE (c j * Polynomial.C (u j)⁻¹) * (S.polyE (Polynomial.C (u j)) * w j)
    rw [S.polyE_mul, mul_assoc, ← mul_assoc (S.polyE (Polynomial.C (u j)⁻¹)),
      S.polyE_C_mul_inv _ (hu j), one_mul]
  · have h := hw.2.2 (fun j ↦ c j * Polynomial.C (u j)) (by
      rw [← hc]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [S.polyE_mul, mul_assoc])
    intro j
    have := h j
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd (Polynomial.C_eq_zero.mp h0) (hu j)

lemma infOrd_polyE_C' (c : C) : S.InfOrd K (S.polyE (Polynomial.C c)) 0 := by
  have := S.infOrd_poly (K := K) (Polynomial.C c)
  rwa [natDegree_C, Nat.cast_zero] at this

lemma InfOrd.scale {z : C⟮S.x⟯⟮S.y⟯} {k : ℤ} (h : S.InfOrd K z k) (u : C) :
    S.InfOrd K (S.polyE (Polynomial.C u) * z) k := by
  have := InfOrd.mul S (S.infOrd_polyE_C' (K := K) u) h
  rwa [zero_add] at this

/-- Scaling by non-zero constants keeps a reduced basis. -/
lemma Reduced.scale {m : ℕ} {w : Fin m → C⟮S.x⟯⟮S.y⟯} {r : Fin m → ℕ} (h : S.Reduced K w r)
    (u : Fin m → C) (hu : ∀ j, u j ≠ 0) :
    S.Reduced K (fun j ↦ S.polyE (Polynomial.C (u j)) * w j) r := by
  intro c hc
  have h0 := h (fun j ↦ c j * u j) (by
    have e : ∑ j, S.polyE (Polynomial.C (c j * u j)) * ((S.polyE (X ^ r j))⁻¹ * w j) =
        ∑ j, S.polyE (Polynomial.C (c j)) *
          ((S.polyE (X ^ r j))⁻¹ * (S.polyE (Polynomial.C (u j)) * w j)) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [Polynomial.C_mul, S.polyE_mul]; ring
    rw [e]; exact hc)
  intro j
  rcases mul_eq_zero.mp (h0 j) with h1 | h1
  · exact h1
  · exact absurd h1 (hu j)

end Scale

section Deriv

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]

variable (S : CurveData C L) (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **The derivation keeps the orders above infinity** (`x′ = η` constant in `x`). -/
theorem infOrd_derivW (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ) (hz : S.InfOrd K z k) :
    S.InfOrd K ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C η) hx z z.2⟩ k := by
  intro N hN l hl r hr
  have hN0 := Nat.pos_of_ne_zero hN
  have hY := S.root_of_mem hl hr
  have hd := S.embG_dSW' (Polynomial.C η) hx hK (infSpeed η N) (single (-(N : ℤ)) 1)
    (dS_infSpeed η N hN0) (infSub N) (infSub_injective N hN0)
    (fun P ↦ by rw [SuperData.infSub_eq_subst]) r hY (z : L) z.2
  simp only [Subtype.coe_eta] at hd
  rw [hd, dS_apply]
  have h1 := hz N hN l hl r hr
  refine LowerBd.add (lowerBd_coefDeriv h1) ?_
  have := (lowerBd_infSpeed (K := K) η N).mul h1.derivative
  exact this.mono (by ring_nf; omega)

/-- The numerators of the rescaled derivation matrix (denominators `x^{rᵢ+1} S₀`). -/
noncomputable def pqV {m : ℕ} (r : Fin m → ℕ) (P : Fin m → Fin m → C[X]) (S0 : C[X]) (i j : Fin m) :
    C[X] :=
  X ^ (r j + 1) * P i j - if i = j then Polynomial.C ((r i : C) * η) * X ^ r i * S0 else 0

include hx in
/-- **The derivation matrix of the rescaled basis** `x^{−rᵢ} wᵢ`. -/
lemma deriv_wTil {m : ℕ} (w : Fin m → C⟮S.x⟯⟮S.y⟯) (r : Fin m → ℕ) (S0 : C[X])
    (P : Fin m → Fin m → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j) (i : Fin m) :
    (S.wTil w r i : L)′ * aeval S.x (X ^ (r i + 1) * S0) =
      ∑ j, aeval S.x (pqV η r P S0 i j) * (S.wTil w r j : L) := by
  classical
  have hx0 : S.x ≠ 0 := S.htr.ne_zero
  have hPi : (w i : L)′ * aeval S.x S0 = ∑ j, aeval S.x (P i j) * (w j : L) := by
    have := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) (hP i)
    simpa [polyE] using this
  have hxe : S.x′ = algebraMap C L η := by rw [hx, aeval_C]
  have hwt : ∀ j, (S.wTil w r j : L) = (S.x ^ r j)⁻¹ * (w j : L) := fun j ↦ by
    simp [wTil, polyE]
  have hR : ∑ j, aeval S.x (pqV η r P S0 i j) * (S.wTil w r j : L) =
      S.x * ∑ j, aeval S.x (P i j) * (w j : L) -
        (r i : L) * algebraMap C L η * aeval S.x S0 * (w i : L) := by
    simp only [pqV, hwt, map_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [map_mul, map_pow, aeval_X, pow_succ]
      field_simp
    · rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
      simp only [ite_true, map_mul, map_pow, aeval_X, aeval_C, map_natCast]
      field_simp
  have hL : (S.wTil w r i : L)′ * aeval S.x (X ^ (r i + 1) * S0) =
      S.x * ((w i : L)′ * aeval S.x S0) - (r i : L) * algebraMap C L η * aeval S.x S0 * (w i : L) := by
    rw [hwt, Derivation.leibniz, Derivation.leibniz_inv, Derivation.leibniz_pow, hxe]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, aeval_X]
    rcases Nat.eq_zero_or_pos (r i) with h0 | hpos
    · rw [h0]; simp; ring
    · have e : S.x ^ (r i - 1) = S.x ^ r i / S.x := by
        rw [eq_div_iff hx0, ← pow_succ]; congr 1; omega
      rw [e]
      field_simp
      ring
  rw [hR, hL, hPi]

end Deriv

section Main

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L) (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
  (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
  (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
  (hcop : Nat.Coprime n d)

include hx hK hn hn0 ha0 hd hw hcop in
/-- **Echelon integral bases of non-constant curves with a single place at infinity.** -/
theorem exists_nkBasis :
    ∃ (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : C[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X]) (W : Fin S.F.natDegree → C[X][X])
      (Q : Fin S.F.natDegree → C[X]),
      (∀ c : Fin S.F.natDegree → C⟮S.x⟯,
        ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (P i j) * w j) ∧
      (∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree) ∧
      (∀ i, Q i ≠ 0 ∧ (S.wTil w r i : L) * aeval S.x (Q i) = S.evXY (W i) ∧ W i ≠ 0 ∧
        (W i).natDegree < n) ∧
      (∀ i, -(n : ℤ) < (wtW n d (W i) : ℤ) - n * (Q i).natDegree ∧
        (wtW n d (W i) : ℤ) - n * (Q i).natDegree ≤ 0) ∧
      (∀ i j, (wtW n d (W i) : ℤ) - n * (Q i).natDegree =
        (wtW n d (W j) : ℤ) - n * (Q j).natDegree → i = j) ∧
      (∀ i j0, j0 < n → (W i).coeff j0 ≠ 0 →
        wtW n d (W i) = n * ((W i).coeff j0).natDegree + j0 * d →
        ((W i).coeff j0).leadingCoeff = (Q i).leadingCoeff) := by
  classical
  -- a branch above infinity
  obtain ⟨N, hN, l, hlen, hl, -⟩ := S.hasBranchesInfB (K := K)
  have hN0 := Nat.pos_of_ne_zero hN
  have hlne : l ≠ [] := by
    intro h; rw [h, List.length_nil, hn] at hlen; omega
  obtain ⟨ρ, hρl⟩ := List.exists_mem_of_ne_nil l hlne
  set hρ := S.root_of_mem hl hρl
  -- an echelon integral basis
  obtain ⟨w0, hw0⟩ := S.exists_IBasis K
  obtain ⟨w1, r1, hw1, hr1, hred1⟩ := S.exists_reduced K w0 hw0
  obtain ⟨w2, r, hw2, hr2, hred2, hdist2⟩ := S.exists_echelon n d hn hn0 ha0 hd hw hcop N hN l hl ρ
    hρl _ w1 r1 hw1 hr1 hred1 rfl
  have hw20 := IBasis.ne_zero S hw2
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  -- representations of the rescaled elements
  have hrep : ∀ i, ∃ (W : C[X][X]) (Q : C[X]), Q ≠ 0 ∧
      (S.wTil w2 r i : L) * aeval S.x Q = S.evXY W ∧ W ≠ 0 ∧ W.natDegree < n := by
    intro i
    obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt (S.wTil w2 r i) hF1
    rw [hn] at hWn
    refine ⟨W, Q, hQ, hWQ, ?_, hWn⟩
    intro h0
    rw [h0, evXY, Polynomial.map_zero, eval_zero] at hWQ
    have hx0 : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
    exact S.wTil_ne_zero w2 r i (hw20 i) (Subtype.ext (by simpa [hx0] using hWQ))
  choose W' Q' hQ' hWQ' hW0' hWn' using hrep
  have hlead := fun i ↦ S.embG_lead_inf n d hn hn0 ha0 hd hw hcop N hN0 ρ hρ (S.wTil w2 r i) (W' i)
    (Q' i) (hQ' i) (hWQ' i) (hW0' i) (hWn' i)
  choose hE0 hord j0 hj0n hj0 hwt hlc using hlead
  set β : Fin S.F.natDegree → C := fun i ↦ ((W' i).coeff (j0 i)).leadingCoeff / (Q' i).leadingCoeff
    with hβ
  have hβ0 : ∀ i, β i ≠ 0 := fun i ↦
    div_ne_zero (leadingCoeff_ne_zero.mpr (hj0 i)) (leadingCoeff_ne_zero.mpr (hQ' i))
  -- the normalized basis
  set w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯ := fun i ↦ S.polyE (Polynomial.C (β i)⁻¹) * w2 i with hwdef
  have hwB : S.IBasis K w := IBasis.scale S hw2 _ fun i ↦ inv_ne_zero (hβ0 i)
  have hrw : ∀ j, S.InfOrd K (w j) (r j) := fun j ↦ InfOrd.scale S (hr2 j) _
  have hredw : S.Reduced K w r := Reduced.scale S hred2 _ fun i ↦ inv_ne_zero (hβ0 i)
  have hwt_eq : ∀ i, S.wTil w r i = S.polyE (Polynomial.C (β i)⁻¹) * S.wTil w2 r i := fun i ↦ by
    simp only [wTil, hwdef]; ring
  -- `S₀ wᵢ′` is a polynomial combination
  have hderiv : ∀ i, ∃ (Wd : C[X][X]) (Qd : C[X]), Qd ≠ 0 ∧
      ((w i : L))′ * aeval S.x Qd = S.evXY Wd := fun i ↦
    S.exists_repr ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩
  choose Wd Qd hQd hWQd using hderiv
  set S0 := UniqueFactorizationMonoid.radical (∏ i, Qd i) with hS0
  have hQprod : ∏ i, Qd i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hQd i
  have hS00 : S0 ≠ 0 := radical_ne_zero' _
  have hcoord : ∀ i, ∃ c : Fin S.F.natDegree → C[X],
      (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (c j) * w j := by
    intro i
    have hreg := S.regularFinite_rad_derivW (K := K) (Polynomial.C η) hx hK (w i) (hwB.1 i) (Wd i)
      (Qd i) (hQd i) (hWQd i)
    obtain ⟨T, hT⟩ : UniqueFactorizationMonoid.radical (Qd i) ∣ S0 :=
      UniqueFactorizationMonoid.radical_dvd_radical (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        hQprod
    have hreg2 := S.regularFinite_polyE_mul (K := K) T hreg
    obtain ⟨c, hc⟩ := hwB.2.1 _ hreg2
    refine ⟨c, ?_⟩
    rw [← hc, hT, S.polyE_mul]
    ring
  choose P hP using hcoord
  -- normality at infinity: the rescaled matrix is bounded
  have hdeg : ∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree := by
    intro i
    have hwt0 : S.InfOrd K (S.wTil w r i) 0 := S.infOrd_wTil w r i (hrw i)
    have hu := S.infOrd_derivW η hx hK (S.wTil w r i) 0 hwt0
    have hq : (X ^ (r i + 1) * S0 : C[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hid := S.deriv_wTil η hx w r S0 P hP i
    refine S.reduced_normal (K := K) w r hrw hredw _ hu (fun j ↦ pqV η r P S0 i j)
      (X ^ (r i + 1) * S0) hq ?_
    have hqL : aeval S.x (X ^ (r i + 1) * S0) ≠ 0 := fun h ↦ hq ((transcendental_iff.mp S.htr) _ h)
    apply Subtype.ext
    have e : ((∑ j, S.polyE (pqV η r P S0 i j) * (S.polyE (X ^ (r i + 1) * S0))⁻¹ *
        ((S.polyE (X ^ r j))⁻¹ * w j) : C⟮S.x⟯⟮S.y⟯) : L) =
        (∑ j, aeval S.x (pqV η r P S0 i j) * (S.wTil w r j : L)) / aeval S.x (X ^ (r i + 1) * S0) := by
      rw [Finset.sum_div]
      push_cast
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [polyE, wTil]
      push_cast
      ring
    rw [e, eq_div_iff hqL]
    exact hid
  refine ⟨w, r, S0, P, W', fun i ↦ Q' i * Polynomial.C (β i), ?_, hS00,
    UniqueFactorizationMonoid.squarefree_radical, hP, hdeg, fun i ↦ ⟨?_, ?_, hW0' i, hWn' i⟩,
    fun i ↦ ?_, fun i j hij ↦ ?_, fun i j1 hj1n hj1 hwt1 ↦ ?_⟩
  · -- independence over `C(x)`: clear denominators
    intro c hc
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    have hpoly : ∀ p : C[X], S.polyE p =
        algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ p) := fun p ↦ Subtype.ext (by
      show aeval S.x p = ((algebraMap C[X] C⟮S.x⟯ p : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple])
    obtain ⟨⟨dd, hdd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors C[X]) (Finset.univ.image c)
    choose p hp using fun j ↦ hdc (c j) (Finset.mem_image_of_mem c (Finset.mem_univ j))
    have hd0 : dd ≠ 0 := nonZeroDivisors.ne_zero hdd
    have h0 := hwB.2.2 p (by
      have : ∑ j, S.polyE (p j) * w j =
          algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ dd) *
            ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hpoly, hp j, Algebra.smul_def, map_mul]
        ring
      rw [this, hc, mul_zero])
    intro j
    have := hp j
    rw [h0 j, map_zero, Algebra.smul_def] at this
    have hdne : algebraMap C[X] C⟮S.x⟯ dd ≠ 0 := fun h ↦ hd0 (IsFractionRing.injective C[X] C⟮S.x⟯
      (by rw [h, map_zero]))
    exact (mul_eq_zero.mp this.symm).resolve_left hdne
  · exact mul_ne_zero (hQ' i) (Polynomial.C_ne_zero.mpr (hβ0 i))
  · rw [hwt_eq, map_mul, ← hWQ' i]
    simp only [polyE, IntermediateField.coe_mul, map_mul, aeval_C]
    have : algebraMap C L (β i) ≠ 0 := (map_ne_zero_iff _ (algebraMap C L).injective).mpr (hβ0 i)
    rw [map_inv₀]
    field_simp
  · -- the window
    have hwin := S.ordR_wTil_window n d hn hn0 ha0 hd hw hcop N hN l hl ρ hρl w2 r hw20 hr2 hred2 i
    have ho := hord i
    simp only [ordR] at hwin
    rw [natDegree_mul_C (hβ0 i)]
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
    have hNpos : (0 : ℤ) < N := by exact_mod_cast hN0
    constructor <;> nlinarith
  · -- distinct weights
    rw [natDegree_mul_C (hβ0 i), natDegree_mul_C (hβ0 j)] at hij
    refine hdist2 i j ?_
    simp only [ordR]
    have h1 := hord i
    have h2 := hord j
    rw [hij] at h1
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
    have : (n : ℤ) * (S.embG (infSub N) (infSub_injective N hN0) ρ hρ (S.wTil w2 r i)).order =
      n * (S.embG (infSub N) (infSub_injective N hN0) ρ hρ (S.wTil w2 r j)).order := by linarith
    exact mul_left_cancel₀ hnpos.ne' this
  · -- leading coefficients `1`
    have hj := S.j0_unique n d hn hn0 ha0 hd hw hcop j1 (j0 i) ((W' i).coeff j1).natDegree
      ((W' i).coeff (j0 i)).natDegree 0 0 hj1n (hj0n i) (by
        have := hwt1.symm.trans (hwt i); push_cast at this ⊢; linarith)
    subst hj
    rw [Polynomial.leadingCoeff_mul, leadingCoeff_C, hβ]
    dsimp only
    rw [mul_div_cancel₀ _ (leadingCoeff_ne_zero.mpr (hQ' i))]

end Main

end CurveData

end Curves
