import RischTragerBronstein.Jacobian.Jets

/-!
# Polynomial functions `a + b y` on `y² = f(x)`

Pairs `ψ = (a, b)` stand for `a + b y`. `hmul`, `hconj`, `hnorm` are the product, the conjugation
`y ↦ −y` and the norm `a² − b² f`. Jets are multiplicative (`jet_hmul`), branch jets of every order
exist at points with `2Y₀` a unit (`exists_branch`), vanishing orders add under products
(`VanishAt.hmul`) and survive division by polynomials in `x` that are units at the point
(`VanishAt.of_mul_unit`) or vanish there to a known order (`VanishAt.of_mul_pow`). `PoleLE g ψ N`
bounds the pole order at infinity (`2 deg a ≤ N`, `2 deg b + 2g + 1 ≤ N`), additive under products.
-/

open Polynomial

namespace Jac

variable {R : Type*} [CommRing R]

/-- The product of `a + b y` and `a' + b' y` modulo `y² = f`. -/
noncomputable def hmul (f : R[X]) (ψ φ : R[X] × R[X]) : R[X] × R[X] :=
  (ψ.1 * φ.1 + ψ.2 * φ.2 * f, ψ.1 * φ.2 + φ.1 * ψ.2)

/-- The conjugate `a − b y`. -/
noncomputable def hconj (ψ : R[X] × R[X]) : R[X] × R[X] := (ψ.1, -ψ.2)

/-- The norm `(a + b y)(a − b y) = a² − b² f`. -/
noncomputable def hnorm (f : R[X]) (ψ : R[X] × R[X]) : R[X] := ψ.1 ^ 2 - ψ.2 ^ 2 * f

/-- Multiplication by a polynomial in `x`. -/
noncomputable def hsmul (w : R[X]) (ψ : R[X] × R[X]) : R[X] × R[X] := (w * ψ.1, w * ψ.2)

lemma hnorm_hmul (f : R[X]) (ψ φ : R[X] × R[X]) :
    hnorm f (hmul f ψ φ) = hnorm f ψ * hnorm f φ := by
  simp only [hnorm, hmul]; ring

/-- **Jets are multiplicative.** -/
lemma jet_hmul {f : R[X]} {x₀ Y₀ : R} {ℓ : ℕ} {V : R[X]} (hV : IsBranch f x₀ Y₀ ℓ V)
    (ψ φ : R[X] × R[X]) :
    X ^ ℓ ∣ jet (hmul f ψ φ).1 (hmul f ψ φ).2 x₀ V - jet ψ.1 ψ.2 x₀ V * jet φ.1 φ.2 x₀ V := by
  have e : jet (hmul f ψ φ).1 (hmul f ψ φ).2 x₀ V - jet ψ.1 ψ.2 x₀ V * jet φ.1 φ.2 x₀ V =
      -((ψ.2 * φ.2).comp (X + C x₀) * (V ^ 2 - f.comp (X + C x₀))) := by
    simp only [jet, hmul, add_comp, mul_comp]; ring
  rw [e, dvd_neg]; exact Dvd.dvd.mul_left hV.2 _

/-- **Branch jets exist** at points with `2Y₀` a unit. -/
theorem exists_branch {f : R[X]} {x₀ Y₀ : R} (h2Y : IsUnit (2 * Y₀)) (hY : Y₀ ^ 2 = f.eval x₀)
    (n : ℕ) : ∃ V, IsBranch f x₀ Y₀ n V := by
  induction n with
  | zero => exact ⟨C Y₀, by simp, by simp⟩
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      refine ⟨C Y₀, by simp, ?_⟩
      rw [zero_add, pow_one, X_dvd_iff, coeff_sub, ← C_pow, coeff_C_zero,
        coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add, hY, sub_self]
    obtain ⟨V, hV0, hV⟩ := ih
    obtain ⟨G, hG⟩ := hV
    obtain ⟨u, hu⟩ := h2Y
    set c : R := G.coeff 0 * ↑u⁻¹
    refine ⟨V - C c * X ^ n, ?_, ?_⟩
    · rw [coeff_sub, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, sub_zero, hV0]
    · have e : (V - C c * X ^ n) ^ 2 - f.comp (X + C x₀) =
          X ^ n * (G - C (2 * c) * V) + C (c ^ 2) * X ^ (2 * n) := by
        rw [show (V - C c * X ^ n) ^ 2 - f.comp (X + C x₀) =
          (V ^ 2 - f.comp (X + C x₀)) - C (2 * c) * X ^ n * V + C (c ^ 2) * X ^ (2 * n) by
          simp only [map_mul, map_pow, map_ofNat]; ring, hG]
        ring
      rw [e]
      refine dvd_add ?_ ?_
      · rw [pow_succ]
        refine mul_dvd_mul_left _ ?_
        rw [X_dvd_iff, coeff_sub, coeff_C_mul, hV0]
        simp only [c]
        rw [show (2 : R) * (G.coeff 0 * ↑u⁻¹) * Y₀ = G.coeff 0 * (↑u⁻¹ * (2 * Y₀)) by ring, ← hu,
          Units.inv_mul, mul_one, sub_self]
      · exact Dvd.dvd.mul_left (pow_dvd_pow X (by omega)) _

/-- A branch of higher order is a branch of lower order. -/
lemma IsBranch.mono {f : R[X]} {x₀ Y₀ : R} {n k : ℕ} {V : R[X]} (hV : IsBranch f x₀ Y₀ n V)
    (hk : k ≤ n) : IsBranch f x₀ Y₀ k V :=
  ⟨hV.1, (pow_dvd_pow X hk).trans hV.2⟩

/-- Vanishing is independent of the branch. -/
lemma VanishAt.jet_dvd {f a b : R[X]} {x₀ Y₀ : R} {k n : ℕ} {V : R[X]} (hY : IsUnit (2 * Y₀))
    (h : VanishAt f a b x₀ Y₀ k) (hV : IsBranch f x₀ Y₀ n V) (hk : k ≤ n) :
    X ^ k ∣ jet a b x₀ V := by
  obtain ⟨W, hW, hj⟩ := h
  have hd := branch_unique hY (hV.mono hk) hW
  have e : jet a b x₀ V = jet a b x₀ W + b.comp (X + C x₀) * (V - W) := by
    simp only [jet]; ring
  rw [e]; exact dvd_add hj (Dvd.dvd.mul_left hd _)

lemma VanishAt.mono {f a b : R[X]} {x₀ Y₀ : R} {k n : ℕ} (h : VanishAt f a b x₀ Y₀ n)
    (hk : k ≤ n) : VanishAt f a b x₀ Y₀ k := by
  obtain ⟨V, hV, hj⟩ := h
  exact ⟨V, hV.mono hk, (pow_dvd_pow X hk).trans hj⟩

/-- **Vanishing orders add under products.** -/
theorem VanishAt.hmul {f : R[X]} {x₀ Y₀ : R} {k k' : ℕ} {ψ φ : R[X] × R[X]}
    (h2Y : IsUnit (2 * Y₀)) (hY : Y₀ ^ 2 = f.eval x₀)
    (h : VanishAt f ψ.1 ψ.2 x₀ Y₀ k) (h' : VanishAt f φ.1 φ.2 x₀ Y₀ k') :
    VanishAt f (hmul f ψ φ).1 (hmul f ψ φ).2 x₀ Y₀ (k + k') := by
  obtain ⟨V, hV⟩ := exists_branch h2Y hY (k + k')
  refine ⟨V, hV, ?_⟩
  have h1 := h.jet_dvd h2Y hV (by omega)
  have h2 := h'.jet_dvd h2Y hV (by omega)
  have := jet_hmul hV ψ φ
  have hp : X ^ (k + k') ∣ jet ψ.1 ψ.2 x₀ V * jet φ.1 φ.2 x₀ V := by
    rw [pow_add]; exact mul_dvd_mul h1 h2
  have e : jet (Jac.hmul f ψ φ).1 (Jac.hmul f ψ φ).2 x₀ V =
      (jet (Jac.hmul f ψ φ).1 (Jac.hmul f ψ φ).2 x₀ V - jet ψ.1 ψ.2 x₀ V * jet φ.1 φ.2 x₀ V) +
        jet ψ.1 ψ.2 x₀ V * jet φ.1 φ.2 x₀ V := by ring
  rw [e]; exact dvd_add this hp

/-- Conjugation exchanges the two points over `x₀`. -/
lemma VanishAt.hconj {f a b : R[X]} {x₀ Y₀ : R} {k : ℕ} (h : VanishAt f a b x₀ Y₀ k) :
    VanishAt f a (-b) x₀ (-Y₀) k := by
  obtain ⟨V, hV, hj⟩ := h
  refine ⟨-V, hV.neg, ?_⟩
  have e : jet a (-b) x₀ (-V) = jet a b x₀ V := by simp only [jet, neg_comp]; ring
  rwa [e]

lemma jet_hsmul (w : R[X]) (ψ : R[X] × R[X]) (x₀ : R) (V : R[X]) :
    jet (hsmul w ψ).1 (hsmul w ψ).2 x₀ V = w.comp (X + C x₀) * jet ψ.1 ψ.2 x₀ V := by
  simp only [jet, hsmul, mul_comp]; ring

/-- Dividing by a polynomial in `x` which is a unit at `x₀` keeps the vanishing order. -/
lemma VanishAt.of_hsmul_unit {f w : R[X]} {ψ : R[X] × R[X]} {x₀ Y₀ : R} {k : ℕ}
    (hw : IsUnit (w.eval x₀)) (h : VanishAt f (Jac.hsmul w ψ).1 (Jac.hsmul w ψ).2 x₀ Y₀ k) :
    VanishAt f ψ.1 ψ.2 x₀ Y₀ k := by
  obtain ⟨V, hV, hj⟩ := h
  refine ⟨V, hV, X_pow_dvd_of_mul (c := w.comp (X + C x₀)) ?_ ?_⟩
  · rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]; exact hw
  · rwa [← jet_hsmul]

/-- Multiplying by a polynomial in `x` keeps vanishing. -/
lemma VanishAt.hsmul {f w : R[X]} {ψ : R[X] × R[X]} {x₀ Y₀ : R} {k : ℕ}
    (h : VanishAt f ψ.1 ψ.2 x₀ Y₀ k) : VanishAt f (hsmul w ψ).1 (hsmul w ψ).2 x₀ Y₀ k := by
  obtain ⟨V, hV, hj⟩ := h
  exact ⟨V, hV, by rw [jet_hsmul]; exact Dvd.dvd.mul_left hj _⟩

/-- Dividing by `(x − x₀)ᵉ` lowers the vanishing order by `e`. -/
lemma VanishAt.of_hsmul_pow {f : R[X]} {ψ : R[X] × R[X]} {x₀ Y₀ : R} {k e : ℕ}
    (h : VanishAt f (Jac.hsmul ((X - C x₀) ^ e) ψ).1 (Jac.hsmul ((X - C x₀) ^ e) ψ).2 x₀ Y₀ (k + e)) :
    VanishAt f ψ.1 ψ.2 x₀ Y₀ k := by
  obtain ⟨V, hV, hj⟩ := h
  refine ⟨V, hV.mono (by omega), ?_⟩
  rw [jet_hsmul, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right, pow_add] at hj
  obtain ⟨q, hq⟩ := hj
  refine ⟨q, ?_⟩
  ext d
  have := congrArg (fun P : R[X] ↦ P.coeff (d + e)) hq
  rw [mul_comm (X ^ e), coeff_mul_X_pow, show X ^ k * X ^ e * q = X ^ k * q * X ^ e by ring,
    coeff_mul_X_pow] at this
  exact this

/-- **Vanishing gives a factor of the norm.** -/
lemma VanishAt.dvd_hnorm {f : R[X]} {ψ : R[X] × R[X]} {x₀ Y₀ : R} {k : ℕ}
    (h : VanishAt f ψ.1 ψ.2 x₀ Y₀ k) : (X - C x₀) ^ k ∣ hnorm f ψ := by
  obtain ⟨V, hV, hj⟩ := h
  apply dvd_of_comp
  have e : (hnorm f ψ).comp (X + C x₀) = jet ψ.1 ψ.2 x₀ V * (ψ.1.comp (X + C x₀) -
      ψ.2.comp (X + C x₀) * V) + (ψ.2.comp (X + C x₀)) ^ 2 * (V ^ 2 - f.comp (X + C x₀)) := by
    simp only [hnorm, jet, sub_comp, mul_comp, pow_comp]; ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_right hj _) (Dvd.dvd.mul_left hV.2 _)

section PoleLE

/-- Pole order at infinity at most `N` (`deg f = 2g + 1`). -/
def PoleLE (g : ℕ) (ψ : R[X] × R[X]) (N : ℕ) : Prop :=
  2 * ψ.1.natDegree ≤ N ∧ (ψ.2 = 0 ∨ 2 * ψ.2.natDegree + 2 * g + 1 ≤ N)

theorem PoleLE.hmul {g : ℕ} {f : R[X]} (hf : f.natDegree ≤ 2 * g + 1) {ψ φ : R[X] × R[X]}
    {N M : ℕ} (h : PoleLE g ψ N) (h' : PoleLE g φ M) : PoleLE g (hmul f ψ φ) (N + M) := by
  obtain ⟨ha, hb⟩ := h
  obtain ⟨ha', hb'⟩ := h'
  have d1 : (ψ.1 * φ.1).natDegree ≤ ψ.1.natDegree + φ.1.natDegree := natDegree_mul_le
  have d2 : (ψ.2 * φ.2 * f).natDegree ≤ ψ.2.natDegree + φ.2.natDegree + f.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
  have d3 : (ψ.1 * φ.2).natDegree ≤ ψ.1.natDegree + φ.2.natDegree := natDegree_mul_le
  have d4 : (φ.1 * ψ.2).natDegree ≤ φ.1.natDegree + ψ.2.natDegree := natDegree_mul_le
  have hT : 2 * (ψ.2 * φ.2 * f).natDegree ≤ N + M := by
    rcases hb with hb | hb
    · simp [hb]
    rcases hb' with hb' | hb'
    · simp [hb']
    omega
  constructor
  · show 2 * (ψ.1 * φ.1 + ψ.2 * φ.2 * f).natDegree ≤ N + M
    refine (Nat.mul_le_mul_left 2 (natDegree_add_le _ _)).trans ?_
    rw [← Nat.mul_max_mul_left]
    exact max_le (by omega) hT
  · show ψ.1 * φ.2 + φ.1 * ψ.2 = 0 ∨ 2 * (ψ.1 * φ.2 + φ.1 * ψ.2).natDegree + 2 * g + 1 ≤ N + M
    rcases hb with hb | hb
    · rcases hb' with hb' | hb'
      · left; simp [hb, hb']
      · right
        rw [hb, mul_zero, add_zero]
        omega
    · right
      have hs := natDegree_add_le (ψ.1 * φ.2) (φ.1 * ψ.2)
      have h5 : 2 * (ψ.1 * φ.2).natDegree + 2 * g + 1 ≤ N + M := by
        rcases hb' with hb' | hb'
        · simp [hb']; omega
        · omega
      have h6 : 2 * (φ.1 * ψ.2).natDegree + 2 * g + 1 ≤ N + M := by omega
      have h7 : 2 * max (ψ.1 * φ.2).natDegree (φ.1 * ψ.2).natDegree + 2 * g + 1 ≤ N + M := by
        rw [← Nat.mul_max_mul_left]
        rcases le_total (2 * (ψ.1 * φ.2).natDegree) (2 * (φ.1 * ψ.2).natDegree) with h8 | h8
        · rw [max_eq_right h8]; exact h6
        · rw [max_eq_left h8]; exact h5
      have := Nat.mul_le_mul_left 2 hs
      omega

lemma PoleLE.hconj {g : ℕ} {ψ : R[X] × R[X]} {N : ℕ} (h : PoleLE g ψ N) :
    PoleLE g (hconj ψ) N := by
  obtain ⟨ha, hb⟩ := h
  refine ⟨ha, ?_⟩
  simp only [Jac.hconj, neg_eq_zero, natDegree_neg]; exact hb

lemma PoleLE.mono {g : ℕ} {ψ : R[X] × R[X]} {N M : ℕ} (h : PoleLE g ψ N) (hNM : N ≤ M) :
    PoleLE g ψ M :=
  ⟨h.1.trans hNM, h.2.imp_right fun h ↦ h.trans hNM⟩

end PoleLE

section Domain

variable [IsDomain R]

/-- The norm of a non-zero function is non-zero when `f` has odd degree. -/
lemma hnorm_ne_zero {f : R[X]} (hf : Odd f.natDegree) {ψ : R[X] × R[X]} (hψ : ψ ≠ (0, 0)) :
    hnorm f ψ ≠ 0 := by
  intro h
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have e : ψ.1 ^ 2 = ψ.2 ^ 2 * f := by rw [hnorm, sub_eq_zero] at h; exact h
  by_cases hb : ψ.2 = 0
  · rw [hb] at e; simp at e
    exact hψ (Prod.ext e hb)
  · have ha : ψ.1 ≠ 0 := by
      intro ha; rw [ha] at e; simp [hb, hf0] at e
    have := congrArg natDegree e
    rw [natDegree_pow, natDegree_mul (pow_ne_zero _ hb) hf0, natDegree_pow] at this
    obtain ⟨r, hr⟩ := hf
    omega

lemma hmul_ne_zero {f : R[X]} (hf : Odd f.natDegree) {ψ φ : R[X] × R[X]} (hψ : ψ ≠ (0, 0))
    (hφ : φ ≠ (0, 0)) : hmul f ψ φ ≠ (0, 0) := by
  intro h
  have := hnorm_hmul f ψ φ
  rw [h] at this
  simp only [hnorm, Prod.fst_zero, Prod.snd_zero] at this
  have h0 : (0 : R[X]) ^ 2 - 0 ^ 2 * f = 0 := by ring
  rw [h0] at this
  exact mul_ne_zero (hnorm_ne_zero hf hψ) (hnorm_ne_zero hf hφ) this.symm

end Domain

end Jac
