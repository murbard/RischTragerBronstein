import RischTragerBronstein.Algebraic.Genus0AutoSq

/-!
# The substitution `t = y/(x − e)` for `y² = (x − e)(Ax + k)`

`x = (e t² + k)/(t² − A)`, `y = t (Ae + k)/(t² − A)`, `1/t′ = −2t(Ae + k)/(t² − A)²`
(`euler_root`, `Ae + k ≠ 0`); with `genus0_decides` this gives `genus0_root_decides`: every tower
of logarithms and exponentials over `Kc(x, √q)`, `q` a quadratic (or linear) polynomial with a
rational root and no double root, is decided — no condition on the leading coefficient.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.Genus0Auto

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly

def rootP (e A k : ℚ) : CPoly ℚ := [k, 0, e]
def rootQ (e A k : ℚ) : CPoly ℚ := [-A, 0, 1]
def rootR (e A k : ℚ) : CPoly ℚ := [0, A * e + k]
def rootρ (e A k : ℚ) : Code 1 :=
  (([0, -2 * (A * e + k)] : CPoly ℚ), ([A ^ 2, 0, -2 * A, 0, 1] : CPoly ℚ))

section Root

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The rational-root substitution.** -/
lemma euler_root (hC : ∀ c : Kc, c′ = 0) (e A k : ℚ) (hne : A * e + k ≠ 0)
    (x y : E) (hx : x′ = 1) (hy : y ^ 2 = (x - e) * (A * x + k)) :
    ev (Kc := Kc) (y / (x - e)) (rootQ e A k) ≠ 0 ∧
    x = ev (Kc := Kc) (y / (x - e)) (rootP e A k) / ev (Kc := Kc) (y / (x - e)) (rootQ e A k) ∧
    y = ev (Kc := Kc) (y / (x - e)) (rootR e A k) / ev (Kc := Kc) (y / (x - e)) (rootQ e A k) ∧
    (y / (x - e))′ * evx Kc (y / (x - e)) (rootρ e A k) = 1 := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hxe : x - (e : E) ≠ 0 := by
    intro h0
    have := congrArg (fun z : E ↦ z′) h0
    simp only [map_sub, hx, deriv_ratCast_L, sub_zero, map_zero] at this
    exact one_ne_zero this
  set t := y / (x - e) with ht
  have hyt : y = t * (x - e) := by rw [ht]; field_simp
  clear_value t
  have hneE : (A : E) * e + k ≠ 0 := by exact_mod_cast hne
  -- `t² (x − e) = A x + k`
  have hrel : t ^ 2 * (x - e) = A * x + k := by
    have h := hy
    rw [hyt] at h
    have : (x - e) * (t ^ 2 * (x - e) - (A * x + k)) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hxe)
  have hQ0 : (t ^ 2 - A : E) ≠ 0 := by
    intro h0
    apply hneE
    have : t ^ 2 = A := by linear_combination h0
    rw [this] at hrel; linear_combination -hrel
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hyt
    have ht0 : t = 0 := (mul_eq_zero.mp hyt.symm).resolve_right hxe
    rw [ht0] at hrel
    -- `A x + k = 0` forces `A = 0` and then `k = 0`
    have hAx : (A : E) * x + k = 0 := by linear_combination -hrel
    by_cases hA : A = 0
    · rw [hA] at hne hAx; simp at hAx; exact hne (by simp [hAx])
    · let pK : Kc[X] := C (A : Kc) * X + C (k : Kc)
      have hp0 : pK ≠ 0 := by
        intro h; have := congrArg (coeff · 1) h
        simp [pK, coeff_X, coeff_C] at this; exact hA this
      apply aeval_ne_zero_of_tr x htrK hp0
      simp only [pK, map_add, map_mul, aeval_C, aeval_X, map_ratCast]
      exact hAx
  have hQ : ev (Kc := Kc) t (rootQ e A k) = t ^ 2 - A := by
    rw [rootQ, ev_list3]; push_cast; ring
  have hP : ev (Kc := Kc) t (rootP e A k) = e * t ^ 2 + k := by
    rw [rootP, ev_list3]; push_cast; ring
  have hR : ev (Kc := Kc) t (rootR e A k) = t * (A * e + k) := by
    rw [rootR, ev_list2]; push_cast; ring
  have hxv : x * (t ^ 2 - A) = e * t ^ 2 + k := by linear_combination hrel
  refine ⟨by rw [hQ]; exact hQ0, ?_, ?_, ?_⟩
  · rw [hP, hQ, eq_div_iff hQ0]; exact hxv
  · rw [hR, hQ, eq_div_iff hQ0, hyt]; linear_combination t * hxv - t * A * 0
  · -- `t′ = −(t² − A)/(2y)`
    have htd : t′ * (2 * y) = -(t ^ 2 - A) := by
      have h := congrArg (fun z : E ↦ z′) hxv
      have hAd : (A : E)′ = 0 := deriv_ratCast_L _
      have hed : (e : E)′ = 0 := deriv_ratCast_L _
      have hkd : (k : E)′ = 0 := deriv_ratCast_L _
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, map_sub, map_add, hx,
        hAd, hed, hkd] at h
      rw [hyt]
      linear_combination h
    have htv : t′ = -(t ^ 2 - A) / (2 * y) := by
      rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]; exact htd
    have hρv : evx Kc t (rootρ e A k) = -2 * y / (t ^ 2 - A) := by
      simp only [PrimN.evx, rootρ]
      have e1 := ev_list2 (Kc := Kc) t 0 (-2 * (A * e + k))
      have e2 : ev (Kc := Kc) t ([A ^ 2, 0, -2 * A, 0, 1] : CPoly ℚ) = (t ^ 2 - A) ^ 2 := by
        simp [ev, CPoly.toPoly, map_ofNat]; ring
      simp only [ev] at e1 e2
      rw [e1, e2]
      push_cast
      rw [div_eq_div_iff (pow_ne_zero 2 hQ0) hQ0, hyt]
      have hxv' : (t ^ 2 - A) * (x - e) = A * e + k := by linear_combination hxv
      linear_combination 2 * t * (t ^ 2 - A) * hxv'
    rw [hρv, htv]
    field_simp

/-- **Towers over `Kc(x, √((x − e)(Ax + k)))` are decided** (`Ae + k ≠ 0`). -/
theorem genus0_root_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (e A k : ℚ) (hne : A * e + k ≠ 0) (hy : y ^ 2 = (x - e) * (A * x + k))
    (iks : (m : ℕ) → IKind m) (ilv : (m : ℕ) → ICode m) (ts : ℕ → E)
    (hts : ∀ m, (ts m)′ = kderI Kc x y ts m (iks m))
    (hts0 : ∀ m (a : ICode m), iks m = .exp a → ts m ≠ 0) (hwk : ∀ m, wfK m (iks m) = true)
    (n : ℕ) (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc (insert x (insert y (ts '' Set.Iio n))))
    (hcert : certX (fun m ↦ trK (rootP e A k) (rootQ e A k) (rootR e A k) (rootQ e A k)
      (rootρ e A k) m (iks m))
      (fun m ↦ tr (rootP e A k) (rootQ e A k) (rootR e A k) (rootQ e A k) m (ilv m)) n = true)
    (Aint : ICode n) (hwA : wfI n Aint = true) :
    HasElementaryIntegral (evI Kc x y ts n Aint) ↔
      elemNX (fun m ↦ trK (rootP e A k) (rootQ e A k) (rootR e A k) (rootQ e A k)
        (rootρ e A k) m (iks m))
        (fun m ↦ tr (rootP e A k) (rootQ e A k) (rootR e A k) (rootQ e A k) m (ilv m)) n
        (scal (rootρ e A k) n
          (tr (rootP e A k) (rootQ e A k) (rootR e A k) (rootQ e A k) n Aint)) = true := by
  obtain ⟨hQ, hxt, hyt, hρ⟩ := euler_root hC e A k hne x y hx hy
  exact genus0_decides hC hCall x y (y / (x - e)) hx _ _ _ _ _ hQ hQ hxt hyt hρ iks ilv ts hts
    hts0 hwk n hgen hcert Aint hwA

end Root

end Tower.Genus0Auto
