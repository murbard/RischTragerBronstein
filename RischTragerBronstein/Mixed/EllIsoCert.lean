import RischTragerBronstein.Mixed.EllIso1728
import RischTragerBronstein.Mixed.EllCompute2

/-!
# Executable height certificates exist on isotrivial curves

`certQ_of_hgap`: the executable check `certQ` (rational arithmetic on code points) is *exactly*
the real inequality `hgap` of `ell_indep`, so a level `k` at which `hgap` holds makes `certQ`
pass. With `hgap_exists` (quadratic twists), `hgap_exists_0` (`j = 0`), `hgap_exists_1728`
(`j = 1728`): for independent represented points on these curves, **`certQ` passes at some level**
(`certQ_exists_quad`, `certQ_exists_0`, `certQ_exists_1728`), i.e. the certificate search
terminates.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- **The executable check is the real inequality.** -/
theorem certQ_of_hgap (Ac : CPoly K) (A B : K[X]) (hA : CPoly.toPoly Ac = A) (k : ℕ)
    (oP oQ : PtC K) (P Q : (shortW A B).toAffine.Point) (hP : Rel A B oP P) (hQ : Rel A B oQ Q)
    (hg : let C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
      let h := hR A B
      let d := MWPair.dbl (G := (shortW A B).toAffine.Point)
      C / 3 / 4 ^ k * (|h (d^[k] P) / 4 ^ k| + |h (d^[k] Q) / 4 ^ k| + C / 3 / 4 ^ k) +
        3 * (C / 3 / 4 ^ k) / 2 * (|h (d^[k] (P + Q)) / 4 ^ k - h (d^[k] P) / 4 ^ k -
          h (d^[k] Q) / 4 ^ k| + 3 * (C / 3 / 4 ^ k) / 2) <
      |h (d^[k] P) / 4 ^ k * (h (d^[k] Q) / 4 ^ k) - ((h (d^[k] (P + Q)) / 4 ^ k -
          h (d^[k] P) / 4 ^ k - h (d^[k] Q) / 4 ^ k) / 2) ^ 2|) :
    certQ Ac (max A.natDegree B.natDegree) k oP oQ = true := by
  have e1 := htC_spec A B _ _ (dblC_spec Ac A B hA k oP P hP)
  have e2 := htC_spec A B _ _ (dblC_spec Ac A B hA k oQ Q hQ)
  have e3 := htC_spec A B _ _ (dblC_spec Ac A B hA k _ _ (addC_spec Ac A B hA oP oQ P Q hP hQ))
  simp only [certQ, decide_eq_true_eq]
  simp only [hR] at hg
  rw [← e1, ← e2, ← e3] at hg
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast [Rat.cast_abs]
  exact_mod_cast hg

theorem certQ_exists_quad {A B D : K[X]} {a b : K} (Ac : CPoly K) (hAc : CPoly.toPoly Ac = A)
    (hD : D ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hA : A = C a * D ^ 2) (hB : B = C b * D ^ 3)
    (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι D ^ 3 ≠ w ^ 2)
    (oP oQ : PtC K) (P Q : (shortW A B).toAffine.Point) (hP : Rel A B oP P) (hQ : Rel A B oQ Q)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k, certQ Ac (max A.natDegree B.natDegree) k oP oQ = true := by
  obtain ⟨k, hk⟩ := hgap_exists hD hΔ hA hB hΔ' hsq P Q hind
  exact ⟨k, certQ_of_hgap Ac A B hAc k oP oQ P Q hP hQ hk⟩

theorem certQ_exists_0 {B : K[X]} (Ac : CPoly K) (hAc : CPoly.toPoly Ac = 0) (hB : B ≠ 0)
    (hΔ' : 4 * (0 : K[X]) ^ 3 + 27 * B ^ 2 ≠ 0)
    (hcube : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι B ≠ w ^ 3)
    (oP oQ : PtC K) (P Q : (shortW 0 B).toAffine.Point) (hP : Rel 0 B oP P) (hQ : Rel 0 B oQ Q)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k, certQ Ac (max (0 : K[X]).natDegree B.natDegree) k oP oQ = true := by
  obtain ⟨k, hk⟩ := hgap_exists_0 hB hΔ' hcube P Q hind
  exact ⟨k, certQ_of_hgap Ac 0 B hAc k oP oQ P Q hP hQ hk⟩

theorem certQ_exists_1728 {A : K[X]} (Ac : CPoly K) (hAc : CPoly.toPoly Ac = A) (hA : A ≠ 0)
    (hΔ' : 4 * A ^ 3 + 27 * (0 : K[X]) ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι A ≠ w ^ 2)
    (oP oQ : PtC K) (P Q : (shortW A 0).toAffine.Point) (hP : Rel A 0 oP P) (hQ : Rel A 0 oQ Q)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k, certQ Ac (max A.natDegree (0 : K[X]).natDegree) k oP oQ = true := by
  obtain ⟨k, hk⟩ := hgap_exists_1728 hA hΔ' hsq P Q hind
  exact ⟨k, certQ_of_hgap Ac A 0 hAc k oP oQ P Q hP hQ hk⟩

end FFHeight



