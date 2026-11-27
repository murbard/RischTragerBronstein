import RischTragerBronstein.Mixed.ExHIndex
import RischTragerBronstein.Mixed.ExHPlace

/-!
# Points of everywhere non-singular reduction on `y² = x³ + A x + B` over `K(X)`

For `A, B ∈ K[X]` let `n = nInf A B` be the least integer with `deg A ≤ 4n`, `deg B ≤ 6n`. The
model at infinity is `(u⁴A, u⁶B)` with `u = X⁻ⁿ` (`uInf n`), reached by `scaleHom`.

* `E0p A B p hp`: points of non-singular reduction at the irreducible polynomial `p`;
* `E0inf A B`: points of non-singular reduction at infinity;
* `E0g A B`: their intersection over all places.

**`exists_exponent`**: if `Δ ≠ 0` and the model is minimal at every finite place (no irreducible
`p` with `p⁴ ∣ A`, `p⁶ ∣ B`), some `N > 0` satisfies `N • P ∈ E0g A B` for every point `P`
(by `local_index` at each place; the model at infinity is minimal by the choice of `n`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace ExH

open FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- The scaling factor at infinity, `X⁻ⁿ`. -/
noncomputable def uInf (n : ℕ) : RatFunc K := (ι X)⁻¹ ^ n

lemma ex_vinf_poly {q : K[X]} (hq : q ≠ 0) : Ex (Vinf (K := K)) (-(q.natDegree : ℤ)) (ι q) :=
  ⟨ι_ne hq, vinf_poly q⟩

lemma ex_uInf (n : ℕ) : Ex (Vinf (K := K)) n (uInf n) := by
  have hX : Ex (Vinf (K := K)) (-((X : K[X]).natDegree : ℤ)) (ι X) := ex_vinf_poly X_ne_zero
  rw [natDegree_X] at hX
  exact (hX.inv.pow n).congr (by push_cast; ring)

lemma uInf_ne (n : ℕ) : (uInf n : RatFunc K) ≠ 0 := (ex_uInf n).ne

lemma ex_inf {n k : ℕ} {q : K[X]} (hq : q ≠ 0) :
    Ex (Vinf (K := K)) ((k : ℤ) * n - q.natDegree) (uInf n ^ k * ι q) :=
  (((ex_uInf n).pow k).mul (ex_vinf_poly hq)).congr (by ring)

lemma dv_inf {n k : ℕ} {q : K[X]} {j : ℤ} (h : j ≤ (k : ℤ) * n - q.natDegree) :
    Dv (Vinf (K := K)) j (uInf n ^ k * ι q) := by
  by_cases hq : q = 0
  · simp [hq, dv_zero]
  · exact (ex_inf hq).dv.mono h

/-- The least `n` with `deg A ≤ 4n` and `deg B ≤ 6n`. -/
def nInf (A B : K[X]) : ℕ := max ((A.natDegree + 3) / 4) ((B.natDegree + 5) / 6)

lemma degA_le (A B : K[X]) : A.natDegree ≤ 4 * nInf A B := by unfold nInf; omega

lemma degB_le (A B : K[X]) : B.natDegree ≤ 6 * nInf A B := by unfold nInf; omega

variable (A B : K[X])

lemma haInf : Dv (Vinf (K := K)) 0 (uInf (nInf A B) ^ 4 * ι A) :=
  dv_inf (by have := degA_le A B; push_cast; omega)

lemma hbInf : Dv (Vinf (K := K)) 0 (uInf (nInf A B) ^ 6 * ι B) :=
  dv_inf (by have := degB_le A B; push_cast; omega)

/-- Points of non-singular reduction at `p`. -/
noncomputable def E0p (p : K[X]) (hp : Irreducible p) :
    AddSubgroup (shortF (ι A) (ι B)).toAffine.Point :=
  E0 (Vp p hp) (ι A) (ι B) (dv_vp_int hp A) (dv_vp_int hp B)

/-- Points of non-singular reduction at infinity. -/
noncomputable def E0inf : AddSubgroup (shortF (ι A) (ι B)).toAffine.Point :=
  (E0 Vinf (uInf (nInf A B) ^ 4 * ι A) (uInf (nInf A B) ^ 6 * ι B) (haInf A B)
    (hbInf A B)).comap (scaleHom (ι A) (ι B) (uInf (nInf A B)) (uInf_ne _))

/-- Points of non-singular reduction at every place. -/
noncomputable def E0g : AddSubgroup (shortF (ι A) (ι B)).toAffine.Point :=
  (⨅ p : {p : K[X] // Irreducible p}, E0p A B p.1 p.2) ⊓ E0inf A B

lemma ιΔ : 4 * (ι A) ^ 3 + 27 * (ι B) ^ 2 = ι (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [map_add, map_mul, map_pow, map_ofNat]

variable {A B}

/-- The model at infinity is minimal. -/
lemma min_inf (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ¬(Dv (Vinf (K := K)) 4 (uInf (nInf A B) ^ 4 * ι A) ∧
      Dv (Vinf (K := K)) 6 (uInf (nInf A B) ^ 6 * ι B)) := by
  rintro ⟨h4, h6⟩
  have hA : A ≠ 0 → (4 : ℤ) ≤ 4 * nInf A B - A.natDegree := fun hA ↦ by
    have := dv_of_ne h4 (ex_inf (n := nInf A B) (k := 4) hA).ne
    rw [(ex_inf (n := nInf A B) (k := 4) hA).2] at this
    simpa using this
  have hB : B ≠ 0 → (6 : ℤ) ≤ 6 * nInf A B - B.natDegree := fun hB ↦ by
    have := dv_of_ne h6 (ex_inf (n := nInf A B) (k := 6) hB).ne
    rw [(ex_inf (n := nInf A B) (k := 6) hB).2] at this
    simpa using this
  have hn : nInf A B = max ((A.natDegree + 3) / 4) ((B.natDegree + 5) / 6) := rfl
  by_cases hA0 : A = 0
  · by_cases hB0 : B = 0
    · exact hΔ (by simp [hA0, hB0])
    · have := hB hB0
      have hdA : A.natDegree = 0 := by rw [hA0, natDegree_zero]
      omega
  · by_cases hB0 : B = 0
    · have := hA hA0
      have hdB : B.natDegree = 0 := by rw [hB0, natDegree_zero]
      omega
    · have := hA hA0
      have := hB hB0
      omega

/-- **A uniform exponent**: some multiple of every point has non-singular reduction at every
place. -/
theorem exists_exponent (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hmin : ∀ p : K[X], Irreducible p → ¬(p ^ 4 ∣ A ∧ p ^ 6 ∣ B)) :
    ∃ N : ℕ, 0 < N ∧ ∀ P : (shortF (ι A) (ι B)).toAffine.Point, N • P ∈ E0g A B := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * ((4 * A ^ 3 + 27 * B ^ 2).natDegree + 12 * nInf A B) + 14 :=
    ⟨_, rfl⟩
  refine ⟨M.factorial, Nat.factorial_pos _, fun P ↦ ?_⟩
  have step : ∀ (G : Type _) [AddCommGroup G] (H : AddSubgroup G) (Q : G),
      (∃ m : ℕ, 0 < m ∧ m ≤ M ∧ m • Q ∈ H) → M.factorial • Q ∈ H := by
    rintro G _ H Q ⟨m, h1, h2, h3⟩
    obtain ⟨c, hc⟩ := Nat.dvd_factorial h1 h2
    rw [hc, mul_nsmul]
    exact H.nsmul_mem h3 c
  have hΔ' : 4 * (ι A) ^ 3 + 27 * (ι B) ^ 2 ≠ 0 := by rw [ιΔ]; exact ι_ne hΔ
  refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [AddSubgroup.mem_iInf]
    rintro ⟨p, hp⟩
    apply step
    obtain ⟨m, h1, h2, h3⟩ := local_index (V := Vp p hp) (dv_vp_int hp A) (dv_vp_int hp B) hΔ'
      (fun h ↦ hmin p hp ⟨(dv_vp_poly hp A 4).mp (by simpa using h.1),
        (dv_vp_poly hp B 6).mp (by simpa using h.2)⟩) P
    refine ⟨m, h1, ?_, h3⟩
    have hv : (Vp p hp).v (4 * (ι A) ^ 3 + 27 * (ι B) ^ 2) ≤
        (4 * A ^ 3 + 27 * B ^ 2).natDegree := by
      rw [ιΔ]; exact vp_le_natDegree hp hΔ
    omega
  · rw [E0inf, AddSubgroup.mem_comap, map_nsmul]
    apply step
    have e12 : 4 * (uInf (nInf A B) ^ 4 * ι A) ^ 3 + 27 * (uInf (nInf A B) ^ 6 * ι B) ^ 2 =
        uInf (nInf A B) ^ 12 * ι (4 * A ^ 3 + 27 * B ^ 2) := by
      rw [← ιΔ]; ring
    have hEx := ex_inf (K := K) (n := nInf A B) (k := 12) hΔ
    obtain ⟨m, h1, h2, h3⟩ := local_index (V := Vinf) (haInf A B) (hbInf A B)
      (by rw [e12]; exact hEx.ne) (min_inf hΔ)
      (scaleHom (ι A) (ι B) (uInf (nInf A B)) (uInf_ne _) P)
    refine ⟨m, h1, ?_, h3⟩
    rw [e12, hEx.2] at h2
    push_cast at h2
    omega

end ExH
