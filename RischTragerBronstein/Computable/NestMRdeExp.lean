import RischTragerBronstein.Computable.NestMRde0
import RischTragerBronstein.Computable.NestMStructure
import RischTragerBronstein.RDE.ValInf
import RischTragerBronstein.Computable.NestPElem

/-!
# The parametric Risch equation over an exponential level: soundness and completeness

`prdeExp` at level `m + 1` (`t = tₘ = exp aₘ`) for towers of exponentials. The proof follows the
algorithm:

* the equation for `y = Y / Q` (`Q = tᵏ D`) is the polynomial equation `A Y′ + B Y = ∑ cᵢ Cᵢ`
  times a non-zero factor (`pe_identity`);
* soundness: the final constant system forces the polynomial equation;
* completeness: every solution has the denominator `Q` (normal primes: `rde_pole_bound`; `t`:
  the special bounds and the structure theorem), a numerator of bounded degree (values at
  infinity, `RDE/ValInf.lean`, and the structure theorem again), and is found by the coefficient
  loop (`rdeLoop_stage`) and the final constant system.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP CPoly

/-! ### Generic facts on `lowZ` and `monicG` -/

section GenericPE

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma toPoly_lowZ : ∀ p : GPoly α,
    GPoly.toPoly M p = X ^ lowZ O p * GPoly.toPoly M (p.drop (lowZ O p))
  | [] => by simp [lowZ]
  | a :: p => by
    by_cases ha : O.isZero a = true
    · have e : lowZ O (a :: p) = lowZ O p + 1 := by simp [lowZ, List.takeWhile_cons, ha]
      rw [e, List.drop_succ_cons, GPoly.toPoly_cons, toPoly_lowZ p, (M.isZero_iff a).mp ha]
      simp [pow_succ]
      ring
    · have e : lowZ O (a :: p) = 0 := by simp [lowZ, List.takeWhile_cons, ha]
      rw [e]; simp

lemma not_X_dvd_drop_lowZ (p : GPoly α) (hp : GPoly.toPoly M p ≠ 0) :
    ¬X ∣ GPoly.toPoly M (p.drop (lowZ O p)) := by
  induction p with
  | nil => simp at hp
  | cons a p ih =>
    by_cases ha : O.isZero a = true
    · have e : lowZ O (a :: p) = lowZ O p + 1 := by simp [lowZ, List.takeWhile_cons, ha]
      rw [e, List.drop_succ_cons]
      refine ih fun h0 ↦ hp ?_
      rw [GPoly.toPoly_cons, h0, (M.isZero_iff a).mp ha]; simp
    · have e : lowZ O (a :: p) = 0 := by simp [lowZ, List.takeWhile_cons, ha]
      rw [e, List.drop_zero, X_dvd_iff, GPoly.toPoly_cons]
      simp only [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero]
      exact fun h0 ↦ ha ((M.isZero_iff a).mpr h0)

lemma toPoly_monicG (p : GPoly α) (hp : GPoly.toPoly M p ≠ 0) :
    GPoly.toPoly M (monicG O p) = C (GPoly.toPoly M p).leadingCoeff⁻¹ * GPoly.toPoly M p ∧
      (GPoly.toPoly M (monicG O p)).Monic := by
  have e : GPoly.toPoly M (monicG O p) = C (GPoly.toPoly M p).leadingCoeff⁻¹ * GPoly.toPoly M p := by
    rw [monicG, GPoly.toPoly_smul, M.sem_inv, GPoly.toPoly_trim, leadG,
      GPoly.leadingCoeff_toPoly M hp]
  refine ⟨e, ?_⟩
  rw [e]
  exact monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hp))

end GenericPE

/-! ### The shape of the output -/

lemma prdeExp_mem (ks : (m : ℕ) → KindN m) (m : ℕ) (a : Code (m + 1))
    (lower : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hcode : Code (m + 2)) (W : List (Code (m + 2))) (r : List ℚ × Code (m + 2))
    (hr : r ∈ prdeExp ks m a lower hcode W) :
    ∃ (kap : ℕ) (Bs : List (List ℚ × GPoly (Code (m + 1)))) (u : CPoly ℚ),
      u ∈ consys ks (m + 1) (Bs.map fun b ↦ ((residE (opsM ks m) (cstN m) (peW (opsM ks m) a)
        (peA (opsM ks m) (peF (opsM ks m) a (cleanG (opsM ks m) hcode)
          (peQ (opsM ks m) kap (peD (opsM ks m) a (peE (opsM ks m) (W.map (cleanG (opsM ks m)))))))
          (peRs (opsM ks m) a (W.map (cleanG (opsM ks m)))
            (peQ (opsM ks m) kap (peD (opsM ks m) a (peE (opsM ks m) (W.map (cleanG (opsM ks m))))))))
        (peB (opsM ks m) (peF (opsM ks m) a (cleanG (opsM ks m) hcode)
          (peQ (opsM ks m) kap (peD (opsM ks m) a (peE (opsM ks m) (W.map (cleanG (opsM ks m)))))))
          (peRs (opsM ks m) a (W.map (cleanG (opsM ks m)))
            (peQ (opsM ks m) kap (peD (opsM ks m) a (peE (opsM ks m) (W.map (cleanG (opsM ks m))))))))
        (peCs (opsM ks m) (peF (opsM ks m) a (cleanG (opsM ks m) hcode)
          (peQ (opsM ks m) kap (peD (opsM ks m) a (peE (opsM ks m) (W.map (cleanG (opsM ks m)))))))
          (peRs (opsM ks m) a (W.map (cleanG (opsM ks m)))
            (peQ (opsM ks m) kap (peD (opsM ks m) a (peE (opsM ks m) (W.map (cleanG (opsM ks m))))))))
        b, [(opsM ks m).one]) : Code (m + 2))) ∧
      r = (vcomb (W.map (cleanG (opsM ks m))).length ((List.range Bs.length).map (u.getD · 0))
        (Bs.map Prod.fst),
        ((lcombGP (opsM ks m) (cstN m) ((List.range Bs.length).map (u.getD · 0)) (Bs.map Prod.snd),
          peQ (opsM ks m) kap (peD (opsM ks m) a (peE (opsM ks m) (W.map (cleanG (opsM ks m))))))
            : Code (m + 2))) := by
  simp only [prdeExp] at hr
  split at hr
  · simp at hr
  · unfold peOut at hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    exact ⟨_, _, u, hu, rfl⟩

/-! ### Degree bounds over an exponential -/

section DegExp

variable {F0 : Type*} [Field F0] [Differential F0] (b : F0)

lemma top_coeff_rdeExp (A B Y : F0[X]) (dA : ℕ) (hA : A.natDegree ≤ dA) (hB : B.natDegree ≤ dA) :
    (A * implicitDeriv (C b * X) Y + B * Y).coeff (dA + Y.natDegree) =
      A.coeff dA * ((Y.leadingCoeff)′ + b * (Y.natDegree * Y.leadingCoeff)) +
        B.coeff dA * Y.leadingCoeff := by
  have hD : (implicitDeriv (C b * X) Y).natDegree ≤ Y.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_implicitDeriv_C_mul_X, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi)]
    simp
  rw [coeff_add, coeff_mul_add_eq_of_natDegree_le hA hD, coeff_mul_add_eq_of_natDegree_le hB le_rfl,
    coeff_implicitDeriv_C_mul_X]
  rfl

lemma natDegree_rdeExp_le (A B Y : F0[X]) (d : ℕ) (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) :
    (A * implicitDeriv (C b * X) Y + B * Y).natDegree ≤ d + Y.natDegree := by
  have hD : (implicitDeriv (C b * X) Y).natDegree ≤ Y.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_implicitDeriv_C_mul_X, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi)]
    simp
  exact (natDegree_add_le _ _).trans (max_le (natDegree_mul_le.trans (add_le_add hA hD))
    (natDegree_mul_le.trans (add_le_add hB le_rfl)))

/-- **`A` dominates** (`deg B < deg A`, or `B = 0`): `deg Y ≤ R - deg A`. -/
lemma natDegree_le_of_rdeExp_A (A B Y r : F0[X]) (R : ℕ) (hr : r.natDegree ≤ R) (hA0 : A ≠ 0)
    (hBA : B = 0 ∨ B.natDegree < A.natDegree)
    (hhom : ∀ k : ℕ, k ≠ 0 → ∀ e : F0, e ≠ 0 → e′ + k * b * e ≠ 0)
    (heq : A * implicitDeriv (C b * X) Y + B * Y = r) : Y.natDegree ≤ R - A.natDegree := by
  by_contra hlt
  push_neg at hlt
  have hY0 : Y ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hlt; omega
  have hN : Y.natDegree ≠ 0 := by omega
  have hBd : B.natDegree ≤ A.natDegree := by rcases hBA with h | h <;> [simp [h]; omega]
  have hBc : B.coeff A.natDegree = 0 := by
    rcases hBA with h | h
    · simp [h]
    · exact coeff_eq_zero_of_natDegree_lt h
  have htop := top_coeff_rdeExp b A B Y A.natDegree le_rfl hBd
  rw [heq, hBc, zero_mul, add_zero, coeff_eq_zero_of_natDegree_lt (by omega)] at htop
  have hlcA : A.coeff A.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have := hhom _ hN _ (leadingCoeff_ne_zero.mpr hY0)
  exact (mul_ne_zero hlcA (by intro h0; apply this; linear_combination h0)) htop.symm

/-- **`B` dominates** (`deg A < deg B`): `Y = 0` or `deg Y + deg B ≤ R`. -/
lemma natDegree_le_of_rdeExp_B (A B Y r : F0[X]) (R : ℕ) (hr : r.natDegree ≤ R) (hB0 : B ≠ 0)
    (hAB : A.natDegree < B.natDegree) (heq : A * implicitDeriv (C b * X) Y + B * Y = r) :
    Y = 0 ∨ Y.natDegree + B.natDegree ≤ R := by
  by_contra hne
  push_neg at hne
  obtain ⟨hY0, hlt⟩ := hne
  have htop := top_coeff_rdeExp b A B Y B.natDegree hAB.le le_rfl
  rw [heq, coeff_eq_zero_of_natDegree_lt hAB, zero_mul, zero_add,
    coeff_eq_zero_of_natDegree_lt (by omega)] at htop
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hB0) (leadingCoeff_ne_zero.mpr hY0) htop.symm

/-- **Balanced** (`deg A = deg B`): `deg Y ≤ R - deg A`, or the top coefficient cancels. -/
lemma natDegree_le_of_rdeExp_bal (A B Y r : F0[X]) (R : ℕ) (hr : r.natDegree ≤ R)
    (hAB : A.natDegree = B.natDegree) (heq : A * implicitDeriv (C b * X) Y + B * Y = r) :
    Y.natDegree ≤ R - A.natDegree ∨
      (Y ≠ 0 ∧ A.leadingCoeff * ((Y.leadingCoeff)′ + Y.natDegree * b * Y.leadingCoeff) +
        B.leadingCoeff * Y.leadingCoeff = 0) := by
  by_cases hlt : Y.natDegree ≤ R - A.natDegree
  · exact Or.inl hlt
  right
  push_neg at hlt
  have hY0 : Y ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hlt; omega
  refine ⟨hY0, ?_⟩
  have htop := top_coeff_rdeExp b A B Y A.natDegree le_rfl hAB.ge
  rw [heq, coeff_eq_zero_of_natDegree_lt (by omega)] at htop
  have hBl : B.leadingCoeff = B.coeff A.natDegree := by rw [leadingCoeff, hAB]
  rw [hBl, show A.leadingCoeff = A.coeff A.natDegree from rfl]
  linear_combination -htop

end DegExp

lemma pow_dvd_derivation_pow_mul {R : Type*} [CommRing R] (D : Derivation ℤ R R) (q e1 : R)
    (E : ℕ) : q ^ E ∣ D (q ^ (E + 1) * e1) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
  simp only [smul_eq_mul, nsmul_eq_mul]
  exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow q (Nat.le_succ E)) _)
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _)

section GenericEps

variable {α : Type} (O : COps α)

lemma peEps_ge : ∀ (Wc : List (GPoly α × GPoly α)) (q : GPoly α × GPoly α), q ∈ Wc →
    GPoly.isZero O q.1 = false → lowZ O q.2 - lowZ O q.1 ≤ peEps O Wc
  | [], _, hq, _ => by simp at hq
  | p :: Wc, q, hq, hz => by
    simp only [peEps, List.foldr_cons] at *
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [if_neg (by simp [hz])]
      exact le_max_right _ _
    · have := peEps_ge Wc q hq hz
      simp only [peEps] at this
      split_ifs
      · exact this
      · exact this.trans (le_max_left _ _)

end GenericEps

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {as : (m : ℕ) → Code (m + 1)}
variable (T : NestMTower Kc E (expK as))

section Level

variable (m : ℕ) (h : T.Tr (m + 1))

/-- The model of level `m`. -/
noncomputable abbrev Mm : CField (Code (m + 1)) (T.F m) (opsM (expK as) m) :=
  T.MP m fun i hi ↦ h i (by omega)

/-- The model of level `m + 1`, typed with pairs of polynomials. -/
noncomputable abbrev M1 : CField (GPoly (Code (m + 1)) × GPoly (Code (m + 1))) (T.F (m + 1))
    ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))) := T.MP (m + 1) h

/-- The polynomial of a code of level `m + 1`, in `F (m + 1)`. -/
noncomputable abbrev σ1 (p : GPoly (Code (m + 1))) : T.F (m + 1) :=
  T.phi m (GPoly.toPoly (T.Mm m h) p)

lemma sem1 (q : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) :
    (T.M1 m h).sem q = T.σ1 m h q.1 / T.σ1 m h q.2 := rfl

/-- The exponent derivative `b = aₘ′`. -/
noncomputable abbrev bE : T.F m := ((T.Mm m h).sem (as m))′

lemma toPoly_peW : GPoly.toPoly (T.Mm m h) (peW (opsM (expK as) m) (as m)) = C (T.bE m h) * X := by
  simp [peW, (T.Mm m h).sem_zero, (T.Mm m h).sem_deriv, bE]

lemma wPoly_eq_bE : T.wPoly m = C (T.bE m h) * X := by
  rw [T.wPoly_expK, bE, T.sem_MP_F]

lemma deriv_phi_exp (P : (T.F m)[X]) :
    (T.phi m P)′ = T.phi m (implicitDeriv (C (T.bE m h) * X) P) := by
  rw [T.deriv_phi, T.wPoly_eq_bE m h]

include h in
lemma phi_injective' : Function.Injective (T.phi m) := T.phi_injective (h m (by omega))

lemma σ1_eq_zero_iff (p : GPoly (Code (m + 1))) :
    T.σ1 m h p = 0 ↔ GPoly.isZero (opsM (expK as) m) p = true := by
  rw [GPoly.isZero_iff (T.Mm m h), σ1, map_eq_zero_iff _ (T.phi_injective' m h)]

lemma sem1_cleanG (q : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) :
    (T.M1 m h).sem (cleanG (opsM (expK as) m) q) = (T.M1 m h).sem q := by
  unfold cleanG
  split_ifs with hz
  · rw [T.sem1, T.sem1, (T.σ1_eq_zero_iff m h q.2).mpr hz]
    simp [σ1, (T.Mm m h).sem_one]
  · rfl

lemma σ1_cleanG_ne (q : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) :
    T.σ1 m h (cleanG (opsM (expK as) m) q).2 ≠ 0 := by
  unfold cleanG
  split_ifs with hz
  · simp [σ1, (T.Mm m h).sem_one]
  · rw [Ne, T.σ1_eq_zero_iff]; exact hz

lemma σ1_mul (a b : GPoly (Code (m + 1))) :
    T.σ1 m h (GPoly.mul (opsM (expK as) m) a b) = T.σ1 m h a * T.σ1 m h b := by
  simp [σ1]

lemma σ1_one : T.σ1 m h [(opsM (expK as) m).one] = 1 := by
  simp [σ1, (T.Mm m h).sem_one]

end Level

section Identity

variable (m : ℕ) (h : T.Tr (m + 1))

/-- **The identity behind `prdeExp`**: the polynomial equation is the Risch equation for `Y / Q`
times the non-zero factor `F₂ P Q`. -/
lemma pe_identity (hc : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (Wc : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))) (Q : GPoly (Code (m + 1)))
    (hQ : T.σ1 m h Q ≠ 0) (Y : (T.F m)[X]) (c : ℕ → Kc) :
    T.phi m (GPoly.toPoly (T.Mm m h) (peA (opsM (expK as) m)
        (peF (opsM (expK as) m) (as m) hc Q) (peRs (opsM (expK as) m) (as m) Wc Q)) *
          implicitDeriv (C (T.bE m h) * X) Y +
      GPoly.toPoly (T.Mm m h) (peB (opsM (expK as) m)
        (peF (opsM (expK as) m) (as m) hc Q) (peRs (opsM (expK as) m) (as m) Wc Q)) * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (c i)) *
        GPoly.toPoly (T.Mm m h) ((peCs (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hc Q)
          (peRs (opsM (expK as) m) (as m) Wc Q)).getD i [])) =
    T.σ1 m h (peF (opsM (expK as) m) (as m) hc Q).2 *
      T.σ1 m h (prodD (GPoly.mul (opsM (expK as) m)) [(opsM (expK as) m).one]
        (peRs (opsM (expK as) m) (as m) Wc Q)) * T.σ1 m h Q *
      ((T.phi m Y / T.σ1 m h Q)′ + ((T.M1 m h).sem hc)′ * (T.phi m Y / T.σ1 m h Q) -
        ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (c i) *
          (T.M1 m h).sem (Wc.getD i ((opsM (expK as) m).monomial
            (peW (opsM (expK as) m) (as m))).zero)) := by
  set O := opsM (expK as) m with hO
  set O' := O.monomial (peW O (as m)) with hO'
  set F := peF O (as m) hc Q with hF
  set Rs := peRs O (as m) Wc Q with hRs
  set P := prodD (GPoly.mul O) [O.one] Rs with hP
  have hadd : ∀ a b, (T.M1 m h).sem (O'.add a b) = (T.M1 m h).sem a + (T.M1 m h).sem b := (T.M1 m h).sem_add
  have hneg : ∀ a, (T.M1 m h).sem (O'.neg a) = -(T.M1 m h).sem a := (T.M1 m h).sem_neg
  have hmul : ∀ a b, (T.M1 m h).sem (O'.mul a b) = (T.M1 m h).sem a * (T.M1 m h).sem b := (T.M1 m h).sem_mul
  have hinv : ∀ a, (T.M1 m h).sem (O'.inv a) = ((T.M1 m h).sem a)⁻¹ := (T.M1 m h).sem_inv
  have hder : ∀ a, (T.M1 m h).sem (O'.deriv a) = ((T.M1 m h).sem a)′ := (T.M1 m h).sem_deriv
  have hQv : (T.M1 m h).sem (Q, [O.one]) = T.σ1 m h Q := by rw [T.sem1, T.σ1_one, div_one]
  have hsF : T.σ1 m h F.1 / T.σ1 m h F.2 = ((T.M1 m h).sem hc)′ - (T.σ1 m h Q)′ / T.σ1 m h Q := by
    rw [← T.sem1, hF, peF, T.sem1_cleanG, hadd, hder, hneg, hmul, hder, hinv, hQv]
    ring
  have hF2 : T.σ1 m h F.2 ≠ 0 := T.σ1_cleanG_ne m h _
  have hRs2 : ∀ p ∈ Rs, T.σ1 m h p.2 ≠ 0 := fun p hp ↦ by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σ1_cleanG_ne m h _
  have hlR : Rs.length = Wc.length := by simp [hRs, peRs]
  have hP0 : T.σ1 m h P ≠ 0 :=
    σ_prodD_ne_zero (GPoly.mul O) [O.one] (T.σ1 m h) (T.σ1_mul m h) (T.σ1_one m h) _ hRs2
  have hsum := sum_cross (GPoly.mul O) [O.one] (T.σ1 m h) (T.σ1_mul m h) (T.σ1_one m h) Rs
    ((List.range Wc.length).map fun i ↦ algebraMap Kc (T.F (m + 1)) (c i)) hRs2
  have hRsv : ∀ i < Wc.length, T.σ1 m h (Rs.getD i ([], [])).1 / T.σ1 m h (Rs.getD i ([], [])).2 =
      T.σ1 m h Q * (T.M1 m h).sem (Wc.getD i O'.zero) := by
    intro i hi
    have hRi : Rs.getD i ([], []) = cleanG O (O'.mul (Q, [O.one]) (Wc.getD i O'.zero)) := by
      simp only [List.getD_eq_getElem?_getD, hRs, peRs, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
      rfl
    rw [hRi, ← T.sem1, T.sem1_cleanG, hmul, hQv]
  have hRHS : ∑ i ∈ Finset.range Wc.length, T.phi m (C (algebraMap Kc (T.F m) (c i))) *
      T.phi m (GPoly.toPoly (T.Mm m h) ((peCs O F Rs).getD i [])) =
      T.σ1 m h F.2 * T.σ1 m h P * (T.σ1 m h Q * ∑ i ∈ Finset.range Wc.length,
        algebraMap Kc (T.F (m + 1)) (c i) * (T.M1 m h).sem (Wc.getD i O'.zero)) := by
    have e1 : ∀ i ∈ Finset.range Wc.length, T.phi m (C (algebraMap Kc (T.F m) (c i))) *
        T.phi m (GPoly.toPoly (T.Mm m h) ((peCs O F Rs).getD i [])) =
        T.σ1 m h F.2 * (algebraMap Kc (T.F (m + 1)) (c i) *
          T.σ1 m h ((cross (GPoly.mul O) [O.one] Rs).getD i [])) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [← T.algebraMap_succ, peCs, NestTower.getD_map' _ _ [] [] (by
        rw [length_cross, hlR]; exact hi'), GPoly.toPoly_mul, map_mul]
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (c i) *
        T.σ1 m h ((cross (GPoly.mul O) [O.one] Rs).getD i []) =
        (List.zipWith (fun c y ↦ c * T.σ1 m h y) ((List.range Wc.length).map fun i ↦
          algebraMap Kc (T.F (m + 1)) (c i)) (cross (GPoly.mul O) [O.one] Rs)).sum := by
      rw [NestTower.zipWith_sum_range _ 0 [] _ _ (by rw [length_cross, hlR]; simp)]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi)]
    have e3 : (List.zipWith (fun c p ↦ c * (T.σ1 m h p.1 / T.σ1 m h p.2)) ((List.range Wc.length).map
        fun i ↦ algebraMap Kc (T.F (m + 1)) (c i)) Rs).sum =
        T.σ1 m h Q * ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (c i) *
          (T.M1 m h).sem (Wc.getD i O'.zero) := by
      rw [NestTower.zipWith_sum_range _ 0 ([], []) _ _ (by rw [hlR]; simp), Finset.mul_sum]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi), hRsv i (Finset.mem_range.mp hi)]
      ring
    rw [e2, hsum, e3]
    ring
  have hA' : T.phi m (GPoly.toPoly (T.Mm m h) (peA O F Rs)) = T.σ1 m h F.2 * T.σ1 m h P :=
    T.σ1_mul m h _ _
  have hB' : T.phi m (GPoly.toPoly (T.Mm m h) (peB O F Rs)) = T.σ1 m h F.1 * T.σ1 m h P :=
    T.σ1_mul m h _ _
  simp only [map_sub, map_add, map_mul, map_sum]
  rw [hA', hB', ← T.deriv_phi_exp m h, hRHS, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  have hF1 : T.σ1 m h F.1 = (((T.M1 m h).sem hc)′ - (T.σ1 m h Q)′ / T.σ1 m h Q) * T.σ1 m h F.2 := by
    rw [← hsF]; field_simp
  rw [hF1]
  field_simp
  ring

end Identity

/-- A relation of the constant system on polynomials over `1`, as a polynomial identity. -/
lemma consys_poly_rel (m : ℕ) (h : T.Tr (m + 1)) (vs : List (Code (m + 2))) (N : ℕ)
    (g : ℕ → GPoly (Code (m + 1))) (hlen : vs.length = N)
    (hvs : ∀ l < N, vs.getD l (opsM (expK as) (m + 1)).zero =
      ((g l, [(opsM (expK as) m).one]) : Code (m + 2)))
    (u : CPoly ℚ) (hu : u ∈ consys (expK as) (m + 1) vs) :
    ∑ l ∈ Finset.range N, C ((u.getD l 0 : ℚ) : T.F m) * GPoly.toPoly (T.Mm m h) (g l) = 0 := by
  have hs := T.consys_sound (m + 1) h _ u hu
  rw [NestTower.zipWith_sum_range _ 0 (opsM (expK as) (m + 1)).zero _ _ (by simp)] at hs
  apply T.phi_injective' m h
  rw [map_zero, ← hs, map_sum]
  simp only [List.length_map, List.length_range]
  rw [hlen]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := Finset.mem_range.mp hl
  have hq : algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc (u.getD l 0)) =
      T.phi m (C ((u.getD l 0 : ℚ) : T.F m)) := by
    rw [eq_ratCast (algebraMap ℚ Kc), map_ratCast, T.phi_C, map_ratCast]
  rw [NestTower.getD_range_map _ _ (by simpa [hlen] using hl'), hq, hvs l hl', map_mul]
  congr 1
  change _ = T.σ1 m h _ / T.σ1 m h [(opsM (expK as) m).one]
  rw [T.σ1_one, div_one]

section Sound

variable (m : ℕ) (h : T.Tr (m + 1))

lemma toPoly_peQ (kap : ℕ) (D : GPoly (Code (m + 1))) :
    GPoly.toPoly (T.Mm m h) (peQ (opsM (expK as) m) kap D) = X ^ kap * GPoly.toPoly (T.Mm m h) D := by
  rw [peQ, GPoly.toPoly_append, List.length_replicate]
  have : GPoly.toPoly (T.Mm m h) (List.replicate kap (opsM (expK as) m).zero) = 0 := by
    induction kap with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, GPoly.toPoly_cons, ih, (T.Mm m h).sem_zero]; simp
  rw [this, zero_add]

/-- The normal part of the common denominator: non-zero, `t`-free, a multiple of every normal
denominator. -/
lemma peE_spec (Wc : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1))))
    (hWc : ∀ q ∈ Wc, GPoly.toPoly (T.Mm m h) q.2 ≠ 0) :
    GPoly.toPoly (T.Mm m h) (peE (opsM (expK as) m) Wc) ≠ 0 ∧
      (∀ q ∈ Wc, GPoly.toPoly (T.Mm m h) (q.2.drop (lowZ (opsM (expK as) m) q.2)) ∣
        GPoly.toPoly (T.Mm m h) (peE (opsM (expK as) m) Wc)) := by
  have hne : ∀ p ∈ Wc.map fun q ↦ q.2.drop (lowZ (opsM (expK as) m) q.2),
      GPoly.toPoly (T.Mm m h) p ≠ 0 := fun p hp ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    intro h0
    apply hWc q hq
    rw [toPoly_lowZ (T.Mm m h) q.2, h0, mul_zero]
  obtain ⟨hdvd, hne0, -⟩ := GPolyLcm.lcmList_spec (T.Mm m h) _ hne
  exact ⟨hne0, fun q hq ↦ hdvd _ (List.mem_map.mpr ⟨q, hq, rfl⟩)⟩

/-- The normal denominator bound: non-zero and monic. -/
lemma peD_spec (e : GPoly (Code (m + 1))) (he : GPoly.toPoly (T.Mm m h) e ≠ 0) :
    GPoly.toPoly (T.Mm m h) (peD (opsM (expK as) m) (as m) e) ≠ 0 ∧
      (GPoly.toPoly (T.Mm m h) (peD (opsM (expK as) m) (as m) e)).Monic := by
  set g := (GPoly.egcd (opsM (expK as) m) e (GPoly.derivT (opsM (expK as) m)
    (peW (opsM (expK as) m) (as m)) e)).1 with hg
  have hge : GPoly.toPoly (T.Mm m h) g ∣ GPoly.toPoly (T.Mm m h) e := (GPoly.egcd_dvd _ _ _).1
  have hg0 : GPoly.toPoly (T.Mm m h) g ≠ 0 := fun h0 ↦ he (zero_dvd_iff.mp (h0 ▸ hge))
  obtain ⟨h1, h2⟩ := toPoly_monicG (T.Mm m h) g hg0
  refine ⟨h2.ne_zero, h2⟩

/-- **Soundness of `prdeExp`**: every returned pair solves the Risch equation (whatever the
one-level-down solver). -/
theorem prdeExp_sound (lower : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hcode : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (W : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))) :
    ∀ r ∈ prdeExp (expK as) m (as m) lower hcode W,
      ((T.M1 m h).sem r.2)′ + ((T.M1 m h).sem hcode)′ * (T.M1 m h).sem r.2 =
        sQ (T.M1 m h) r.1 W := by
  intro r hr
  obtain ⟨kap, Bs, u, hu, rfl⟩ := prdeExp_mem (expK as) m (as m) lower hcode W r hr
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = W.map (cleanG (opsM (expK as) m)) := ⟨_, rfl⟩
  obtain ⟨hcl, hhcl⟩ : ∃ hcl, hcl = cleanG (opsM (expK as) m) hcode := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = peD (opsM (expK as) m) (as m) (peE (opsM (expK as) m) Wc) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = peQ (opsM (expK as) m) kap D := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = peF (opsM (expK as) m) (as m) hcl Q := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = peRs (opsM (expK as) m) (as m) Wc Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = peA (opsM (expK as) m) F Rs := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = peB (opsM (expK as) m) F Rs := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = peCs (opsM (expK as) m) F Rs := ⟨_, rfl⟩
  rw [← hWc, ← hhcl, ← hD, ← hQ, ← hF, ← hRs, ← hA, ← hB, ← hCs] at hu
  rw [← hWc, ← hD, ← hQ]
  have hWc0 : ∀ q ∈ Wc, GPoly.toPoly (T.Mm m h) q.2 ≠ 0 := fun q hq ↦ by
    rw [hWc] at hq
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hq
    have := T.σ1_cleanG_ne m h v
    intro h0
    exact this (by rw [σ1, h0, map_zero])
  obtain ⟨he0, -⟩ := T.peE_spec m h Wc hWc0
  obtain ⟨hD0, -⟩ := T.peD_spec m h _ he0
  rw [← hD] at hD0
  have hQ0 : T.σ1 m h Q ≠ 0 := by
    rw [σ1, hQ, T.toPoly_peQ, map_ne_zero_iff _ (T.phi_injective' m h)]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hD0
  set β := (List.range Bs.length).map (u.getD · 0) with hβ
  have hβD : ∀ l < Bs.length, β.getD l 0 = u.getD l 0 := fun l hl ↦
    NestTower.getD_range_map _ _ hl
  have hqK : ∀ q : ℚ, algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc q) = (q : T.F (m + 1)) :=
    fun q ↦ by rw [← map_ratCast (algebraMap Kc (T.F (m + 1))), ← map_ratCast (algebraMap ℚ Kc)]; rfl
  have hqK' : ∀ q : ℚ, algebraMap Kc (T.F m) (algebraMap ℚ Kc q) = (q : T.F m) :=
    fun q ↦ by rw [← map_ratCast (algebraMap Kc (T.F m)), ← map_ratCast (algebraMap ℚ Kc)]; rfl
  have hphiq : ∀ q : ℚ, T.phi m (C (q : T.F m)) = (q : T.F (m + 1)) := fun q ↦ by
    rw [T.phi_C]; exact map_ratCast _ q
  have hw := T.toPoly_peW m h
  have hcst : ∀ q, (T.Mm m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
  -- the constant system gives `∑ uₗ resₗ = 0`
  have hres0 : ∑ l ∈ Finset.range Bs.length, C ((u.getD l 0 : ℚ) : T.F m) *
      resQ (T.Mm m h) (T.bE m h) A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2) = 0 := by
    have := T.consys_poly_rel m h _ Bs.length
      (fun l ↦ residE (opsM (expK as) m) (cstN m) (peW (opsM (expK as) m) (as m)) A B Cs
        (Bs.getD l ([], []))) (List.length_map _) (fun l hl ↦
          NestTower.getD_map' _ _ ([], []) _ hl) u hu
    rw [← this]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [toPoly_residE (T.bE m h) A B Cs hcst (peW (opsM (expK as) m) (as m)) hw]
  -- the polynomial equation
  set c := vcomb Wc.length β (Bs.map Prod.fst) with hcdef
  set Y := GPoly.toPoly (T.Mm m h) (lcombGP (opsM (expK as) m) (cstN m) β (Bs.map Prod.snd)) with hY
  have hYs : Y = ∑ l ∈ Finset.range Bs.length, C ((β.getD l 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2 := by
    rw [hY, toPoly_lcombGP (T.Mm m h) (cstN m) hcst,
      zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦
        C (q : T.F m) * GPoly.toPoly (T.Mm m h) p) 0 [] (by simp), List.length_map]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl)]
  have hlCs : Cs.length = Wc.length := by simp [hCs, peCs, length_cross, hRs, peRs]
  have hpoly : resQ (T.Mm m h) (T.bE m h) A B Cs c Y = 0 := by
    have := resQ_comb (M := T.Mm m h) (T.bE m h) A B Cs Bs β 0
    rw [add_zero, ← hYs, hlCs, ← hcdef] at this
    rw [this, show Lop (T.Mm m h) (T.bE m h) A B 0 = 0 by simp [Lop, Dz], add_zero, ← hres0]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hβD l (Finset.mem_range.mp hl)]
  -- the identity
  have hid := T.pe_identity m h hcl Wc Q hQ0 Y (fun i ↦ algebraMap ℚ Kc (c.getD i 0))
  rw [← hF, ← hRs, ← hA, ← hB, ← hCs] at hid
  have hlhs : GPoly.toPoly (T.Mm m h) A * implicitDeriv (C (T.bE m h) * X) Y +
      GPoly.toPoly (T.Mm m h) B * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (algebraMap ℚ Kc (c.getD i 0))) *
        GPoly.toPoly (T.Mm m h) (Cs.getD i []) = 0 := by
    have h' := hpoly
    unfold resQ at h'
    rw [hlCs] at h'
    have hs2 : ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (algebraMap ℚ Kc (c.getD i 0))) *
        GPoly.toPoly (T.Mm m h) (Cs.getD i []) = ∑ i ∈ Finset.range Wc.length,
          C ((c.getD i 0 : ℚ) : T.F m) * GPoly.toPoly (T.Mm m h) (Cs.getD i []) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hqK']
    rw [hs2]
    exact h'
  rw [hlhs, map_zero] at hid
  have hne : T.σ1 m h F.2 * T.σ1 m h (prodD (GPoly.mul (opsM (expK as) m)) [(opsM (expK as) m).one] Rs) * T.σ1 m h Q ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by rw [hF]; exact T.σ1_cleanG_ne m h _) ?_) hQ0
    exact σ_prodD_ne_zero (GPoly.mul (opsM (expK as) m)) [(opsM (expK as) m).one] (T.σ1 m h) (T.σ1_mul m h) (T.σ1_one m h) _
      (fun p hp ↦ by
        rw [hRs] at hp
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
        exact T.σ1_cleanG_ne m h _)
  have hbr := (mul_eq_zero.mp hid.symm).resolve_left hne
  -- the goal
  have hsol : (T.M1 m h).sem (lcombGP (opsM (expK as) m) (cstN m) β (Bs.map Prod.snd), Q) = T.phi m Y / T.σ1 m h Q :=
    T.sem1 m h _
  have hhc : (T.M1 m h).sem hcode = (T.M1 m h).sem hcl := by rw [hhcl, T.sem1_cleanG]
  simp only
  rw [hsol, hhc]
  unfold sQ
  have e : ∀ i ∈ Finset.range W.length, ((c.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.M1 m h).sem (W.getD i ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero) =
      algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc (c.getD i 0)) *
        (T.M1 m h).sem (Wc.getD i ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hwc : (T.M1 m h).sem (Wc.getD i ((opsM (expK as) m).monomial
        (peW (opsM (expK as) m) (as m))).zero) = (T.M1 m h).sem (W.getD i ((opsM (expK as) m).monomial
          (peW (opsM (expK as) m) (as m))).zero) := by
      rw [hWc, NestTower.getD_map' _ _ ((opsM (expK as) m).monomial
        (peW (opsM (expK as) m) (as m))).zero _ hi', T.sem1_cleanG]
    rw [hqK, hwc]
  rw [Finset.sum_congr rfl e, show W.length = Wc.length by simp [hWc]]
  linear_combination hbr

end Sound

section Denominator

variable (m : ℕ) (h : T.Tr (m + 1))

set_option maxHeartbeats 1600000 in
/-- **The denominator bound**: every solution of `y′ + h′ y = ∑ cᵢ wᵢ` is `Y / Q`, `Q = tᵏ D`. -/
theorem pe_denominator
    (hc2 : ∀ u ∈ consys (expK as) m ((opsM (expK as) m).deriv (as m) :: dExps as m),
      u.getD 0 0 = 0)
    (hcl : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (hhcl : GPoly.toPoly (T.Mm m h) hcl.2 ≠ 0)
    (Wc : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1))))
    (hWc : ∀ q ∈ Wc, GPoly.toPoly (T.Mm m h) q.2 ≠ 0) (c : ℕ → Kc) (y : T.F (m + 1))
    (hy : y′ + ((T.M1 m h).sem hcl)′ * y = ∑ i ∈ Finset.range Wc.length,
      algebraMap Kc (T.F (m + 1)) (c i) * (T.M1 m h).sem (Wc.getD i ([], []))) :
    ∃ Yv : (T.F m)[X], y * T.σ1 m h (peQ (opsM (expK as) m)
      (peKap (expK as) m (as m) hcl (peEps (opsM (expK as) m) Wc))
        (peD (opsM (expK as) m) (as m) (peE (opsM (expK as) m) Wc))) = T.phi m Yv := by
  classical
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  obtain ⟨e, he⟩ : ∃ e, e = peE (opsM (expK as) m) Wc := ⟨_, rfl⟩
  obtain ⟨he0, hediv⟩ := T.peE_spec m h Wc hWc
  rw [← he] at he0 hediv
  obtain ⟨g, hg⟩ : ∃ g, g = (GPoly.egcd (opsM (expK as) m) e (GPoly.derivT (opsM (expK as) m)
    (peW (opsM (expK as) m) (as m)) e)).1 := ⟨_, rfl⟩
  have hge : GPoly.toPoly (T.Mm m h) g ∣ GPoly.toPoly (T.Mm m h) e := by
    rw [hg]; exact (GPoly.egcd_dvd _ _ _).1
  have hg0 : GPoly.toPoly (T.Mm m h) g ≠ 0 := fun h0 ↦ he0 (zero_dvd_iff.mp (h0 ▸ hge))
  obtain ⟨D, hD⟩ : ∃ D, D = peD (opsM (expK as) m) (as m) e := ⟨_, rfl⟩
  have hDg : GPoly.toPoly (T.Mm m h) D =
      C (GPoly.toPoly (T.Mm m h) g).leadingCoeff⁻¹ * GPoly.toPoly (T.Mm m h) g := by
    rw [hD, peD, ← hg]; exact (toPoly_monicG (T.Mm m h) g hg0).1
  obtain ⟨s1, t1, hbezout⟩ : ∃ s1 t1 : (T.F m)[X], s1 * GPoly.toPoly (T.Mm m h) e +
      t1 * implicitDeriv (C (T.bE m h) * X) (GPoly.toPoly (T.Mm m h) e) =
        GPoly.toPoly (T.Mm m h) g := by
    have := GPoly.egcd_spec (T.Mm m h) e (GPoly.derivT (opsM (expK as) m)
      (peW (opsM (expK as) m) (as m)) e)
    rw [GPoly.toPoly_derivT, T.toPoly_peW m h] at this
    exact ⟨_, _, hg ▸ this⟩
  obtain ⟨kap, hkap⟩ : ∃ kap, kap = peKap (expK as) m (as m) hcl (peEps (opsM (expK as) m) Wc) :=
    ⟨_, rfl⟩
  rw [← he, ← hD, ← hkap]
  -- the setting `K = F m (t)`
  set t := T.ts m with ht
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
    algebraMap_adjoinSimple _
  have hDe : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.bE m h) * X) P := fun P ↦ by
    change implicitDeriv (T.wPoly m) P = _
    rw [T.wPoly_eq_bE m h]
  set φK := algebraMap (T.F m)[X] (T.F m)⟮t⟯ with hφK
  have hinj : Function.Injective φK := IsFractionRing.injective _ _
  -- the transfer `F (m + 1) → K`
  let toK : T.F (m + 1) → (T.F m)⟮t⟯ := fun z ↦ ⟨(z : E), (T.mem_F_succ).mp z.2⟩
  have htoK_phi : ∀ P, toK (T.phi m P) = φK P := fun P ↦ Subtype.ext (by
    change ((T.phi m P : T.F (m + 1)) : E) = _
    rw [T.coe_phi, hφK, hcoe])
  have htoK_inj : ∀ a b, toK a = toK b → a = b := fun a b hab ↦
    Subtype.ext (congrArg Subtype.val hab)
  have hsemK : ∀ q : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
      toK ((T.M1 m h).sem q) = φK (GPoly.toPoly (T.Mm m h) q.1) / φK (GPoly.toPoly (T.Mm m h) q.2) :=
    fun q ↦ Subtype.ext (by
      change (((T.σ1 m h q.1 / T.σ1 m h q.2 : T.F (m + 1))) : E) = _
      rw [IntermediateField.coe_div, IntermediateField.coe_div, T.coe_phi, T.coe_phi, hcoe, hcoe])
  -- the equation in `K`
  set yK := toK y with hyK
  set hK := toK ((T.M1 m h).sem hcl) with hhK
  set gK := toK (∑ i ∈ Finset.range Wc.length,
    algebraMap Kc (T.F (m + 1)) (c i) * (T.M1 m h).sem (Wc.getD i ([], []))) with hgK
  have hrde : yK′ + hK′ * yK = gK := Subtype.ext (by
    change ((y′ + ((T.M1 m h).sem hcl)′ * y : T.F (m + 1)) : E) = _
    rw [hy])
  have hgK : gK = ∑ i ∈ Finset.range Wc.length, φK (C (algebraMap Kc (T.F m) (c i))) *
      (φK (GPoly.toPoly (T.Mm m h) (Wc.getD i ([], [])).1) /
        φK (GPoly.toPoly (T.Mm m h) (Wc.getD i ([], [])).2)) := by
    apply Subtype.ext
    change ((∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (c i) *
      (T.M1 m h).sem (Wc.getD i ([], [])) : T.F (m + 1)) : E) = _
    rw [AddSubmonoidClass.coe_finset_sum, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, hcoe, aeval_C]
    congr 1
  -- the weights
  have hWi : ∀ i < Wc.length, ∃ (dd qq : (T.F m)[X]) (s : ℕ),
      GPoly.toPoly (T.Mm m h) (Wc.getD i ([], [])).2 = X ^ s * dd ∧ dd ≠ 0 ∧ ¬X ∣ dd ∧
      GPoly.toPoly (T.Mm m h) e = dd * qq := by
    intro i hi
    have hmem : Wc.getD i ([], []) ∈ Wc := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    have hq0 := hWc _ hmem
    obtain ⟨qq, hqq⟩ := hediv _ hmem
    refine ⟨_, qq, _, toPoly_lowZ (T.Mm m h) _, fun h0 ↦ hq0 ?_,
      not_X_dvd_drop_lowZ (T.Mm m h) _ hq0, hqq⟩
    rw [toPoly_lowZ (T.Mm m h), h0, mul_zero]
  -- normal primes
  have hnormal : ∀ (p : (T.F m)[X]) (_ : p.Monic) (hp : Irreducible p), ¬X ∣ p →
      yK * φK (GPoly.toPoly (T.Mm m h) D) ∈ regularAt (T.F m)⟮t⟯ p hp.prime := by
    intro p _ hp hXp
    have hnorm : ¬p ∣ p′ := T.normal_exp m htr rfl p hp hXp
    have hpX : ¬p ∣ X := fun hdvd ↦ hXp (hp.dvd_symm irreducible_X hdvd)
    have hgreg : gK * φK (GPoly.toPoly (T.Mm m h) e) ∈ regularAt (T.F m)⟮t⟯ p hp.prime := by
      rw [hgK, Finset.sum_mul]
      refine Subring.sum_mem _ fun i hi ↦ ?_
      obtain ⟨dd, qq, s, hds, hdd0, -, heq⟩ := hWi i (Finset.mem_range.mp hi)
      rw [mul_assoc]
      refine mul_mem (algebraMap_mem_regularAt _ _) ?_
      have hφ : φK (X ^ s * dd) ≠ 0 := (map_ne_zero_iff _ hinj).mpr
        (mul_ne_zero (pow_ne_zero _ X_ne_zero) hdd0)
      have e1 : φK (GPoly.toPoly (T.Mm m h) (Wc.getD i ([], [])).1) /
          φK (GPoly.toPoly (T.Mm m h) (Wc.getD i ([], [])).2) * φK (GPoly.toPoly (T.Mm m h) e) =
          φK (GPoly.toPoly (T.Mm m h) (Wc.getD i ([], [])).1 * qq) / φK (X ^ s) := by
        rw [hds, heq, map_mul, map_mul, map_mul]
        have hφX : φK (X ^ s) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
        have hφd : φK dd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hdd0
        field_simp
      rw [e1]
      have hφX : φK (X ^ s) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
      exact ⟨GPoly.toPoly (T.Mm m h) (Wc.getD i ([], [])).1 * qq, X ^ s,
        fun hdvd ↦ hpX (hp.prime.dvd_of_dvd_pow hdvd), div_mul_cancel₀ _ hφX⟩
    have hek0 : GPoly.toPoly (T.Mm m h) e ≠ 0 := he0
    obtain ⟨j, e1, he1, hej⟩ := exists_pow_mul_not_dvd hp.prime hek0
    have hunit : IsUnitAt (T.F m)⟮t⟯ p (φK e1) :=
      ⟨e1, 1, he1, hp.prime.not_dvd_one, by simp [hφK]⟩
    have hgj : gK * φK p ^ j ∈ regularAt (T.F m)⟮t⟯ p hp.prime := by
      have h1 := mul_mem hgreg (hunit.inv_mem_regularAt hp.prime)
      have hne : φK e1 ≠ 0 := map_ne_zero_of_not_dvd hp.prime he1
      rw [hej, map_mul, map_pow] at h1
      rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hne, mul_one] at h1
    cases j with
    | zero =>
      have := rde_pole_bound hp.prime hnorm (not_dvd_natCast_polynomial hp.prime) hK yK gK 0
        (by
          rw [zero_add, pow_one]
          have h2 := mul_mem hgj (algebraMap_mem_regularAt hp.prime p)
          rwa [pow_zero, mul_one] at h2) hrde
      rw [pow_zero, mul_one] at this
      exact mul_mem this (algebraMap_mem_regularAt _ _)
    | succ E =>
      have hyE := rde_pole_bound hp.prime hnorm (not_dvd_natCast_polynomial hp.prime) hK yK gK E hgj
        hrde
      have hpe : p ^ E ∣ GPoly.toPoly (T.Mm m h) e := ⟨p * e1, by rw [hej]; ring⟩
      have hpe' : p ^ E ∣ implicitDeriv (C (T.bE m h) * X) (GPoly.toPoly (T.Mm m h) e) := by
        rw [hej]
        exact pow_dvd_derivation_pow_mul ((implicitDeriv (C (T.bE m h) * X)).restrictScalars ℤ)
          p e1 E
      have hpD : p ^ E ∣ GPoly.toPoly (T.Mm m h) D := by
        rw [hDg]
        refine dvd_mul_of_dvd_right ?_ _
        exact hbezout ▸ dvd_add (dvd_mul_of_dvd_right hpe _) (dvd_mul_of_dvd_right hpe' _)
      obtain ⟨q, hq⟩ := hpD
      rw [hq, map_mul, map_pow, ← mul_assoc]
      exact mul_mem hyE (algebraMap_mem_regularAt _ _)
  -- the special prime `t`
  have hbE : T.bE m h = (T.valN m (as m))′ := by rw [bE, T.sem_MP_F]
  have hhomZ : ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + (j : T.F m) * T.bE m h * e ≠ 0 :=
    fun j hj e he ↦ by rw [hbE]; exact T.no_hom_exp_int m hm hc2 j hj e he
  obtain ⟨eps, heps⟩ : ∃ eps, eps = peEps (opsM (expK as) m) Wc := ⟨_, rfl⟩
  rw [← heps] at hkap
  have hgX : gK * φK (X ^ eps) ∈ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X := by
    rw [hgK, Finset.sum_mul]
    refine Subring.sum_mem _ fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [mul_assoc]
    refine mul_mem (algebraMap_mem_regularAt _ _) ?_
    have hmem : Wc.getD i ([], []) ∈ Wc := by
      rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem _
    set q := Wc.getD i ([], []) with hqd
    by_cases hz : GPoly.isZero (opsM (expK as) m) q.1 = true
    · rw [(GPoly.isZero_iff (T.Mm m h) _).mp hz, map_zero, zero_div, zero_mul]; exact zero_mem _
    · have hle := peEps_ge (opsM (expK as) m) Wc q hmem (by simpa using hz)
      rw [← heps] at hle
      have hq2 := hWc q hmem
      have hu := toPoly_lowZ (T.Mm m h) q.1
      have hs := toPoly_lowZ (T.Mm m h) q.2
      have hXd := not_X_dvd_drop_lowZ (T.Mm m h) q.2 hq2
      set u := lowZ (opsM (expK as) m) q.1
      set v := lowZ (opsM (expK as) m) q.2
      set n' := GPoly.toPoly (T.Mm m h) (q.1.drop u)
      set d := GPoly.toPoly (T.Mm m h) (q.2.drop v)
      have hd0 : d ≠ 0 := fun h0 ↦ hq2 (by rw [hs, h0, mul_zero])
      have hφd : φK d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
      have hφX : ∀ k, φK (X ^ k) ≠ 0 := fun k ↦
        (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
      refine ⟨X ^ (u + eps - v) * n', d, hXd, ?_⟩
      rw [hu, hs, map_mul, map_mul, map_mul]
      have hpow : (X : (T.F m)[X]) ^ (u + eps) = X ^ (u + eps - v) * X ^ v := by
        rw [← pow_add]; congr 1; omega
      have h1 : φK (X ^ u) * φK (X ^ eps) = φK (X ^ (u + eps - v)) * φK (X ^ v) := by
        rw [← map_mul, ← map_mul, ← pow_add, hpow]
      simp only [← hφK]
      have hv0 := hφX v
      field_simp
      linear_combination φK n' * h1
  -- the three cases for `h` at `t`
  have hhn := toPoly_lowZ (T.Mm m h) hcl.1
  have hhd := toPoly_lowZ (T.Mm m h) hcl.2
  have hXd := not_X_dvd_drop_lowZ (T.Mm m h) hcl.2 hhcl
  obtain ⟨u, hu⟩ : ∃ u, u = lowZ (opsM (expK as) m) hcl.1 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = lowZ (opsM (expK as) m) hcl.2 := ⟨_, rfl⟩
  obtain ⟨n', hn'⟩ : ∃ n', n' = GPoly.toPoly (T.Mm m h) (hcl.1.drop u) := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d', d' = GPoly.toPoly (T.Mm m h) (hcl.2.drop v) := ⟨_, rfl⟩
  rw [← hu, ← hn'] at hhn
  rw [← hv, ← hd'] at hhd hXd
  have hd'0 : d' ≠ 0 := fun h0 ↦ hhcl (by rw [hhd, h0, mul_zero])
  have hφd' : φK d' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd'0
  have hφXk : ∀ k, φK (X ^ k) ≠ 0 := fun k ↦
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hKv : hK = φK (X ^ u * n') / φK (X ^ v * d') := by rw [hhK, hsemK, ← hhn, ← hhd]
  have hspecial : yK * φK (X ^ kap) ∈ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X := by
    by_cases hz : GPoly.isZero (opsM (expK as) m) hcl.1 = true
    · -- `h = 0`
      have hkap' : kap = eps := by rw [hkap]; simp only [peKap, hz, ↓reduceIte]
      have hK0 : hK = φK (C 0) + φK X * 0 := by
        rw [hhK, hsemK, (GPoly.isZero_iff (T.Mm m h) _).mp hz]; simp
      rw [hkap']
      refine rde_special_bound_reg hDe hK yK gK eps eps le_rfl hgX 0 0 (zero_mem _) hK0
        (fun k hk e he ↦ ?_) hrde
      have := hhomZ (-(k : ℤ)) (by omega) e he
      intro h0
      apply this
      rw [Derivation.map_zero] at h0
      push_cast
      linear_combination h0
    · by_cases hlt : lowZ (opsM (expK as) m) hcl.1 < lowZ (opsM (expK as) m) hcl.2
      · -- `h` has a pole at `t`
        have hkap' : kap = eps := by
          rw [hkap]; simp only [peKap, hz, hlt, Bool.false_eq_true, ↓reduceIte]
        rw [← hu, ← hv] at hlt
        have hn'0 : ¬X ∣ n' := by
          rw [hn', hu]
          refine not_X_dvd_drop_lowZ (T.Mm m h) hcl.1 fun h0 ↦ hz ?_
          exact (GPoly.isZero_iff (T.Mm m h) _).mpr h0
        have hKnot : hK ∉ regularAt (T.F m)⟮t⟯ (X : (T.F m)[X]) prime_X := by
          rintro ⟨a, b', hb', heq⟩
          rw [hKv] at heq
          simp only [← hφK] at heq
          have hne : φK (X ^ v * d') ≠ 0 := by
            rw [map_mul]; exact mul_ne_zero (hφXk v) hφd'
          have hx : X ^ u * n' * b' = a * (X ^ v * d') := by
            apply hinj
            field_simp at heq
            simp only [map_mul] at heq ⊢
            linear_combination heq
          obtain ⟨w, rfl⟩ : ∃ w, v = u + (w + 1) := ⟨v - u - 1, by omega⟩
          have hx' : n' * b' = X * (X ^ w * a * d') := by
            apply mul_left_cancel₀ (pow_ne_zero u (X_ne_zero : (X : (T.F m)[X]) ≠ 0))
            rw [← mul_assoc, hx]
            ring
          rcases (prime_X (R := T.F m)).dvd_or_dvd ⟨_, hx'⟩ with h1 | h1
          · exact hn'0 h1
          · exact hb' h1
        rw [hkap']
        refine rde_special_bound_pole hDe (fun l hl e he h0 ↦ ?_) hK yK gK eps hgX hKnot hrde
        have := hhomZ (-(l : ℤ)) (by omega) e he
        apply this
        push_cast
        linear_combination h0
      · -- `h` is regular at `t`
        push_neg at hlt
        rw [← hu, ← hv] at hlt
        obtain ⟨w, rfl⟩ : ∃ w, u = v + w := ⟨u - v, by omega⟩
        set h0 := (T.Mm m h).sem (peH0 (opsM (expK as) m) hcl) with hh0
        have hcn : (GPoly.toPoly (T.Mm m h) hcl.1).coeff v =
            (T.Mm m h).sem (hcl.1.getD v (opsM (expK as) m).zero) := coeff_toPoly_getD' _ _ _
        have hcd : (GPoly.toPoly (T.Mm m h) hcl.2).coeff v =
            (T.Mm m h).sem (hcl.2.getD v (opsM (expK as) m).zero) := coeff_toPoly_getD' _ _ _
        rw [hhn] at hcn
        rw [hhd] at hcd
        have hd0' : d'.coeff 0 ≠ 0 := fun h0 ↦ hXd (X_dvd_iff.mpr h0)
        have c1 : (X ^ (v + w) * n').coeff v = (X ^ w * n').coeff 0 := by
          rw [pow_add, mul_assoc, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
        have c2 : (X ^ v * d').coeff v = d'.coeff 0 := by
          rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
        have hh0v : h0 * d'.coeff 0 = (X ^ w * n').coeff 0 := by
          rw [hh0, peH0, (T.Mm m h).sem_mul, (T.Mm m h).sem_inv, ← hv, ← hcn, ← hcd, c1, c2]
          field_simp
        obtain ⟨q, hq⟩ : X ∣ X ^ w * n' - C h0 * d' := by
          rw [X_dvd_iff, coeff_sub, coeff_C_mul, hh0v, sub_self]
        have hKr : hK = φK (C h0) + φK X * (φK q / φK d') := by
          rw [hKv]
          have e1 : X ^ (v + w) * n' = X ^ v * (C h0 * d' + X * q) := by
            rw [← hq, pow_add]; ring
          rw [e1, map_mul, map_mul, map_add, map_mul, map_mul]
          have := hφXk v
          field_simp
        have hlt' : ¬lowZ (opsM (expK as) m) hcl.1 < lowZ (opsM (expK as) m) hcl.2 := by
          rw [← hu, ← hv]; omega
        refine rde_special_bound_reg hDe hK yK gK eps kap (by
          rw [hkap]
          simp only [peKap, hz, hlt', Bool.false_eq_true, ↓reduceIte]
          split <;> simp) hgX h0 _ ⟨q, d', hXd, div_mul_cancel₀ _ hφd'⟩ hKr
          (fun k hk e he h00 ↦ ?_) hrde
        -- a solution would contradict the bound `κ`
        have hlog : (evN Kc T.x T.ts m ((opsM (expK as) m).neg (peH0 (opsM (expK as) m) hcl)) +
            ((k : ℤ) : E) * T.aE m)′ = logDeriv ((e : T.F m) : E) := by
          have hEe : ((e : T.F m) : E) ≠ 0 := fun h1 ↦ he (Subtype.ext h1)
          have hsemV : evN Kc T.x T.ts m ((opsM (expK as) m).neg (peH0 (opsM (expK as) m) hcl)) =
              -((h0 : T.F m) : E) := by
            rw [← T.sem_MP m hm, (T.MP m hm).sem_neg]
            rfl
          have hb : (T.aE m)′ = ((T.bE m h : T.F m) : E) := by
            rw [bE, coe_deriv, T.sem_MP]
          have := congrArg Subtype.val h00
          simp only [IntermediateField.coe_add, IntermediateField.coe_mul, coe_deriv,
            AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero] at this
          rw [hsemV, map_add, Derivation.leibniz, hb]
          unfold logDeriv
          rw [show ((((k : ℤ) : E))′) = 0 by simpa using T.deriv_ratCast_E (k : ℚ)]
          simp only [smul_eq_mul, mul_zero, add_zero, map_neg]
          field_simp
          push_cast at this ⊢
          linear_combination -this
        have hp := T.pld_spec m hm hc2 _ k _ (e.2) (fun h1 ↦ he (Subtype.ext h1)) hlog
        have hk' : k ≤ kap := by
          rw [hkap]
          simp only [peKap, hz, hlt', Bool.false_eq_true, ↓reduceIte]
          rw [hp]
          simp [natOfQ]
        omega
  -- the combination
  have hreg : ∀ (p : (T.F m)[X]) (_ : p.Monic) (hp : Irreducible p),
      yK * φK (GPoly.toPoly (T.Mm m h) (peQ (opsM (expK as) m) kap D)) ∈
        regularAt (T.F m)⟮t⟯ p hp.prime := by
    intro p hpm hp
    rw [T.toPoly_peQ, map_mul]
    by_cases hXp : X ∣ p
    · have hpX : p = X := eq_of_monic_of_associated hpm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp)
      subst hpX
      rw [← mul_assoc]
      exact mul_mem hspecial (algebraMap_mem_regularAt _ _)
    · rw [mul_comm (φK _), ← mul_assoc]
      exact mul_mem (hnormal p hpm hp hXp) (algebraMap_mem_regularAt _ _)
  obtain ⟨Yv, hYv⟩ := exists_polynomial_of_regularAt _ hreg
  refine ⟨Yv, htoK_inj _ _ ?_⟩
  change yK * toK (T.phi m (GPoly.toPoly (T.Mm m h) (peQ (opsM (expK as) m) kap D))) =
    toK (T.phi m Yv)
  rw [htoK_phi, htoK_phi]
  exact hYv

end Denominator

end NestMTower

end Tower.NestM
