import RischTragerBronstein.Computable.NestXRdeSpec

/-!
# The parametric Risch equation over `ℚ(x)` in mixed towers: soundness and completeness

`prde0X ks fr W` returns a basis of the pairs `(c, y)` with `y′ + f y = ∑ cᵢ wᵢ`, `y ∈ Kc(x)`, for
`f = h′ + ∑ cⱼ vⱼ′ / vⱼ` (constant `cⱼ`):

* soundness: the null-space relation is the polynomial equation `A Y′ + B Y = ∑ eᵢ Cᵢ`, which is
  the Risch equation for `Y / D` times the non-zero factor `F₂ P D` (`prde0X_identity`);
* completeness: every solution has denominator dividing `D = gcd(e, e′) · Lᴺ`
  (`rde_log_denominator` at every prime, the positive integer residues being bounded by
  `logBound0` through `ratVal`), numerator of degree at most the bound, hence is a constant
  combination of the null-space basis.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly

/-! ### The data of `prde0BF` -/

def p0FX (fc : GFrac ℚ) (D : CPoly ℚ) : GFrac ℚ :=
  cleanQ ((ops₁g ℚ).add fc ((ops₁g ℚ).neg ((ops₁g ℚ).mul
    ((ops₁g ℚ).deriv (p0Dc D)) ((ops₁g ℚ).inv (p0Dc D)))))
def p0AX (fc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : CPoly ℚ :=
  CPoly.mul (p0FX fc D).2 (p0P Wc D)
def p0BX (fc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : CPoly ℚ :=
  CPoly.mul (p0FX fc D).1 (p0P Wc D)
def p0CsX (fc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : List (CPoly ℚ) :=
  (cross CPoly.mul [1] (p0Rs Wc D)).map (CPoly.mul (p0FX fc D).2)

/-- The factor of `L` contributed by a logarithm. -/
def facX0 (cw : GFrac ℚ × GFrac ℚ) : CPoly ℚ :=
  CPoly.mul (if CPoly.isZero cw.2.1 then [1] else cw.2.1) (if CPoly.isZero cw.2.2 then [1] else cw.2.2)

/-- `L`, the product of the non-zero numerators and denominators of the logarithms. -/
def logLX0 (logs : List (GFrac ℚ × GFrac ℚ)) : CPoly ℚ :=
  logs.foldr (fun cw acc ↦ CPoly.mul (facX0 cw) acc) [1]

lemma toPoly_facX0_ne (cw : GFrac ℚ × GFrac ℚ) : CPoly.toPoly (facX0 cw) ≠ 0 := by
  unfold facX0
  rw [CPoly.toPoly_mul]
  refine mul_ne_zero ?_ ?_ <;> split_ifs with hz
  · simp [CPoly.toPoly]
  · rwa [Ne, ← CPoly.isZero_iff]
  · simp [CPoly.toPoly]
  · rwa [Ne, ← CPoly.isZero_iff]

lemma toPoly_logLX0_ne : ∀ logs : List (GFrac ℚ × GFrac ℚ), CPoly.toPoly (logLX0 logs) ≠ 0
  | [] => by simp [logLX0, CPoly.toPoly]
  | cw :: l => by
    rw [logLX0, List.foldr_cons, CPoly.toPoly_mul]
    exact mul_ne_zero (toPoly_facX0_ne cw) (toPoly_logLX0_ne l)

lemma facX0_dvd : ∀ (logs : List (GFrac ℚ × GFrac ℚ)) (i : ℕ), i < logs.length →
    CPoly.toPoly (facX0 (logs.getD i (([], [1]), ([], [1])))) ∣ CPoly.toPoly (logLX0 logs)
  | [], i, hi => by simp at hi
  | cw :: l, 0, _ => by
    rw [logLX0, List.foldr_cons, CPoly.toPoly_mul]
    exact dvd_mul_right _ _
  | cw :: l, i + 1, hi => by
    rw [logLX0, List.foldr_cons, CPoly.toPoly_mul, List.getD_cons_succ]
    exact dvd_mul_of_dvd_right (facX0_dvd l i (by simpa using hi)) _

lemma toPoly_foldr_pow (L : CPoly ℚ) : ∀ l : List ℕ,
    CPoly.toPoly (l.foldr (fun _ acc ↦ CPoly.mul L acc) [1]) = CPoly.toPoly L ^ l.length
  | [] => by simp [CPoly.toPoly]
  | a :: l => by
    rw [List.foldr_cons, CPoly.toPoly_mul, toPoly_foldr_pow L l, List.length_cons, pow_succ]
    ring

lemma prde0X_eq (ks : (m : ℕ) → KindN m) (fr : FRep (GFrac ℚ)) (W : List (GFrac ℚ)) :
    prde0X ks fr W =
      let D := CPoly.mul (CPoly.egcd (((W.map cleanQ).foldr (fun w acc ↦ lcmQ w.2 acc) [1]))
        (CPoly.deriv ((W.map cleanQ).foldr (fun w acc ↦ lcmQ w.2 acc) [1]))).1
        ((List.range (logBound0 ks fr.logs)).foldr (fun _ acc ↦ CPoly.mul (logLX0 fr.logs) acc) [1])
      if CPoly.isZero D then [] else prde0BF (fCode (ops₁g ℚ) fr) (W.map cleanQ) D := rfl

lemma prde0BF_eq (fc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) :
    prde0BF fc Wc D = (nullBasis ((p0CsX fc Wc D).map CPoly.neg ++
      (List.range (degBoundU (p0AX fc Wc D) (p0BX fc Wc D)
        (((p0CsX fc Wc D).map cdeg).foldr max 0) + 1)).map
        (colY (p0AX fc Wc D) (p0BX fc Wc D)))).map fun u ↦
      ((List.range Wc.length).map (u.getD · 0),
        (((List.range (degBoundU (p0AX fc Wc D) (p0BX fc Wc D)
          (((p0CsX fc Wc D).map cdeg).foldr max 0) + 1)).map fun k ↦ u.getD (Wc.length + k) 0),
          D)) := by
  simp only [prde0BF, List.length_map, List.length_range]
  rfl

/-- The code `∑ vⱼ cⱼ` of `logBound0`. -/
def codeX0 (ks : (m : ℕ) → KindN m) (v : List ℤ) (logs : List (GFrac ℚ × GFrac ℚ)) :
    GFrac ℚ :=
  (List.zip v logs).foldr (fun p acc2 ↦
    (ops₁g ℚ).add ((ops₁g ℚ).mul (cstN 0 ((p.1 : ℤ) : ℚ)) p.2.1) acc2) (ops₁g ℚ).zero

lemma logBound0_eq (ks : (m : ℕ) → KindN m) (logs : List (GFrac ℚ × GFrac ℚ)) :
    logBound0 ks logs = (intVecs (logs.map fun cw ↦ cdeg cw.2.1 + cdeg cw.2.2)).foldr
      (fun v acc ↦ match ratVal ks 0 (codeX0 ks v logs) with
        | some q => max acc ((natOfQ q).getD 0)
        | none => acc) 0 := rfl

lemma le_foldr_ratX0 (g : List ℤ → Option ℚ) : ∀ (l : List (List ℤ)) (v : List ℤ), v ∈ l →
    ∀ q, g v = some q → (natOfQ q).getD 0 ≤ l.foldr (fun v acc ↦ match g v with
      | some q => max acc ((natOfQ q).getD 0)
      | none => acc) 0
  | [], _, hv, _, _ => by simp at hv
  | w :: l, v, hv, q, hq => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · rw [hq]; exact le_max_right _ _
    · have := le_foldr_ratX0 g l v hv q hq
      split
      · exact this.trans (le_max_left _ _)
      · exact this

lemma list_sum_map_getDX0 {γ M : Type*} [AddCommMonoid M] (f : γ → M) (d : γ) : ∀ l : List γ,
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, list_sum_map_getDX0 f d l, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

/-- **The identity behind `prde0BF`**: the polynomial equation is the Risch equation for
`Y / D` times the non-zero factor `F₂ P D`. -/
lemma prde0X_identity (h0 : T.Tr 0) (fc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ)
    (hσD : T.σ0 D ≠ 0) (Y : Kc[X]) (c : ℕ → Kc) :
    T.phi0 ((CPoly.toPoly (p0AX fc Wc D)).map (algebraMap ℚ Kc) * derivative Y +
      (CPoly.toPoly (p0BX fc Wc D)).map (algebraMap ℚ Kc) * Y -
      ∑ i ∈ Finset.range Wc.length, C (c i) *
        (CPoly.toPoly ((p0CsX fc Wc D).getD i [])).map (algebraMap ℚ Kc)) =
    T.σ0 (p0FX fc D).2 * T.σ0 (p0P Wc D) * T.σ0 D *
      ((T.phi0 Y / T.σ0 D)′ + (T.M0 h0).sem fc * (T.phi0 Y / T.σ0 D) -
        ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c i) *
          (T.M0 h0).sem (Wc.getD i (ops₁g ℚ).zero)) := by
  set M := T.M0 h0 with hM
  set fv := M.sem fc with hfv
  have hadd : ∀ a b, M.sem ((ops₁g ℚ).add a b) = M.sem a + M.sem b := M.sem_add
  have hneg : ∀ a, M.sem ((ops₁g ℚ).neg a) = -M.sem a := M.sem_neg
  have hmul : ∀ a b, M.sem ((ops₁g ℚ).mul a b) = M.sem a * M.sem b := M.sem_mul
  have hinv : ∀ a, M.sem ((ops₁g ℚ).inv a) = (M.sem a)⁻¹ := M.sem_inv
  have hder : ∀ a, M.sem ((ops₁g ℚ).deriv a) = (M.sem a)′ := M.sem_deriv
  have hDcv : M.sem (p0Dc D) = T.σ0 D := by rw [T.sem0' h0, p0Dc]; simp [T.σ0_one]
  have hsF : T.σ0 (p0FX fc D).1 / T.σ0 (p0FX fc D).2 = fv - (T.σ0 D)′ / T.σ0 D := by
    rw [← T.sem0' h0, p0FX, T.sem0_cleanQ' h0, hadd, hneg, hmul, hder, hinv, hDcv]
    ring
  have hF2 : T.σ0 (p0FX fc D).2 ≠ 0 := T.σ0_cleanQ_ne _
  have hRs2 : ∀ p ∈ p0Rs Wc D, T.σ0 p.2 ≠ 0 := fun p hp ↦ by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σ0_cleanQ_ne _
  have hlR : (p0Rs Wc D).length = Wc.length := by simp [p0Rs]
  have hP0 : T.σ0 (p0P Wc D) ≠ 0 :=
    σ_prodD_ne_zero CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one _ hRs2
  have hsum := sum_cross CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one (p0Rs Wc D)
    ((List.range Wc.length).map fun i ↦ algebraMap Kc (T.F 0) (c i)) hRs2
  have hRsv : ∀ i < Wc.length, T.σ0 ((p0Rs Wc D).getD i ([], [])).1 /
      T.σ0 ((p0Rs Wc D).getD i ([], [])).2 = T.σ0 D * M.sem (Wc.getD i (ops₁g ℚ).zero) := by
    intro i hi
    have hRi : (p0Rs Wc D).getD i ([], []) =
        cleanQ ((ops₁g ℚ).mul (p0Dc D) (Wc.getD i (ops₁g ℚ).zero)) := by
      simp only [List.getD_eq_getElem?_getD, p0Rs, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    rw [hRi, ← T.sem0' h0, T.sem0_cleanQ' h0, hmul, hDcv]
  have hRHS : ∑ i ∈ Finset.range Wc.length, T.phi0 (C (c i)) *
      T.phi0 ((CPoly.toPoly ((p0CsX fc Wc D).getD i [])).map (algebraMap ℚ Kc)) =
      T.σ0 (p0FX fc D).2 * T.σ0 (p0P Wc D) * (T.σ0 D * ∑ i ∈ Finset.range Wc.length,
        algebraMap Kc (T.F 0) (c i) * M.sem (Wc.getD i (ops₁g ℚ).zero)) := by
    have e1 : ∀ i ∈ Finset.range Wc.length, T.phi0 (C (c i)) *
        T.phi0 ((CPoly.toPoly ((p0CsX fc Wc D).getD i [])).map (algebraMap ℚ Kc)) =
        T.σ0 (p0FX fc D).2 * (algebraMap Kc (T.F 0) (c i) *
          T.σ0 ((cross CPoly.mul [1] (p0Rs Wc D)).getD i [])) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [T.phi0_C, p0CsX, NestTower.getD_map' _ _ [] [] (by rw [length_cross, hlR]; exact hi')]
      change _ * T.σ0 (CPoly.mul (p0FX fc D).2 _) = _
      rw [T.σ0_mul]
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c i) *
        T.σ0 ((cross CPoly.mul [1] (p0Rs Wc D)).getD i []) =
        (List.zipWith (fun c y ↦ c * T.σ0 y) ((List.range Wc.length).map fun i ↦
          algebraMap Kc (T.F 0) (c i)) (cross CPoly.mul [1] (p0Rs Wc D))).sum := by
      rw [NestTower.zipWith_sum_range _ 0 [] _ _ (by rw [length_cross, hlR]; simp)]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi)]
    have e3 : (List.zipWith (fun c p ↦ c * (T.σ0 p.1 / T.σ0 p.2)) ((List.range Wc.length).map
        fun i ↦ algebraMap Kc (T.F 0) (c i)) (p0Rs Wc D)).sum =
        T.σ0 D * ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c i) *
          M.sem (Wc.getD i (ops₁g ℚ).zero) := by
      rw [NestTower.zipWith_sum_range _ 0 ([], []) _ _ (by rw [hlR]; simp), Finset.mul_sum]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi), hRsv i (Finset.mem_range.mp hi)]
      ring
    rw [e2, hsum, e3]
    change T.σ0 (p0FX fc D).2 * (_ * T.σ0 (p0P Wc D)) = _
    ring
  have hA' : T.phi0 ((CPoly.toPoly (p0AX fc Wc D)).map (algebraMap ℚ Kc)) =
      T.σ0 (p0FX fc D).2 * T.σ0 (p0P Wc D) := T.σ0_mul _ _
  have hB' : T.phi0 ((CPoly.toPoly (p0BX fc Wc D)).map (algebraMap ℚ Kc)) =
      T.σ0 (p0FX fc D).1 * T.σ0 (p0P Wc D) := T.σ0_mul _ _
  have hY' : T.phi0 (derivative Y) = (T.phi0 Y)′ := by
    rw [T.deriv_phi0, implicitDeriv_one_of_trivial T.hC]
  simp only [map_sub, map_add, map_mul, map_sum]
  rw [hA', hB', hY', hRHS, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  have hF1 : T.σ0 (p0FX fc D).1 = (fv - (T.σ0 D)′ / T.σ0 D) * T.σ0 (p0FX fc D).2 := by
    rw [← hsF]; field_simp
  rw [hF1]
  field_simp
  ring

/-- **Soundness of `prde0BF`** (for any `D` with non-zero value). -/
theorem prde0BF_sound (h0 : T.Tr 0) (fc : GFrac ℚ) (W : List (GFrac ℚ)) (D : CPoly ℚ)
    (hσD : T.σ0 D ≠ 0) :
    ∀ r ∈ prde0BF fc (W.map cleanQ) D, ((T.M0 h0).sem r.2)′ + (T.M0 h0).sem fc * (T.M0 h0).sem r.2 =
      sQ (T.M0 h0) r.1 W := by
  intro r hr
  set M := T.M0 h0 with hM
  set aq := algebraMap ℚ Kc with haq
  set Wc := W.map cleanQ with hWc
  set A := p0AX fc Wc D with hA
  set B := p0BX fc Wc D with hB
  set Cs := p0CsX fc Wc D with hCs
  set NN := degBoundU A B ((Cs.map cdeg).foldr max 0) + 1 with hNN
  set ys := (List.range NN).map (colY A B) with hys
  rw [prde0BF_eq] at hr
  obtain ⟨u, hu, hru⟩ := List.mem_map.mp hr
  have hlW : Wc.length = W.length := by simp [hWc]
  have hlen : Cs.length = Wc.length := by simp [hCs, p0CsX, length_cross, p0Rs]
  have hlys : ys.length = NN := by simp [hys]
  have hysD : ∀ k < ys.length, ys.getD k [] = colY A B k := by
    intro k hk
    rw [hys] at hk ⊢
    exact NestTower.getD_range_map _ _ (by simpa using hk)
  have hrel := prde0B_rel Cs ys A B hysD u (nullBasis_sound _ u hu)
  rw [hlen, hlys] at hrel
  set Yq := ∑ k ∈ Finset.range NN, Polynomial.C (u.getD (Wc.length + k) 0) * X ^ k with hYq
  set Yk := Yq.map aq with hYk
  have hrelK := congrArg (Polynomial.map aq) hrel
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_C] at hrelK
  have hid := T.prde0X_identity h0 fc Wc D hσD Yk (fun i ↦ aq (u.getD i 0))
  rw [← hA, ← hB, ← hCs] at hid
  have hz : (CPoly.toPoly A).map aq * derivative Yk + (CPoly.toPoly B).map aq * Yk -
      ∑ i ∈ Finset.range Wc.length, C (aq (u.getD i 0)) *
        (CPoly.toPoly (Cs.getD i [])).map aq = 0 := by
    rw [hYk, derivative_map]; linear_combination hrelK
  rw [hz, map_zero] at hid
  have hRs2 : ∀ p ∈ p0Rs Wc D, T.σ0 p.2 ≠ 0 := fun p hp ↦ by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σ0_cleanQ_ne _
  have hne : T.σ0 (p0FX fc D).2 * T.σ0 (p0P Wc D) * T.σ0 D ≠ 0 :=
    mul_ne_zero (mul_ne_zero (T.σ0_cleanQ_ne _)
      (σ_prodD_ne_zero CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one _ hRs2)) hσD
  have hbr := (mul_eq_zero.mp hid.symm).resolve_left hne
  have hL : T.σ0 ((List.range NN).map fun k ↦ u.getD (Wc.length + k) 0) = T.phi0 Yk := by
    rw [σ0, toPoly_range_map]
  have hsol : M.sem r.2 = T.phi0 Yk / T.σ0 D := by
    rw [← hru]
    exact (T.sem0' h0 _).trans (congrArg (· / T.σ0 D) hL)
  rw [hsol]
  unfold sQ
  have hr1 : r.1 = (List.range Wc.length).map fun x ↦ u.getD x 0 := by rw [← hru]
  rw [hr1, ← hlW]
  have e4 : ∀ i ∈ Finset.range Wc.length,
      ((((List.range Wc.length).map fun x ↦ u.getD x 0).getD i 0 : ℚ) : T.F 0) *
        M.sem (W.getD i (ops₁g ℚ).zero) =
      algebraMap Kc (T.F 0) (aq (u.getD i 0)) * M.sem (Wc.getD i (ops₁g ℚ).zero) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hwc : M.sem (Wc.getD i (ops₁g ℚ).zero) = M.sem (W.getD i (ops₁g ℚ).zero) := by
      rw [hWc, NestTower.getD_map' _ _ (ops₁g ℚ).zero _ (by simpa [hWc] using hi'),
        T.sem0_cleanQ' h0]
    rw [NestTower.getD_range_map _ _ hi', hwc, haq, eq_ratCast (algebraMap ℚ Kc),
      map_ratCast]
  rw [Finset.sum_congr rfl e4]
  linear_combination hbr

set_option maxHeartbeats 1600000 in
/-- **Completeness of `prde0BF`**, given that the solution has denominator dividing `D`. -/
theorem prde0BF_complete (h0 : T.Tr 0) (fc : GFrac ℚ) (W : List (GFrac ℚ)) (D : CPoly ℚ)
    (hσD : T.σ0 D ≠ 0) (c : List Kc)
    (hcl : ∀ i, W.length ≤ i → c.getD i 0 = 0) (y : T.F 0)
    (hy : y′ + (T.M0 h0).sem fc * y = sC (algebraMap Kc (T.F 0)) (T.M0 h0) c W)
    (Yv : Kc[X]) (hyY : y = T.phi0 Yv / T.σ0 D) :
    ∃ β : List Kc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (prde0BF fc (W.map cleanQ) D).length,
        β.getD k 0 * algebraMap ℚ Kc
          (((prde0BF fc (W.map cleanQ) D).getD k ([], (ops₁g ℚ).zero)).1.getD i 0)) ∧
      y = ∑ k ∈ Finset.range (prde0BF fc (W.map cleanQ) D).length,
        algebraMap Kc (T.F 0) (β.getD k 0) *
          (T.M0 h0).sem ((prde0BF fc (W.map cleanQ) D).getD k ([], (ops₁g ℚ).zero)).2 := by
  classical
  set M := T.M0 h0 with hM
  set fv := M.sem fc with hfv
  set ι := algebraMap Kc (T.F 0) with hι
  set aq := algebraMap ℚ Kc with haq
  have hsem : ∀ q : GFrac ℚ, M.sem q = T.σ0 q.1 / T.σ0 q.2 := T.sem0 h0
  have hsemc : ∀ q : GFrac ℚ, M.sem (cleanQ q) = M.sem q := T.sem0_cleanQ h0
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = W.map cleanQ := ⟨_, rfl⟩
  rw [← hWc]
  have hlW : Wc.length = W.length := by simp [hWc]
  obtain ⟨g, hg⟩ : ∃ g, g = sC ι M c W := ⟨_, rfl⟩
  -- the polynomial equation
  set A := p0AX fc Wc D with hA
  set B := p0BX fc Wc D with hB
  set Cs := p0CsX fc Wc D with hCs
  set a := (CPoly.toPoly A).map aq with ha
  set b := (CPoly.toPoly B).map aq with hb
  set r := ∑ i ∈ Finset.range Wc.length, C (c.getD i 0) * (CPoly.toPoly (Cs.getD i [])).map aq
    with hr
  have hlCs : Cs.length = Wc.length := by simp [hCs, p0CsX, length_cross, p0Rs]
  have hpoly : a * derivative Yv + b * Yv = r := by
    have hid := T.prde0X_identity h0 fc Wc D hσD Yv (fun i ↦ c.getD i 0)
    have hsum0 : ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c.getD i 0) *
        M.sem (Wc.getD i (ops₁g ℚ).zero) = g := by
      rw [hg, hlW]
      unfold sC
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := Finset.mem_range.mp hi
      congr 1
      rw [hWc, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, hsemc,
        List.getD_eq_getElem _ _ hi']
    rw [hsum0, ← hyY] at hid
    have hz : y′ + fv * y - g = 0 := by rw [hg]; rw [hy]; ring
    rw [hz, mul_zero] at hid
    have := T.phi0_injective (hid.trans (map_zero _).symm)
    rw [hlCs.symm] at this
    rw [hr, ← hlCs]
    linear_combination this
  -- the degree bound
  set R := (Cs.map cdeg).foldr max 0 with hR
  have hcdeg : ∀ p : CPoly ℚ, (CPoly.toPoly p).natDegree ≤ cdeg p := fun p ↦ by
    by_cases h : CPoly.trim p = []
    · rw [(CPoly.trim_eq_nil_iff p).mp h]; simp
    · rw [(natDegree_toPoly_of_trim_ne_nil h).1]; rfl
  have hrdeg : r.natDegree ≤ R := by
    rw [hr]
    refine (natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_map]
    have hi' := Finset.mem_range.mp hi
    refine (hcdeg _).trans (le_foldr_max _ _ (List.mem_map.mpr ⟨_, ?_, rfl⟩))
    rw [List.getD_eq_getElem _ _ (by rw [hlCs]; exact hi')]
    exact List.getElem_mem _
  have hA0 : CPoly.toPoly A ≠ 0 := by
    rw [hA, p0AX, CPoly.toPoly_mul]
    refine mul_ne_zero (cleanQ_den_ne' _) ?_
    intro h0
    have := T.σ_prodD_ne_zero' (p0Rs Wc D) (fun p hp ↦ by
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
      exact T.σ0_cleanQ_ne _)
    exact this (by rw [σ0, ← p0P, h0]; simp)
  have hlead : ∀ p : CPoly ℚ, CPoly.toPoly p ≠ 0 →
      ((CPoly.toPoly p).map aq).leadingCoeff = aq (clead p) ∧
        ((CPoly.toPoly p).map aq).natDegree = cdeg p := fun p hp ↦ by
    refine ⟨by rw [leadingCoeff_map, CPoly.leadingCoeff_toPoly hp]; rfl, ?_⟩
    rw [natDegree_map]
    have hne : CPoly.trim p ≠ [] := fun h ↦ hp ((CPoly.trim_eq_nil_iff p).mp h)
    rw [(natDegree_toPoly_of_trim_ne_nil hne).1]; rfl
  set N := degBoundU A B R with hN
  have hqq : b ≠ 0 → b.natDegree + 1 = a.natDegree → ∀ N' : ℕ,
      (N' : Kc) * a.leadingCoeff + b.leadingCoeff = 0 →
      N' ≤ (if !CPoly.isZero B && decide (cdeg B + 1 = cdeg A) then
        ((natOfQ (-(clead B / clead A))).getD 0) else 0) := by
    intro hb0 hdb N' hN'
    have hB0 : CPoly.toPoly B ≠ 0 := fun h0 ↦ hb0 (by rw [hb, h0, Polynomial.map_zero])
    obtain ⟨hla, hda⟩ := hlead A hA0
    obtain ⟨hlb, hdb'⟩ := hlead B hB0
    rw [hla, hlb] at hN'
    rw [hda, hdb'] at hdb
    have hq : ((N' : ℚ)) = -(clead B / clead A) := by
      have hca : aq (clead A) ≠ 0 := by
        rw [← hla]
        exact leadingCoeff_ne_zero.mpr ((Polynomial.map_ne_zero_iff aq.injective).mpr hA0)
      have hca' : clead A ≠ 0 := fun h ↦ hca (by rw [h, map_zero])
      apply aq.injective
      rw [map_natCast, map_neg, map_div₀]
      field_simp
      linear_combination hN'
    have hBz : CPoly.isZero B = false := by
      rw [Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact hB0
    simp only [hBz, Bool.not_false, Bool.true_and, decide_eq_true_eq, hdb, if_true]
    rw [← hq, natOfQ]
    simp
  have hdeg : Yv.natDegree ≤ N :=
    natDegree_le_of_rde0 a b Yv r R _ hrdeg ((Polynomial.map_ne_zero_iff aq.injective).mpr hA0)
      hpoly hqq
  -- the relation over `Kc`
  set ys := (List.range (N + 1)).map (colY A B) with hys
  set cols := Cs.map CPoly.neg ++ ys with hcols
  set n := Wc.length with hn
  have hYsum : Yv = ∑ k ∈ Finset.range (N + 1), C (Yv.coeff k) * X ^ k := by
    ext j
    rw [finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hj
    · rfl
    · exact coeff_eq_zero_of_natDegree_lt (by simp at hj; omega)
  set cv := (List.range n).map (fun i ↦ c.getD i 0) ++ (List.range (N + 1)).map Yv.coeff with hcv
  have hlcols : cols.length = n + (N + 1) := by simp [hcols, hys, hlCs, hn]
  have hlcv : cv.length = cols.length := by rw [hlcols]; simp [hcv]
  have h0 : lcombS aq cv cols = 0 := by
    rw [lcombS, NestTower.zipWith_sum_range _ 0 [] _ _ hlcv, hlcv, hlcols, Finset.sum_range_add]
    have e1 : ∀ i ∈ Finset.range n, C (cv.getD i 0) * (CPoly.toPoly (cols.getD i [])).map aq =
        -(C (c.getD i 0) * (CPoly.toPoly (Cs.getD i [])).map aq) := fun i hi ↦ by
      have hi' := Finset.mem_range.mp hi
      rw [hcv, List.getD_append _ _ _ _ (by simpa using hi'), NestTower.getD_range_map _ _ hi',
        hcols, List.getD_append _ _ _ _ (by simpa [hlCs] using hi'),
        NestTower.getD_map' _ _ [] [] (by rw [hlCs]; exact hi'), CPoly.toPoly_neg,
        Polynomial.map_neg]
      ring
    have e2 : ∀ k ∈ Finset.range (N + 1), C (cv.getD (n + k) 0) *
        (CPoly.toPoly (cols.getD (n + k) [])).map aq =
        a * derivative (C (Yv.coeff k) * X ^ k) + b * (C (Yv.coeff k) * X ^ k) := fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      rw [hcv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, NestTower.getD_range_map _ _ hk', hcols,
        List.getD_append_right _ _ _ _ (by simp [hlCs]), List.length_map, hlCs,
        Nat.add_sub_cancel_left, hys, NestTower.getD_range_map _ _ hk', colY, CPoly.toPoly_add,
        CPoly.toPoly_mul, CPoly.toPoly_mul, CPoly.toPoly_deriv, CPoly.toPoly_monomial]
      simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map, Polynomial.map_C,
        map_one, one_mul, Polynomial.map_pow, map_X, derivative_C_mul, ha, hb]
      rw [← derivative_map, Polynomial.map_pow, map_X]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← derivative_sum, ← hYsum,
      hpoly, hr]
    ring
  obtain ⟨β, hβ⟩ := nullBasis_coeffs cols cv hlcv h0
  set NB := nullBasis cols with hNB
  have hout2 : prde0BF fc Wc D = NB.map fun u ↦ ((List.range n).map (u.getD · 0),
      (((List.range ys.length).map fun k ↦ u.getD (n + k) 0), D)) := by
    rw [prde0BF_eq]
    simp only [List.length_map, List.length_range, hys, hNB, hcols, hn, hN, hR, hA, hB, hCs]
  rw [hout2]
  have hget : ∀ k < NB.length, (NB.map fun u ↦ ((List.range n).map (u.getD · 0),
      (((List.range ys.length).map fun k ↦ u.getD (n + k) 0), D))).getD k ([], (ops₁g ℚ).zero) =
      ((List.range n).map ((NB.getD k []).getD · 0),
        (((List.range ys.length).map fun j ↦ (NB.getD k []).getD (n + j) 0), D)) :=
    fun k hk ↦ NestTower.getD_map' _ _ [] _ hk
  refine ⟨β, fun i ↦ ?_, ?_⟩
  · rw [List.length_map]
    have e : ∀ k ∈ Finset.range NB.length, β.getD k 0 * aq (((NB.map fun u ↦
        ((List.range n).map (u.getD · 0), (((List.range ys.length).map fun k ↦ u.getD (n + k) 0),
          D))).getD k ([], (ops₁g ℚ).zero)).1.getD i 0) =
        β.getD k 0 * aq (if i < n then (NB.getD k []).getD i 0 else 0) := fun k hk ↦ by
      rw [hget k (Finset.mem_range.mp hk)]
      dsimp only
      split_ifs with hi
      · rw [NestTower.getD_range_map _ _ hi]
      · rw [List.getD_eq_default ((List.range n).map ((NB.getD k []).getD · 0)) 0
          (by rw [List.length_map, List.length_range]; omega)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · simp only [if_pos hi]
      rw [← hβ i, hcv, List.getD_append _ _ _ _ (by simpa using hi), NestTower.getD_range_map _ _ hi]
    · simp only [if_neg hi, map_zero, mul_zero, Finset.sum_const_zero]
      exact hcl i (by rw [← hlW]; omega)
  · rw [List.length_map, hyY]
    have e : ∀ k ∈ Finset.range NB.length, ι (β.getD k 0) * M.sem ((NB.map fun u ↦
        ((List.range n).map (u.getD · 0), (((List.range ys.length).map fun k ↦ u.getD (n + k) 0),
          D))).getD k ([], (ops₁g ℚ).zero)).2 =
        ι (β.getD k 0) * T.phi0 (∑ j ∈ Finset.range (N + 1),
          C (aq ((NB.getD k []).getD (n + j) 0)) * X ^ j) / T.σ0 D := fun k hk ↦ by
      rw [hget k (Finset.mem_range.mp hk), hsem]
      dsimp only
      rw [σ0, toPoly_range_map, hys, List.length_map, List.length_range]
      simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        map_X]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.sum_div]
    congr 1
    rw [hYsum, map_sum]
    simp only [map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hYj : Yv.coeff j = cv.getD (n + j) 0 := by
      rw [hcv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, NestTower.getD_range_map _ _ (Finset.mem_range.mp hj)]
    rw [hYj, hβ, map_mul, T.phi0_C, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [map_mul, T.phi0_C, hι]
    ring

lemma sem_codeX0 (h0 : T.Tr 0) : ∀ (logs : List (GFrac ℚ × GFrac ℚ)) (v : List ℤ),
    v.length = logs.length →
    (T.M0 h0).sem (codeX0 ks v logs) = ∑ i ∈ Finset.range logs.length,
      ((v.getD i 0 : ℤ) : T.F 0) * (T.M0 h0).sem (logs.getD i (([], [1]), ([], [1]))).1
  | [], v, hv => by
    rw [List.length_nil, List.length_eq_zero_iff] at hv
    subst hv
    simp [codeX0, (T.M0 h0).sem_zero]
  | cw :: l, v, hv => by
    obtain ⟨x, v', rfl⟩ : ∃ x v', v = x :: v' := by
      cases v with
      | nil => simp at hv
      | cons x v' => exact ⟨x, v', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hv
    have ih := sem_codeX0 h0 l v' hv
    have e : codeX0 ks (x :: v') (cw :: l) =
        (ops₁g ℚ).add ((ops₁g ℚ).mul (cstN 0 ((x : ℤ) : ℚ)) cw.1) (codeX0 ks v' l) := rfl
    have hc : (T.M0 h0).sem (cstN 0 ((x : ℤ) : ℚ)) = (((x : ℤ) : ℚ) : T.F 0) := T.sem_cstN 0 h0 _
    have hm : (T.M0 h0).sem ((ops₁g ℚ).mul (cstN 0 ((x : ℤ) : ℚ)) cw.1) =
        (((x : ℤ) : ℚ) : T.F 0) * (T.M0 h0).sem cw.1 := by
      rw [← hc]; exact (T.M0 h0).sem_mul _ _
    rw [e, (T.M0 h0).sem_add, hm, ih, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    ring

set_option maxHeartbeats 3200000 in
/-- **Completeness of `prde0X`**. -/
theorem prde0X_complete (h0 : T.Tr 0) (fr : FRep (GFrac ℚ)) (hok : FRepOK (T.M0 h0) fr)
    (W : List (GFrac ℚ)) (c : List Kc) (hcl : ∀ i, W.length ≤ i → c.getD i 0 = 0) (y : T.F 0)
    (hy : y′ + (T.M0 h0).sem (fCode (ops₁g ℚ) fr) * y =
      sC (algebraMap Kc (T.F 0)) (T.M0 h0) c W) :
    ∃ β : List Kc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (prde0X ks fr W).length,
        β.getD k 0 * algebraMap ℚ Kc (((prde0X ks fr W).getD k ([], (ops₁g ℚ).zero)).1.getD i 0)) ∧
      y = ∑ k ∈ Finset.range (prde0X ks fr W).length, algebraMap Kc (T.F 0) (β.getD k 0) *
        (T.M0 h0).sem ((prde0X ks fr W).getD k ([], (ops₁g ℚ).zero)).2 := by
  classical
  set M := T.M0 h0 with hM
  set ι := algebraMap Kc (T.F 0) with hι
  set aq := algebraMap ℚ Kc with haq
  set φ := algebraMap Kc[X] (T.F 0) with hφ
  have hsem : ∀ q : GFrac ℚ, M.sem q = T.σ0 q.1 / T.σ0 q.2 := T.sem0 h0
  have hsemc : ∀ q : GFrac ℚ, M.sem (cleanQ q) = M.sem q := T.sem0_cleanQ h0
  have hσφ : ∀ p : CPoly ℚ, T.σ0 p = φ ((CPoly.toPoly p).map aq) := fun p ↦ rfl
  set logs := fr.logs with hlogs
  set len := logs.length with hlen
  set d0 : GFrac ℚ × GFrac ℚ := (([], [1]), ([], [1])) with hd0
  set wi : ℕ → GFrac ℚ × GFrac ℚ := fun i ↦ logs.getD i d0 with hwi
  have hwimem : ∀ i < len, wi i ∈ logs := fun i hi ↦ by
    simp only [hwi]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  -- the constants
  have hconst : ∀ i, i < len → ∃ κ : Kc, M.sem (wi i).1 = ι κ := fun i hi ↦
    T.const_F _ (hok _ (hwimem i hi))
  choose! cK hcK using hconst
  -- the logarithms with non-zero numerator and denominator
  set s := (Finset.range len).filter
    (fun i ↦ CPoly.isZero (wi i).2.1 = false ∧ CPoly.isZero (wi i).2.2 = false) with hs
  set Nw : ℕ → Kc[X] := fun i ↦ (CPoly.toPoly (wi i).2.1).map aq with hNw
  set Dw : ℕ → Kc[X] := fun i ↦ (CPoly.toPoly (wi i).2.2).map aq with hDw
  have hnz : ∀ p : CPoly ℚ, CPoly.isZero p = false → (CPoly.toPoly p).map aq ≠ 0 := by
    intro p hp h0
    rw [Polynomial.map_eq_zero_iff aq.injective] at h0
    rw [(CPoly.isZero_iff p).mpr h0] at hp
    exact Bool.noConfusion hp
  have hND : ∀ i ∈ s, Nw i ≠ 0 ∧ Dw i ≠ 0 := fun i hi ↦ by
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hi
    exact ⟨hnz _ h1, hnz _ h2⟩
  -- the logarithmic part
  have hlog : logSumV M logs = ∑ i ∈ s, φ (C (cK i)) * logDeriv (φ (Nw i) / φ (Dw i)) := by
    unfold logSumV
    rw [list_sum_map_getDX0 _ d0, hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    change M.sem (wi i).1 * logDeriv (M.sem (wi i).2) = _
    split_ifs with hz
    · rw [hcK i hi', hsem, hσφ, hσφ, ← T.phi0_C]
      rfl
    · have hw0 : M.sem (wi i).2 = 0 := by
        rw [hsem]
        rcases not_and_or.mp hz with h1 | h1
        · rw [Bool.not_eq_false] at h1
          rw [(T.σ0_eq_zero_iff _).mpr h1, zero_div]
        · rw [Bool.not_eq_false] at h1
          rw [(T.σ0_eq_zero_iff _).mpr h1, div_zero]
      rw [hw0, logDeriv, map_zero, zero_div, mul_zero]
  -- the data of the algorithm
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = W.map cleanQ := ⟨_, rfl⟩
  have hWc0 : ∀ w ∈ Wc, CPoly.toPoly w.2 ≠ 0 := fun w hw ↦ by
    rw [hWc] at hw
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw
    exact cleanQ_den_ne' v
  obtain ⟨e, he⟩ : ∃ e, e = Wc.foldr (fun w acc ↦ lcmQ w.2 acc) [1] := ⟨_, rfl⟩
  obtain ⟨hediv, he0⟩ := lcm_fold_spec Wc hWc0
  rw [← he] at hediv he0
  obtain ⟨G, hG⟩ : ∃ G, G = (CPoly.egcd e (CPoly.deriv e)).1 := ⟨_, rfl⟩
  have hGe : CPoly.toPoly G ∣ CPoly.toPoly e := hG ▸ (CPoly.egcd_dvd e (CPoly.deriv e)).1
  have hG0 : CPoly.toPoly G ≠ 0 := fun h ↦ he0 (zero_dvd_iff.mp (h ▸ hGe))
  set N := logBound0 ks logs with hN
  set L := logLX0 logs with hL
  obtain ⟨D, hD⟩ : ∃ D, D = CPoly.mul G ((List.range N).foldr (fun _ acc ↦ CPoly.mul L acc) [1]) :=
    ⟨_, rfl⟩
  have hDpoly : CPoly.toPoly D = CPoly.toPoly G * CPoly.toPoly L ^ N := by
    rw [hD, CPoly.toPoly_mul, toPoly_foldr_pow, List.length_range]
  have hD0 : CPoly.toPoly D ≠ 0 := by
    rw [hDpoly]; exact mul_ne_zero hG0 (pow_ne_zero _ (toPoly_logLX0_ne _))
  have hDz : CPoly.isZero D = false := by
    rw [Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact hD0
  have hσD : T.σ0 D ≠ 0 := by rw [Ne, T.σ0_eq_zero_iff, hDz]; exact Bool.false_ne_true
  have hout : prde0X ks fr W = prde0BF (fCode (ops₁g ℚ) fr) (W.map cleanQ) D := by
    rw [prde0X_eq]
    simp only [← hWc, ← he, ← hG, ← hlogs, ← hL, ← hN, ← hD, hDz]
    rfl
  -- the Kc-polynomials
  obtain ⟨ek, hek⟩ : ∃ ek, ek = (CPoly.toPoly e).map aq := ⟨_, rfl⟩
  have hek0 : ek ≠ 0 := by rw [hek]; exact (Polynomial.map_ne_zero_iff aq.injective).mpr he0
  set Gk := (CPoly.toPoly G).map aq with hGk
  set Lk := (CPoly.toPoly L).map aq with hLk
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD' : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  have hbezK : (CPoly.toPoly (CPoly.egcd e (CPoly.deriv e)).2.1).map aq * ek +
      (CPoly.toPoly (CPoly.egcd e (CPoly.deriv e)).2.2).map aq * ek′ = Gk := by
    have := congrArg (Polynomial.map aq) (CPoly.egcd_spec e (CPoly.deriv e))
    simp only [Polynomial.map_add, Polynomial.map_mul, CPoly.toPoly_deriv] at this
    rw [hGk, hG, ← this, hek, hD', derivative_map]
  obtain ⟨g, hg⟩ : ∃ g, g = sC ι M c W := ⟨_, rfl⟩
  -- `g ek` has no pole
  have hgreg : ∀ (p : Kc[X]) (hp : Irreducible p), g * φ ek ∈ regularAt (T.F 0) p hp.prime := by
    intro p hp
    rw [hg]
    unfold sC
    rw [Finset.sum_mul]
    refine Subring.sum_mem _ fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    have hwi : W.getD i (ops₁g ℚ).zero ∈ W := by
      rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem _
    have hcw : cleanQ (W.getD i (ops₁g ℚ).zero) ∈ Wc := by
      rw [hWc]; exact List.mem_map.mpr ⟨_, hwi, rfl⟩
    obtain ⟨q, hq⟩ := hediv _ hcw
    rw [mul_assoc, ← hsemc, hsem]
    refine mul_mem ?_ ?_
    · rw [hι, ← T.phi0_C, T.phi0_eq_algebraMap]
      exact algebraMap_mem_regularAt _ _
    · have hden : T.σ0 (cleanQ (W.getD i (ops₁g ℚ).zero)).2 ≠ 0 := T.σ0_cleanQ_ne _
      have : T.σ0 (cleanQ (W.getD i (ops₁g ℚ).zero)).1 /
          T.σ0 (cleanQ (W.getD i (ops₁g ℚ).zero)).2 * φ ek =
          φ ((CPoly.toPoly (cleanQ (W.getD i (ops₁g ℚ).zero)).1).map aq * q.map aq) := by
        rw [hek, hq, Polynomial.map_mul, map_mul, map_mul, hσφ, hσφ]
        rw [hσφ] at hden
        field_simp
      rw [this]
      exact algebraMap_mem_regularAt _ _
  -- the equation
  have hrde : y′ + ((M.sem fr.h)′ + ∑ i ∈ s, φ (C (cK i)) * logDeriv (φ (Nw i) / φ (Dw i))) * y =
      g := by
    rw [hg, ← hy, sem_fCode, show logSumV M fr.logs = _ from hlog]
  -- the bound on the residues
  have hLdvd : ∀ i ∈ s, ∀ p : Kc[X], p ∣ Nw i * Dw i → p ∣ Lk := by
    intro i hi p hp
    obtain ⟨hi', h1, h2⟩ := Finset.mem_filter.mp hi
    have hf := facX0_dvd logs i (Finset.mem_range.mp hi')
    have hfac : facX0 (logs.getD i d0) = CPoly.mul (wi i).2.1 (wi i).2.2 := by
      simp only [facX0, hwi] at h1 h2 ⊢
      rw [h1, h2]; rfl
    rw [hfac, CPoly.toPoly_mul] at hf
    have := Polynomial.map_dvd aq hf
    rw [Polynomial.map_mul] at this
    exact hp.trans this
  have hcdeg : ∀ p : CPoly ℚ, (CPoly.toPoly p).natDegree ≤ cdeg p := fun p ↦ by
    by_cases h : CPoly.trim p = []
    · rw [(CPoly.trim_eq_nil_iff p).mp h]; simp
    · rw [(natDegree_toPoly_of_trim_ne_nil h).1]; rfl
  have hNb : ∀ (k : ℕ) (n : ℕ → ℤ), 0 < k →
      (∀ i ∈ s, |n i| ≤ (((Nw i).natDegree + (Dw i).natDegree : ℕ) : ℤ)) →
      (k : Kc) = ∑ i ∈ s, cK i * n i → k ≤ N := by
    intro k n _ hbd hkn
    set v : List ℤ := (List.range len).map fun i ↦ if i ∈ s then n i else 0 with hv
    have hvl : v.length = len := by simp [hv]
    have hvi : ∀ i < len, v.getD i 0 = if i ∈ s then n i else 0 := fun i hi ↦ by
      rw [hv]; exact NestTower.getD_range_map _ _ hi
    have hcode : (T.M0 h0).sem (codeX0 ks v logs) = ((k : ℚ) : T.F 0) := by
      rw [T.sem_codeX0 h0 logs v hvl]
      have e1 : ∀ i ∈ Finset.range len, ((v.getD i 0 : ℤ) : T.F 0) *
          (T.M0 h0).sem (logs.getD i d0).1 =
          if i ∈ s then ι (cK i * n i) else 0 := fun i hi ↦ by
        have hi' := Finset.mem_range.mp hi
        rw [hvi i hi']
        split_ifs with his
        · rw [show (T.M0 h0).sem (logs.getD i d0).1 = M.sem (wi i).1 from rfl, hcK i hi',
            map_mul, map_intCast]
          ring
        · simp
      rw [← hlen, Finset.sum_congr rfl e1, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr (Finset.filter_subset _ _), ← map_sum, ← hkn]
      simp
    have hrv := T.ratVal_spec 0 h0 (codeX0 ks v logs) (k : ℚ) hcode
    have hmem : v ∈ intVecs (logs.map fun cw ↦ cdeg cw.2.1 + cdeg cw.2.2) := by
      refine mem_intVecs _ v (by simp [hvl, hlen]) fun j hj ↦ ?_
      rw [List.length_map] at hj
      rw [hvi j hj, NestTower.getD_map' _ _ d0 0 hj]
      split_ifs with hjs
      · refine (hbd j hjs).trans ?_
        have h1 : (Nw j).natDegree ≤ cdeg (wi j).2.1 := by
          rw [hNw]; dsimp only; rw [natDegree_map]; exact hcdeg _
        have h2 : (Dw j).natDegree ≤ cdeg (wi j).2.2 := by
          rw [hDw]; dsimp only; rw [natDegree_map]; exact hcdeg _
        have : (Nw j).natDegree + (Dw j).natDegree ≤ cdeg (wi j).2.1 + cdeg (wi j).2.2 := by
          omega
        exact_mod_cast this
      · simp only [abs_zero]; positivity
    have := le_foldr_ratX0 (fun v ↦ ratVal ks 0 (codeX0 ks v logs)) _ v hmem (k : ℚ) hrv
    rw [natOfQ_natCast] at this
    rw [hN]
    exact this
  -- the denominator
  have hreg : ∀ (p : Kc[X]) (_ : p.Monic) (hp : Irreducible p),
      y * φ (Gk * Lk ^ N) ∈ regularAt (T.F 0) p hp.prime := by
    intro p _ hp
    have hnorm : ¬p ∣ p′ := fun hdvd ↦ by
      rw [hD'] at hdvd
      have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
      have hne : derivative p ≠ 0 := fun h0' ↦ hpos (derivative_eq_zero.mp h0')
      exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
    exact rde_log_denominator (F := Kc) (K := T.F 0) hp hnorm (M.sem fr.h) y g s cK Nw Dw hND
      ek hek0 (hgreg p hp) Gk _ _ hbezK Lk (fun i hi hpd ↦ hLdvd i hi p hpd) N hNb hrde
  obtain ⟨Yv, hYv⟩ := exists_polynomial_of_regularAt (y * φ (Gk * Lk ^ N)) hreg
  have hσDk : T.σ0 D = φ (Gk * Lk ^ N) := by
    rw [hσφ, hDpoly, Polynomial.map_mul, Polynomial.map_pow]
  have hyY : y = T.phi0 Yv / T.σ0 D := by
    have hne : φ (Gk * Lk ^ N) ≠ 0 := hσDk ▸ hσD
    rw [T.phi0_eq_algebraMap, ← hYv, hσDk, mul_div_cancel_right₀ _ hne]
  rw [hout]
  exact T.prde0BF_complete h0 _ W D hσD c hcl y hy Yv hyY

theorem prde0X_spec' (h0 : T.Tr 0) (fr : FRep (GFrac ℚ)) (hok : FRepOK (T.M0 h0) fr) :
    RdeSpecK (algebraMap Kc (T.F 0)) (T.M0 h0) ((T.M0 h0).sem (fCode (ops₁g ℚ) fr))
      (prde0X ks fr) := by
  refine ⟨fun W r hr ↦ ?_, fun W c hc z hz ↦ T.prde0X_complete h0 fr hok W c hc z hz⟩
  rw [prde0X_eq] at hr
  dsimp only at hr
  split_ifs at hr with hz
  · simp at hr
  · refine T.prde0BF_sound h0 _ W _ ?_ r hr
    rw [Ne, T.σ0_eq_zero_iff]; exact hz

/-- **The parametric Risch equation over `ℚ(x)` is sound and complete.** -/
theorem prde0X_spec (h0 : T.Tr 0) (fr : FRep (Code 1)) (hok : FRepOK (T.MP 0 h0) fr) :
    RdeSpecK (algebraMap Kc (T.F 0)) (T.MP 0 h0) ((T.MP 0 h0).sem (fCode (opsM ks 0) fr))
      (prde0X ks fr) :=
  T.prde0X_spec' h0 fr hok

end NestMTower

end Tower.NestM
