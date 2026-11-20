import RischTragerBronstein.Computable.EuclidDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.List.Sections

/-!
# Irreducibility over `ℚ` by Kronecker's method

`CPoly.Kron.irredQ F` certifies that a primitive integral polynomial `F ∈ ℤ[x]` (given as a list of
rationals with denominator `1`) is irreducible over `ℚ`: for every degree `1 ≤ e ≤ deg F / 2` and
`e + 1` distinct integer points `aᵢ` with `F(aᵢ) ≠ 0`, every tuple `(dᵢ)` of (signed) divisors of the
`F(aᵢ)` is interpolated (the interpolant is computed by an untrusted Lagrange formula and *checked*
at the points), and the interpolant of degree `e` does not divide `F`. A factor `G ∈ ℤ[x]` of
degree `e` would have values `G(aᵢ) ∣ F(aᵢ)` and coincide with the interpolant of its values
(`eq_of_degrees_lt_of_eval_finset_eq`); Gauss's lemma transfers irreducibility from `ℤ[x]` to
`ℚ[x]` (`irredQ_sound`). An untrusted factoriser `factorQ` uses the same search to split `F`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

namespace Kron

/-! ### Evaluation -/

section Eval

variable {R : Type*} [CommRing R]

/-- Horner evaluation. -/
def evalC (p : CPoly R) (a : R) : R := p.foldr (fun c acc ↦ c + a * acc) 0

lemma evalC_eq (p : CPoly R) (a : R) : evalC p a = (toPoly p).eval a := by
  induction p with
  | nil => simp [evalC]
  | cons c p ih =>
    simp only [evalC, List.foldr_cons] at ih ⊢
    rw [ih, toPoly_cons, eval_add, eval_mul, eval_C, eval_X]

end Eval

/-! ### The data of the search -/

/-- The signed divisors of an integer (all its divisors when it is non-zero). -/
def divsZ (v : ℤ) : List ℤ :=
  ((List.range (v.natAbs + 1)).filter fun d : ℕ ↦ decide (0 < d) && decide (d ∣ v.natAbs)).flatMap
    fun d : ℕ ↦ [Int.ofNat d, -Int.ofNat d]

lemma mem_divsZ {v d : ℤ} (hv : v ≠ 0) (hd : d ∣ v) : d ∈ divsZ v := by
  have hd0 : d ≠ 0 := fun h0 ↦ hv (zero_dvd_iff.mp (h0 ▸ hd))
  have hle : d.natAbs ≤ v.natAbs := Int.natAbs_le_of_dvd_ne_zero hd hv
  have hdn : d.natAbs ∣ v.natAbs := Int.natAbs_dvd_natAbs.mpr hd
  rw [divsZ, List.mem_flatMap]
  refine ⟨d.natAbs, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, ?_⟩
  · simp [Int.natAbs_pos.mpr hd0, hdn]
  · rcases Int.natAbs_eq d with h | h
    · rw [h]; simp
    · rw [h]; simp

/-- The first `n` candidate points `0, -1, 1, -2, 2, …`. -/
def candPts (n : ℕ) : List ℤ :=
  (List.range n).map fun i ↦ if i % 2 = 0 then ((i / 2 : ℕ) : ℤ) else -(((i + 1) / 2 : ℕ) : ℤ)

lemma candPts_nodup (n : ℕ) : (candPts n).Nodup := by
  refine List.Nodup.map_on (fun i _ j _ hij ↦ ?_) List.nodup_range
  split_ifs at hij <;> omega

/-- The first `k` candidate points where `F` does not vanish (among `length F + k` candidates,
enough since `F ≠ 0` has fewer than `length F` roots). -/
def ptsFor (F : CPoly ℚ) (k : ℕ) : List ℤ :=
  ((candPts (F.length + k)).filter fun a : ℤ ↦ evalC F (Int.cast a : ℚ) ≠ 0).take k

lemma ptsFor_nodup (F : CPoly ℚ) (k : ℕ) : (ptsFor F k).Nodup :=
  ((candPts_nodup _).filter _).sublist (List.take_sublist _ _)

lemma ptsFor_ne (F : CPoly ℚ) (k : ℕ) {a : ℤ} (ha : a ∈ ptsFor F k) :
    evalC F (Int.cast a : ℚ) ≠ 0 := by
  have := (List.take_sublist _ _).subset ha
  simpa using (List.mem_filter.mp this).2

/-- The polynomial `∏_{j ≠ i} (x - pⱼ) / (pᵢ - pⱼ)`. -/
def basisL (pts : List ℚ) (i : ℕ) : CPoly ℚ :=
  ((List.range pts.length).filter (· ≠ i)).foldr (fun j acc ↦
    mul (smul (1 / (pts.getD i 0 - pts.getD j 0)) [-(pts.getD j 0), 1]) acc) [1]

/-- The Lagrange interpolant (untrusted: its values are checked). -/
def lagr (pts vals : List ℚ) : CPoly ℚ :=
  (List.range pts.length).foldr (fun i acc ↦ add (smul (vals.getD i 0) (basisL pts i)) acc) []

/-- The degree, from the trimmed length. -/
def degC (p : CPoly ℚ) : ℕ := (trim p).length - 1

/-- Integral coefficients (a cheap filter before the division test). -/
def intC (g : CPoly ℚ) : Bool := g.all fun q ↦ q.den == 1

lemma intC_of_toPoly_eq {g : CPoly ℚ} {G : ℤ[X]} (h : toPoly g = G.map (Int.castRingHom ℚ)) :
    intC g = true := by
  simp only [intC, List.all_eq_true, beq_iff_eq]
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  have := coeff_toPoly g i
  rw [h, coeff_map, List.getD_eq_getElem _ _ hi] at this
  rw [← this]
  simp

/-- A cheap divisibility filter: an integral factor `g` of `F` has `g(b) ∣ F(b)` at integers `b`. -/
def valTest (F g : CPoly ℚ) : Bool :=
  ([2, -2, 3, -3, 4, -4] : List ℤ).all fun b ↦
    decide ((evalC g (Int.cast b : ℚ)).num ∣ (evalC F (Int.cast b : ℚ)).num)

/-- A common denominator `W` of the Lagrange basis at `pts`. -/
def lagDen (pts : List ℚ) : ℕ :=
  ((List.range pts.length).flatMap fun i ↦ basisL pts i).foldr (fun q acc ↦ Nat.lcm q.den acc) 1

/-- The scaled basis `W Bᵢ`, as integer lists. -/
def basisZ (pts : List ℚ) : List (CPoly ℤ) :=
  (List.range pts.length).map fun i ↦ (smul ((lagDen pts : ℕ) : ℚ) (basisL pts i)).map Rat.num

/-- Is the scaled basis integral (so that `basisZ` is exact)? -/
def basisOk (pts : List ℚ) : Bool :=
  (List.range pts.length).all fun i ↦ intC (smul ((lagDen pts : ℕ) : ℚ) (basisL pts i))

/-- `W · (the interpolant of ds)`, computed in integers. -/
def lagZ (BZ : List (CPoly ℤ)) (ds : List ℤ) : CPoly ℤ :=
  (List.range ds.length).foldr (fun i acc ↦ add (smul (ds.getD i 0) (BZ.getD i [])) acc) []

/-- **The integer filter** on `cZ = W g`: `W` divides every coefficient, and `g(b) ∣ F(b)` at
`b = ±2, ±3, ±4`. Every integral factor passes (`zFilter_of`). -/
def zFilter (F : CPoly ℚ) (W : ℤ) (cZ : CPoly ℤ) : Bool :=
  cZ.all (fun c ↦ c % W == 0) &&
    ([2, -2, 3, -3, 4, -4] : List ℤ).all fun b ↦
      decide (evalC cZ b / W ∣ (evalC F (Int.cast b : ℚ)).num)

/-- **No factor of degree `e`**: every interpolant of divisor values either is not of degree `e` or
does not divide `F`. Candidates failing the integer filter are discarded first. -/
def noFactor (F : CPoly ℚ) (e : ℕ) : Bool :=
  let pts := ptsFor F (e + 1)
  let ptsQ := pts.map fun a : ℤ ↦ (Int.cast a : ℚ)
  let W : ℤ := ((lagDen ptsQ : ℕ) : ℤ)
  let BZ := basisZ ptsQ
  let ok := basisOk ptsQ
  pts.length == e + 1 &&
    (List.sections (pts.map fun a : ℤ ↦ divsZ (evalC F (Int.cast a : ℚ)).num)).all fun ds ↦
      (ok && !zFilter F W (lagZ BZ ds)) ||
      let g := lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
      (List.zip pts ds).all (fun p ↦ evalC g (Int.cast p.1 : ℚ) == (Int.cast p.2 : ℚ)) &&
        decide ((trim g).length ≤ e + 1) &&
        (decide ((trim g).length ≠ e + 1) || !intC g || !valTest F g || !isZero (divMod F g).2)

/-- The gcd of a list of integers. -/
def gcdL (l : List ℤ) : ℕ := l.foldr (fun a acc ↦ Int.gcd a acc) 0

/-- **The irreducibility certificate**: `F` is integral, primitive, of positive degree, and has no
factor of degree `1 ≤ e ≤ deg F / 2`. -/
def irredQ (F : CPoly ℚ) : Bool :=
  F.all (fun q ↦ q.den == 1) && gcdL (F.map Rat.num) == 1 && decide (1 ≤ degC F) &&
    (List.range (degC F / 2)).all fun e ↦ noFactor F (e + 1)

/-! ### Soundness -/

section Sound

/-- The integral polynomial of an integral list of rationals. -/
noncomputable def polyZ (F : CPoly ℚ) : ℤ[X] := toPoly (F.map Rat.num)

lemma polyZ_map (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) :
    (polyZ F).map (Int.castRingHom ℚ) = toPoly F := by
  induction F with
  | nil => simp [polyZ]
  | cons q F ih =>
    have hq : ((q.num : ℤ) : ℚ) = q := by
      have := Rat.num_div_den q
      rw [hint q List.mem_cons_self, Nat.cast_one, div_one] at this
      exact this
    simp only [polyZ, List.map_cons, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, map_C,
      map_X, eq_intCast, Int.cast_id] at ih ⊢
    rw [ih fun r hr ↦ hint r (List.mem_cons_of_mem _ hr), Polynomial.map_intCast, ← C_eq_intCast, hq]

lemma evalC_polyZ (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) (a : ℤ) :
    evalC F (Int.cast a : ℚ) = (((polyZ F).eval a : ℤ) : ℚ) := by
  rw [evalC_eq, ← polyZ_map F hint, eval_map]
  exact Polynomial.eval₂_hom (Int.castRingHom ℚ) a

lemma num_evalC (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) (a : ℤ) :
    (evalC F (Int.cast a : ℚ)).num = (polyZ F).eval a := by
  rw [evalC_polyZ F hint, Rat.num_intCast]

/-! #### Lagrange interpolation -/

lemma toPoly_foldr_mul' {α : Type*} (f : α → CPoly ℚ) : ∀ l : List α,
    toPoly (l.foldr (fun j acc ↦ mul (f j) acc) [1]) = (l.map fun j ↦ toPoly (f j)).prod
  | [] => by simp [CPoly.toPoly]
  | a :: l => by rw [List.foldr_cons, toPoly_mul, toPoly_foldr_mul' f l, List.map_cons, List.prod_cons]

lemma toPoly_basisL (pts : List ℚ) (i : ℕ) :
    toPoly (basisL pts i) = (((List.range pts.length).filter (· ≠ i)).map fun j ↦
      C (1 / (pts.getD i 0 - pts.getD j 0)) * (X - C (pts.getD j 0))).prod := by
  unfold basisL
  rw [toPoly_foldr_mul']
  congr 1
  refine List.map_congr_left fun j _ ↦ ?_
  rw [toPoly_smul]
  simp [CPoly.toPoly]
  left; ring

lemma eval_basisL (pts : List ℚ) (hnd : pts.Nodup) (i k : ℕ) (hi : i < pts.length)
    (hk : k < pts.length) :
    (toPoly (basisL pts i)).eval (pts.getD k 0) = if k = i then 1 else 0 := by
  rw [toPoly_basisL, eval_list_prod, List.map_map]
  have hne : ∀ j < pts.length, j ≠ i → pts.getD i 0 - pts.getD j 0 ≠ 0 := by
    intro j hj hji h0
    apply hji
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h0
    exact ((List.Nodup.getElem_inj_iff hnd).mp (sub_eq_zero.mp h0)).symm
  split_ifs with hki
  · subst hki
    refine List.prod_eq_one fun v hv ↦ ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hjr, hji⟩ := List.mem_filter.mp hj
    simp only [decide_eq_true_eq] at hji
    simp only [Function.comp_apply, eval_mul, eval_C, eval_sub, eval_X]
    rw [one_div_mul_eq_div]
    exact div_self (hne j (List.mem_range.mp hjr) hji)
  · refine List.prod_eq_zero (List.mem_map.mpr ⟨k, List.mem_filter.mpr
      ⟨List.mem_range.mpr hk, by simpa using hki⟩, ?_⟩)
    simp

lemma toPoly_foldr_add {α : Type*} (v : α → ℚ) (b : α → CPoly ℚ) : ∀ l : List α,
    toPoly (l.foldr (fun i acc ↦ add (smul (v i) (b i)) acc) []) =
      (l.map fun i ↦ C (v i) * toPoly (b i)).sum
  | [] => by simp [CPoly.toPoly]
  | a :: l => by
    rw [List.foldr_cons, toPoly_add, toPoly_smul, toPoly_foldr_add v b l, List.map_cons,
      List.sum_cons]

lemma list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n : ℕ,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n,
      Finset.sum_range_succ]
    simp

lemma toPoly_lagr (pts vals : List ℚ) :
    toPoly (lagr pts vals) = ∑ i ∈ Finset.range pts.length,
      C (vals.getD i 0) * toPoly (basisL pts i) := by
  unfold lagr
  rw [toPoly_foldr_add, list_sum_range]

/-- **The interpolant interpolates.** -/
lemma eval_lagr (pts vals : List ℚ) (hnd : pts.Nodup) (k : ℕ) (hk : k < pts.length) :
    (toPoly (lagr pts vals)).eval (pts.getD k 0) = vals.getD k 0 := by
  rw [toPoly_lagr, eval_finset_sum]
  rw [Finset.sum_eq_single k]
  · rw [eval_mul, eval_C, eval_basisL pts hnd k k hk hk, if_pos rfl, mul_one]
  · intro i hi hik
    rw [eval_mul, eval_basisL pts hnd i k (Finset.mem_range.mp hi) hk, if_neg (Ne.symm hik),
      mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hk) h

lemma natDegree_basisL (pts : List ℚ) (i : ℕ) (hi : i < pts.length) :
    (toPoly (basisL pts i)).natDegree ≤ pts.length - 1 := by
  rw [toPoly_basisL]
  refine (natDegree_list_prod_le _).trans ?_
  have : ∀ v ∈ ((List.range pts.length).filter (· ≠ i)).map (fun j ↦
      C (1 / (pts.getD i 0 - pts.getD j 0)) * (X - C (pts.getD j 0))), v.natDegree ≤ 1 :=
    fun v hv ↦ by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
      exact (natDegree_C_mul_le _ _).trans (by simp)
  refine (List.sum_le_card_nsmul _ 1 ?_).trans ?_
  · intro n hn
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
    exact this v hv
  · simp only [List.length_map, smul_eq_mul, mul_one]
    have := (List.length_filter_lt_length_iff_exists (l := List.range pts.length)
      (p := fun x ↦ decide (x ≠ i))).mpr ⟨i, List.mem_range.mpr hi, by simp⟩
    rw [List.length_range] at this
    omega

lemma natDegree_lagr (pts vals : List ℚ) :
    (toPoly (lagr pts vals)).natDegree ≤ pts.length - 1 := by
  rw [toPoly_lagr]
  refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
  exact (natDegree_C_mul_le _ _).trans (natDegree_basisL pts i (Finset.mem_range.mp hi))

lemma valTest_of_toPoly_eq (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) {g : CPoly ℚ} {G : ℤ[X]}
    (h : toPoly g = G.map (Int.castRingHom ℚ)) (hG : G ∣ polyZ F) : valTest F g = true := by
  simp only [valTest, List.all_eq_true, decide_eq_true_eq]
  intro b _
  rw [num_evalC F hint, evalC_eq, h, Polynomial.eval_intCast_map]
  simpa using eval_dvd (x := b) hG

lemma toPoly_eq_zero_of_dvd_of_degree_lt {g r : ℚ[X]} (hg : g ∣ r) (hd : r.degree < g.degree) :
    r = 0 := by
  by_contra hr
  exact absurd (Polynomial.degree_le_of_dvd hg hr) (not_le.mpr hd)

/-! #### The integer filter keeps every integral factor -/

lemma lagDen_pos (pts : List ℚ) : 0 < lagDen pts := by
  unfold lagDen
  generalize (List.range pts.length).flatMap (fun i ↦ basisL pts i) = L
  induction L with
  | nil => simp
  | cons q L ih => simp only [List.foldr_cons]; exact Nat.lcm_pos q.den_pos ih

lemma toPoly_foldr_addZ {α : Type*} (v : α → ℤ) (b : α → CPoly ℤ) : ∀ l : List α,
    toPoly (l.foldr (fun i acc ↦ add (smul (v i) (b i)) acc) []) =
      (l.map fun i ↦ C (v i) * toPoly (b i)).sum
  | [] => by simp [CPoly.toPoly]
  | a :: l => by
    rw [List.foldr_cons, toPoly_add, toPoly_smul, toPoly_foldr_addZ v b l, List.map_cons,
      List.sum_cons]

lemma toPoly_mapZ (p : CPoly ℤ) :
    toPoly (p.map fun d : ℤ ↦ (d : ℚ)) = (toPoly p).map (Int.castRingHom ℚ) := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih]

lemma map_num_cast_of_intC {L : CPoly ℚ} (h : intC L = true) :
    (L.map Rat.num).map (fun d : ℤ ↦ (d : ℚ)) = L := by
  simp only [intC, List.all_eq_true, beq_iff_eq] at h
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun q hq ↦ Rat.coe_int_num_of_den_eq_one (h q hq)

/-- **The integer filter is harmless**: the values of an integral factor `G` of `F` pass it. -/
lemma zFilter_of (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) (pts ds : List ℤ)
    (hlen : ds.length = pts.length) (G : ℤ[X]) (hG : G ∣ polyZ F)
    (hgG : toPoly (lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ)))
      = G.map (Int.castRingHom ℚ))
    (hok : basisOk (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) = true) :
    zFilter F ((lagDen (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) : ℕ) : ℤ)
      (lagZ (basisZ (pts.map fun a : ℤ ↦ (Int.cast a : ℚ))) ds) = true := by
  set Q := pts.map fun a : ℤ ↦ (Int.cast a : ℚ) with hQ
  set W : ℕ := lagDen Q with hW
  have hW0 : (W : ℤ) ≠ 0 := by exact_mod_cast (lagDen_pos Q).ne'
  set cZ := lagZ (basisZ Q) ds with hcZ
  have hQl : Q.length = ds.length := by rw [hQ, List.length_map, hlen]
  have hB : ∀ i < Q.length, ((basisZ Q).getD i []).map (fun d : ℤ ↦ (d : ℚ)) =
      smul ((W : ℕ) : ℚ) (basisL Q i) := by
    intro i hi
    simp only [basisOk, List.all_eq_true, List.mem_range] at hok
    rw [basisZ, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact map_num_cast_of_intC (hok i hi)
  have hcZq : (toPoly cZ).map (Int.castRingHom ℚ) = (C (W : ℤ) * G).map (Int.castRingHom ℚ) := by
    rw [Polynomial.map_mul, map_C, ← hgG, toPoly_lagr, Finset.mul_sum, hcZ, lagZ, toPoly_foldr_addZ,
      ← Polynomial.coe_mapRingHom, map_list_sum, List.map_map, list_sum_range, hQl]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < Q.length := by rw [hQl]; exact Finset.mem_range.mp hi
    simp only [Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_mul, map_C]
    rw [← toPoly_mapZ, hB i hi', toPoly_smul]
    have : (ds.map fun d : ℤ ↦ (Int.cast d : ℚ)).getD i 0 = ((ds.getD i 0 : ℤ) : ℚ) := by
      rw [List.getD_eq_getElem _ _ (by simpa [← hQl] using hi'),
        List.getD_eq_getElem _ _ (by rw [← hQl]; exact hi'), List.getElem_map]
    rw [this]
    simp only [eq_intCast, Int.cast_natCast]
    ring
  have hcZ' : toPoly cZ = C (W : ℤ) * G :=
    Polynomial.map_injective _ (RingHom.injective_int _) hcZq
  unfold zFilter
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have h1 := coeff_toPoly cZ i
    rw [hcZ', coeff_C_mul, List.getD_eq_getElem _ _ hi] at h1
    rw [← h1]
    exact Int.mul_emod_right _ _
  · intro b _
    rw [evalC_eq, hcZ', eval_mul, eval_C, Int.mul_ediv_cancel_left _ hW0, num_evalC F hint]
    exact eval_dvd hG

/-- **No factor of degree `e`.** -/
theorem noFactor_sound (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) (e : ℕ)
    (h : noFactor F e = true) (G : ℤ[X]) (hG : G ∣ polyZ F) (hGd : G.natDegree = e)
    (hF0 : toPoly F ≠ 0) : False := by
  classical
  simp only [noFactor, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  set pts := ptsFor F (e + 1) with hpts
  set GQ := G.map (Int.castRingHom ℚ) with hGQ
  have hFZ0 : polyZ F ≠ 0 := fun h0 ↦ hF0 (by rw [← polyZ_map F hint, h0, Polynomial.map_zero])
  have hG0 : G ≠ 0 := fun h0 ↦ hFZ0 (zero_dvd_iff.mp (h0 ▸ hG))
  -- the tuple of values of `G`
  set ds := pts.map fun a ↦ G.eval a with hds
  have hmem : ds ∈ List.sections (pts.map fun a : ℤ ↦ divsZ (evalC F (Int.cast a : ℚ)).num) := by
    rw [List.mem_sections, hds, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro a ha
    rw [num_evalC F hint]
    refine mem_divsZ ?_ (eval_dvd hG)
    have := ptsFor_ne F (e + 1) ha
    rw [evalC_polyZ F hint] at this
    exact_mod_cast this
  have hds_len : ds.length = pts.length := by simp [hds]
  have hndQ : (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)).Nodup :=
    (ptsFor_nodup F (e + 1)).map Int.cast_injective
  have hgG' : toPoly (lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ))
      (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))) = GQ := by
    set sF := (pts.map fun a : ℤ ↦ (a : ℚ)).toFinset with hsF
    have hcard : sF.card = e + 1 := by
      rw [hsF, List.toFinset_card_of_nodup hndQ, List.length_map, hlen]
    have hgnd := natDegree_lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ))
      (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
    simp only [List.length_map, hlen, Nat.add_sub_cancel] at hgnd
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq sF ?_ ?_ ?_
    · rw [hcard]
      exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hgnd)
    · rw [hcard, hGQ, degree_map_eq_of_injective (RingHom.injective_int _),
        degree_eq_natDegree hG0, hGd]
      exact_mod_cast Nat.lt_succ_self e
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have := eval_lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
        hndQ i (by simpa using hi)
      rw [List.getD_eq_getElem _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa [hds_len] using hi)] at this
      simp only [List.getElem_map, hds] at this
      rw [this, hGQ, eval_map]
      exact (Polynomial.eval₂_hom (Int.castRingHom ℚ) pts[i]).symm
  have hc := hall ds hmem
  rw [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · rw [Bool.and_eq_true, Bool.not_eq_true'] at hc
    rw [zFilter_of F hint pts ds hds_len G hG hgG' hc.1] at hc
    exact Bool.noConfusion hc.2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨hvals, hdeg⟩, hdiv⟩ := hc
  set g := lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ)) with hg
  -- `g` agrees with `G` at the points
  have hev : ∀ a ∈ pts, (toPoly g).eval (a : ℚ) = GQ.eval (a : ℚ) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hz : (pts[i], G.eval pts[i]) ∈ List.zip pts ds := by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [hds, hi], ?_⟩
      simp [hds]
    have := hvals _ hz
    rw [evalC_eq] at this
    rw [this, hGQ, eval_map]
    exact (Polynomial.eval₂_hom (Int.castRingHom ℚ) pts[i]).symm
  -- uniqueness of the interpolant
  set sF := (pts.map fun a : ℤ ↦ (a : ℚ)).toFinset with hsF
  have hcard : sF.card = e + 1 := by
    rw [hsF, List.toFinset_card_of_nodup ((ptsFor_nodup F (e + 1)).map Int.cast_injective),
      List.length_map, hlen]
  have hdeg' : (trim g).length ≤ e + 1 := by simpa using hdeg
  have hgnd : (toPoly g).natDegree ≤ e := by
    by_cases hg0 : toPoly g = 0
    · rw [hg0, natDegree_zero]; exact Nat.zero_le _
    · have htr : trim g ≠ [] := fun h0 ↦ hg0 ((trim_eq_nil_iff g).mp h0)
      have := length_trim htr
      omega
  have hgdeg : (toPoly g).degree < sF.card := by
    rw [hcard]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hgnd)
  have hGdeg : GQ.degree < sF.card := by
    rw [hcard, hGQ, degree_map_eq_of_injective (RingHom.injective_int _), degree_eq_natDegree hG0,
      hGd]
    exact_mod_cast Nat.lt_succ_self e
  have hgG : toPoly g = GQ := Polynomial.eq_of_degrees_lt_of_eval_finset_eq _ hgdeg hGdeg
    (fun x hx ↦ by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact hev a ha)
  -- `g` has degree `e` and divides `F`
  have hGQ0 : GQ ≠ 0 := by
    rw [hGQ]; exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hG0
  have hlen' : (trim g).length = e + 1 := by
    have htr : trim g ≠ [] := fun h0 ↦ hGQ0 (by rw [← hgG]; exact (trim_eq_nil_iff g).mp h0)
    rw [length_trim htr, hgG, hGQ, natDegree_map_eq_of_injective (RingHom.injective_int _), hGd]
  have hdvd : toPoly g ∣ toPoly F := by
    rw [hgG, hGQ, ← polyZ_map F hint]
    exact Polynomial.map_dvd _ hG
  have hr0 : toPoly (divMod F g).2 = 0 := by
    have hspec := divMod_spec F g
    refine toPoly_eq_zero_of_dvd_of_degree_lt ?_ (divMod_degree_lt F g (by rw [hgG]; exact hGQ0))
    have : toPoly (divMod F g).2 = toPoly F - toPoly (divMod F g).1 * toPoly g := by
      rw [hspec]; ring
    rw [this]
    exact dvd_sub hdvd (dvd_mul_left _ _)
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hdiv
  rcases hdiv with ((h1 | h1) | h1) | h1
  · exact h1 hlen'
  · rw [intC_of_toPoly_eq hgG] at h1
    exact Bool.noConfusion h1
  · rw [valTest_of_toPoly_eq F hint hgG hG] at h1
    exact Bool.noConfusion h1
  · rw [(isZero_iff _).mpr hr0] at h1
    exact Bool.noConfusion h1

lemma dvd_gcdL (r : ℤ) : ∀ l : List ℤ, (∀ a ∈ l, r ∣ a) → r ∣ (gcdL l : ℤ)
  | [], _ => by simp [gcdL]
  | a :: l, h => by
    simp only [gcdL, List.foldr_cons]
    exact Int.dvd_coe_gcd (h a List.mem_cons_self)
      (dvd_gcdL r l fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-- **Kronecker's certificate is sound**: `F` is irreducible over `ℚ`. -/
theorem irredQ_sound (F : CPoly ℚ) (h : irredQ F = true) : Irreducible (toPoly F) := by
  classical
  simp only [irredQ, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hint, hgcd⟩, hdeg⟩, hnf⟩ := h
  have hint' : ∀ q ∈ F, q.den = 1 := fun q hq ↦ by simpa using hint q hq
  have hF0 : toPoly F ≠ 0 := by
    intro h0
    rw [degC, (trim_eq_nil_iff F).mpr h0] at hdeg
    simp at hdeg
  have htr : trim F ≠ [] := fun h0 ↦ hF0 ((trim_eq_nil_iff F).mp h0)
  have hdegF : degC F = (toPoly F).natDegree := by rw [degC, length_trim htr]; simp
  set FZ := polyZ F with hFZ
  have hmap := polyZ_map F hint'
  have hnd : FZ.natDegree = (toPoly F).natDegree := by
    rw [← hmap, natDegree_map_eq_of_injective (RingHom.injective_int _)]
  -- `FZ` is primitive
  have hprim : FZ.IsPrimitive := by
    intro r hr
    have hdvd : r ∣ (gcdL (F.map Rat.num) : ℤ) := dvd_gcdL r _ fun a ha ↦ by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have := (Polynomial.C_dvd_iff_dvd_coeff r FZ).mp hr i
      rwa [hFZ, polyZ, coeff_toPoly, List.getD_eq_getElem _ _ hi] at this
    rw [hgcd, Nat.cast_one] at hdvd
    exact isUnit_of_dvd_one hdvd
  -- `FZ` is irreducible in `ℤ[x]`
  have hirr : Irreducible FZ := by
    refine ⟨fun hu ↦ ?_, fun a b hab ↦ ?_⟩
    · have := natDegree_eq_zero_of_isUnit hu
      omega
    · have hFZ0 : FZ ≠ 0 := fun h0 ↦ hF0 (by
        have h0' : polyZ F = 0 := hFZ ▸ h0
        rw [← hmap, h0', Polynomial.map_zero])
      have ha0 : a ≠ 0 := fun h0 ↦ hFZ0 (by rw [hab, h0, zero_mul])
      have hb0 : b ≠ 0 := fun h0 ↦ hFZ0 (by rw [hab, h0, mul_zero])
      have hsum : a.natDegree + b.natDegree = FZ.natDegree := by
        rw [hab, natDegree_mul ha0 hb0]
      have hconst : ∀ c : ℤ[X], c ∣ FZ → c.natDegree = 0 → IsUnit c := fun c hc hc0 ↦ by
        rw [eq_C_of_natDegree_eq_zero hc0] at hc ⊢
        exact isUnit_C.mpr (hprim _ hc)
      by_cases ha' : a.natDegree = 0
      · exact Or.inl (hconst a ⟨b, hab⟩ ha')
      by_cases hb' : b.natDegree = 0
      · exact Or.inr (hconst b ⟨a, by rw [hab, mul_comm]⟩ hb')
      exfalso
      rcases le_total a.natDegree b.natDegree with hle | hle
      · have he := hnf (a.natDegree - 1) (List.mem_range.mpr (by rw [hdegF, ← hnd]; omega))
        exact noFactor_sound F hint' _ he a ⟨b, by rw [← hFZ, hab]⟩ (by omega) hF0
      · have he := hnf (b.natDegree - 1) (List.mem_range.mpr (by rw [hdegF, ← hnd]; omega))
        exact noFactor_sound F hint' _ he b ⟨a, by rw [← hFZ, hab, mul_comm]⟩ (by omega) hF0
  have := (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirr
  rwa [show (algebraMap ℤ ℚ) = Int.castRingHom ℚ from rfl, hmap] at this

end Sound

end Kron

end CPoly
