import RischTragerBronstein.Mixed.FrontSqrtAuto
import RischTragerBronstein.Mixed.FrontRootW
import RischTragerBronstein.Mixed.RootArith

/-!
# The front end with an `n`-th root over a logarithm, arbitrary rational expressions in `θ`

`SE.splitN n a s` rewrites an expression `s : SE` (the atom `th` is `θ`, `θⁿ = a`) as
`∑_{j<n} eⱼ θʲ` by arithmetic in `K(θ)`: products by the multiplication matrix (`mulV`,
`mul_lemma`), inverses by the first column of the adjugate over the determinant (`invV`,
symbolic determinants `detE` by expansion along the first column, `inv_lemma`).
`SE.splitN_spec`: the rewriting is correct when `1, θ, …, θⁿ⁻¹` are independent over a field
containing the values (`theta_indep`: `Xⁿ − A` is the minimal polynomial over `Fₘ₊₁`).
`frontRootAuto` decides `∫ s` through `frontRootLog`; `frontRootAuto_sound`; with the
antiderivative `frontRootAutoW`, `frontRootAutoW_valid`.
-/

open Polynomial Differential IntermediateField Finset

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- The sum of a list, dropping zeros. -/
def sumL (l : List EE) : EE := l.foldr addS (EE.cst 0)

/-- The multiplication matrix of `u`, symbolically. -/
def mcolE (n : ℕ) (a : EE) (u : List EE) (k j : ℕ) : EE :=
  if j ≤ k then u.getD (k - j) (EE.cst 0) else mulS a (u.getD (k + n - j) (EE.cst 0))

/-- **A symbolic determinant**, expanded along the first column. -/
def detE : (n : ℕ) → (Fin n → Fin n → EE) → EE
  | 0, _ => EE.cst 1
  | n + 1, M => sumL ((List.finRange (n + 1)).map fun i : Fin (n + 1) ↦
      mulS (if (i : ℕ) % 2 = 0 then EE.cst 1 else EE.cst (-1))
        (mulS (M i 0) (detE n fun r s ↦ M (i.succAbove r) s.succ)))

/-- The product of two elements of `K(θ)`. -/
def mulV (n : ℕ) (a : EE) (u v : List EE) : List EE :=
  (List.range n).map fun k ↦
    sumL ((List.range n).map fun j ↦ mulS (mcolE n a u k j) (v.getD j (EE.cst 0)))

/-- The first column of the adjugate. -/
def radjE (n : ℕ) (a : EE) (u : List EE) (i : ℕ) : EE :=
  detE n fun r s ↦ if (r : ℕ) = 0 then (if (s : ℕ) = i then EE.cst 1 else EE.cst 0)
    else mcolE n a u r s

/-- The inverse of an element of `K(θ)`. -/
def invV (n : ℕ) (a : EE) (u : List EE) : List EE :=
  (List.range n).map fun i ↦
    mulS (radjE n a u i) (EE.inv (detE n fun r s ↦ mcolE n a u r s))

namespace SE

/-- **The splitting** `s = ∑_{j<n} eⱼ θʲ`, `θⁿ = a`. -/
def splitN (n : ℕ) (a : EE) : SE → List EE
  | x => [EE.x]
  | y => [EE.y]
  | th => if n = 1 then [a] else [EE.cst 0, EE.cst 1]
  | cst c => [EE.cst c]
  | add u v => (List.range n).map fun k ↦
      addS ((splitN n a u).getD k (EE.cst 0)) ((splitN n a v).getD k (EE.cst 0))
  | mul u v => mulV n a (splitN n a u) (splitN n a v)
  | neg u => (splitN n a u).map negS
  | inv u => invV n a (splitN n a u)
  | exp b => [EE.exp b]
  | log b => [EE.log b]

end SE

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **The front end for `∫ s`, `s` rational in `θ`, `θⁿ = a`, over a logarithm.** -/
def frontRootAuto (n : ℕ) (a : EE) (s : SE) (N : ℕ) : Option Bool :=
  frontRootLog Fc n a (s.splitN n a) N

/-- The tower expression of `frontRootAuto`. -/
def raE (n : ℕ) (a : EE) (s : SE) : EE := rtE a (s.splitN n a)

/-- **`frontRootAuto` with the antiderivative.** -/
def frontRootAutoW (n : ℕ) (a : EE) (s : SE) (N : ℕ) : Option (Option RootW) :=
  frontRootLogW Fc n a (s.splitN n a) N

theorem frontRootAutoW_isSome (n : ℕ) (a : EE) (s : SE) (N : ℕ) :
    (frontRootAutoW Fc n a s N).map Option.isSome = frontRootAuto Fc n a s N :=
  frontRootLogW_isSome Fc _ _ _ _

/-- The display of the answer. -/
def frontRootAutoShow (n : ℕ) (a : EE) (s : SE) (N : ℕ) : List String :=
  ("integrand components: " ++ ", ".intercalate ((s.splitN n a).map EE.toStr)) ::
    frontRootLogShow Fc n a (s.splitN n a) N

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-! ### Evaluation -/

section Eval

variable (T : MTower Fc ks Cc L) (nodes : List EE)

lemma evE_sumL (l : List EE) : evE Fc T nodes (sumL l) = (l.map (evE Fc T nodes)).sum := by
  induction l with
  | nil => simp [sumL, evE]
  | cons e l ih =>
    rw [sumL, List.foldr_cons, evE_addS, ← sumL, ih]
    simp

lemma list_sum_range (n : ℕ) (f : ℕ → L) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

lemma getD_range_map (n : ℕ) (f : ℕ → EE) (k : ℕ) (d : EE) :
    ((List.range n).map f).getD k d = if k < n then f k else d := by
  by_cases h : k < n
  · rw [if_pos h, List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [if_neg h, List.getD_eq_default _ _ (by simp; omega)]

lemma evE_inv (e : EE) : evE Fc T nodes (EE.inv e) = (evE Fc T nodes e)⁻¹ := rfl

lemma ev_detE : ∀ (n : ℕ) (M : Fin n → Fin n → EE),
    evE Fc T nodes (detE n M) = (Matrix.of fun i j ↦ evE Fc T nodes (M i j)).det
  | 0, M => by simp [detE, evE]
  | n + 1, M => by
    rw [detE, evE_sumL, List.map_map, Matrix.det_succ_column_zero, Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, evE_mulS, ev_detE n]
    rcases Nat.mod_two_eq_zero_or_one (i : ℕ) with h | h
    · rw [if_pos h, (Nat.even_iff.mpr h).neg_one_pow]
      simp [evE]; first | rfl | exact Or.inl rfl
    · rw [if_neg (by omega), (Nat.odd_iff.mpr h).neg_one_pow]
      simp [evE]; first | rfl | exact Or.inl rfl

/-- The value of a vector of components. -/
noncomputable def valV (θ : L) (n : ℕ) (u : List EE) : L :=
  ∑ j ∈ range n, evE Fc T nodes (u.getD j (EE.cst 0)) * θ ^ j

lemma valV_single (θ : L) (n : ℕ) (hn : 1 ≤ n) (e : EE) :
    valV T nodes θ n [e] = evE Fc T nodes e := by
  rw [valV, sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp [evE]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

lemma valV_th (θ : L) (n : ℕ) (hn : 2 ≤ n) :
    valV T nodes θ n [EE.cst 0, EE.cst 1] = θ := by
  rw [valV, sum_eq_single 1]
  · simp [evE]
  · intro j _ hj
    rcases j with _ | _ | j
    · simp [evE]
    · exact absurd rfl hj
    · simp [evE]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

lemma ev_mcolE (n : ℕ) (a : EE) (u : List EE) (k j : ℕ) :
    evE Fc T nodes (mcolE n a u k j) =
      mcolL n (evE Fc T nodes a) (fun i ↦ evE Fc T nodes (u.getD i (EE.cst 0))) k j := by
  unfold mcolE mcolL
  split
  · rfl
  · rw [evE_mulS]

/-- **The splitting is correct**: if `θⁿ = a` and `1, θ, …, θⁿ⁻¹` are independent over a field
`K` containing the values of all `θ`-free expressions, then `s = ∑ eⱼ θʲ`. -/
theorem SE.splitN_spec (n : ℕ) (hn : 1 ≤ n) (a : EE) (θ : L)
    (hθ : θ ^ n = evE Fc T nodes a) (K : Subfield L) (hmem : ∀ e : EE, evE Fc T nodes e ∈ K)
    (hind : ∀ w : ℕ → L, (∀ i, w i ∈ K) → ∑ i ∈ range n, w i * θ ^ i = 0 →
      ∀ i < n, w i = 0) :
    ∀ s : SE, evS T nodes θ s = valV T nodes θ n (s.splitN n a)
  | SE.x => by rw [SE.splitN, valV_single T nodes θ n hn]; rfl
  | SE.y => by rw [SE.splitN, valV_single T nodes θ n hn]; rfl
  | SE.th => by
    rw [SE.splitN]
    split_ifs with h1
    · subst h1; rw [valV_single T nodes θ 1 hn, ← hθ, pow_one]; rfl
    · rw [valV_th T nodes θ n (by omega)]; rfl
  | SE.cst c => by rw [SE.splitN, valV_single T nodes θ n hn]; rfl
  | SE.add u v => by
    rw [evS, SE.splitN_spec n hn a θ hθ K hmem hind u, SE.splitN_spec n hn a θ hθ K hmem hind v,
      SE.splitN, valV, valV, valV, ← sum_add_distrib]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [getD_range_map, if_pos (mem_range.mp hk), evE_addS, add_mul]
  | SE.mul u v => by
    rw [evS, SE.splitN_spec n hn a θ hθ K hmem hind u, SE.splitN_spec n hn a θ hθ K hmem hind v,
      SE.splitN, valV, valV, valV, mul_lemma n _ θ hθ]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [mulV, getD_range_map, if_pos (mem_range.mp hk), evE_sumL, List.map_map,
      list_sum_range]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [Function.comp_apply, evE_mulS, ev_mcolE]
  | SE.neg u => by
    rw [evS, SE.splitN_spec n hn a θ hθ K hmem hind u, SE.splitN, valV, valV, ← sum_neg_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    have : EE.cst 0 = negS (EE.cst 0) := by simp [negS]
    rw [this, List.getD_map, ← this, evE_negS, neg_mul]
  | SE.inv u => by
    rw [evS, SE.splitN_spec n hn a θ hθ K hmem hind u, SE.splitN, valV, valV]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [inv_lemma K n' (evE Fc T nodes a) θ hθ (hmem a) _ (fun i ↦ hmem _) hind]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [invV, getD_range_map, if_pos (mem_range.mp hi), evE_mulS, radjE, ev_detE, evE_inv,
      ev_detE]
    congr 2
    · rw [radj]
      congr 1
      ext r s
      simp only [Matrix.of_apply]
      split_ifs <;> simp [evE, ev_mcolE]
    · rw [mMat]
      congr 2
      ext r s
      simp only [Matrix.of_apply, ev_mcolE]
  | SE.exp b => by rw [SE.splitN, valV_single T nodes θ n hn]; rfl
  | SE.log b => by rw [SE.splitN, valV_single T nodes θ n hn]; rfl

end Eval

/-! ### Independence of the powers of `θ` -/

/-- **`1, θ, …, θⁿ⁻¹` are independent over `Fₘ₊₁`** when `θⁿ = A(tₘ)`, `A` squarefree of
positive degree. -/
lemma theta_indep (T : MTower Fc ks Cc L) (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A) (w : ℕ → L)
    (hw : ∀ i, w i ∈ T.F (m + 1)) (h0 : ∑ i ∈ range n, w i * θ ^ i = 0) :
    ∀ i < n, w i = 0 := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set p₁ : (T.F m)[X] := GPoly.toPoly (T.MP m hTm) A with hp₁
  have hsq₁ : Squarefree p₁ := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg₁ : p₁.natDegree = degG (MO Fc ks m) A := (degG_eq (T.MP m hTm) A).symm
  have hy₁ : θ ^ n = aeval (T.ts m) p₁ := by
    rw [hp₁, T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm), hθ]
  let S₁ : SuperData (T.F m) L :=
    ⟨T.ts m, θ, n, p₁, hTr m (by omega), hn, hsq₁, by rw [hdeg₁]; exact hdegpos, hy₁,
      by exact_mod_cast hn.ne'⟩
  have hmp := S₁.minpoly_eq
  set Kx := IntermediateField.adjoin (T.F m) {S₁.x}
  let wk : Fin n → Kx := fun i ↦ ⟨w i, (T.mem_F_succ).mp (hw i)⟩
  set p : Kx[X] := ∑ i : Fin n, Polynomial.C (wk i) * X ^ (i : ℕ) with hp
  have hcoeff : ∀ i : Fin n, p.coeff i = wk i := fun i ↦ by
    rw [hp, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [if_neg (fun h ↦ hj (Fin.ext h.symm))]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hev : aeval θ p = 0 := by
    rw [hp, map_sum, ← h0, ← Fin.sum_univ_eq_sum_range (fun i ↦ w i * θ ^ i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, aeval_C, map_pow, aeval_X]
    rfl
  have hp0 : p = 0 := by
    by_contra hne
    have h1 := minpoly.degree_le_of_ne_zero Kx θ hne hev
    have h2 : (minpoly Kx θ).degree = n := by
      have : minpoly Kx θ = minpoly Kx S₁.y := rfl
      rw [this, hmp, degree_X_pow_sub_C (by exact hn)]
    have h3 := Polynomial.degree_sum_fin_lt (fun i : Fin n ↦ wk i)
    rw [← hp] at h3
    rw [h2] at h1
    exact absurd (lt_of_le_of_lt h1 h3) (lt_irrefl _)
  intro i hi
  have := hcoeff ⟨i, hi⟩
  rw [hp0, Polynomial.coeff_zero] at this
  exact congrArg Subtype.val this.symm

/-! ### Soundness -/

/-- **What an answer of `frontRootLog` certifies about `a`.** -/
lemma frontRootLog_data (n : ℕ) (a : EE) (es : List EE) (N : ℕ) (b : Bool)
    (hb : frontRootLog Fc n a es N = some b) :
    ∃ (m : ℕ) (qa : LC (m + 1)), (rtE a es).nodesOf.length = m + 1 ∧
      certC Fc (ksOf Fc (rtE a es)) (lvOf Fc (rtE a es)) (m + 1) = true ∧
      comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) a = some qa ∧
      degG (MO Fc (ksOf Fc (rtE a es)) m) qa.2 = 0 ∧
      GPoly.isZero (MO Fc (ksOf Fc (rtE a es)) m) qa.2 = false ∧
      GPoly.squarefreeCheck (MO Fc (ksOf Fc (rtE a es)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m).mul ((MO Fc (ksOf Fc (rtE a es)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m).zero)))) = true ∧
      0 < degG (MO Fc (ksOf Fc (rtE a es)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m).mul ((MO Fc (ksOf Fc (rtE a es)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m).zero)))) ∧ 0 < n := by
  classical
  unfold frontRootLog at hb
  obtain ⟨m, hlen⟩ : ∃ m, (rtE a es).nodesOf.length = m + 1 := by
    rcases h0 : (rtE a es).nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc (rtE a es)) (lvOf Fc (rtE a es)) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨-, hc⟩ := Bool.and_eq_true_iff.mp hcs
  split at hb
  · cases hb
  rcases hqa : comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hf0 : comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) (es.getD 0 (EE.cst 0))
    with _ | f0
  · rw [hqa, hf0] at hb; cases hb
  rw [hqa, hf0] at hb
  dsimp only at hb
  by_cases hd1 : degG (MO Fc (ksOf Fc (rtE a es)) m) qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc (rtE a es)) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc (rtE a es)) m)
      (qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m).mul ((MO Fc (ksOf Fc (rtE a es)) m).inv
        (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m).zero))))) = true ∨
      degG (MO Fc (ksOf Fc (rtE a es)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m).mul ((MO Fc (ksOf Fc (rtE a es)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m).zero)))) = 0 ∨
      Nat.gcd n (degG (MO Fc (ksOf Fc (rtE a es)) m)
        (qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m).mul ((MO Fc (ksOf Fc (rtE a es)) m).inv
          (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m).zero))))) ≠ 1 ∨ n = 0 ∨ n < es.length
  · rw [if_pos hd2] at hb; cases hb
  push Not at hd2
  obtain ⟨hsq, hdegpos, -, hn0, -⟩ := hd2
  exact ⟨m, qa, hlen, hc, hqa, hd1.1, by simpa using hd1.2, by simpa using hsq,
    Nat.pos_of_ne_zero hdegpos, Nat.pos_of_ne_zero hn0⟩

/-- Shared setup: the splitting is correct for every realization. -/
lemma frontRootAuto_split (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (n : ℕ) (a : EE) (s : SE) (N : ℕ) (b : Bool) (hb : frontRootAuto Fc n a s N = some b)
    (T : MTower Fc (ksOf Fc (raE n a s)) Cc L) (hn : T.n = (raE n a s).nodesOf.length)
    (θ : L) (hθ : θ ^ n = evE Fc T (raE n a s).nodesOf a) :
    evS T (raE n a s).nodesOf θ s = ∑ j ∈ range n,
      evE Fc T (raE n a s).nodesOf ((s.splitN n a).getD j (EE.cst 0)) * θ ^ j := by
  classical
  obtain ⟨m, qa, hlen, hc, hqa, hd, hz, hsqc, hdegpos, hn0⟩ :=
    frontRootLog_data n a (s.splitN n a) N b hb
  have hTn : T.n = m + 1 := by rw [hn]; exact hlen
  have MS := T.mspecs hmon hdeg (lvOf Fc (raE n a s)) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hva := comp_spec Fc T (raE n a s).nodesOf (m + 1) hTr a qa hqa
  have hθA : θ ^ n = T.evP m (qa.1.map ((MO Fc (ksOf Fc (raE n a s)) m).mul
      ((MO Fc (ksOf Fc (raE n a s)) m).inv
        (qa.2.getD 0 (MO Fc (ksOf Fc (raE n a s)) m).zero)))) := by
    rw [hθ, ← hva, ev_constDen T m hTm qa hd hz]
  refine SE.splitN_spec T _ n hn0 a θ hθ (T.F T.n).toSubfield (evE_mem T _) ?_ s
  intro w hw h0
  exact theta_indep T m hTr _ hsqc hdegpos n hn0 θ hθA w (fun i ↦ by rw [← hTn]; exact hw i) h0

/-- **Every answer of `frontRootAuto` is correct**: for every realization `T` of the compiled
tower and every `n`-th root `θ` of `a` generating `L` over it, `∫ s` is elementary iff the
answer is `true`. -/
theorem frontRootAuto_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (n : ℕ) (a : EE) (s : SE) (N : ℕ) (b : Bool) (hb : frontRootAuto Fc n a s N = some b)
    (T : MTower Fc (ksOf Fc (raE n a s)) Cc L) (hn : T.n = (raE n a s).nodesOf.length)
    (θ : L) (hθ : θ ^ n = evE Fc T (raE n a s).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (raE n a s).nodesOf.length) {θ}) :
    HasElementaryIntegral (evS T (raE n a s).nodesOf θ s) ↔ b = true := by
  rw [frontRootAuto_split hmon hdeg n a s N b hb T hn θ hθ]
  exact frontRootLog_sound hmon hdeg n a _ N b hb T hn θ hθ hgen

/-- **Every antiderivative returned by `frontRootAutoW` is valid**, for the integrand `s`. -/
theorem frontRootAutoW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (n : ℕ) (a : EE) (s : SE) (N : ℕ) (m : ℕ) (w0 : ADW (m + 1)) (ys : List (LC (m + 1)))
    (hb : frontRootAutoW Fc n a s N = some (some (.mk m w0 ys)))
    (T : MTower Fc (ksOf Fc (raE n a s)) Cc L) (hn : T.n = (raE n a s).nodesOf.length)
    (θ : L) (hθ : θ ^ n = evE Fc T (raE n a s).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (raE n a s).nodesOf.length) {θ}) :
    evS T (raE n a s).nodesOf θ s = ∑ j ∈ range n,
      evE Fc T (raE n a s).nodesOf ((s.splitN n a).getD j (EE.cst 0)) * θ ^ j ∧
    (∃ f0 : LC (m + 1), T.ev (m + 1) f0 =
        evE Fc T (raE n a s).nodesOf ((s.splitN n a).getD 0 (EE.cst 0)) ∧
      T.ValidW (m + 1) f0 w0) ∧
    ∀ j ∈ Finset.Ico 1 n, (T.ev (m + 1) (ys.getD j (MO Fc (ksOf Fc (raE n a s)) (m + 1)).zero) *
      θ ^ j)′ = evE Fc T (raE n a s).nodesOf ((s.splitN n a).getD j (EE.cst 0)) * θ ^ j := by
  have hsome : (frontRootAutoW Fc n a s N).map Option.isSome = some true := by rw [hb]; rfl
  rw [frontRootAutoW_isSome] at hsome
  exact ⟨frontRootAuto_split hmon hdeg n a s N true hsome T hn θ hθ,
    frontRootLogW_valid hmon hdeg n a _ N m w0 ys hb T hn θ hθ hgen⟩

end Curves.MT.Front
