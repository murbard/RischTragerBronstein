import RischTragerBronstein.Computable.CPoly
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.TakeDrop
import RischTragerBronstein.Computable.EuclidDegree

/-!
# A verified linear dependency finder

`d + 1` (or more) vectors of length `d` over a field are linearly dependent. `CPoly.depend d vs`
computes coefficients, not all zero, of a vanishing linear combination, by elimination of the
first coordinate: with `p` the first vector whose first coordinate `a` is nonzero, every other
vector `v` is replaced by `tail v - (v₀ / a) tail p`, a dependency among these is found
recursively (dimension `d - 1`), and the coefficient of `p` is chosen to cancel the first
coordinate. `depend_spec` is the correctness statement.
-/

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- The `k`-th coordinate (`0` beyond the length). -/
def coord (v : List R) (k : ℕ) : R := v.getD k 0

/-- `∑ᵢ cᵢ vᵢ[k]`. -/
def lincombAt (c : List R) (vs : List (List R)) (k : ℕ) : R :=
  (List.zipWith (fun ci v ↦ ci * coord v k) c vs).sum

/-- `tail v - (v₀ / a) pt`. -/
def elimFirst (a : R) (pt : List R) (v : List R) : List R :=
  List.zipWith (fun x y ↦ x - v.headD 0 / a * y) v.tail pt

/-- Coefficients of a vanishing linear combination of `vs` (vectors of length `d`, more than
`d` of them). -/
def depend : ℕ → List (List R) → List R
  | 0, vs => match vs with
    | [] => []
    | _ :: rest => 1 :: List.replicate rest.length 0
  | d + 1, vs =>
    match vs.span (fun v ↦ v.headD 0 = 0) with
    | (pre, []) => depend d ((pre ++ []).map List.tail)
    | (pre, p :: post) =>
      let a := p.headD 0
      let c := depend d ((pre ++ post).map (elimFirst a p.tail))
      let cpre := c.take pre.length
      let cpost := c.drop pre.length
      cpre ++ (-(lincombAt cpost post 0) / a) :: cpost

lemma coord_cons_succ (h : R) (t : List R) (k : ℕ) : coord (h :: t) (k + 1) = coord t k := rfl

lemma coord_cons_zero (h : R) (t : List R) : coord (h :: t) 0 = h := rfl

lemma coord_tail_succ (v : List R) (k : ℕ) : coord v (k + 1) = coord v.tail k := by
  cases v <;> rfl

lemma coord_zero_eq_headD (v : List R) : coord v 0 = v.headD 0 := by cases v <;> rfl

lemma coord_zipWith {f : R → R → R} {l₁ l₂ : List R} {k : ℕ} (h₁ : k < l₁.length)
    (h₂ : k < l₂.length) : coord (List.zipWith f l₁ l₂) k = f (coord l₁ k) (coord l₂ k) := by
  simp only [coord]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂]

lemma coord_append_left (l₁ l₂ : List R) {k : ℕ} (h : k < l₁.length) :
    coord (l₁ ++ l₂) k = coord l₁ k := by
  simp only [coord]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
    List.getElem_append_left h]

lemma coord_append_right (l₁ l₂ : List R) (k : ℕ) :
    coord (l₁ ++ l₂) (l₁.length + k) = coord l₂ k := by
  simp only [coord]
  by_cases h : k < l₂.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
      List.getElem_append_right (by omega)]
    congr 1; omega
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma lincombAt_append {c₁ c₂ : List R} {v₁ v₂ : List (List R)} (h : c₁.length = v₁.length)
    (k : ℕ) : lincombAt (c₁ ++ c₂) (v₁ ++ v₂) k = lincombAt c₁ v₁ k + lincombAt c₂ v₂ k := by
  simp only [lincombAt]
  rw [List.zipWith_append h, List.sum_append]

lemma lincombAt_cons (ci : R) (c : List R) (v : List R) (vs : List (List R)) (k : ℕ) :
    lincombAt (ci :: c) (v :: vs) k = ci * coord v k + lincombAt c vs k := by
  simp [lincombAt]

lemma lincombAt_map (c : List R) (vs : List (List R)) (f : List R → List R) (k : ℕ) :
    lincombAt c (vs.map f) k = (List.zipWith (fun ci v ↦ ci * coord (f v) k) c vs).sum := by
  simp only [lincombAt]
  rw [List.zipWith_map_right]

lemma zipWith_congr_of_mem {c : List R} {vs : List (List R)} {f g : R → List R → R}
    (h : ∀ v ∈ vs, ∀ ci, f ci v = g ci v) : List.zipWith f c vs = List.zipWith g c vs := by
  induction c generalizing vs with
  | nil => simp
  | cons ci c ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      simp only [List.zipWith_cons_cons]
      rw [h v List.mem_cons_self, ih fun w hw ↦ h w (List.mem_cons_of_mem _ hw)]

lemma dropWhile_eq_cons_not {P : List R → Bool} :
    ∀ {l : List (List R)} {p : List R} {post : List (List R)},
      l.dropWhile P = p :: post → P p = false := by
  intro l
  induction l with
  | nil => intro p post h; simp at h
  | cons x l ih =>
    intro p post h
    rw [List.dropWhile_cons] at h
    split_ifs at h with hx
    · exact ih h
    · rw [List.cons.injEq] at h
      rw [← h.1]
      simpa using hx

/-- Linearity: `∑ cᵢ (xᵢ - yᵢ t) = ∑ cᵢ xᵢ - t ∑ cᵢ yᵢ`. -/
lemma zipWith_sum_sub (c : List R) (vs : List (List R)) (x y : List R → R) (t : R) :
    (List.zipWith (fun ci v ↦ ci * (x v - y v * t)) c vs).sum =
      (List.zipWith (fun ci v ↦ ci * x v) c vs).sum -
        t * (List.zipWith (fun ci v ↦ ci * y v) c vs).sum := by
  induction c generalizing vs with
  | nil => simp
  | cons ci c ih =>
    cases vs with
    | nil => simp
    | cons v vs => simp only [List.zipWith_cons_cons, List.sum_cons, ih]; ring

lemma lincombAt_zero_of_heads {c : List R} {vs : List (List R)}
    (h : ∀ v ∈ vs, v.headD 0 = 0) : lincombAt c vs 0 = 0 := by
  induction c generalizing vs with
  | nil => simp [lincombAt]
  | cons ci c ih =>
    cases vs with
    | nil => simp [lincombAt]
    | cons v vs =>
      rw [lincombAt_cons, coord_zero_eq_headD, h v (List.mem_cons_self), mul_zero, zero_add]
      exact ih fun w hw ↦ h w (List.mem_cons_of_mem _ hw)

lemma lincombAt_succ_map_tail (c : List R) (vs : List (List R)) (k : ℕ) :
    lincombAt c vs (k + 1) = lincombAt c (vs.map List.tail) k := by
  rw [lincombAt_map]
  simp only [lincombAt, coord_tail_succ]

lemma length_elimFirst (a : R) {pt v : List R} {d : ℕ} (hpt : pt.length = d)
    (hv : v.length = d + 1) : (elimFirst a pt v).length = d := by
  simp only [elimFirst, List.length_zipWith, List.length_tail, hv, hpt]
  omega

/-- The coordinates of `elimFirst`. -/
lemma coord_elimFirst (a : R) {pt v : List R} {d k : ℕ} (hpt : pt.length = d)
    (hv : v.length = d + 1) (hk : k < d) :
    coord (elimFirst a pt v) k = coord v (k + 1) - coord v 0 / a * coord pt k := by
  simp only [elimFirst]
  rw [coord_zipWith (by simp [hv]; omega) (by omega), coord_tail_succ, coord_zero_eq_headD]

theorem depend_spec (d : ℕ) : ∀ vs : List (List R), d < vs.length → (∀ v ∈ vs, v.length = d) →
    (depend d vs).length = vs.length ∧ (∃ i, coord (depend d vs) i ≠ 0) ∧
      ∀ k < d, lincombAt (depend d vs) vs k = 0 := by
  induction d with
  | zero =>
    intro vs hlen _
    cases vs with
    | nil => simp at hlen
    | cons v rest =>
      refine ⟨by simp [depend], ⟨0, by simp [depend, coord]⟩, fun k hk ↦ absurd hk (by omega)⟩
  | succ d ih =>
    intro vs hlen hv
    have hspan := List.span_eq_takeWhile_dropWhile (fun v : List R ↦ decide (v.headD 0 = 0)) vs
    have hsplit : vs.takeWhile (fun v : List R ↦ decide (v.headD 0 = 0)) ++
        vs.dropWhile (fun v : List R ↦ decide (v.headD 0 = 0)) = vs :=
      List.takeWhile_append_dropWhile
    have hpre : ∀ v ∈ vs.takeWhile (fun v : List R ↦ decide (v.headD 0 = 0)), v.headD 0 = 0 :=
      fun v hv' ↦ by simpa using List.mem_takeWhile_imp hv'
    set pre := vs.takeWhile (fun v : List R ↦ decide (v.headD 0 = 0)) with hpredef
    set rest := vs.dropWhile (fun v : List R ↦ decide (v.headD 0 = 0)) with hrestdef
    cases hr : rest with
    | nil =>
      -- all first coordinates vanish
      rw [hr, List.append_nil] at hsplit
      have hvs' : vs = pre := hsplit.symm
      simp only [depend, hspan, hr, List.append_nil]
      rw [← hvs']
      have hlen' : d < (vs.map List.tail).length := by simp; omega
      have hv' : ∀ w ∈ vs.map List.tail, w.length = d := fun w hw ↦ by
        obtain ⟨v, hv1, rfl⟩ := List.mem_map.mp hw
        simp [hv v hv1]
      obtain ⟨h1, h2, h3⟩ := ih _ hlen' hv'
      refine ⟨by simpa using h1, h2, fun k hk ↦ ?_⟩
      cases k with
      | zero => exact lincombAt_zero_of_heads (hvs' ▸ hpre)
      | succ k => rw [lincombAt_succ_map_tail]; exact h3 k (by omega)
    | cons p post =>
      have hp0 : p.headD 0 ≠ 0 := by
        have := dropWhile_eq_cons_not (hrestdef ▸ hr)
        simpa using this
      have hvs' : vs = pre ++ p :: post := by rw [← hsplit, hr]
      simp only [depend, hspan, hr]
      set a := p.headD 0 with ha
      have hp : p.length = d + 1 := hv p (by rw [hvs']; simp)
      have hpt : p.tail.length = d := by simp [hp]
      set others := (pre ++ post).map (elimFirst a p.tail) with hothers
      have hlen' : d < others.length := by
        have := congrArg List.length hvs'
        simp at this
        simp [hothers]; omega
      have hv' : ∀ w ∈ others, w.length = d := fun w hw ↦ by
        obtain ⟨v, hv1, rfl⟩ := List.mem_map.mp hw
        refine length_elimFirst a hpt (hv v ?_)
        rw [hvs']
        rcases List.mem_append.mp hv1 with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      obtain ⟨h1, h2, h3⟩ := ih _ hlen' hv'
      set c := depend d others with hc
      have hclen : c.length = pre.length + post.length := by simpa [hothers] using h1
      have htake : (c.take pre.length).length = pre.length := by simp; omega
      have hdrop : (c.drop pre.length).length = post.length := by simp; omega
      have hcsplit : c = c.take pre.length ++ c.drop pre.length := (List.take_append_drop _ _).symm
      refine ⟨?_, ?_, fun k hk ↦ ?_⟩
      · rw [hvs']; simp; omega
      · obtain ⟨i, hi⟩ := h2
        by_cases hipre : i < pre.length
        · refine ⟨i, ?_⟩
          rw [coord_append_left _ _ (by rw [htake]; exact hipre)]
          rwa [hcsplit, coord_append_left _ _ (by rw [htake]; exact hipre)] at hi
        · refine ⟨i + 1, ?_⟩
          obtain ⟨j, hj⟩ : ∃ j, i = pre.length + j := ⟨i - pre.length, by omega⟩
          have e1 : i + 1 = (c.take pre.length).length + (j + 1) := by rw [htake]; omega
          have e2 : i = (c.take pre.length).length + j := by rw [htake]; exact hj
          rw [e1, coord_append_right, coord_cons_succ]
          rw [hcsplit, e2, coord_append_right] at hi
          exact hi
      · rw [hvs', lincombAt_append htake, lincombAt_cons]
        cases k with
        | zero =>
          rw [lincombAt_zero_of_heads hpre, coord_zero_eq_headD, ← ha]
          field_simp
          ring
        | succ k =>
          have hk' : k < d := by omega
          have hsum := h3 k hk'
          rw [hothers, lincombAt_map] at hsum
          have hcoord : ∀ v ∈ pre ++ post, coord (elimFirst a p.tail v) k =
              coord v (k + 1) - coord v 0 / a * coord p.tail k := fun v hv1 ↦ by
            refine coord_elimFirst a hpt (hv v ?_) hk'
            rw [hvs']
            rcases List.mem_append.mp hv1 with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
          have hzip : (List.zipWith (fun ci v ↦ ci * coord (elimFirst a p.tail v) k) c
              (pre ++ post)).sum = (List.zipWith (fun ci v ↦
                ci * (coord v (k + 1) - coord v 0 * (coord p.tail k / a))) c (pre ++ post)).sum := by
            congr 1
            exact zipWith_congr_of_mem fun v hv1 ci ↦ by rw [hcoord v hv1]; ring
          rw [hzip, zipWith_sum_sub c (pre ++ post) (fun v ↦ coord v (k + 1)) (fun v ↦ coord v 0),
            hcsplit, List.zipWith_append htake, List.zipWith_append htake,
            List.sum_append, List.sum_append] at hsum
          have hpre0 : (List.zipWith (fun ci v ↦ ci * coord v 0) (c.take pre.length) pre).sum = 0 :=
            lincombAt_zero_of_heads hpre
          rw [hpre0, zero_add] at hsum
          change lincombAt (c.take pre.length) pre (k + 1) + (-(lincombAt (c.drop pre.length) post 0) / a *
            coord p (k + 1) + lincombAt (c.drop pre.length) post (k + 1)) = 0
          change (lincombAt (c.take pre.length) pre (k + 1) + lincombAt (c.drop pre.length) post (k + 1)) -
            coord p.tail k / a * lincombAt (c.drop pre.length) post 0 = 0 at hsum
          rw [coord_tail_succ p k]
          linear_combination hsum

end CPoly
