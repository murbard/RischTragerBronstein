import RischTragerBronstein.Algebraic.SupGlobalCert
import RischTragerBronstein.Computable.LinSolve

/-!
# Finding global certificates

`solveLamF` solves for a non-speciality certificate `λ` by linear algebra over any field
(`solveLamF_sound`, `solveLamF_complete`), and `certSearch` tries all ordered choices of base
points among candidate points `(x, ζᵏ y)`. By `exists_cert_lists`, `certSearch` succeeds once
there are enough candidates (`certSearch_complete`); whatever it returns is a valid certificate
(`certSearch_sound`).
-/

open Polynomial CPoly

namespace Sup

section Helpers

variable {K : Type*} [Field K]

lemma coeff_lcomb (m : ℕ) : ∀ (cs : List K) (vs : List (CPoly K)),
    (lcomb cs vs).coeff m = (List.zipWith (fun c v ↦ c * v.getD m 0) cs vs).sum
  | [], _ => by simp [lcomb]
  | _ :: _, [] => by simp [lcomb]
  | c :: cs, v :: vs => by
    have := coeff_lcomb m cs vs
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul,
      coeff_toPoly] at this ⊢
    rw [this]

lemma zipWith_sum_range {α : Type*} (f : K → α → K) (da : α) :
    ∀ (cs : List K) (vs : List α), cs.length = vs.length →
      (List.zipWith f cs vs).sum = ∑ q ∈ Finset.range vs.length, f (cs.getD q 0) (vs.getD q da)
  | [], [], _ => by simp
  | c :: cs, v :: vs, h => by
    have := zipWith_sum_range f da cs vs (by simpa using h)
    rw [List.zipWith_cons_cons, List.sum_cons, this, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma sum_range_mul (F : ℕ → K) (a b : ℕ) :
    ∑ q ∈ Finset.range (a * b), F q = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, F (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma getD_flatMap_blocks {α : Type*} (f : ℕ → List α) (b : ℕ) (hb : ∀ i, (f i).length = b)
    (da : α) : ∀ (a i j : ℕ), i < a → j < b →
      ((List.range a).flatMap f).getD (i * b + j) da = (f i).getD j da
  | 0, _, _, h, _ => by omega
  | a + 1, i, j, hi, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range a).flatMap f).length = a * b := by
      rw [List.length_flatMap]
      simp [hb]
    rcases Nat.lt_or_ge i a with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact getD_flatMap_blocks f b hb da a i j h hj
    · have hia : i = a := by omega
      subst hia
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
        show i * b + j - i * b = j by omega]

lemma length_flatMap_blocks {α : Type*} (f : ℕ → List α) (b : ℕ) (hb : ∀ i, (f i).length = b)
    (a : ℕ) : ((List.range a).flatMap f).length = a * b := by
  rw [List.length_flatMap]; simp [hb]

end Helpers

section Solve

variable {K : Type*} [Field K] [DecidableEq K]

/-- The columns: values of the monomial basis at the conjugate points. -/
def lamCols (n d g : ℕ) (xs ys : List K) (ζ : K) : List (CPoly K) :=
  (List.range g).flatMap fun i' ↦ (List.range (n - 1)).map fun k ↦
    (basisN n d (n * g)).map fun ai ↦ xs.getD i' 0 ^ ai.1 * (ζ ^ (k + 1) * ys.getD i' 0) ^ ai.2

/-- The target: values of the monomial basis at the base point `i`. -/
def lamTarget (n d g : ℕ) (xs ys : List K) (i : ℕ) : CPoly K :=
  (basisN n d (n * g)).map fun ai ↦ xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2

/-- Solve every target. -/
def solveAll (cols : List (CPoly K)) : List (CPoly K) → Option (List (List K))
  | [] => some []
  | w :: ws =>
    match linSolve cols w, solveAll cols ws with
    | some cs, some rest => some (cs :: rest)
    | _, _ => none

/-- **The certificate by linear algebra.** -/
def solveLamF (n d g : ℕ) (xs ys : List K) (ζ : K) : Option (List (List K)) :=
  solveAll (lamCols n d g xs ys ζ) ((List.range g).map (lamTarget n d g xs ys))

lemma solveAll_spec (cols : List (CPoly K)) : ∀ (ws : List (CPoly K)) (ls : List (List K)),
    solveAll cols ws = some ls → ∀ i < ws.length,
      linSolve cols (ws.getD i []) = some (ls.getD i [])
  | [], ls, _, i, hi => by simp at hi
  | w :: ws, ls, h, i, hi => by
    unfold solveAll at h
    split at h
    · rename_i cs rest h1 h2
      cases h
      rcases i with _ | i
      · simpa using h1
      · simpa using solveAll_spec cols ws rest h2 i (by simpa using hi)
    · cases h

lemma solveAll_complete (cols : List (CPoly K)) : ∀ (ws : List (CPoly K)),
    (∀ w ∈ ws, linSolve cols w ≠ none) → solveAll cols ws ≠ none
  | [], _ => by simp [solveAll]
  | w :: ws, h => by
    unfold solveAll
    obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp (h w List.mem_cons_self)
    obtain ⟨rest, hrest⟩ := Option.ne_none_iff_exists'.mp
      (solveAll_complete cols ws fun w' hw' ↦ h w' (List.mem_cons_of_mem _ hw'))
    rw [hcs, hrest]
    simp

lemma length_lamCols (n d g : ℕ) (xs ys : List K) (ζ : K) :
    (lamCols n d g xs ys ζ).length = g * (n - 1) :=
  length_flatMap_blocks _ (n - 1) (fun _ ↦ by simp) g

lemma lamCols_entry (n d g : ℕ) (xs ys : List K) (ζ : K) {i' k m : ℕ} (hi' : i' < g)
    (hk : k < n - 1) (hm : m < (basisN n d (n * g)).length) :
    ((lamCols n d g xs ys ζ).getD (i' * (n - 1) + k) []).getD m 0 =
      xs.getD i' 0 ^ ((basisN n d (n * g))[m]).1 *
        (ζ ^ (k + 1) * ys.getD i' 0) ^ ((basisN n d (n * g))[m]).2 := by
  unfold lamCols
  rw [getD_flatMap_blocks _ (n - 1) (fun _ ↦ by simp) [] g i' k hi' hk]
  have h1 : ((List.range (n - 1)).map fun k ↦ (basisN n d (n * g)).map fun ai ↦
      xs.getD i' 0 ^ ai.1 * (ζ ^ (k + 1) * ys.getD i' 0) ^ ai.2).getD k [] =
      (basisN n d (n * g)).map fun ai ↦
        xs.getD i' 0 ^ ai.1 * (ζ ^ (k + 1) * ys.getD i' 0) ^ ai.2 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]
  rw [h1, List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map]

/-- The coefficient identity of a solved system, as a double sum. -/
lemma lcomb_entry (n d g : ℕ) (xs ys : List K) (ζ : K) (cs : List K)
    (hcs : cs.length = g * (n - 1)) {m : ℕ} (hm : m < (basisN n d (n * g)).length) :
    (lcomb cs (lamCols n d g xs ys ζ)).coeff m =
      ∑ i' ∈ Finset.range g, ∑ k ∈ Finset.range (n - 1), cs.getD (i' * (n - 1) + k) 0 *
        (xs.getD i' 0 ^ ((basisN n d (n * g))[m]).1 *
          (ζ ^ (k + 1) * ys.getD i' 0) ^ ((basisN n d (n * g))[m]).2) := by
  rw [coeff_lcomb, zipWith_sum_range _ [] _ _ (by rw [hcs, length_lamCols]), length_lamCols,
    sum_range_mul]
  refine Finset.sum_congr rfl fun i' hi' ↦ Finset.sum_congr rfl fun k hk ↦ ?_
  rw [lamCols_entry n d g xs ys ζ (Finset.mem_range.mp hi') (Finset.mem_range.mp hk) hm]

/-- Reindexing `k ↦ k + 1` and reading `λ` through `lamK`. -/
lemma sum_lamK (n g i : ℕ) (hn : 2 ≤ n) (lam : List (List K)) (F : ℕ → ℕ → K) :
    ∑ i' ∈ Finset.range g, ∑ k ∈ Finset.range (n - 1),
        (lam.getD i []).getD (i' * (n - 1) + k) 0 * F i' (k + 1) =
      ∑ i' ∈ Finset.range g, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k * F i' k := by
  refine Finset.sum_congr rfl fun i' _ ↦ ?_
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold lamK
  rw [show 1 + k - 1 = k by omega, add_comm 1 k]

/-- **Soundness of `solveLamF`**: its output is a certificate. -/
theorem solveLamF_sound {n d g : ℕ} (hn : 2 ≤ n) {xs ys : List K} {ζ : K} {lam : List (List K)}
    (h : solveLamF n d g xs ys ζ = some lam) :
    ∀ i < g, ∀ ai ∈ basisN n d (n * g), xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
      ∑ i' ∈ Finset.range g, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k *
        (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2) := by
  intro i hi ai hai
  have hs := solveAll_spec _ _ _ h i (by simpa using hi)
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range] at hs
  obtain ⟨hlen, hcomb⟩ := linSolve_sound _ _ _ hs
  rw [length_lamCols] at hlen
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hai
  have hc := congrArg (fun p ↦ p.coeff m) hcomb
  rw [lcomb_entry n d g xs ys ζ _ hlen hm, coeff_toPoly, lamTarget,
    List.getD_eq_getElem ((basisN n d (n * g)).map fun ai ↦ xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2)
      0 (by simpa using hm), List.getElem_map] at hc
  rw [← hc, ← sum_lamK n g i hn lam (fun i' k ↦ xs.getD i' 0 ^ ((basisN n d (n * g))[m]).1 *
    (ζ ^ k * ys.getD i' 0) ^ ((basisN n d (n * g))[m]).2)]

/-- **Completeness of `solveLamF`**: if a certificate exists, one is found. -/
theorem solveLamF_complete {n d g : ℕ} (hn : 2 ≤ n) {xs ys : List K} {ζ : K}
    (lam0 : List (List K))
    (hcert : ∀ i < g, ∀ ai ∈ basisN n d (n * g), xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
      ∑ i' ∈ Finset.range g, ∑ k ∈ Finset.Ico 1 n, lamK lam0 n i i' k *
        (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2)) :
    solveLamF n d g xs ys ζ ≠ none := by
  refine solveAll_complete _ _ fun w hw ↦ ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  have hi' := List.mem_range.mp hi
  -- the candidate solution: row `i` of `lam0`, padded
  set cs : List K := List.ofFn fun q : Fin (g * (n - 1)) ↦ (lam0.getD i []).getD q 0 with hcsdef
  have hcsl : cs.length = g * (n - 1) := by simp [hcsdef]
  have hcsget : ∀ q < g * (n - 1), cs.getD q 0 = (lam0.getD i []).getD q 0 := fun q hq ↦ by
    rw [hcsdef, List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_ofFn]
  refine linSolve_complete_map (RingHom.id K) _ _ cs (by rw [hcsl, length_lamCols]) ?_
  have hS : lcombS (RingHom.id K) cs (lamCols n d g xs ys ζ) = lcomb cs (lamCols n d g xs ys ζ) := by
    simp [lcombS, lcomb, Polynomial.map_id]
  rw [hS, Polynomial.map_id]
  ext m
  by_cases hm : m < (basisN n d (n * g)).length
  · rw [lcomb_entry n d g xs ys ζ cs hcsl hm, coeff_toPoly, lamTarget,
      List.getD_eq_getElem ((basisN n d (n * g)).map fun ai ↦
        xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2) 0 (by simpa using hm), List.getElem_map,
      hcert i hi' _ (List.getElem_mem hm), ← sum_lamK n g i hn lam0]
    refine Finset.sum_congr rfl fun i' hi'' ↦ Finset.sum_congr rfl fun k hk ↦ ?_
    rw [hcsget _ (by
      have := Finset.mem_range.mp hi''
      have := Finset.mem_range.mp hk
      calc i' * (n - 1) + k < i' * (n - 1) + (n - 1) := by omega
        _ = (i' + 1) * (n - 1) := by ring
        _ ≤ g * (n - 1) := Nat.mul_le_mul_right _ (by omega))]
  · rw [coeff_toPoly, List.getD_eq_default _ _ (by simp [lamTarget]; omega)]
    rw [coeff_lcomb, zipWith_sum_range _ [] _ _ (by rw [hcsl, length_lamCols])]
    refine Finset.sum_eq_zero fun q hq ↦ ?_
    have hq' := Finset.mem_range.mp hq
    rw [length_lamCols] at hq'
    have hcol : ((lamCols n d g xs ys ζ).getD q []).length = (basisN n d (n * g)).length := by
      have hq2 : q = q / (n - 1) * (n - 1) + q % (n - 1) := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod q (n - 1)).symm
      have hn1 : 0 < n - 1 := by omega
      unfold lamCols
      rw [hq2, getD_flatMap_blocks _ (n - 1) (fun _ ↦ by simp) [] g _ _
        (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hq')) (Nat.mod_lt _ hn1),
        List.getD_eq_getElem _ _ (by simpa using Nat.mod_lt _ hn1)]
      simp
    rw [List.getD_eq_default ((lamCols n d g xs ys ζ).getD q []) 0 (by omega), mul_zero]

end Solve

section Search

variable {K : Type*} [Field K] [DecidableEq K]

/-- The candidate base points: `(x, ζᵏ y)` for candidates `(x, y)` with `x ∉ avoid`. -/
def certChoices (n : ℕ) (ζ : K) (cands : List (K × K)) (avoid : List K) : List (K × K) :=
  (cands.filter fun c ↦ c.1 ∉ avoid).flatMap fun c ↦ (List.range n).map fun k ↦ (c.1, ζ ^ k * c.2)

/-- **The certificate search**: all ordered choices of `g` base points. -/
def certSearch (d n : ℕ) (ζ : K) (cands : List (K × K)) (avoid : List K) :
    Option (List K × List K × List (List K)) :=
  (List.sections (List.replicate (((n - 1) * (d - 1) + 1) / 2) (certChoices n ζ cands avoid))).findSome?
    fun tup ↦ if (tup.map Prod.fst).Nodup then
      (solveLamF n d (((n - 1) * (d - 1) + 1) / 2) (tup.map Prod.fst) (tup.map Prod.snd) ζ).map
        fun lam ↦ (tup.map Prod.fst, tup.map Prod.snd, lam)
      else none

/-- **Soundness of `certSearch`.** -/
theorem certSearch_sound {d n : ℕ} (hn : 2 ≤ n) {ζ : K} {cands : List (K × K)} {avoid : List K}
    {xs ys : List K} {lam : List (List K)} (h : certSearch d n ζ cands avoid = some (xs, ys, lam)) :
    xs.length = ((n - 1) * (d - 1) + 1) / 2 ∧ ys.length = xs.length ∧ xs.Nodup ∧
      (∀ i < xs.length, ∃ c ∈ cands, c.1 ∉ avoid ∧ xs.getD i 0 = c.1 ∧
        ∃ k < n, ys.getD i 0 = ζ ^ k * c.2) ∧
      ∀ i < xs.length, ∀ ai ∈ basisN n d (n * xs.length),
        xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
          ∑ i' ∈ Finset.range xs.length, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k *
            (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2) := by
  unfold certSearch at h
  obtain ⟨tup, htup, hres⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hres with hnd
  obtain ⟨lam', hlam', heq⟩ := Option.map_eq_some_iff.mp hres
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hlen : tup.length = ((n - 1) * (d - 1) + 1) / 2 := by
    have := (List.mem_sections.mp htup).length_eq
    simpa using this
  refine ⟨by simp [hlen], by simp, hnd, ?_, ?_⟩
  · intro i hi
    simp only [List.length_map] at hi
    have hmem : tup[i] ∈ certChoices n ζ cands avoid := by
      have h2 := List.mem_sections.mp htup
      have := List.forall₂_iff_get.mp h2
      have hget := this.2 i (by simpa using hi) (by simp [hlen] at hi ⊢; omega)
      simpa using hget
    obtain ⟨c, hc, hck⟩ := List.mem_flatMap.mp hmem
    obtain ⟨k, hk, hkc⟩ := List.mem_map.mp hck
    rw [List.mem_filter] at hc
    refine ⟨c, hc.1, by simpa using hc.2, ?_, k, List.mem_range.mp hk, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, ← hkc]
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, ← hkc]
  · rw [List.length_map, hlen]
    exact solveLamF_sound hn hlam'

/-- **Completeness of `certSearch`**: with more than `g + d` usable candidate abscissae (distinct,
non-zero `y`), a certificate is found. -/
theorem certSearch_complete {d n : ℕ} (hn : 2 ≤ n) (hcop : Nat.Coprime n d) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (cands : List (K × K)) (avoid : List K)
    (hy : ∀ c ∈ cands, c.2 ≠ 0)
    (hX : ((n - 1) * (d - 1) + 1) / 2 + d <
      ((cands.filter fun c ↦ c.1 ∉ avoid).map Prod.fst).toFinset.card) :
    certSearch d n ζ cands avoid ≠ none := by
  classical
  set Xs := ((cands.filter fun c ↦ c.1 ∉ avoid).map Prod.fst).toFinset with hXs
  set y : K → K := fun x ↦ ((cands.find? fun c ↦ c.1 = x).map Prod.snd).getD 0 with hydef
  -- every candidate abscissa has its `y` in the list
  have hfind : ∀ x ∈ Xs, ∃ c ∈ cands, c.1 = x ∧ c.1 ∉ avoid ∧ y x = c.2 := by
    intro x hx
    obtain ⟨c0, hc0, hc0x⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    rw [List.mem_filter] at hc0
    have hs : (cands.find? fun c ↦ decide (c.1 = x)).isSome :=
      List.find?_isSome.mpr ⟨c0, hc0.1, by simp [hc0x]⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
    have hcx : c.1 = x := by simpa using List.find?_some hc
    refine ⟨c, List.mem_of_find?_eq_some hc, hcx, ?_, ?_⟩
    · rw [hcx, ← hc0x]; simpa using hc0.2
    · simp only [hydef]; rw [hc]; rfl
  have hyX : ∀ x ∈ Xs, y x ≠ 0 := by
    intro x hx
    obtain ⟨c, hc, -, -, hyc⟩ := hfind x hx
    rw [hyc]; exact hy c hc
  obtain ⟨xs, ys, lam, hxl, hyl, hnd, hpts, hcert⟩ := exists_cert_lists hn hcop hζ Xs y hyX hX
  set tup := List.zip xs ys with htup
  have htl : tup.length = ((n - 1) * (d - 1) + 1) / 2 := by simp [htup, hxl, hyl]
  have hfst : tup.map Prod.fst = xs := by rw [htup, List.map_fst_zip]; omega
  have hsnd : tup.map Prod.snd = ys := by rw [htup, List.map_snd_zip]; omega
  have hsec : tup ∈ List.sections (List.replicate (((n - 1) * (d - 1) + 1) / 2)
      (certChoices n ζ cands avoid)) := by
    rw [List.mem_sections, List.forall₂_iff_get]
    refine ⟨by simp [htl], fun i h1 h2 ↦ ?_⟩
    simp only [List.get_eq_getElem, List.getElem_replicate]
    have hi : i < xs.length := by simp [htup] at h1; omega
    obtain ⟨hxX, k, hk, hyk⟩ := hpts i hi
    obtain ⟨c, hc, hcx, hcav, hyc⟩ := hfind _ hxX
    rw [certChoices, List.mem_flatMap]
    refine ⟨c, List.mem_filter.mpr ⟨hc, by simpa using hcav⟩, List.mem_map.mpr ⟨k,
      List.mem_range.mpr hk, ?_⟩⟩
    simp only [htup, List.getElem_zip]
    rw [List.getD_eq_getElem _ _ hi] at hcx hyk hyc
    rw [List.getD_eq_getElem _ _ (by omega)] at hyk
    rw [hcx, hyk, hyc]
  unfold certSearch
  intro hnone
  rw [List.findSome?_eq_none_iff] at hnone
  have := hnone tup hsec
  rw [hfst, hsnd, if_pos hnd] at this
  rw [hxl] at hcert
  exact solveLamF_complete hn lam hcert (Option.map_eq_none_iff.mp this)

end Search

end Sup
