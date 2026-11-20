import RischTragerBronstein.Torsion.PlaceExist3
import RischTragerBronstein.Torsion.NonPrincComplete

/-!
# Assembling place certificates from local data

A `PlaceCert` lists the places of all fibres in one list. `LocPlaces` is the data of one fibre:
its places `(e, y, prec)`, its roots `(place, s, ζ)` (local place indices), the multiplicities
`Γ` of its places, a bound `cf` and the test precision `tp`. `assemble` concatenates the local
data (shifting the place indices by the offsets `offF`), and **`assemble_check`**: if every fibre
satisfies the local conditions (`LocOK`), the abscissae are distinct and `∑ Γ = cΓ n`, the
assembled certificate passes `PlaceCert.check`.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Flatten

variable {β : Type*}

/-- The offset of the block `j`. -/
def offF (P : List (List β)) (j : ℕ) : ℕ := ((P.take j).map List.length).sum

lemma offF_succ (L : List β) (P : List (List β)) (j : ℕ) :
    offF (L :: P) (j + 1) = L.length + offF P j := by
  simp [offF]

lemma offF_zero (P : List (List β)) : offF P 0 = 0 := by simp [offF]

lemma getD_flatten : ∀ (P : List (List β)) (j : ℕ), j < P.length → ∀ t < (P.getD j []).length,
    ∀ d : β, P.flatten.getD (offF P j + t) d = (P.getD j []).getD t d
  | [], _, h, _, _, _ => by simp at h
  | L :: P, 0, _, t, ht, d => by
    simp only [List.getD_cons_zero] at ht ⊢
    rw [offF_zero, zero_add, List.flatten_cons, List.getD_append _ _ _ _ ht]
  | L :: P, j + 1, hj, t, ht, d => by
    simp only [List.getD_cons_succ] at ht ⊢
    rw [offF_succ, List.flatten_cons, add_assoc, List.getD_append_right _ _ _ _ (by omega),
      Nat.add_sub_cancel_left]
    exact getD_flatten P j (by simpa using hj) t ht d

lemma sum_range_flatten {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ P : List (List β),
    ∑ π ∈ Finset.range P.flatten.length, f π =
      ∑ j ∈ Finset.range P.length, ∑ t ∈ Finset.range (P.getD j []).length, f (offF P j + t)
  | [] => by simp
  | L :: P => by
    rw [List.flatten_cons, List.length_append, Finset.sum_range_add, List.length_cons,
      Finset.sum_range_succ', sum_range_flatten (fun π ↦ f (L.length + π)) P, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [List.getD_cons_succ]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [offF_succ, add_assoc]
    · simp [offF_zero]

lemma exists_decomp : ∀ (P : List (List β)) (π : ℕ), π < P.flatten.length →
    ∃ j < P.length, ∃ t < (P.getD j []).length, π = offF P j + t
  | [], π, h => by simp at h
  | L :: P, π, h => by
    rw [List.flatten_cons, List.length_append] at h
    by_cases hπ : π < L.length
    · exact ⟨0, by simp, π, by simpa using hπ, by rw [offF_zero, zero_add]⟩
    · obtain ⟨j, hj, t, ht, e⟩ := exists_decomp P (π - L.length) (by omega)
      refine ⟨j + 1, by simpa using hj, t, by simpa using ht, ?_⟩
      rw [offF_succ]; omega

lemma offF_add_lt : ∀ (P : List (List β)) (j : ℕ), j < P.length → ∀ t < (P.getD j []).length,
    offF P j + t < P.flatten.length
  | [], _, h, _, _ => by simp at h
  | L :: P, 0, _, t, ht => by
    simp only [List.getD_cons_zero] at ht
    rw [offF_zero, List.flatten_cons, List.length_append]; omega
  | L :: P, j + 1, hj, t, ht => by
    simp only [List.getD_cons_succ] at ht
    have := offF_add_lt P j (by simpa using hj) t ht
    rw [offF_succ, List.flatten_cons, List.length_append]; omega

end Flatten

section Local

variable {F : Type*} [Field F] [DecidableEq F]

/-- The place data of one fibre. -/
structure LocPlaces (F : Type*) where
  α : F
  N : ℕ
  /-- the places `(e, y, prec)` -/
  pls : List (ℕ × CPoly F × ℕ)
  /-- the roots `(local place, s, ζ)` -/
  rts : List (ℕ × ℕ × F)
  /-- the multiplicities of the places -/
  Γ : List ℕ
  cf : ℕ
  tp : ℕ

namespace LocPlaces

variable (L : LocPlaces F)

def e (t : ℕ) : ℕ := (L.pls.getD t (1, [], 0)).1
def y (t : ℕ) : CPoly F := (L.pls.getD t (1, [], 0)).2.1
def pp (t : ℕ) : ℕ := (L.pls.getD t (1, [], 0)).2.2
def idx (k : ℕ) : ℕ := (L.rts.getD k (0, 1, 1)).1
def s (k : ℕ) : ℕ := (L.rts.getD k (0, 1, 1)).2.1
def ζ (k : ℕ) : F := (L.rts.getD k (0, 1, 1)).2.2

/-- The global place entries of the fibre `j`. -/
def placeList (j : ℕ) : List (ℕ × ℕ × CPoly F × ℕ) :=
  L.pls.map fun x ↦ (j, x.1, x.2.1, x.2.2)

/-- **The local conditions.** -/
structure OK (Fc : BPoly F) (n : ℕ) : Prop where
  pls : ∀ t < L.pls.length, 0 < L.e t ∧ rootCheck Fc L.α (L.e t) (L.pp t) (L.y t) = true
  Γlen : L.Γ.length = L.pls.length
  rtsLen : L.rts.length = n
  rts : ∀ k < n, L.idx k < L.pls.length ∧ 0 < L.s k ∧ L.N = L.s k * L.e (L.idx k) ∧
    L.ζ k ^ L.N = 1 ∧ L.tp ≤ L.s k * L.pp (L.idx k)
  sep : ∀ k < n, ∀ l < n, k ≠ l → ∃ i < L.tp,
    (conjC (L.ζ k) (L.s k) (L.y (L.idx k))).getD i 0 ≠ (conjC (L.ζ l) (L.s l) (L.y (L.idx l))).getD i 0
  Γle : ∀ t < L.pls.length, L.Γ.getD t 0 ≤ L.cf * L.e t
  dsum : ∑ k ∈ Finset.range n, L.s k * L.Γ.getD (L.idx k) 0 = L.N * L.Γ.sum
  dle : L.Γ.sum ≤ n * L.cf
  esum : ∑ t ∈ Finset.range L.pls.length, L.e t = n
  surj : ∀ t < L.pls.length, ∃ k < n, L.idx k = t

end LocPlaces

/-- The default local data. -/
def locDef : LocPlaces F := ⟨0, 1, [], [], [], 0, 0⟩

/-- The blocks of places. -/
def plBlocks (Ls : List (LocPlaces F)) : List (List (ℕ × ℕ × CPoly F × ℕ)) :=
  (List.range Ls.length).map fun j ↦ (Ls.getD j locDef).placeList j

/-- **The assembled certificate.** -/
def assemble (Ls : List (LocPlaces F)) (cΓ : ℕ) : PlaceCert F where
  fib := Ls.map fun L ↦ (L.α, L.N)
  pl := (plBlocks Ls).flatten
  rt := (List.range Ls.length).map fun j ↦
    (Ls.getD j locDef).rts.map fun r ↦ (offF (plBlocks Ls) j + r.1, r.2.1, r.2.2)
  Γp := (Ls.map (·.Γ)).flatten
  cf := Ls.map (·.cf)
  dΓ := Ls.map (·.Γ.sum)
  cΓ := cΓ
  tp := Ls.map (·.tp)

variable (Ls : List (LocPlaces F)) (cΓ : ℕ)

lemma plBlocks_length : (plBlocks Ls).length = Ls.length := by simp [plBlocks]

lemma plBlocks_getD (j : ℕ) (hj : j < Ls.length) :
    (plBlocks Ls).getD j [] = (Ls.getD j locDef).placeList j := by
  rw [plBlocks, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

lemma plBlocks_getD_length (j : ℕ) (hj : j < Ls.length) :
    ((plBlocks Ls).getD j []).length = (Ls.getD j locDef).pls.length := by
  rw [plBlocks_getD Ls j hj, LocPlaces.placeList, List.length_map]

lemma offF_Γ (j : ℕ) (hΓ : ∀ L ∈ Ls, L.Γ.length = L.pls.length) :
    offF (Ls.map (·.Γ)) j = offF (plBlocks Ls) j := by
  simp only [offF, plBlocks]
  rw [List.map_take, List.map_take, List.map_map, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_map, Function.comp_apply, List.getElem_range,
    LocPlaces.placeList, List.length_map]
  have hi : i < Ls.length := by simp at h2; exact h2.2
  rw [List.getD_eq_getElem _ _ hi]
  exact hΓ _ (List.getElem_mem hi)

section Access

variable {Ls}

lemma assemble_pl_getD (j : ℕ) (hj : j < Ls.length) (t : ℕ) (ht : t < (Ls.getD j locDef).pls.length) :
    (assemble Ls cΓ).pl.getD (offF (plBlocks Ls) j + t) (0, 1, [], 0) =
      (j, (Ls.getD j locDef).e t, (Ls.getD j locDef).y t, (Ls.getD j locDef).pp t) := by
  simp only [assemble]
  rw [getD_flatten _ j (by rw [plBlocks_length]; exact hj) t
    (by rw [plBlocks_getD_length Ls j hj]; exact ht), plBlocks_getD Ls j hj, LocPlaces.placeList,
    List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
  rw [LocPlaces.e, LocPlaces.y, LocPlaces.pp, List.getD_eq_getElem _ _ ht]

lemma assemble_pj (j : ℕ) (hj : j < Ls.length) (t : ℕ) (ht : t < (Ls.getD j locDef).pls.length) :
    (assemble Ls cΓ).pj (offF (plBlocks Ls) j + t) = j := by
  rw [PlaceCert.pj, assemble_pl_getD cΓ j hj t ht]

lemma assemble_pe (j : ℕ) (hj : j < Ls.length) (t : ℕ) (ht : t < (Ls.getD j locDef).pls.length) :
    (assemble Ls cΓ).pe (offF (plBlocks Ls) j + t) = (Ls.getD j locDef).e t := by
  rw [PlaceCert.pe, assemble_pl_getD cΓ j hj t ht]

lemma assemble_py (j : ℕ) (hj : j < Ls.length) (t : ℕ) (ht : t < (Ls.getD j locDef).pls.length) :
    (assemble Ls cΓ).py (offF (plBlocks Ls) j + t) = (Ls.getD j locDef).y t := by
  rw [PlaceCert.py, assemble_pl_getD cΓ j hj t ht]

lemma assemble_pp (j : ℕ) (hj : j < Ls.length) (t : ℕ) (ht : t < (Ls.getD j locDef).pls.length) :
    (assemble Ls cΓ).pp (offF (plBlocks Ls) j + t) = (Ls.getD j locDef).pp t := by
  rw [PlaceCert.pp, assemble_pl_getD cΓ j hj t ht]

lemma assemble_Γp (hΓ : ∀ L ∈ Ls, L.Γ.length = L.pls.length) (j : ℕ) (hj : j < Ls.length) (t : ℕ)
    (ht : t < (Ls.getD j locDef).pls.length) :
    (assemble Ls cΓ).Γp.getD (offF (plBlocks Ls) j + t) 0 = (Ls.getD j locDef).Γ.getD t 0 := by
  simp only [assemble]
  have hjL : (Ls.getD j locDef) ∈ Ls := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  have hmap : (Ls.map (·.Γ)).getD j [] = (Ls.getD j locDef).Γ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]
  rw [← offF_Γ Ls j hΓ, getD_flatten _ j (by simpa using hj) t
    (by rw [hmap, hΓ _ hjL]; exact ht), hmap]

lemma assemble_fα (j : ℕ) (hj : j < Ls.length) : (assemble Ls cΓ).fα j = (Ls.getD j locDef).α := by
  simp [PlaceCert.fα, assemble, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem?_getD, hj]

lemma assemble_fN (j : ℕ) (hj : j < Ls.length) : (assemble Ls cΓ).fN j = (Ls.getD j locDef).N := by
  simp [PlaceCert.fN, assemble, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem?_getD, hj]

lemma assemble_rt (j : ℕ) (hj : j < Ls.length) : (assemble Ls cΓ).rt.getD j [] =
    (Ls.getD j locDef).rts.map fun r ↦ (offF (plBlocks Ls) j + r.1, r.2.1, r.2.2) := by
  simp only [assemble]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

lemma assemble_rtk (j : ℕ) (hj : j < Ls.length) (k : ℕ) (hk : k < (Ls.getD j locDef).rts.length) :
    ((assemble Ls cΓ).rt.getD j []).getD k (0, 1, 1) =
      (offF (plBlocks Ls) j + (Ls.getD j locDef).idx k, (Ls.getD j locDef).s k,
        (Ls.getD j locDef).ζ k) := by
  rw [assemble_rt cΓ j hj, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  rw [LocPlaces.idx, LocPlaces.s, LocPlaces.ζ, List.getD_eq_getElem _ _ hk]

lemma assemble_rπ (j : ℕ) (hj : j < Ls.length) (k : ℕ) (hk : k < (Ls.getD j locDef).rts.length) :
    (assemble Ls cΓ).rπ j k = offF (plBlocks Ls) j + (Ls.getD j locDef).idx k := by
  rw [PlaceCert.rπ, assemble_rtk cΓ j hj k hk]

lemma assemble_rs (j : ℕ) (hj : j < Ls.length) (k : ℕ) (hk : k < (Ls.getD j locDef).rts.length) :
    (assemble Ls cΓ).rs j k = (Ls.getD j locDef).s k := by
  rw [PlaceCert.rs, assemble_rtk cΓ j hj k hk]

lemma assemble_rζ (j : ℕ) (hj : j < Ls.length) (k : ℕ) (hk : k < (Ls.getD j locDef).rts.length) :
    (assemble Ls cΓ).rζ j k = (Ls.getD j locDef).ζ k := by
  rw [PlaceCert.rζ, assemble_rtk cΓ j hj k hk]

lemma assemble_cf (j : ℕ) (hj : j < Ls.length) : (assemble Ls cΓ).cf.getD j 0 = (Ls.getD j locDef).cf := by
  simp [assemble, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem?_getD, hj]

lemma assemble_dΓ (j : ℕ) (hj : j < Ls.length) :
    (assemble Ls cΓ).dΓ.getD j 0 = (Ls.getD j locDef).Γ.sum := by
  simp [assemble, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem?_getD, hj]

lemma assemble_tp (j : ℕ) (hj : j < Ls.length) : (assemble Ls cΓ).tp.getD j 0 = (Ls.getD j locDef).tp := by
  simp [assemble, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem?_getD, hj]

end Access

variable {Ls cΓ}

lemma sum_tsub_of_le {ι : Type*} (s : Finset ι) (a b : ι → ℕ) (h : ∀ i ∈ s, b i ≤ a i) :
    ∑ i ∈ s, (a i - b i) + ∑ i ∈ s, b i = ∑ i ∈ s, a i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi ↦ Nat.sub_add_cancel (h i hi)

/-- **Local conditions give a valid certificate.** -/
theorem assemble_check (Fc : BPoly F) (n : ℕ) (hok : ∀ L ∈ Ls, L.OK Fc n)
    (hnd : (Ls.map (·.α)).Nodup) (hΓ : ∑ j ∈ Finset.range Ls.length, (Ls.getD j locDef).Γ.sum = cΓ * n) :
    (assemble Ls cΓ).check Fc n = true := by
  classical
  set D := assemble Ls cΓ with hD
  have hok' : ∀ j < Ls.length, (Ls.getD j locDef).OK Fc n := fun j hj ↦
    hok _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)
  have hΓl : ∀ L ∈ Ls, L.Γ.length = L.pls.length := fun L hL ↦ (hok L hL).Γlen
  have hfl : D.fib.length = Ls.length := by simp [hD, assemble]
  have hpl : D.pl.length = (plBlocks Ls).flatten.length := rfl
  -- decomposition of the global place indices
  have hdec : ∀ π < D.pl.length, ∃ j < Ls.length, ∃ t < (Ls.getD j locDef).pls.length,
      π = offF (plBlocks Ls) j + t := fun π hπ ↦ by
    obtain ⟨j, hj, t, ht, e⟩ := exists_decomp _ π hπ
    rw [plBlocks_length] at hj
    exact ⟨j, hj, t, by rwa [plBlocks_getD_length Ls j hj] at ht, e⟩
  have hin : ∀ j < Ls.length, ∀ t < (Ls.getD j locDef).pls.length,
      offF (plBlocks Ls) j + t < D.pl.length := fun j hj t ht ↦
    offF_add_lt _ j (by rw [plBlocks_length]; exact hj) t (by rw [plBlocks_getD_length Ls j hj]; exact ht)
  -- sums over the places
  have hsum : ∀ f : ℕ → ℕ, ∑ π ∈ Finset.range D.pl.length, f π =
      ∑ j ∈ Finset.range Ls.length, ∑ t ∈ Finset.range (Ls.getD j locDef).pls.length,
        f (offF (plBlocks Ls) j + t) := fun f ↦ by
    rw [hpl, sum_range_flatten, plBlocks_length]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [plBlocks_getD_length Ls j (Finset.mem_range.mp hj)]
  simp only [PlaceCert.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- distinct abscissae
    simpa [PlaceCert.αs, hD, assemble, List.map_map, Function.comp_def] using hnd
  · -- the places
    intro π hπ
    obtain ⟨j, hj, t, ht, rfl⟩ := hdec π hπ
    rw [assemble_pj cΓ j hj t ht, assemble_pe cΓ j hj t ht, assemble_pp cΓ j hj t ht,
      assemble_py cΓ j hj t ht, assemble_fα cΓ j hj, hfl]
    exact ⟨⟨hj, ((hok' j hj).pls t ht).1⟩, ((hok' j hj).pls t ht).2⟩
  · simp [hD, assemble]
  · -- the roots
    intro j hj
    rw [hfl] at hj
    have hL := hok' j hj
    refine ⟨by rw [assemble_rt cΓ j hj, List.length_map, hL.rtsLen], fun k hk ↦ ?_⟩
    have hk' : k < (Ls.getD j locDef).rts.length := by rw [hL.rtsLen]; exact hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL.rts k hk
    rw [assemble_rπ cΓ j hj k hk', assemble_pj cΓ j hj _ h1, assemble_rs cΓ j hj k hk',
      assemble_fN cΓ j hj, assemble_pe cΓ j hj _ h1, assemble_rζ cΓ j hj k hk',
      assemble_tp cΓ j hj, assemble_pp cΓ j hj _ h1]
    exact ⟨⟨⟨⟨⟨hin j hj _ h1, rfl⟩, h2⟩, h3⟩, h4⟩, h5⟩
  · -- separation
    simp only [PlaceCert.sepCheckP, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      decide_eq_true_eq, List.any_eq_true]
    intro j hj k hk l hl
    rw [hfl] at hj
    have hL := hok' j hj
    by_cases hkl : k = l
    · exact Or.inl hkl
    right
    have hk' : k < (Ls.getD j locDef).rts.length := by rw [hL.rtsLen]; exact hk
    have hl' : l < (Ls.getD j locDef).rts.length := by rw [hL.rtsLen]; exact hl
    obtain ⟨i, hi, hne⟩ := hL.sep k hk l hl hkl
    refine ⟨i, by rw [assemble_tp cΓ j hj]; exact hi, ?_⟩
    simp only [PlaceCert.apx]
    rw [assemble_rπ cΓ j hj k hk', assemble_rπ cΓ j hj l hl', assemble_rs cΓ j hj k hk',
      assemble_rs cΓ j hj l hl', assemble_rζ cΓ j hj k hk', assemble_rζ cΓ j hj l hl',
      assemble_py cΓ j hj _ (hL.rts k hk).1, assemble_py cΓ j hj _ (hL.rts l hl).1]
    exact hne
  · -- the bounds on the multiplicities
    intro π hπ
    obtain ⟨j, hj, t, ht, rfl⟩ := hdec π hπ
    rw [assemble_Γp cΓ hΓl j hj t ht, assemble_pj cΓ j hj t ht, assemble_cf cΓ j hj,
      assemble_pe cΓ j hj t ht]
    exact (hok' j hj).Γle t ht
  · -- the degrees on the fibres
    intro j hj
    rw [hfl] at hj
    have hL := hok' j hj
    rw [assemble_dΓ cΓ j hj, assemble_cf cΓ j hj, assemble_fN cΓ j hj]
    refine ⟨?_, hL.dle⟩
    rw [← hL.dsum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k < (Ls.getD j locDef).rts.length := by rw [hL.rtsLen]; exact Finset.mem_range.mp hk
    rw [assemble_rs cΓ j hj k hk', assemble_rπ cΓ j hj k hk',
      assemble_Γp cΓ hΓl j hj _ (hL.rts k (Finset.mem_range.mp hk)).1]
  · -- the total degree
    rw [hfl, show D.cΓ = cΓ from rfl, ← hΓ]
    exact Finset.sum_congr rfl fun j hj ↦ assemble_dΓ cΓ j (Finset.mem_range.mp hj)
  · -- the count `mP`
    rw [hsum (fun π ↦ D.cf.getD (D.pj π) 0 * D.pe π - D.Γp.getD π 0), hfl]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    have hL := hok' j hj'
    rw [assemble_cf cΓ j hj', assemble_dΓ cΓ j hj']
    have e1 : ∀ t ∈ Finset.range (Ls.getD j locDef).pls.length,
        D.cf.getD (D.pj (offF (plBlocks Ls) j + t)) 0 * D.pe (offF (plBlocks Ls) j + t) -
          D.Γp.getD (offF (plBlocks Ls) j + t) 0 =
        (Ls.getD j locDef).cf * (Ls.getD j locDef).e t - (Ls.getD j locDef).Γ.getD t 0 := by
      intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [assemble_pj cΓ j hj' t ht', assemble_cf cΓ j hj', assemble_pe cΓ j hj' t ht',
        assemble_Γp cΓ hΓl j hj' t ht']
    rw [Finset.sum_congr rfl e1]
    have h1 := sum_tsub_of_le (Finset.range (Ls.getD j locDef).pls.length)
      (fun t ↦ (Ls.getD j locDef).cf * (Ls.getD j locDef).e t) (fun t ↦ (Ls.getD j locDef).Γ.getD t 0)
      fun t ht ↦ hL.Γle t (Finset.mem_range.mp ht)
    rw [← Finset.mul_sum, hL.esum] at h1
    have h2 : ∑ t ∈ Finset.range (Ls.getD j locDef).pls.length, (Ls.getD j locDef).Γ.getD t 0 =
        (Ls.getD j locDef).Γ.sum := by
      rw [← hL.Γlen, ← sum_range_list]
      congr 1
      exact map_getD_range _ 0
    rw [h2] at h1
    have := hL.dle
    rw [mul_comm n]
    omega
  · -- the places carry `Γ`
    rw [hsum (fun π ↦ D.Γp.getD π 0), show D.cΓ = cΓ from rfl, ← hΓ]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    have hL := hok' j hj'
    rw [Finset.sum_congr rfl fun t ht ↦ assemble_Γp cΓ hΓl j hj' t (Finset.mem_range.mp ht),
      ← hL.Γlen, ← sum_range_list]
    congr 1
    exact map_getD_range _ 0
  · -- every place has a root
    intro π hπ
    obtain ⟨j, hj, t, ht, rfl⟩ := hdec π hπ
    obtain ⟨k, hk, hkt⟩ := (hok' j hj).surj t ht
    have hk' : k < (Ls.getD j locDef).rts.length := by rw [(hok' j hj).rtsLen]; exact hk
    exact ⟨j, by rw [hfl]; exact hj, k, hk, by rw [assemble_rπ cΓ j hj k hk', hkt]⟩

end Local

end Curves
