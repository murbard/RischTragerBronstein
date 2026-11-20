import RischTragerBronstein.Mixed.KQSem
import RischTragerBronstein.Algebraic.SqrtIndep
import RischTragerBronstein.Algebraic.SupLocalCert

/-!
# Residue classes modulo squares, computably

* `qsqrt_sq`: the rational square root finds every square;
* `inGB` decides `SqrtIndep.InG` (`inGB_iff`), `findRep` writes `a = c² ∏_{i ∈ T} gᵢ`
  (`findRep_spec`);
* `gensOf`: greedily chosen generators, multiplicatively independent modulo squares
  (`gensOf_mindep`), in whose group every nonzero input lies (`findRep_gensOf`).
-/

open SqrtIndep

namespace Curves.MT

lemma qsqrt_sq (y : ℚ) : (qsqrt (y ^ 2)).isSome := by
  unfold qsqrt
  have hnn : ¬ y ^ 2 < 0 := not_lt.mpr (sq_nonneg y)
  rw [if_neg hnn]
  have hnum : (y ^ 2).num.toNat = y.num.natAbs ^ 2 := by
    rw [Rat.num_pow]
    have : y.num ^ 2 = ((y.num.natAbs ^ 2 : ℕ) : ℤ) := by
      rw [Int.natCast_pow, Int.natCast_natAbs, sq_abs]
    rw [this, Int.toNat_natCast]
  have hden : (y ^ 2).den = y.den ^ 2 := Rat.den_pow y 2
  rw [if_pos ⟨by rw [hnum, Nat.sqrt_eq', sq], by rw [hden, Nat.sqrt_eq', sq]⟩]
  rfl

/-- Decide `InG`. -/
def inGB : List ℚ → ℚ → Bool
  | [], a => a != 0 && (qsqrt a).isSome
  | g :: s, a => inGB s a || inGB s (a / g)

lemma inGB_iff : ∀ (s : List ℚ), (∀ g ∈ s, g ≠ 0) → ∀ a, inGB s a = true ↔ InG s a
  | [], _, a => by
    simp only [inGB, Bool.and_eq_true, bne_iff_ne, ne_eq, InG]
    constructor
    · rintro ⟨ha, hs⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨h2, -⟩ := qsqrt_spec hy
      exact ⟨y, fun h0 ↦ ha (by rw [← h2, h0]; ring), h2.symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨pow_ne_zero 2 hc, qsqrt_sq c⟩
  | g :: s, hs, a => by
    have hg : g ≠ 0 := hs g (by simp)
    have ih := inGB_iff s (fun g' hg' ↦ hs g' (by simp [hg']))
    simp only [inGB, Bool.or_eq_true, InG]
    rw [ih, ih]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨a / g, h, by field_simp⟩
    · rintro (h | ⟨b, hb, rfl⟩)
      · exact Or.inl h
      · right; rwa [mul_div_cancel_left₀ _ hg]

/-- The product of the selected elements. -/
def prodSub : List ℚ → List Bool → ℚ
  | g :: s, b :: T => (if b then g else 1) * prodSub s T
  | _, _ => 1

/-- `a = c² ∏_{i ∈ T} gᵢ`, `c ≥ 0`. -/
def findRep : List ℚ → ℚ → Option (List Bool × ℚ)
  | [], a => (qsqrt a).map fun c ↦ ([], c)
  | g :: s, a =>
    match findRep s a with
    | some (T, c) => some (false :: T, c)
    | none => (findRep s (a / g)).map fun p ↦ (true :: p.1, p.2)

lemma findRep_spec : ∀ (s : List ℚ), (∀ g ∈ s, g ≠ 0) → ∀ (a : ℚ) (T : List Bool) (c : ℚ),
    findRep s a = some (T, c) → T.length = s.length ∧ a = c ^ 2 * prodSub s T ∧ 0 ≤ c
  | [], _, a, T, c, h => by
    simp only [findRep, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, hyT⟩ := h
    simp only [Prod.mk.injEq] at hyT
    obtain ⟨rfl, rfl⟩ := hyT
    obtain ⟨h2, h0⟩ := qsqrt_spec hy
    exact ⟨rfl, by simp [prodSub, h2], h0⟩
  | g :: s, hs, a, T, c, h => by
    have hg : g ≠ 0 := hs g (by simp)
    have ih := findRep_spec s (fun g' hg' ↦ hs g' (by simp [hg']))
    simp only [findRep] at h
    split at h
    · rename_i T' c' hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih a T' _ hr
      exact ⟨by simp [h1], by simp [prodSub, h2], h3⟩
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨T', c'⟩, hr, hp⟩ := h
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨h1, h2, h3⟩ := ih (a / g) T' _ hr
      refine ⟨by simp [h1], ?_, h3⟩
      simp only [prodSub, if_true]
      rw [show a = g * (a / g) by field_simp, h2]; ring

lemma findRep_isSome : ∀ (s : List ℚ), (∀ g ∈ s, g ≠ 0) → ∀ a, InG s a → (findRep s a).isSome
  | [], _, a, ⟨y, hy, ha⟩ => by
    subst ha
    simp only [findRep, Option.isSome_map]
    exact qsqrt_sq y
  | g :: s, hs, a, h => by
    have hg : g ≠ 0 := hs g (by simp)
    have ih := findRep_isSome s (fun g' hg' ↦ hs g' (by simp [hg']))
    simp only [findRep]
    split
    · rfl
    · rename_i hn
      rw [Option.isSome_map]
      rcases h with h | ⟨b, hb, rfl⟩
      · exact absurd (ih a h) (by rw [hn]; simp)
      · rw [mul_div_cancel_left₀ _ hg]; exact ih b hb

/-- The greedy generators. -/
def gensOf (ks : List ℚ) : List ℚ :=
  ks.foldl (fun gens κ ↦ if κ != 0 && !inGB gens κ then κ :: gens else gens) []

lemma InG_one : ∀ s : List ℚ, InG s 1
  | [] => ⟨1, one_ne_zero, by ring⟩
  | _ :: s => Or.inl (InG_one s)

lemma gensOf_aux : ∀ (ks gens : List ℚ), MIndep gens → (∀ g ∈ gens, g ≠ 0) →
    MIndep (ks.foldl (fun gens κ ↦ if κ != 0 && !inGB gens κ then κ :: gens else gens) gens) ∧
    (∀ g ∈ ks.foldl (fun gens κ ↦ if κ != 0 && !inGB gens κ then κ :: gens else gens) gens,
      g ≠ 0) ∧
    (∀ a, InG gens a →
      InG (ks.foldl (fun gens κ ↦ if κ != 0 && !inGB gens κ then κ :: gens else gens) gens) a) ∧
    ∀ κ ∈ ks, κ ≠ 0 →
      InG (ks.foldl (fun gens κ ↦ if κ != 0 && !inGB gens κ then κ :: gens else gens) gens) κ
  | [], gens, hm, h0 => ⟨hm, h0, fun _ h ↦ h, fun _ h ↦ absurd h (by simp)⟩
  | κ :: ks, gens, hm, h0 => by
    simp only [List.foldl_cons]
    by_cases hκ : (κ != 0 && !inGB gens κ) = true
    · rw [if_pos hκ]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hκ
      have hm' : MIndep (κ :: gens) := ⟨hm, hκ.1, fun h ↦ by
        rw [← inGB_iff gens h0] at h; rw [h] at hκ; exact Bool.noConfusion hκ.2⟩
      have h0' : ∀ g ∈ κ :: gens, g ≠ 0 := fun g hg ↦ by
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hκ.1
        · exact h0 g hg
      obtain ⟨A1, A2, A3, A4⟩ := gensOf_aux ks (κ :: gens) hm' h0'
      refine ⟨A1, A2, fun a ha ↦ A3 a (Or.inl ha), fun κ' hκ' hne ↦ ?_⟩
      rcases List.mem_cons.mp hκ' with rfl | h
      · exact A3 _ (Or.inr ⟨1, InG_one gens, by ring⟩)
      · exact A4 κ' h hne
    · rw [if_neg hκ]
      obtain ⟨A1, A2, A3, A4⟩ := gensOf_aux ks gens hm h0
      refine ⟨A1, A2, A3, fun κ' hκ' hne ↦ ?_⟩
      rcases List.mem_cons.mp hκ' with rfl | h
      · have : inGB gens κ' = true := by
          by_contra hn
          apply hκ
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
          exact ⟨hne, by simpa using hn⟩
        exact A3 _ ((inGB_iff gens h0 _).mp this)
      · exact A4 κ' h hne

/-- **The generators.** -/
theorem gensOf_spec (ks : List ℚ) :
    MIndep (gensOf ks) ∧ (∀ g ∈ gensOf ks, g ≠ 0) ∧ ∀ κ ∈ ks, κ ≠ 0 → InG (gensOf ks) κ := by
  obtain ⟨A1, A2, -, A4⟩ := gensOf_aux ks [] trivial (fun _ h ↦ absurd h (by simp))
  exact ⟨A1, A2, A4⟩

section Alg

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

variable (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))

/-- The squared residues. -/
def kqKs : List ℚ := (List.range cs.length).map (kqK Fc ks m η A B l cs)

/-- The generators of the square classes. -/
def kqGens : List ℚ := gensOf (kqKs Fc ks m η A B l cs)

/-- The class `T_q` and the rational `c_q` with `κ_q = c_q² ∏_{T_q} g`. -/
def kqRep (q : ℕ) : List Bool × ℚ :=
  (findRep (kqGens Fc ks m η A B l cs) (kqK Fc ks m η A B l cs q)).getD ([], 0)

/-- The classes. -/
def kqCls : List (List Bool) :=
  ((List.range cs.length).map fun q ↦ (kqRep Fc ks m η A B l cs q).1).dedup

/-- The common denominator of the `c_q`. -/
def kqDenM : ℕ := ((List.range cs.length).map fun q ↦ (kqRep Fc ks m η A B l cs q).2.den).prod

/-- The multiplicity `M c_q ∈ ℕ`. -/
def kqMNm (q : ℕ) : ℕ :=
  (((kqDenM Fc ks m η A B l cs / (kqRep Fc ks m η A B l cs q).2.den : ℕ) : ℤ) *
    (kqRep Fc ks m η A B l cs q).2.num).toNat

/-- The class value `s_T = ∏_T g`. -/
def kqS (T : List Bool) : ℚ := prodSub (kqGens Fc ks m η A B l cs) T

/-- The ordinate `s_T c_q (η − c_q′) R_q / B(c_q)` on `ỹ² = s_T A`. -/
def kqBm (q : ℕ) : LC m :=
  let O := MO Fc ks m
  normC Fc m (O.mul (mcst Fc ks m (kqS Fc ks m η A B l cs (kqRep Fc ks m η A B l cs q).1 *
      (kqRep Fc ks m η A B l cs q).2))
    (O.mul (kqD Fc ks m η cs q) (O.mul (kqR Fc ks m A l cs q)
      (O.inv (evalGC Fc ks m B (kqC Fc ks m cs q))))))

/-- The poles of the class `T`. -/
def kqQs (T : List Bool) : List ℕ :=
  (List.range cs.length).filter fun q ↦ (kqRep Fc ks m η A B l cs q).1 == T

/-- The twisted polynomial `s_T A` over `Kₘ`. -/
def kqFKm (T : List Bool) : CPoly (KF Fc m) :=
  CPoly.trim ((A.map ((MO Fc ks m).mul (mcst Fc ks m (kqS Fc ks m η A B l cs T)))).map (trC Fc m))

/-- The points of the class `T` over `Kₘ`. -/
def kqAlm (T : List Bool) : Fin (kqQs Fc ks m η A B l cs T).length → KF Fc m :=
  fun i ↦ trC Fc m (kqC Fc ks m cs ((kqQs Fc ks m η A B l cs T)[i]))

def kqBem (T : List Bool) : Fin (kqQs Fc ks m η A B l cs T).length → KF Fc m :=
  fun i ↦ trC Fc m (kqBm Fc ks m η A B l cs ((kqQs Fc ks m η A B l cs T)[i]))

def kqMqm (T : List Bool) : Fin (kqQs Fc ks m η A B l cs T).length → ℕ :=
  fun i ↦ kqMNm Fc ks m η A B l cs ((kqQs Fc ks m η A B l cs T)[i])

/-- Every squared residue has a representation. -/
def kqRepOK : Bool :=
  (List.range cs.length).all fun q ↦
    (findRep (kqGens Fc ks m η A B l cs) (kqK Fc ks m η A B l cs q)).isSome

/-- The torsion answer of one class. -/
def kqTorsC (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (T : List Bool) : Option (Option ℕ) :=
  torsOracleC (redAtKF Fc m rs) (cpf (kqFKm Fc ks m η A B l cs T)) ps bound
    (kqFKm Fc ks m η A B l cs T) 2
    (gammaL (kqAlm Fc ks m η A B l cs T) (kqBem Fc ks m η A B l cs T)
      (kqMqm Fc ks m η A B l cs T) 1)

/-- The witness of one class (order `N`). -/
def kqWit (T : List Bool) (N : ℕ) : Option (BPoly (KF Fc m)) :=
  witW (kqFKm Fc ks m η A B l cs T) 2 ((kqFKm Fc ks m η A B l cs T).length - 1)
    (kqAlm Fc ks m η A B l cs T) (kqBem Fc ks m η A B l cs T) (kqMqm Fc ks m η A B l cs T) N

/-- The column `B_W` of one class. -/
def kqCol (T : List Bool) (Wb : BPoly (KF Fc m)) : LC (m + 1) :=
  normC Fc (m + 1) (logCol Fc ks m
    (A.map ((MO Fc ks m).mul (mcst Fc ks m (kqS Fc ks m η A B l cs T))))
    ((Wb.getD 0 []).map (unTr Fc m)) ((Wb.getD 1 []).map (unTr Fc m)) (MO Fc ks m).one)

/-- **The decision, several residue classes** (`none`: data not accepted, or a torsion oracle
did not answer within its bounds). -/
def kqmDecideC (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option Bool :=
  let O := MO Fc ks m
  let rhs : LC (m + 1) := (B, GPoly.mul O (prodLinG Fc ks m cs) (powG O A l))
  let frA := kpFr Fc ks m 1 2 A
  let cls := kqCls Fc ks m η A B l cs
  if cs.length = 0 then none
  else if !kqOK Fc ks m A B l cs then none
  else if !kqConst Fc ks m η A B l cs then some false
  else if !kqRepOK Fc ks m η A B l cs then none
  else
    let tors := cls.map (kqTorsC Fc ks m η A B l cs cpf ps bound rs)
    if tors.any (· == none) then none
    else if tors.any (· == some none) then some false
    else
      let wits := (List.zip cls tors).map fun p ↦
        kqWit Fc ks m η A B l cs p.1 ((p.2.getD none).getD 0)
      match wits.allSome with
      | none => none
      | some Wbs =>
        let cols := (List.zip cls Wbs).map fun p ↦ kqCol Fc ks m η A B l cs p.1 p.2
        some ((prdeC Fc ks lv (m + 1) frA (rhs :: cols)).any fun r ↦ decide (r.1.getD 0 0 ≠ 0))

/-- The torsion answer of one class (certificates by search modulo `p`). -/
def kqTors (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (T : List Bool) : Option (Option ℕ) :=
  kqTorsC Fc ks m η A B l cs (fun fK ↦ searchCert fK 2) ps bound rs T

/-- **The decision, several residue classes** (certificates by search modulo `p`). -/
def kqmDecide (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kqmDecideC Fc ks lv m η A B l cs (fun fK ↦ searchCert fK 2) ps bound rs

/-- **The decision with local torsion certificates** (answers for every large bound at suitable
residues, `kqmDecideL_decides`). -/
def kqmDecideL (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  kqmDecideC Fc ks lv m η A B l cs (fun fK ↦ localCert fK 2) ps bound rs

end Alg

end Curves.MT
