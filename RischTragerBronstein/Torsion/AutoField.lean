import RischTragerBronstein.Torsion.AutoLog
import RischTragerBronstein.Algebraic.NFSplit
import RischTragerBronstein.Algebraic.NFRootFinder
import RischTragerBronstein.Algebraic.NFRootsZ
import RischTragerBronstein.Algebraic.SupRedOracle

/-!
# The field-extension loop

For an integrand over `ℚ`, `decideLoop` runs the automatic decision over number fields
`ℚ[γ]/(M)`: `probeMissing` finds the first polynomial whose roots the pipeline needs but which does
not split (special points, edge polynomials of the Newton polygons, roots of unity), `extStep`
adjoins a root (Trager's primitive element: the new field contains the old one), and the
pipeline restarts over the larger field. The root finder is the complete `rfNF` or, with
`fast = true`, the Zassenhaus-based `rfNFZ` (candidates checked by multiplicities). The
certificates of the integrand are recomputed with the extra precisions `exs` in turn (a log
witness with a large multiplier needs more precision along the branches).

**`decideLoop_spec`**: every answer is correct for the integrand over `ℚ` (on any curve over an
algebraically closed field of constants).
-/

namespace Curves

open CPoly Sup EllQuad.QCoords

section Probe

variable {F : Type*} [Field F] [DecidableEq F]

/-- The first missing polynomial along the branches above `a` (edge polynomials and the
polynomials `Tᴱ − 1`, `Tᴺ − 1`). -/
def probeAt (rf : RootFinder F) (G : BPoly F) (a : F) (L fuel : ℕ) : Option (CPoly F) :=
  match puiseuxAt rf G a L fuel with
  | .error g => some g
  | .ok bs =>
    let N := bs.foldr (fun b m ↦ Nat.lcm b.E m) 1
    ((N :: bs.map PBranch.E).map fun E ↦ xnm1 (F := F) E).find? fun P ↦ (rf P).isNone

/-- **The first polynomial whose roots are missing**, for the curve `Fc` (weights `k`, `kI`) and
the denominator `D`. -/
def probeMissing (rf : RootFinder F) (Fc : BPoly F) (n k kI : ℕ) (D : CPoly F) (L fuel : ℕ) :
    Option (CPoly F) :=
  let R0 := trim (mul (discRC Fc n k) D)
  if R0.length ≤ 1 then none else
  match rf R0 with
  | none => some R0
  | some rs =>
    (rs.map fun a ↦ probeAt rf Fc a L fuel).findSome? id |>.orElse fun _ ↦
      (probeAt rf (invB Fc k (k * n)) 0 L fuel).orElse fun _ ↦
        probeAt rf (invB Fc kI (kI * n)) 0 L fuel

end Probe

section Loop

variable (P0 : CurveProb ℚ)

/-- The integer coefficients of `M` (if integral). -/
def intCoeffs (M : CPoly ℚ) : Option (List ℤ) :=
  if M.all fun q ↦ q.den = 1 then some (M.map Rat.num) else none

/-- The reductions of `ℚ[γ]/(M)`. -/
def redAtM (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] : (p : ℕ) → Option (RedFns p (NFC.NF M)) :=
  match intCoeffs M with
  | some mZ => Sup.nfRedAt (M := M) mZ
  | none => fun _ ↦ none

/-- Candidate pairs of primes for the field `ℚ[γ]/(M)`: the first primes (from `11` on) at which
`M` has a certified reduction (`redAtM`), paired consecutively. -/
def autoPairs (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (count : ℕ) : List (ℕ × ℕ) :=
  let ps := ((List.range 3000).filter fun p ↦ decide (11 ≤ p) && decide p.Prime &&
    (redAtM M p).isSome).take (2 * count)
  (List.range count).filterMap fun i ↦
    match ps[2 * i]?, ps[2 * i + 1]? with
    | some p, some q => some (p, q)
    | _, _ => none

/-- The first `k` numbers `≥ i` satisfying `P`, among `fuel` candidates (a lazy
`((List.range' i fuel).filter P).take k`). -/
def scanTake (P : ℕ → Bool) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | _ + 1, _, 0 => []
  | f + 1, i, k + 1 => if P i then i :: scanTake P f (i + 1) k else scanTake P f (i + 1) (k + 1)

lemma scanTake_eq (P : ℕ → Bool) : ∀ (f i k : ℕ),
    scanTake P f i k = ((List.range' i f).filter P).take k
  | 0, _, _ => by simp [scanTake]
  | _ + 1, _, 0 => by simp [scanTake]
  | f + 1, i, k + 1 => by
    rw [scanTake, List.range'_succ, List.filter_cons]
    split_ifs with h
    · rw [List.take_succ_cons, scanTake_eq P f (i + 1) k]
    · rw [scanTake_eq P f (i + 1) (k + 1)]

/-- `autoPairs` stopping at the first `2 count` primes: the compiled code. -/
def autoPairsF (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (count : ℕ) : List (ℕ × ℕ) :=
  let ps := scanTake (fun p ↦ decide (11 ≤ p) && decide p.Prime && (redAtM M p).isSome) 3000 0
    (2 * count)
  (List.range count).filterMap fun i ↦
    match ps[2 * i]?, ps[2 * i + 1]? with
    | some p, some q => some (p, q)
    | _, _ => none

@[csimp] theorem autoPairs_eq_autoPairsF : @autoPairs = @autoPairsF := by
  funext M _ count
  simp only [autoPairs, autoPairsF, scanTake_eq, List.range_eq_range']

/-- One stage: the decision over `ℚ[γ]/(M)`, or the polynomial to adjoin (with `pqs = []`, the
primes are chosen by `autoPairs`). -/
def stageNF (fast : Bool) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (kI : ℕ) (exs : List ℕ)
    (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) : Except (CPoly (NFC.NF M)) (Option Bool) :=
  let φ := algebraMap ℚ (NFC.NF M)
  let rf := if fast then NFC.rfNFZ M else NFC.rfNF M
  let Fc := P0.Fc.map (·.map φ)
  let A := P0.A.map (·.map φ)
  let D := P0.D.map φ
  let pqs := if pqs.isEmpty then autoPairs M 3 else pqs
  match probeMissing rf Fc P0.n P0.k kI D L fuel with
  | some g => .error g
  | none =>
    .ok ((autoGlobal rf Fc P0.n kI ex fuel).bind fun T ↦
      exs.findSome? fun e ↦ (autoCurveProb rf Fc P0.n P0.k A D e).bind fun P ↦
        pqs.findSome? fun pq ↦
          decideAutoFull rf (redAtM M) (P0.baseChange φ P0.k P.pts P.inf) T L tp B pq.1 pq.2)

/-- The part of `g` without roots in `K` (after removing the linear factors of the roots found):
adjoining a root of it enlarges the field. -/
def remRoots (fast : Bool) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (g : CPoly (NFC.NF M)) :
    CPoly (NFC.NF M) :=
  let g := sqfreePart g
  let rs := ((if fast then NFC.rootsInZ M g else NFC.rootsIn M g).getD []).dedup
  (divMod g (EllQuad.prodLin rs)).1

/-- **The loop over number fields** (fuel `m`). -/
def decideLoop (fast : Bool) (kI : ℕ) (exs : List ℕ) (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) :
    ℕ → (M : CPoly ℚ) → Kron.irredQ M = true → Option Bool
  | 0, _, _ => none
  | m + 1, M, hM =>
    haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    match stageNF P0 fast M kI exs ex fuel L tp B pqs with
    | .ok r => r
    | .error g =>
      match NFC.extStep M (remRoots fast M g) with
      | some ⟨M', hM'⟩ => decideLoop fast kI exs ex fuel L tp B pqs m M' hM'
      | none => none

end Loop

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

lemma redAtM_valid (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] :
    ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p (NFC.NF M)), redAtM M p = some R →
      ∃ φ : NFC.NF M →+* ℚ_[p], RedValid p R φ := by
  intro p _ R h
  cases hc : intCoeffs M with
  | none => simp [redAtM, hc] at h
  | some mZ =>
    simp only [redAtM, hc] at h
    refine Sup.nfRedAt_valid mZ ?_ p R h
    unfold intCoeffs at hc
    split_ifs at hc with hall
    obtain rfl := Option.some.inj hc
    rw [← Sup.toPoly_mapHom, List.map_map]
    congr 1
    conv_lhs => rw [← List.map_id M]
    refine List.map_congr_left fun q hq ↦ ?_
    have := (List.all_eq_true.mp hall) q hq
    simp only [decide_eq_true_eq] at this
    simp [Function.comp_apply, Rat.coe_int_num_of_den_eq_one this]

open IntermediateField Differential Polynomial in
/-- **Soundness of the loop over number fields.** -/
theorem decideLoop_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (P0 : CurveProb ℚ)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc)))
    (fast : Bool) (kI : ℕ) (exs : List ℕ) (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) :
    ∀ (m : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (b : Bool),
      decideLoop P0 fast kI exs ex fuel L tp B pqs m M hM = some b →
      (HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true) := by
  intro m
  induction m with
  | zero => intro M hM b h; exact absurd h (by simp [decideLoop])
  | succ m ih =>
    intro M hM b h
    have : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    unfold decideLoop at h
    split at h
    · rename_i r hr
      -- a stage answered
      unfold stageNF at hr
      dsimp only at hr
      split at hr
      · exact absurd hr (by simp)
      · obtain rfl := Except.ok.inj hr
        simp only [Option.bind_eq_some_iff, List.findSome?_eq_some_iff] at h
        obtain ⟨T, -, -, e, -, -, ⟨P, -, l1, pq, l2, -, hpq, -⟩, -⟩ := h
        set ι : NFC.NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NFC.NF M) (M := Kc)).toRingHom
        have hι : ι.comp (algebraMap ℚ (NFC.NF M)) = algebraMap ℚ Kc := Subsingleton.elim _ _
        have hSF' : S.F = (toB (P0.baseChange (algebraMap ℚ (NFC.NF M)) P0.k P.pts P.inf).Fc).map
            (mapRingHom ι) := by
          rw [hSF, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]
        have key := decideAutoFull_spec hC S hx hgen _ (redAtM M) (redAtM_valid M)
          _ ι hSF' T L tp B pq.1 pq.2 b hpq
        rwa [S.fE_baseChange, hι] at key
    · rename_i g hg
      split at h
      · rename_i M' hM' _
        exact ih M' hM' b h
      · exact absurd h (by simp)

end Main

end Curves
