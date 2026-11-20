import RischTragerBronstein.Mixed.KXMain
import RischTragerBronstein.Mixed.KXForwardDep

/-!
# The Mordell–Weil exception with dependent classes: the decision is correct

`kxDecideD_correct`: whenever `kxDecideD` (`kxDecide`, then the search for relations
`N Δ_T ± M δ₀ ∼ 0` when `P₊ − ∞` is not torsion) answers `some b`, the integral is elementary
exactly when `b = true`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section Spec

variable [Fact (Irreducible (toPoly (fKc Fc)))]

/-- What a witness of `kxWitAny` is. -/
lemma kxWitAny_spec (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (z : LC m) (nmax : ℕ) (T : List Bool) (t : Option (Option ℕ)) (Wb : BPoly (KF Fc m))
    (h : kxWitAny Fc ks m g A B kt l cs z nmax T t = some Wb) :
    ∃ (N M : ℕ) (bt : KF Fc m), (t = some (some N) ∧ kxWit Fc ks m g A B kt l cs T N = some Wb ∧
      M = 0) ∨ (1 ≤ N ∧ kxWitD Fc ks m g A B kt l cs T bt N M = some Wb ∧
        bt * bt = (kxFKm Fc ks m g A B kt l cs T).getD 0 0 ∧ bt ≠ 0) := by
  unfold kxWitAny at h
  rcases t with _ | _ | N
  · exact absurd h (by simp)
  · simp only at h
    unfold kxDepSearch at h
    split at h
    · exact absurd h (by simp)
    rename_i b hb
    obtain ⟨c, hc, hcW⟩ := List.exists_of_findSome?_eq_some h
    unfold kxDepTry at hcW
    split_ifs at hcW with hchk
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hchk
    obtain ⟨N, M, bt⟩ := c
    unfold kxDepCands at hc
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨N', -, M', -, hc⟩ := hc
    have hN : N = N' + 1 := by rcases hc with h | h <;> exact (Prod.ext_iff.mp h).1
    exact ⟨N, M, bt, Or.inr ⟨by omega, hcW, hchk.1, hchk.2⟩⟩
  · exact ⟨N, 0, 0, Or.inl ⟨rfl, h, rfl⟩⟩

omit [CharZero Cc] [CharZero L] in
/-- **The parametric equation of `kxSolveDepC`.** -/
lemma kxSolveDep_spec (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (z : LC m) (nmax : ℕ) (b : Bool)
    (h : kxSolveDepC Fc ks lv m g A B kt l cs cpf ps bound rs z nmax = some b) :
    ∃ (Ns Ms : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
      (bts : Fin (kxCls Fc ks m g A B kt l cs).length → KF Fc m)
      (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m)),
      (∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
        (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
          some (some (Ns k)) ∧
          kxWit Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Ns k) = some (Wbs k) ∧
          Ms k = 0) ∨
        (1 ≤ Ns k ∧ kxWitD Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (bts k)
            (Ns k) (Ms k) = some (Wbs k) ∧
          bts k * bts k =
            (kxFKm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).getD 0 0 ∧
          bts k ≠ 0)) ∧
      b = (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
        (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) ::
          List.ofFn fun k ↦ kxCol Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]
            (Wbs k))).any (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) := by
  set cls := kxCls Fc ks m g A B kt l cs with hcls
  set tors := cls.map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs) with htorsdef
  unfold kxSolveDepC at h
  dsimp only at h
  generalize hw : ((List.zip cls tors).map fun p ↦
    kxWitAny Fc ks m g A B kt l cs z nmax p.1 p.2).allSome = ow at h
  rcases ow with _ | Wbl
  · exact absurd h (by simp)
  obtain ⟨hWl, hWv⟩ := MTower.allSome_spec _ Wbl hw
  have hlc : (List.zip cls tors).length = cls.length := by simp [htorsdef]
  have hWl' : Wbl.length = cls.length := by rw [hWl, List.length_map, hlc]
  set Wbs : Fin cls.length → BPoly (KF Fc m) := fun k ↦ Wbl[(k : ℕ)]'(by rw [hWl']; exact k.2)
    with hWbs
  have hwa : ∀ k : Fin cls.length, kxWitAny Fc ks m g A B kt l cs z nmax cls[(k : ℕ)]
      (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs cls[(k : ℕ)]) = some (Wbs k) := fun k ↦ by
    have := hWv k (by rw [List.length_map, hlc]; exact k.2) (by rw [hWl']; exact k.2)
    simpa [List.getElem_map, List.getElem_zip, htorsdef] using this
  have hex := fun k ↦ kxWitAny_spec m g A B kt l cs z nmax _ _ _ (hwa k)
  choose Ns Ms bts hNMb using hex
  have hcols : (List.zip cls Wbl).map (fun p ↦ kxCol Fc ks m g A B kt l cs p.1 p.2) =
      List.ofFn fun k : Fin cls.length ↦ kxCol Fc ks m g A B kt l cs cls[(k : ℕ)] (Wbs k) := by
    apply List.ext_getElem
    · simp [hWl']
    · intro i h1 h2
      simp [List.getElem_zip, hWbs]
  simp only at h
  refine ⟨Ns, Ms, bts, Wbs, hNMb, ?_⟩
  rw [← hcols]
  exact (Option.some.inj h).symm

end Spec

namespace MTower

variable (T : MTower Fc ks Cc L)

section Main

variable [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecideDepC` is correct**: whenever it answers `some b`, the integral is elementary
exactly when `b = true`. -/
theorem kxDecideDepC_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (nmax : ℕ)
    (b : Bool) (hdec : kxDecideDepC Fc ks lv m g A B kt l cs cpf ps bound rs nmax = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔
      b = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  unfold kxDecideDepC at hdec
  dsimp only at hdec
  by_cases hr0 : cs.length = 0
  · rw [if_pos hr0] at hdec; exact absurd hdec (by simp)
  rw [if_neg hr0] at hdec
  by_cases hok : kxOK Fc ks m A B kt l cs = true
  swap
  · rw [if_pos (by simpa using hok)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hok])] at hdec
  by_cases hcst : kxConst Fc ks m g A B kt l cs = true
  swap
  · rw [if_pos (by simpa using hcst)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hcst])] at hdec
  by_cases hrep : kxRepOK Fc ks m g A B kt l cs = true
  swap
  · rw [if_pos (by simpa using hrep)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hrep])] at hdec
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs).2
  by_cases hnone : ((kxCls Fc ks m g A B kt l cs).map
      (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)).any (· == none) = true
  · rw [if_pos hnone] at hdec; exact absurd hdec (by simp)
  rw [if_neg hnone] at hdec
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hok0.1
  rcases hz : kxZ Fc ks lv m A with _ | z
  · simp only [hz] at hdec; exact absurd hdec (by simp)
  simp only [hz] at hdec
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  obtain ⟨hz0, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q0 z hq0
  have hκs : ∀ κ' ∈ kxKap Fc ks m A z :: kxGens Fc ks m g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
    rcases List.mem_cons.mp h with rfl | h
    · exact hκ0
    · exact hg0 κ' h
  rcases ht0 : kxTors0C Fc ks m A cpf ps bound rs z with _ | _ | N
  · simp only [ht0] at hdec; exact absurd hdec (by simp)
  swap
  · simp only [ht0] at hdec; exact absurd hdec (by simp)
  simp only [ht0] at hdec
  obtain ⟨Ns, Ms, bts, Wbs, hwit, rfl⟩ := kxSolveDep_spec m g A B kt l cs ps bound rs cpf z nmax b hdec
  constructor
  · intro hf
    obtain ⟨E, _, _, _, TE, θE, rts0, ι, sI, c, u, v, hTEn, hθE, hrl0, hrts0, hcd, hu, hv, heq⟩ :=
      T.kqm_lift m hn A θ hθ hgen _ hf _ hκs
    obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
    exact TE.kx_forward_dep hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst hrep ps
      bound rs cpf Ns Ms bts Wbs hwit z s hz ht0 hs2 hs' θE hθE sI c u hcd hu v hv heq rts hrl hrts
  · intro h
    have h' := h
    rw [← List.nil_append (List.ofFn _)] at h'
    exact (T.kx_backward m hTr g A B kt l cs θ hθ hA0 [] (by simp) Wbs hspecA
      h').hasElementaryIntegral

open Classical in
/-- **`kxDecideD` is correct**: whenever it answers `some b`, the integral of
`B(t) θ / (tᵏ ∏_q (t − c_q) A(t)ˡ)` is elementary exactly when `b = true`. -/
theorem kxDecideD_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (nmax : ℕ) (b : Bool) (hdec : kxDecideD Fc ks lv m g A B kt l cs ps bound rs nmax = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔
      b = true := by
  unfold kxDecideD at hdec
  cases hkx : kxDecide Fc ks lv m g A B kt l cs ps bound rs with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecide_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound rs
      _ hkx
  | none =>
    rw [hkx] at hdec
    exact T.kxDecideDepC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs _ nmax b hdec

end Main

end MTower

end Curves.MT
