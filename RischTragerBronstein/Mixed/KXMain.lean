import RischTragerBronstein.Mixed.KXForward

/-!
# Square roots over an exponential level with poles: the decision is correct

`kxDecide_correct`: whenever `kxDecide` answers `some b`,
`∫ B(t) θ / (tᵏ ∏ (t − c_q) A(t)ˡ)` (`θ² = A(t)`, `t` an exponential level of a certified tower,
poles at `c_q ≠ 0` with residues in any number of classes `ℚ √s`) is elementary iff `b = true`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

section Main

variable [Fact (Irreducible (toPoly (fKc Fc)))]

omit [CharZero Cc] [CharZero L] in
/-- **The parametric equation of `kxSolve`**: all classes torsion, with their witnesses. -/
lemma kxSolve_spec (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (extra : List (LC (m + 1))) (b : Bool)
    (hnone : ¬ ((kxCls Fc ks m g A B kt l cs).map
      (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)).any (· == none) = true)
    (hsn : ¬ ((kxCls Fc ks m g A B kt l cs).map
      (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)).any (· == some none) = true)
    (h : kxSolveC Fc ks lv m g A B kt l cs cpf ps bound rs extra = some b) :
    ∃ (Ns : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
      (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m)),
      (∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
        kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
          some (some (Ns k))) ∧
      (∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
        kxWit Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Ns k) = some (Wbs k)) ∧
      b = (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
        (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: (extra ++
          List.ofFn fun k ↦ kxCol Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]
            (Wbs k)))).any (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) := by
  set cls := kxCls Fc ks m g A B kt l cs with hcls
  set tors := cls.map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs) with htorsdef
  have hall : ∀ k : Fin cls.length, ∃ N, kxTorsC Fc ks m g A B kt l cs cpf ps bound rs cls[(k : ℕ)] =
      some (some N) := by
    intro k
    rcases h : kxTorsC Fc ks m g A B kt l cs cpf ps bound rs cls[(k : ℕ)] with _ | _ | N
    · exfalso; apply hnone
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem k.2, h⟩, by simp⟩
    · exfalso; apply hsn
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem k.2, h⟩, by simp⟩
    · exact ⟨N, rfl⟩
  choose Ns hNs using hall
  have hNs' : ∀ k : Fin cls.length,
      ((tors[(k : ℕ)]'(by simp [htorsdef])).getD none).getD 0 = Ns k := fun k ↦ by
    simp [htorsdef, hNs k]
  unfold kxSolveC at h
  dsimp only at h
  generalize hw : ((List.zip cls tors).map fun p ↦
    kxWit Fc ks m g A B kt l cs p.1 ((p.2.getD none).getD 0)).allSome = ow at h
  rcases ow with _ | Wbl
  · exact absurd h (by simp)
  obtain ⟨hWl, hWv⟩ := allSome_spec _ Wbl hw
  have hlc : (List.zip cls tors).length = cls.length := by simp [htorsdef]
  have hWl' : Wbl.length = cls.length := by rw [hWl, List.length_map, hlc]
  set Wbs : Fin cls.length → BPoly (KF Fc m) := fun k ↦ Wbl[(k : ℕ)]'(by rw [hWl']; exact k.2)
    with hWbs
  have hwit : ∀ k : Fin cls.length,
      kxWit Fc ks m g A B kt l cs cls[(k : ℕ)] (Ns k) = some (Wbs k) := fun k ↦ by
    have := hWv k (by rw [List.length_map, hlc]; exact k.2) (by rw [hWl']; exact k.2)
    simp only [List.getElem_map, List.getElem_zip] at this
    rw [hNs' k] at this
    exact this
  have hcols : (List.zip cls Wbl).map (fun p ↦ kxCol Fc ks m g A B kt l cs p.1 p.2) =
      List.ofFn fun k : Fin cls.length ↦ kxCol Fc ks m g A B kt l cs cls[(k : ℕ)] (Wbs k) := by
    apply List.ext_getElem
    · simp [hWl']
    · intro i h1 h2
      simp [List.getElem_zip, hWbs]
  simp only at h
  refine ⟨Ns, Wbs, hNs, hwit, ?_⟩
  rw [← hcols]
  exact (Option.some.inj h).symm

/-- **Backward**: a solution of the parametric equation gives an antiderivative. -/
theorem kx_backward (m : ℕ) (hTr : T.Tr (m + 1)) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (θ : L) (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0)
    (extra : List (LC (m + 1)))
    (hextra : ∀ c ∈ extra, ∀ q : ℚ, HasElementaryIntegralIn ((q : L) * (T.ev (m + 1) c * θ)))
    (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m))
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (h : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
        (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: (extra ++
          List.ofFn fun k ↦ kxCol Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]
            (Wbs k)))).any (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true) :
    HasElementaryIntegralIn (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) := by
  refine T.prde_backward_gen m hTr A θ hθ hA0 hspec _ _ (fun c hc q ↦ ?_) h
  rcases List.mem_append.mp hc with hc | hc
  · exact hextra c hc q
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs).2
    rw [kxCol, T.ev_normC (m + 1) hTr]
    exact T.kq_hcolIn m hTr A θ hθ hA0 _ (prodSub_ne _ hg0 _) _ _ q

/-- The column of `P₊ − ∞` is elementary. -/
lemma kx_col0_hei (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0) (z : LC m) (hz0 : T.ev m z ≠ 0)
    (hκ0 : kxKap Fc ks m A z ≠ 0) (W0b : BPoly (KF Fc m)) :
    ∀ c ∈ [kxCol0 Fc ks m A z W0b], ∀ q : ℚ,
      HasElementaryIntegralIn ((q : L) * (T.ev (m + 1) c * θ)) := by
  intro c hc q
  rw [List.mem_singleton] at hc
  subst hc
  rw [kxCol0, T.ev_normC (m + 1) hTr]
  exact T.hcolIn m hTr A θ hθ hA0 z hz0 _ hκ0 _ _ q

omit [CharZero Cc] [CharZero L] in
lemma roots_cons {E : Type*} [Field E] [Differential E] (κ : ℚ) (gens : List ℚ) (rts : List E)
    (hrl : rts.length = (κ :: gens).length)
    (hrts : ∀ i (hi : i < rts.length) (hi' : i < (κ :: gens).length),
      rts[i] ^ 2 = ((κ :: gens)[i] : E) ∧ rts[i]′ = 0) :
    ∃ (s : E) (rts' : List E), s ^ 2 = (κ : E) ∧ s′ = 0 ∧ rts'.length = gens.length ∧
      ∀ i (hi : i < rts'.length) (hi' : i < gens.length), rts'[i] ^ 2 = (gens[i] : E) ∧ rts'[i]′ = 0 := by
  cases rts with
  | nil => simp at hrl
  | cons s rts' =>
    have h0 := hrts 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    refine ⟨s, rts', h0.1, h0.2, by simpa using hrl, fun i hi hi' ↦ ?_⟩
    have := hrts (i + 1) (by simp; omega) (by simp; omega)
    simpa using this

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θ / (tᵏ ∏_q (t − c_q) A(t)ˡ)` (`θ² = A(t)`, `t` an exponential level of a certified tower)
is elementary exactly when `b = true`. -/
theorem kxDecideC_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (b : Bool) (hdec : kxDecideC Fc ks lv m g A B kt l cs cpf ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔
      b = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  unfold kxDecideC at hdec
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
  · rw [if_pos (by simpa using hcst)] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨E, _, _, _, TE, θE, -, ι, sI, c, u, v, hTEn, hθE, -, -, hcd, hu, hv, heq⟩ :=
      T.kq_lift m hn A θ hθ hgen _ hf 1 one_ne_zero
    exact hcst (TE.kx_forward_const hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok θE hθE
      sI c u hcd hu v hv heq)
  rw [if_neg (by simp [hcst])] at hdec
  by_cases hrep : kxRepOK Fc ks m g A B kt l cs = true
  swap
  · rw [if_pos (by simpa using hrep)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hrep])] at hdec
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs).2
  set cls := kxCls Fc ks m g A B kt l cs with hcls
  set tors := cls.map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs) with htorsdef
  by_cases hnone : tors.any (· == none) = true
  · rw [if_pos hnone] at hdec; exact absurd hdec (by simp)
  rw [if_neg hnone] at hdec
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hok0.1
  -- a class without torsion
  have hnt_k : tors.any (· == some none) = true → ∃ k : Fin cls.length,
      kxTorsC Fc ks m g A B kt l cs cpf ps bound rs cls[(k : ℕ)] = some none := fun hsn ↦ by
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp hsn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < cls.length := by simpa [htorsdef] using hi
    refine ⟨⟨i, hi'⟩, ?_⟩
    have := hx0; simp only [beq_iff_eq] at this; simpa [htorsdef] using this
  rcases hz : kxZ Fc ks lv m A with _ | z
  · -- `A(0)` not a square in `Fₘ`
    simp only [hz] at hdec
    by_cases hsn : tors.any (· == some none) = true
    · rw [if_neg (by simp [hsn])] at hdec
      obtain rfl := Option.some.inj hdec
      simp only [Bool.false_eq_true, iff_false]
      intro hf
      obtain ⟨k, htk⟩ := hnt_k hsn
      obtain ⟨E, _, _, _, TE, θE, rts, ι, sI, c, u, v, hTEn, hθE, hrl, hrts, hcd, hu, hv, heq⟩ :=
        T.kqm_lift m hn A θ hθ hgen _ hf (kxGens Fc ks m g A B kt l cs) hg0
      exact TE.kx_forward_nontors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst hrep
        ps bound rs cpf k htk (Or.inl hz) θE hθE sI c u hcd hu v hv heq rts hrl hrts
    · rw [if_pos (by simp [hsn])] at hdec
      obtain ⟨Ns, Wbs, hNs, hwit, rfl⟩ :=
        kxSolve_spec m g A B kt l cs ps bound rs cpf [] b hnone hsn hdec
      simp only [List.nil_append]
      constructor
      · intro hf
        obtain ⟨E, _, _, _, TE, θE, rts, ι, sI, c, u, v, hTEn, hθE, hrl, hrts, hcd, hu, hv, heq⟩ :=
          T.kqm_lift m hn A θ hθ hgen _ hf (kxGens Fc ks m g A B kt l cs) hg0
        exact TE.kx_forward_tors_mu0 hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst
          hrep ps bound rs cpf Ns hNs Wbs hwit (Or.inl hz) θE hθE sI c u hcd hu v hv heq rts hrl hrts
      · intro h
        have h' := h
        rw [← List.nil_append (List.ofFn _)] at h'
        exact (T.kx_backward m hTr g A B kt l cs θ hθ hA0 [] (by simp) Wbs hspecA
          h').hasElementaryIntegral
  · -- `A(0) = κ/z²`
    simp only [hz] at hdec
    obtain ⟨q0, hq0⟩ := kxZ_some hz
    obtain ⟨hz0, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q0 z hq0
    have hκs : ∀ κ' ∈ kxKap Fc ks m A z :: kxGens Fc ks m g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
      rcases List.mem_cons.mp h with rfl | h
      · exact hκ0
      · exact hg0 κ' h
    rcases ht0 : kxTors0C Fc ks m A cpf ps bound rs z with _ | _ | N
    · simp only [ht0] at hdec; exact absurd hdec (by simp)
    · -- `P₊ − ∞` not torsion
      simp only [ht0] at hdec
      by_cases hsn : tors.any (· == some none) = true
      · rw [if_neg (by simp [hsn])] at hdec; exact absurd hdec (by simp)
      rw [if_pos (by simp [hsn])] at hdec
      obtain ⟨Ns, Wbs, hNs, hwit, rfl⟩ :=
        kxSolve_spec m g A B kt l cs ps bound rs cpf [] b hnone hsn hdec
      simp only [List.nil_append]
      constructor
      · intro hf
        obtain ⟨E, _, _, _, TE, θE, rts0, ι, sI, c, u, v, hTEn, hθE, hrl0, hrts0, hcd, hu, hv, heq⟩ :=
          T.kqm_lift m hn A θ hθ hgen _ hf _ hκs
        obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
        exact TE.kx_forward_tors_mu0 hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst
          hrep ps bound rs cpf Ns hNs Wbs hwit (Or.inr ⟨z, s, hz, ht0, hs2, hs'⟩) θE hθE sI c u hcd hu v
          hv heq rts hrl hrts
      · intro h
        have h' := h
        rw [← List.nil_append (List.ofFn _)] at h'
        exact (T.kx_backward m hTr g A B kt l cs θ hθ hA0 [] (by simp) Wbs hspecA
          h').hasElementaryIntegral
    · -- `P₊ − ∞` torsion of order `N`
      simp only [ht0] at hdec
      rcases hw0 : kxWit0 Fc ks m A z N with _ | W0b
      · simp only [hw0] at hdec; exact absurd hdec (by simp)
      simp only [hw0] at hdec
      by_cases hsn : tors.any (· == some none) = true
      · rw [if_neg (by simp [hsn])] at hdec
        obtain rfl := Option.some.inj hdec
        simp only [Bool.false_eq_true, iff_false]
        intro hf
        obtain ⟨k, htk⟩ := hnt_k hsn
        obtain ⟨E, _, _, _, TE, θE, rts0, ι, sI, c, u, v, hTEn, hθE, hrl0, hrts0, hcd, hu, hv, heq⟩ :=
          T.kqm_lift m hn A θ hθ hgen _ hf _ hκs
        obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
        exact TE.kx_forward_nontors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst
          hrep ps bound rs cpf k htk (Or.inr ⟨z, N, W0b, s, hz, ht0, hw0, hs2, hs'⟩) θE hθE sI c u hcd
          hu v hv heq rts hrl hrts
      · rw [if_pos (by simp [hsn])] at hdec
        obtain ⟨Ns, Wbs, hNs, hwit, rfl⟩ :=
          kxSolve_spec m g A B kt l cs ps bound rs cpf _ b hnone hsn hdec
        constructor
        · intro hf
          obtain ⟨E, _, _, _, TE, θE, rts0, ι, sI, c, u, v, hTEn, hθE, hrl0, hrts0, hcd, hu, hv,
            heq⟩ := T.kqm_lift m hn A θ hθ hgen _ hf _ hκs
          obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
          exact TE.kx_forward_tors_W0 hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst
            hrep ps bound rs cpf Ns hNs Wbs hwit z N W0b s hz ht0 hw0 hs2 hs' θE hθE sI c u hcd hu v hv
            heq rts hrl hrts
        · intro h
          exact (T.kx_backward m hTr g A B kt l cs θ hθ hA0 _
            (T.kx_col0_hei m hTr A θ hθ hA0 z hz0 hκ0 W0b) Wbs hspecA h).hasElementaryIntegral

open Classical in
/-- **`kxDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θ / (tᵏ ∏_q (t − c_q) A(t)ˡ)` (`θ² = A(t)`, `t` an exponential level of a certified tower)
is elementary exactly when `b = true`. -/
theorem kxDecide_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (b : Bool) (hdec : kxDecide Fc ks lv m g A B kt l cs ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔
      b = true :=
  T.kxDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound rs _ b hdec

end Main

end MTower

end Curves.MT
