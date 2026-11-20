import RischTragerBronstein.Mixed.KZSem

/-!
# Radicals with poles in `Kₘ ⊗ N`: the forward direction

As `KYForward`, with the poles `ψ c_q`, `c_q ∈ Kₘ ⊗ N`: `kzSolve_spec`, `kz_forward_pos` (every
component torsion ⇒ the parametric equation is solvable), `kz_forward_neg` (a component not
torsion with the orders over `x = 0` killed ⇒ no Liouville form), `kz_forward_const` (a Liouville
form ⇒ the residues are constant).
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable [Fact (Irreducible (toPoly (fKc Fc)))]

omit [CharZero Cc] [CharZero L] in
/-- **The parametric equation of `kySolve`**: all components torsion, with witnesses and
columns. -/
lemma kzSolve_spec (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (extra : List (LC (m + 1))) (b : Bool)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length),
      ∃ N, kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N))
    (h : kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs extra = some b) :
    let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
    ∃ (Ns : Fin comps.length → ℕ) (Wbs : Fin comps.length → BPoly (NFM Fc m M))
      (colss : Fin comps.length → List (LC (m + 1))),
      (∀ t : Fin comps.length,
        kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs comps[(t : ℕ)] = some (some (Ns t))) ∧
      (∀ t : Fin comps.length,
        kzWit Fc ks m n j M g A B kt l cs zN gs comps[(t : ℕ)] (Ns t) = some (Wbs t)) ∧
      (∀ t : Fin comps.length, kyColM Fc ks m n M A (MO Fc ks m).one j (Wbs t) = some (colss t)) ∧
      b = (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
        (((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) :: (extra ++ (List.ofFn colss).flatten))).any
          (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) := by
  intro comps
  set tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs) with htorsdef
  have hall' : ∀ t : Fin comps.length, ∃ N,
      kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs comps[(t : ℕ)] = some (some N) :=
    fun t ↦ hall _ (List.getElem_mem t.2)
  choose Ns hNs using hall'
  have hNs' : ∀ t : Fin comps.length,
      ((tors[(t : ℕ)]'(by simp [htorsdef])).getD none).getD 0 = Ns t := fun t ↦ by
    simp [htorsdef, hNs t]
  unfold kzSolveC at h
  dsimp only at h
  generalize hw : ((List.zip comps tors).map fun p ↦
    kzWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0)).allSome = ow at h
  rcases ow with _ | Wbl
  · exact absurd h (by simp)
  obtain ⟨hWl, hWv⟩ := allSome_spec _ Wbl hw
  have hlc : (List.zip comps tors).length = comps.length := by simp [htorsdef]
  have hWl' : Wbl.length = comps.length := by rw [hWl, List.length_map, hlc]
  set Wbs : Fin comps.length → BPoly (NFM Fc m M) := fun t ↦ Wbl[(t : ℕ)]'(by rw [hWl']; exact t.2)
    with hWbs
  have hwit : ∀ t : Fin comps.length,
      kzWit Fc ks m n j M g A B kt l cs zN gs comps[(t : ℕ)] (Ns t) = some (Wbs t) := fun t ↦ by
    have := hWv t (by rw [List.length_map, hlc]; exact t.2) (by rw [hWl']; exact t.2)
    simp only [List.getElem_map, List.getElem_zip] at this
    rw [hNs' t] at this
    exact this
  simp only at h
  generalize hc : (Wbl.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome = oc at h
  rcases oc with _ | cll
  · exact absurd h (by simp)
  obtain ⟨hcl, hcv⟩ := allSome_spec _ cll hc
  have hcl' : cll.length = comps.length := by rw [hcl, List.length_map, hWl']
  set colss : Fin comps.length → List (LC (m + 1)) := fun t ↦ cll[(t : ℕ)]'(by rw [hcl']; exact t.2)
    with hcolss
  have hcol : ∀ t : Fin comps.length,
      kyColM Fc ks m n M A (MO Fc ks m).one j (Wbs t) = some (colss t) := fun t ↦ by
    have := hcv t (by rw [List.length_map, hWl']; exact t.2) (by rw [hcl']; exact t.2)
    simp only [List.getElem_map] at this
    exact this
  have hofn : List.ofFn colss = cll := by
    apply List.ext_getElem
    · simp [hcl']
    · intro i h1 h2; simp [hcolss]
  refine ⟨Ns, Wbs, colss, hNs, hwit, hcol, ?_⟩
  rw [hofn]
  exact (Option.some.inj h).symm

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Forward, every component torsion**: given the zero-fibre data (`W₀`, its `j`-th coordinate
as a combination of the `extra` columns), a Liouville form makes the parametric equation of
`kySolve` solvable with a non-zero coefficient of the integrand. -/
theorem kz_forward_pos (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kzOK Fc ks m M A B kt l cs dC = true) (hc : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (W₀ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯)
    (hZ : ∀ U : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
      U ≠ 0 → (T.krS m hTr A hsq hdegA n hn θ hθ).Supp (K := AlgebraicClosure (T.F m)) U →
      ∃ e : T.F m, e′ = 0 ∧
        (T.krS m hTr A hsq hdegA n hn θ hθ).four (aeval ρ (toPoly zN)) hζ ⟨j, hjn⟩
          ((T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
            (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) U) =
        (T.krS m hTr A hsq hdegA n hn θ hθ).cst e *
          (T.krS m hTr A hsq hdegA n hn θ hθ).four (aeval ρ (toPoly zN)) hζ ⟨j, hjn⟩
          ((T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
            (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) W₀))
    (E0 : Fin n → (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯)
    (hE0 : (T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
        (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) W₀ =
      ∑ i, algebraMap (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯
        (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ (E0 i) *
          AdjoinSimple.gen (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯
            (T.krS m hTr A hsq hdegA n hn θ hθ).y ^ (i : ℕ))
    (extra : List (LC (m + 1))) (wx : List L) (hwx : wx.length = extra.length)
    (hwxc : ∀ w ∈ wx, w′ = 0)
    (hE0j : ((E0 ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) =
      (List.zipWith (fun w c ↦ w * T.ev (m + 1) c) wx extra).sum)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length),
      ∃ N, kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N))
    (b : Bool) (hsolve : kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs extra = some b) :
    b = true := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set K := AlgebraicClosure (T.F m)
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  obtain ⟨Ns, Wbs, colss, hNs, hwit, hcol, rfl⟩ :=
    kzSolve_spec (lv := lv) m n j g M zN gs A B kt l cs dC ps bound rs extra b hall hsolve
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kzFieldOK_spec hF
  have hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 :=
    hmin_of_irr M ρ hρ (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)
  have hM0' : toPoly M ≠ 0 := fun h0 ↦ by
    have := (CPoly.trim_eq_nil_iff M).mpr h0
    rw [htrim] at this; rw [this] at hlen; simp at hlen
  have hok' := T.kzOK_spec m hTm M ρ hρ A B kt l cs dC hok
  have hD0 : ∀ q < cs.length, T.psiNFM m hTm M ρ hρ (kzD Fc ks m M g cs q) ≠ 0 := fun q hq ↦
    T.kzD_ne m hM hk M ρ hρ hM0' cs q (hok'.2.2 q hq).1
  obtain ⟨-, hβf, hresf⟩ := T.kz_points m hTm n j hn hjc g A B kt l M cs dC ρ hρ zN gs hok hc hF hmin hD0
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  -- the witnesses of the components
  have hW : ∀ t : Fin comps.length, ∃ W : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯, W ≠ 0 ∧
      (∀ q < cs.length, ∀ k < n, ((T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K W
        (algebraMap (T.F m) K (T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q)))
        (algebraMap (T.F m) K (aeval ρ (toPoly zN) ^ k *
          ψ (kzBeta Fc ks m n j M g A B kt l cs gs q))) : ℚ) =
          Ns t * kyDen n j M zN gs cs.length comps[(t : ℕ)] * kyR n j M zN gs comps[(t : ℕ)] (q * n + k)) ∧
      (∀ a b : K, b ^ n = ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a → a ≠ 0 →
        (∀ q < cs.length, a ≠ algebraMap (T.F m) K (T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q))) →
        (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K W a b = 0) ∧
      ∃ EW : Fin n → (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯,
        (T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X) (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) W =
          ∑ i, algebraMap (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ (EW i) *
            AdjoinSimple.gen (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯ (T.krS m hTr A hsq hdegA n hn θ hθ).y ^ (i : ℕ) ∧
        ((EW ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) = ∑ f ∈ Finset.range (M.length - 1),
          T.ev (m + 1) ((colss t).getD f (MO Fc ks (m + 1)).zero) * ((ρ : T.F m) : L) ^ f := by
    intro t
    obtain ⟨hWdeg, W, hW0, ⟨uu, huu, hWe⟩, hWo, hWz⟩ := T.kz_comp_wit m hTr A hsq hdegA n hn hcopA θ hθ j hjc g
      B kt l M cs dC ρ hρ zN gs hok hc hF hmin hD0 comps[(t : ℕ)] (Ns t) (Wbs t) (hwit t)
    refine ⟨W, hW0, hWo, hWz, ?_⟩
    have hone : (T.MP m hTm).sem (MO Fc ks m).one / (1 : T.F m) = 1 := by
      rw [(T.MP m hTm).sem_one, div_one]
    have hel0 : (T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB (Wbs t)).map (mapRingHom ψ)).comp
        (Polynomial.C (Polynomial.C ((T.MP m hTm).sem (MO Fc ks m).one / 1)) * X)) ≠ 0 := by
      rw [hone]
      intro h0
      apply hW0
      rw [hWe, h0, zero_mul]
    have hAh : T.ev (m + 1) (pcP Fc ks m A) = (T.ev m (MO Fc ks m).one / ((1 : T.F m) : L)) ^ n *
        T.evP m A := by
      rw [T.ev_one_code m hTm]
      change T.evP m A / T.evP m [(MO Fc ks m).one] = _
      rw [T.evP_single, T.ev_one_code m hTm]
      simp
    obtain ⟨E', hE', hE'j⟩ := T.ky_dl_coords m hTr A hsq hdegA n hn θ hθ hmn hk M htrim hlen ρ hρ A
      (MO Fc ks m).one 1 one_ne_zero hAh (by rw [T.ev_one_code m hTm]; exact one_ne_zero) (Wbs t)
      hWdeg hel0 j hjn (colss t) (hcol t)
    have hel0' : (T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB (Wbs t)).map (mapRingHom ψ)).comp
        (Polynomial.C (Polynomial.C 1) * X)) ≠ 0 := by rw [← hone]; exact hel0
    rw [hone] at hE'
    obtain ⟨EW, hEW, hEWj⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).dl_mul_base _ (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) _ hel0'
      uu huu E' hE'
    refine ⟨EW, ?_, ?_⟩
    · rw [hWe]; exact hEW
    · have h1 := congrArg Subtype.val (hEWj ⟨j, hjn⟩ (by simp; omega))
      refine h1.trans (hE'j.trans ?_)
      simp
  choose Wt hWt0 hWo hWz EWc hEWc hEWj using hW
  -- the data of `ky_liouville`
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  obtain ⟨hb, hbm, hDR, hDoff, hbP⟩ := T.kz_data m hTr A hsq hdegA n hn θ hθ M ρ hρ B kt l cs dC hok'.2.1 j
  set cq : Fin cs.length → T.F m := fun q ↦ T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q) with hcq
  set βq : Fin cs.length → T.F m := fun q ↦ ψ (kzBeta Fc ks m n j M g A B kt l cs gs q) with hβq
  set ν : Fin comps.length → T.F m := fun t ↦ ρ ^ comps[(t : ℕ)] with hν
  set rr : Fin cs.length → ℕ → Fin comps.length → ℚ := fun q kk t ↦
    kyR n j M zN gs comps[(t : ℕ)] (q * n + kk % n) with hrr
  have hc0 : ∀ q : Fin cs.length, cq q ≠ 0 := fun q ↦ (hok'.2.2 q q.2).1
  have hRne : ∀ q : Fin cs.length, (X ^ kt * ((cs.eraseIdx q).map fun c ↦ X - Polynomial.C (T.psiNFM m hTm M ρ hρ c)).prod).eval
      (cq q) ≠ 0 := fun q h0 ↦ by
    have := (hok'.2.2 q q.2).2.1
    rw [T.psi_kzR] at this
    apply this
    simp only [eval_mul, eval_pow, eval_X, eval_list_prod, List.map_map, Function.comp_def,
      eval_sub, eval_C, hcq] at h0
    rw [h0, zero_mul]
  have hβq' : ∀ q : Fin cs.length, βq q ≠ 0 ∧ βq q ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n = (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (cq q) := fun q ↦ hβf q q.2
  have hres : ∀ (q : Fin cs.length) (kk : ℕ), (GPoly.toPoly (T.MP m hTm) B).eval (cq q) *
      (aeval ρ (toPoly zN) ^ kk * βq q) ^ j =
      (∑ t, (rr q kk t : T.F m) * ν t) * (((T.val m g)′ * cq q - (cq q)′) *
        (X ^ kt * ((cs.eraseIdx q).map fun c ↦ X - Polynomial.C (T.psiNFM m hTm M ρ hρ c)).prod * (T.krS m hTr A hsq hdegA n hn θ hθ).p ^ l).eval (cq q)) := by
    intro q kk
    have h1 := hresf q q.2 kk
    have hi : (q : ℕ) * n + kk % n < cs.length * n := by
      have := Nat.mod_lt kk hn
      nlinarith [q.2]
    have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
    have hMdeg : (toPoly M).natDegree = M.length - 1 := by
      have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
      rw [htrim] at this; omega
    rw [hMdeg, ky_res_comps n j M zN gs cs.length (fun f ↦ (ρ : T.F m) ^ f) _ hi] at h1
    rw [h1, T.psi_kzD m hTm M ρ hρ g cs hM0', T.psi_kzR, T.sem_eq_val m hTm g]
    simp only [hrr, hν, hcq]
    congr 1
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hSp]
    simp only [eval_mul, eval_pow, eval_X, eval_list_prod, List.map_map, Function.comp_def,
      eval_sub, eval_C]
  have hme : ∀ t : Fin comps.length, 0 < Ns t * kyDen n j M zN gs cs.length comps[(t : ℕ)] := by
    intro t
    refine Nat.mul_pos (T.kz_comp_pos m hTr A hsq hdegA n hn hcopA θ hθ j hjc g B kt l M cs dC ρ hρ zN
      gs hok hc hF hmin hD0 ps bound rs _ _ (hNs t)) ?_
    exact lcmL_pos fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact Rat.den_pos _
  have hWo' : ∀ t (q : Fin cs.length) (kk : Fin (T.krS m hTr A hsq hdegA n hn θ hθ).n), ((T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K (Wt t)
      (Differential.SuperData.pq (K := K) (aeval ρ (toPoly zN)) cq βq q kk).1
      (Differential.SuperData.pq (K := K) (aeval ρ (toPoly zN)) cq βq q kk).2 : ℚ) =
      ((Ns t * kyDen n j M zN gs cs.length comps[(t : ℕ)] : ℕ) : ℚ) * rr q kk t := by
    intro t q kk
    have := hWo t q q.2 kk kk.2
    simp only [Differential.SuperData.pq, hrr]
    rw [this, show (kk : ℕ) % n = kk from Nat.mod_eq_of_lt kk.2]; push_cast; ring
  have hWz' : ∀ t (a b : K), b ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n = ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a → a ≠ 0 →
      (∀ q : Fin cs.length, a ≠ algebraMap (T.F m) K (cq q)) → (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K (Wt t) a b = 0 :=
    fun t a b hv ha hq ↦ hWz t a b hv ha (fun q hq' ↦ hq ⟨q, hq'⟩)
  have hu' : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ := fun i hi ↦
    ⟨(hu i hi).1, T.krS_mem m hTr A hsq hdegA n hn θ hθ _ (hu i hi).2⟩
  obtain ⟨a, ha, ee, e0, hee, he0, hae⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).ky_liouville (K := K) _ hx (aeval ρ (toPoly zN)) hζ
    ⟨j, hjn⟩ (fun c ↦ deriv_algebraMap c) (T.keS_good m hM hk) (T.keS_constC m) cq hc0
    (GPoly.toPoly (T.MP m hTm) B) l _ hb _ _ hDR hRne hDoff hbP βq hβq' ν rr hres hj0 hbm sI c u hcd
    hu' v (T.krS_mem m hTr A hsq hdegA n hn θ hθ _ hv) heq Wt hWt0 _ hme hWo' hWz' W₀ hZ EWc hEWc E0 hE0
  -- the parametric equation
  have hA0 : T.evP m A ≠ 0 := by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    exact fun h0 ↦ (T.krS m hTr A hsq hdegA n hn θ hθ).htr ⟨_, hsq.ne_zero, h0⟩
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hM0 : toPoly M ≠ 0 := fun h ↦ hMne (by
    have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)
  have hρL : aeval ((ρ : T.F m) : L) (toPoly M) = 0 := by
    rw [show ((ρ : T.F m) : L) = algebraMap (T.F m) L ρ from rfl, aeval_algebraMap_apply, hρ,
      map_zero]
  have hρd : ((ρ : T.F m) : L)′ = 0 := MTower.deriv_root_rat _ _ hM0 hρL
  set wsc : Fin comps.length → List L := fun t ↦
    (List.range (M.length - 1)).map fun f ↦ algebraMap (T.F m) L (ee t) * ((ρ : T.F m) : L) ^ f with hwsc
  have hcl : ∀ t, (colss t).length = M.length - 1 := fun t ↦ kyColM_length (Fc := Fc) (ks := ks) m n M A _ j _ _ (hcol t)
  have hflat : (List.ofFn wsc).flatten.length = (List.ofFn colss).flatten.length := by
    simp only [List.length_flatten, List.map_ofFn]
    congr 1
    apply List.ext_getElem
    · simp <;> rfl
    · intro i h1 h2; simp [hwsc, hcl]
  refine T.prde_forward_listN (lv := lv) m n j hn hTr A hA0 θ hθ hspec _
    (extra ++ (List.ofFn colss).flatten) a ((T.mem_F_succ).mpr ha)
    ((wx.map fun w ↦ algebraMap (T.F m) L e0 * w) ++ (List.ofFn wsc).flatten)
    (by simp only [List.length_append, List.length_map, hwx, hflat]) ?_ ?_
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      rw [Derivation.leibniz, hwxc w' hw', deriv_algebraMap, he0]; simp
    · obtain ⟨lst, hl, hwl⟩ := List.mem_flatten.mp hw
      obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨f, -, rfl⟩ := List.mem_map.mp hwl
      rw [Derivation.leibniz, Derivation.leibniz_pow, hρd, deriv_algebraMap, hee t]; simp
  · have hy : (T.krS m hTr A hsq hdegA n hn θ hθ).y = θ := rfl
    rw [hy] at hae
    rw [hae, List.zipWith_append (by simp [hwx]), List.sum_append,
      zipWith_flatten_sum _ _ _ (by simp <;> rfl) (fun i h1 h2 ↦ by simp [hwsc, hcl])]
    have hx1 : (List.zipWith (fun w c ↦ w * T.ev (m + 1) c * θ ^ j)
        (wx.map fun w ↦ algebraMap (T.F m) L e0 * w) extra).sum =
        algebraMap (T.F m) L e0 * (((E0 ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) *
          θ ^ j) := by
      rw [hE0j, List.zipWith_map_left, zipWith_sum_fin _ _ _ hwx, zipWith_sum_fin _ _ _ hwx,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have hx2 : (List.zipWith (fun w c ↦ (List.zipWith (fun w c ↦ w * T.ev (m + 1) c * θ ^ j) w c).sum)
        (List.ofFn wsc) (List.ofFn colss)).sum = ∑ t, algebraMap (T.F m) L (ee t) *
          (((EWc t ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) * θ ^ j) := by
      rw [zipWith_ofFn, List.sum_ofFn]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [zipWith_range_sum _ _ _ _ _ (MO Fc ks (m + 1)).zero (hcl t), hEWj t, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ ↦ ?_
      ring
    rw [hx1, hx2]
    ring_nf
    rfl

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Forward, a component not torsion**: when the orders over `x = 0` can be killed (`hkill`), a
Liouville form is impossible. -/
theorem kz_forward_neg (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kzOK Fc ks m M A B kt l cs dC = true) (hc : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (f0 : ℕ)
    (hf0 : f0 ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length))
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (htors : kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f0 = some none)
    (hkill : ∀ V : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
      V ≠ 0 → (∀ α β' : AlgebraicClosure (T.F m), β' ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
        ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval α → α ≠ 0 →
        (∀ q : Fin cs.length, α ≠ algebraMap (T.F m) _ (T.psiNFM m hTr.of_succ M ρ hρ (kzC Fc m M cs q))) →
        (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V α β' = 0) →
      ∃ V' : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
        V' ≠ 0 ∧ ∃ M' : ℕ, 0 < M' ∧
        (∀ α β' : AlgebraicClosure (T.F m), β' ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
          ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval α → α ≠ 0 →
          (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V' α β' =
            M' * (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V α β') ∧
        (∀ β' : AlgebraicClosure (T.F m), β' ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
          ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval 0 →
          (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V' 0 β' = 0))
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i)) : False := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set K := AlgebraicClosure (T.F m)
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kzFieldOK_spec hF
  have hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 :=
    hmin_of_irr M ρ hρ (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)
  have hM0' : toPoly M ≠ 0 := fun h0 ↦ by
    have := (CPoly.trim_eq_nil_iff M).mpr h0
    rw [htrim] at this; rw [this] at hlen; simp at hlen
  have hok' := T.kzOK_spec m hTm M ρ hρ A B kt l cs dC hok
  have hD0 : ∀ q < cs.length, T.psiNFM m hTm M ρ hρ (kzD Fc ks m M g cs q) ≠ 0 := fun q hq ↦
    T.kzD_ne m hM hk M ρ hρ hM0' cs q (hok'.2.2 q hq).1
  obtain ⟨-, hβf, hresf⟩ := T.kz_points m hTm n j hn hjc g A B kt l M cs dC ρ hρ zN gs hok hc hF hmin hD0
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  obtain ⟨hb, hbm, hDR, hDoff, hbP⟩ := T.kz_data m hTr A hsq hdegA n hn θ hθ M ρ hρ B kt l cs dC hok'.2.1 j
  set cq : Fin cs.length → T.F m := fun q ↦ T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q) with hcq
  set βq : Fin cs.length → T.F m := fun q ↦ ψ (kzBeta Fc ks m n j M g A B kt l cs gs q) with hβq
  set ν : Fin comps.length → T.F m := fun t ↦ ρ ^ comps[(t : ℕ)] with hν
  set rr : Fin cs.length → ℕ → Fin comps.length → ℚ := fun q kk t ↦
    kyR n j M zN gs comps[(t : ℕ)] (q * n + kk % n) with hrr
  have hc0 : ∀ q : Fin cs.length, cq q ≠ 0 := fun q ↦ (hok'.2.2 q q.2).1
  have hRne : ∀ q : Fin cs.length, (X ^ kt * ((cs.eraseIdx q).map fun c ↦
      X - Polynomial.C (T.psiNFM m hTm M ρ hρ c)).prod).eval (cq q) ≠ 0 := fun q h0 ↦ by
    have := (hok'.2.2 q q.2).2.1
    rw [T.psi_kzR] at this
    apply this
    simp only [eval_mul, eval_pow, eval_X, eval_list_prod, List.map_map, Function.comp_def,
      eval_sub, eval_C, hcq] at h0
    rw [h0, zero_mul]
  have hβq' : ∀ q : Fin cs.length, βq q ≠ 0 ∧ βq q ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (cq q) := fun q ↦ hβf q q.2
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hMdeg : (toPoly M).natDegree = M.length - 1 := by
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  have hres : ∀ (q : Fin cs.length) (kk : ℕ), (GPoly.toPoly (T.MP m hTm) B).eval (cq q) *
      (aeval ρ (toPoly zN) ^ kk * βq q) ^ j =
      (∑ t, (rr q kk t : T.F m) * ν t) * (((T.val m g)′ * cq q - (cq q)′) *
        (X ^ kt * ((cs.eraseIdx q).map fun c ↦ X - Polynomial.C (T.psiNFM m hTm M ρ hρ c)).prod *
          (T.krS m hTr A hsq hdegA n hn θ hθ).p ^ l).eval (cq q)) := by
    intro q kk
    have h1 := hresf q q.2 kk
    have hi : (q : ℕ) * n + kk % n < cs.length * n := by
      have := Nat.mod_lt kk hn
      nlinarith [q.2]
    rw [hMdeg, ky_res_comps n j M zN gs cs.length (fun f ↦ (ρ : T.F m) ^ f) _ hi] at h1
    rw [h1, T.psi_kzD m hTm M ρ hρ g cs hM0', T.psi_kzR, T.sem_eq_val m hTm g]
    simp only [hrr, hν, hcq]
    congr 1
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hSp]
    simp only [eval_mul, eval_pow, eval_X, eval_list_prod, List.map_map, Function.comp_def,
      eval_sub, eval_C]
  -- the independence of the coordinates
  have hnd : comps.Nodup := (List.nodup_range).filter _
  have hlt : ∀ t : Fin comps.length, comps[(t : ℕ)] < (toPoly M).natDegree := fun t ↦ by
    have := List.mem_filter.mp (List.getElem_mem t.2)
    rw [hMdeg]; exact List.mem_range.mp this.1
  have hνi : ∀ tt : Fin comps.length → ℚ, ∑ e, (tt e : T.F m) * ν e = 0 → ∀ e, tt e = 0 := by
    intro tt htt e
    set t' : ℕ → ℚ := fun f ↦ ∑ e' : Fin comps.length, if comps[(e' : ℕ)] = f then tt e' else 0 with ht'
    have hsum : ∑ f ∈ Finset.range (toPoly M).natDegree, (t' f : T.F m) * ρ ^ f = 0 := by
      rw [← htt]
      simp only [ht', Rat.cast_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e' _ ↦ ?_
      rw [Finset.sum_eq_single comps[(e' : ℕ)] (fun f _ hf ↦ by
          rw [if_neg (Ne.symm hf)]; simp)
        (fun h ↦ absurd (Finset.mem_range.mpr (hlt e')) h), if_pos rfl]
    have := pow_indep M ρ hmin (by intro h; exact hMne (by
      have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)) t' hsum _ (hlt e)
    simp only [ht'] at this
    rwa [Finset.sum_eq_single e (fun e' _ he' ↦ by
        rw [if_neg]; intro h; exact he' (Fin.ext (hnd.getElem_inj_iff.mp h)))
      (fun h ↦ absurd (Finset.mem_univ e) h), if_pos rfl] at this
  obtain ⟨e0, he0l, he0⟩ := List.mem_iff_getElem.mp hf0
  have hu' : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ :=
    fun i hi ↦ ⟨(hu i hi).1, T.krS_mem m hTr A hsq hdegA n hn θ hθ _ (hu i hi).2⟩
  obtain ⟨V, hV0, Mv, hMv, hVo, hVz, hV0z⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).ky_nontors (K := K)
    _ hx (aeval ρ (toPoly zN)) hζ ⟨j, hjn⟩ (fun c ↦ deriv_algebraMap c) (T.keS_good m hM hk)
    (T.keS_constC m) cq hc0 (GPoly.toPoly (T.MP m hTm) B) l _ hb _ _ hDR hRne hDoff hbP βq hβq' ν rr
    hres hj0 hbm hνi hkill sI c u hcd hu' v (T.krS_mem m hTr A hsq hdegA n hn θ hθ _ hv) heq
    ⟨e0, he0l⟩
  -- the points and the oracle
  set ζ' := aeval ρ (toPoly zN) with hζ'
  have hin : ∀ i : Fin (cs.length * n), (i : ℕ) / n < cs.length :=
    fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  set α : Fin (cs.length * n) → T.F m := fun i ↦ T.psiNFM m hTm M ρ hρ (kzC Fc m M cs (i / n)) with hαdef
  set β : Fin (cs.length * n) → T.F m := fun i ↦ ζ' ^ ((i : ℕ) % n) *
    ψ (kzBeta Fc ks m n j M g A B kt l cs gs (i / n)) with hβdef
  have hcinj := T.kz_cinj m hTm M ρ hρ A B kt l cs dC hok
  have hβ : ∀ i, β i ≠ 0 ∧ β i ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (α i) := fun i ↦ by
    obtain ⟨h0, hpw⟩ := hβf _ (hin i)
    refine ⟨mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) h0, ?_⟩
    show _ ^ n = (GPoly.toPoly (T.MP m hTm) A).eval _
    rw [mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hpw]
  have hP : Function.Injective fun i ↦ (α i, β i) := by
    intro i i' h
    have h1 : (i : ℕ) / n = i' / n := by
      have := congrArg Prod.fst h
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    have h2 := congrArg Prod.snd h
    simp only [hβdef, h1] at h2
    have h3 := mul_right_cancel₀ (hβf _ (hin i')).1 h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1, h4]
  have hpf : Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p = (toPoly (kyFA Fc m M A)).map ψ := by
    rw [one_pow, map_one, one_mul, hψ, T.kyFA_map m hTm M ρ hρ]; rfl
  have hp0 : Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p ≠ 0 := by rw [one_pow, map_one, one_mul]; exact hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p) := by rw [one_pow, map_one, one_mul]; exact hsq
  have hcopp : Nat.Coprime n (Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p).natDegree := by
    rw [one_pow, map_one, one_mul]; exact hcopA
  obtain ⟨hd, hsqK, hcop2⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hα : ∀ i, ψ (kzAl Fc m n M cs i) = α i := fun i ↦ by
    simp only [kzAl, hψ, hαdef]
  have hβ' : ∀ i, ψ (kzBe Fc ks m n j M g A B kt l cs zN gs i) = 1 * β i := fun i ↦ by
    simp only [kzBe, map_mul, map_pow, hψ, T.psiNFM_ofQ, one_mul, hβdef, hζ']
  have hΓK : ∀ i, (((T.krS m hTr A hsq hdegA n hn θ hθ).n : ℕ) : NFM Fc m M) *
      (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ ((T.krS m hTr A hsq hdegA n hn θ hθ).n - 1) ≠ 0 ∧
      (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i) := fun i ↦ by
    constructor
    · intro h0
      have := congrArg ψ h0
      rw [map_mul, map_pow, hβ' i, one_mul, map_natCast, map_zero] at this
      exact mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ (hβ i).1) this
    · apply ψ.injective
      rw [map_pow, hβ' i, one_mul, (hβ i).2, ← eval₂_at_apply, ← eval_map, ← hpf, hα i, one_pow,
        map_one, one_mul]
  have hspecT := torsOracleC_specY (redAtNFM Fc m M rs) cpf
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) ps bound hsqK hcop2
  have hvK : ∀ i, kzBe Fc ks m n j M g A B kt l cs zN gs i ≠ 0 ∧
      (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i) := fun i ↦ by
    refine ⟨fun h0 ↦ ?_, (hΓK i).2⟩
    have := congrArg ψ h0
    rw [hβ' i, one_mul, map_zero] at this
    exact (hβ i).1 this
  have hinjK : Function.Injective fun i ↦ (kzAl Fc m n M cs i, kzBe Fc ks m n j M g A B kt l cs zN gs i) := by
    intro i i' h
    apply hP
    simp only [Prod.ext_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [← hα i, ← hα i', h.1]
    · have := congrArg ψ h.2
      rw [hβ' i, hβ' i', one_mul, one_mul] at this
      exact this
  have hnot := (hspecT (cs.length * n) _ _ (kyMult n j M zN gs cs.length f0) hvK hinjK).2 htors
  have hnp := (T.krS m hTr A hsq hdegA n hn θ hθ).pts_not_principal (K := K) hcopA α β hP hβ
    (kyMult n j M zN gs cs.length f0) ψ (kyFA Fc m M A) 1 one_ne_zero hpf hd _ _ hα hβ' hΓK hnot
  apply hnp Mv hMv
  -- `V^{L} ∏ (x − c_q)^{M sh_q}` has divisor `M Γ`
  set Lf : ℕ := kyDen n j M zN gs cs.length f0 with hLf
  set sh : ℕ → ℤ := fun q ↦ kySh n j M zN gs cs.length f0 q with hsh
  set U : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ :=
    ∏ q : Fin cs.length, (T.krS m hTr A hsq hdegA n hn θ hθ).polyX (X - Polynomial.C (cq q)) ^
      ((Mv : ℤ) * sh q) with hU
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ ↦
    zpow_ne_zero _ ((T.krS m hTr A hsq hdegA n hn θ hθ).polyX_ne_zero (X_sub_C_ne_zero _))
  have hVL : V ^ (Lf : ℤ) ≠ 0 := zpow_ne_zero _ hV0
  have hordU : ∀ a b : K, b ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a →
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K U a b =
        ∑ q : Fin cs.length, (Mv : ℤ) * sh q *
          (if a = algebraMap (T.F m) K (cq q) then (if b = 0 then ((T.krS m hTr A hsq hdegA n hn θ hθ).n : ℤ) else 1) else 0) := by
    intro a b hv
    rw [hU, (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_prod hv _ _ (fun q _ ↦ zpow_ne_zero _
      ((T.krS m hTr A hsq hdegA n hn θ hθ).polyX_ne_zero (X_sub_C_ne_zero _)))]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [(T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_zpow hv,
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_X_sub _ a b hv]
  have hgam0 : ∀ a b : K, (∀ q : Fin cs.length, a ≠ algebraMap (T.F m) K (cq q)) →
      Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f0) (a, b) = 0 := by
    intro a b ha
    rw [Differential.SuperData.gammaPts]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [if_neg]
    intro h
    exact ha ⟨_, hin i⟩ (by simpa [hαdef, hcq] using (Prod.ext_iff.mp h).1)
  have hord : ∀ a b : K, b ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a →
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K (V ^ (Lf : ℤ) * U) a b =
        Mv * Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f0) (a, b) := by
    intro a b hv
    rw [(T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_mul hv hVL hU0,
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_zpow hv, hordU a b hv]
    by_cases hq : ∃ q : Fin cs.length, a = algebraMap (T.F m) K (cq q)
    · obtain ⟨q, rfl⟩ := hq
      have hb0 : algebraMap (T.F m) K (βq q) ≠ 0 := (_root_.map_ne_zero _).mpr (hβq' q).1
      have hv0 : (algebraMap (T.F m) K (βq q)) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
          ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval
            (algebraMap (T.F m) K (cq q)) := by
        rw [← map_pow, (hβq' q).2, eval_map, eval₂_at_apply]
      obtain ⟨kk, hkk0, rfl⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).over_k ζ' hζ _ _ hb0 hv0 b hv
      have hkk : kk < n := hkk0
      have hbb : algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ ((_root_.map_ne_zero _).mpr (hζ.ne_zero hn.ne'))) hb0
      set i : Fin (cs.length * n) := ⟨q * n + kk, by nlinarith [q.2]⟩ with hi
      have hiq : (i : ℕ) / n = q := by
        simp only [hi]
        rw [Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ hn,
          Nat.div_eq_of_lt hkk, add_zero]
      have hik : (i : ℕ) % n = kk := by
        simp only [hi]; rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hkk]
      have hpti : (algebraMap (T.F m) K (cq q), algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) =
          (algebraMap (T.F m) K (α i), algebraMap (T.F m) K (β i)) := by
        simp [hαdef, hβdef, hiq, hik, hcq, hβq]
      have hgi : Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f0)
          (algebraMap (T.F m) K (cq q), algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) =
          kyMult n j M zN gs cs.length f0 i := by
        rw [hpti, Differential.SuperData.gammaPts, Finset.sum_eq_single i]
        · simp
        · intro i' _ hi'
          rw [if_neg]
          intro h
          apply hi'
          apply hP
          simp only [Prod.ext_iff] at h ⊢
          exact ⟨((algebraMap (T.F m) K).injective h.1).symm, ((algebraMap (T.F m) K).injective h.2).symm⟩
        · simp
      rw [hgi, Finset.sum_eq_single q (fun q' _ hq' ↦ by
          rw [if_neg, mul_zero]; intro h; apply hq'; apply hcinj
          exact ((algebraMap (T.F m) K).injective h).symm) (fun h ↦ absurd (Finset.mem_univ _) h),
        if_pos rfl, if_neg hbb, mul_one]
      -- the orders of `V` and the multiplicity
      have hVq := hVo q ⟨kk, hkk⟩
      simp only [Differential.SuperData.pq, map_mul, map_pow] at hVq
      have hzc := Differential.SuperData.rat_mul_den_int (kyR n j M zN gs f0 i) Lf
        (dvd_lcmL (List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩))
      have hshq : -kyZc n j M zN gs cs.length f0 i ≤ kySh n j M zN gs cs.length f0 q := by
        simp only [kySh]
        refine foldr_max_ge _ _ (List.mem_map.mpr ⟨kk, List.mem_range.mpr hkk, ?_⟩)
        simp only [hi]
      have hmult : (kyMult n j M zN gs cs.length f0 i : ℤ) =
          kyZc n j M zN gs cs.length f0 i + kySh n j M zN gs cs.length f0 q := by
        rw [kyMult, hiq, Int.toNat_of_nonneg (by omega)]
      have hrrq : rr q kk ⟨e0, he0l⟩ = kyR n j M zN gs f0 i := by
        simp only [hrr, he0, hi]
        rw [Nat.mod_eq_of_lt hkk]
      rw [hrrq] at hVq
      have hfin : ((Lf : ℤ) * (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K V
          (algebraMap (T.F m) K (cq q)) (algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) : ℚ) =
          Mv * kyZc n j M zN gs cs.length f0 i := by
        push_cast
        rw [hVq, kyZc, ← hzc]
        ring
      have hfin' : (Lf : ℤ) * (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K V
          (algebraMap (T.F m) K (cq q)) (algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) =
          Mv * kyZc n j M zN gs cs.length f0 i := by exact_mod_cast hfin
      rw [hfin', hmult, hsh]
      ring
    · push Not at hq
      rw [hgam0 a b hq, Finset.sum_eq_zero fun q _ ↦ by rw [if_neg (hq q), mul_zero]]
      by_cases ha : a = 0
      · subst ha; rw [hV0z b hv]; simp
      · rw [hVz a b hv ha hq]; simp
  refine ⟨V ^ (Lf : ℤ) * U, mul_ne_zero hVL hU0, fun a b hv ↦ ?_, fun Q hQ ↦ hord Q.1 Q.2 hQ⟩
  rw [hord a b hv]
  positivity

open Classical in
/-- **Forward, the residues**: a Liouville form makes every `ρ_qⁿ A(c_q)ʲ` constant. -/
theorem kz_forward_const (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)
    (hM0' : toPoly M ≠ 0) (hok : kzOK Fc ks m M A B kt l cs dC = true)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    kzConst Fc ks m n j M g A B kt l cs = true := by
  have hTm : T.Tr m := hTr.of_succ
  have hok' := T.kzOK_spec m hTm M ρ hρ A B kt l cs dC hok
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  obtain ⟨hb, hbm, hDR, hDoff, hbP⟩ := T.kz_data m hTr A hsq hdegA n hn θ hθ M ρ hρ B kt l cs dC hok'.2.1 j
  set cq : Fin cs.length → T.F m := fun q ↦ T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q) with hcq
  have hRne : ∀ q : Fin cs.length, (X ^ kt * ((cs.eraseIdx q).map fun c ↦
      X - Polynomial.C (T.psiNFM m hTm M ρ hρ c)).prod).eval (cq q) ≠ 0 := fun q h0 ↦ by
    have := (hok'.2.2 q q.2).2.1
    rw [T.psi_kzR] at this
    apply this
    simp only [eval_mul, eval_pow, eval_X, eval_list_prod, List.map_map, Function.comp_def,
      eval_sub, eval_C, hcq] at h0
    rw [h0, zero_mul]
  have hbadc : ∀ q : Fin cs.length, ¬ (algebraMap (T.F m) (AlgebraicClosure (T.F m)) (cq q) = 0) :=
    fun q h ↦ (hok'.2.2 q q.2).1 ((algebraMap (T.F m) _).injective (by rw [h, map_zero]))
  have hpc : ∀ q : Fin cs.length, (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (cq q) ≠ 0 :=
    fun q ↦ (hok'.2.2 q q.2).2.2.1
  have hu' : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ :=
    fun i hi ↦ ⟨(hu i hi).1, T.krS_mem m hTr A hsq hdegA n hn θ hθ _ (hu i hi).2⟩
  refine T.kzConst_of m hTm n j M ρ hρ g A B kt l cs hM0' fun q hq ↦ ?_
  obtain ⟨ξ, hξ, hξe⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).ky_resid_const
    (K := AlgebraicClosure (T.F m)) _ hx (fun c ↦ deriv_algebraMap c) (· = 0) (T.kxS_good m hM hk)
    (T.keS_constC m) cq hbadc (GPoly.toPoly (T.MP m hTm) B) l _ hb _ _ hDR hRne hDoff hbP hpc j hj0 hjn
    hbm sI c u hcd hu' v (T.krS_mem m hTr A hsq hdegA n hn θ hθ _ hv) heq ⟨q, hq⟩
  have hden : T.psiNFM m hTm M ρ hρ (kzD Fc ks m M g cs q) * T.psiNFM m hTm M ρ hρ (kzR Fc m M A kt l cs q) =
      (((Polynomial.C (T.val m g)′ * X).eval (cq ⟨q, hq⟩) - (cq ⟨q, hq⟩)′) *
        (X ^ kt * ((cs.eraseIdx q).map fun c ↦ X - Polynomial.C (T.psiNFM m hTm M ρ hρ c)).prod *
          (T.krS m hTr A hsq hdegA n hn θ hθ).p ^ l).eval (cq ⟨q, hq⟩)) := by
    rw [T.psi_kzD m hTm M ρ hρ g cs hM0', T.psi_kzR, T.sem_eq_val m hTm g]
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hSp]
    simp only [eval_mul, eval_pow, eval_X, eval_C, eval_list_prod, List.map_map, Function.comp_def,
      eval_sub, hcq]
  have hD0 : T.psiNFM m hTm M ρ hρ (kzD Fc ks m M g cs q) ≠ 0 := T.kzD_ne m hM hk M ρ hρ hM0' cs q (hok'.2.2 q hq).1
  have hR0 := (hok'.2.2 q hq).2.1
  have hval : T.psiNFM m hTm M ρ hρ (kzQ Fc ks m n j M g A B kt l cs q) = ξ := by
    rw [T.psi_kzQ, T.psi_kzRho m hTm M ρ hρ g A B kt l cs, div_pow]
    have hdn : (T.psiNFM m hTm M ρ hρ (kzD Fc ks m M g cs q) * T.psiNFM m hTm M ρ hρ (kzR Fc m M A kt l cs q)) ^ n
        ≠ 0 := pow_ne_zero _ (mul_ne_zero hD0 hR0)
    field_simp
    rw [hden]
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    have := hξe
    have hSn : (T.krS m hTr A hsq hdegA n hn θ hθ).n = n := rfl
    rw [hSp, hSn] at this
    rw [hSp]
    simp only [hcq] at this ⊢
    linear_combination this
  rw [hval, hξ]

end MTower

end Curves.MT
