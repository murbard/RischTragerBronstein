import RischTragerBronstein.Algebraic.SuperPrincipalSem

/-!
# The principality test decides principality

`supPrincipalC_iff`: for a superelliptic curve `yⁿ = f(x)` with `f` over a computable field `F ⊆ C`,
and an effective divisor `Γ` of ordinary points with coordinates in `F`, the executable test
`supPrincipalC f n (deg f) Γ (deg Γ)` answers iff `Γ − (deg Γ) ∞` is principal
(`IsPrincipalS`, over any algebraically closed `K ⊇ C`).
-/

open Polynomial IntermediateField HahnSeries CPoly

namespace Sup

lemma mult_of_mem {α β : Type*} [DecidableEq β] (key : α → β) (val : α → ℕ) :
    ∀ (Γ : List α), (Γ.map key).Nodup → ∀ q ∈ Γ,
      ((Γ.filter fun q' ↦ key q' = key q).map val).sum = val q
  | [], _, q, hq => absurd hq (by simp)
  | a :: Γ, hnd, q, hq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [List.filter_cons, if_pos (by simp)]
      rw [List.filter_eq_nil_iff.mpr (fun q' hq' h ↦ ha (by
        simp only [decide_eq_true_eq] at h; rw [← h]; exact List.mem_map_of_mem hq'))]
      simp
    · have hne : key a ≠ key q := fun h ↦ ha (h ▸ List.mem_map_of_mem hq)
      rw [List.filter_cons, if_neg (by simpa using hne)]
      exact mult_of_mem key val Γ hnd q hq

lemma sum_mult {α β : Type*} [DecidableEq β] (key : α → β) (val : α → ℕ) (Γ : List α)
    (hnd : (Γ.map key).Nodup) :
    ∑ Q ∈ (Γ.map key).toFinset, ((Γ.filter fun q' ↦ key q' = Q).map val).sum = (Γ.map val).sum := by
  rw [List.sum_toFinset _ hnd, List.map_map]
  congr 1
  exact List.map_congr_left fun q hq ↦ mult_of_mem key val Γ hnd q hq

end Sup

namespace Differential

namespace SuperData

open Sup

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

lemma vanishAtN_map {F : Type*} [Field F] [DecidableEq F] {T : Type*} [Field T] (ψ : F →+* T)
    {f : F[X]} {n : ℕ} {W : F[X][X]} {α β : F} {ℓ : ℕ} (h : VanishAtN f n W α β ℓ) :
    VanishAtN (f.map ψ) n (W.map (mapRingHom ψ)) (ψ α) (ψ β) ℓ := by
  obtain ⟨V, hV, hd⟩ := h
  refine ⟨V.map ψ, hV.map ψ, ?_⟩
  rw [← jetN_map]
  have := Polynomial.map_dvd ψ hd
  rwa [Polynomial.map_pow, Polynomial.map_X] at this

open Classical in
/-- **The principality test decides principality.** -/
theorem supPrincipalC_iff {F : Type*} [Field F] [DecidableEq F] (φ : F →+* C)
    (hcop : Nat.Coprime S.n S.p.natDegree) (f : CPoly F) (hf : S.p = (toPoly f).map φ)
    (Γ : List (F × F × ℕ)) (hΓ : ∀ q ∈ Γ, q.2.1 ≠ 0 ∧ q.2.1 ^ S.n = (toPoly f).eval q.1)
    (hnd : (Γ.map fun q ↦ (q.1, q.2.1)).Nodup) :
    supPrincipalC f S.n (toPoly f).natDegree Γ (Γ.map fun q ↦ q.2.2).sum ≠ none ↔
      S.IsPrincipalS K (fun Q ↦ if Q ∈ (Γ.map fun q ↦ ((algebraMap C K).comp φ q.1,
          (algebraMap C K).comp φ q.2.1)).toFinset then
        ((Γ.filter fun q ↦ ((algebraMap C K).comp φ q.1, (algebraMap C K).comp φ q.2.1) = Q).map
          fun q ↦ q.2.2).sum else 0) 1 := by
  set ψ := (algebraMap C K).comp φ
  set key : F × F × ℕ → K × K := fun q ↦ (ψ q.1, ψ q.2.1)
  have hψinj : Function.Injective ψ := ψ.injective
  have hndK : (Γ.map key).Nodup := by
    rw [show key = (fun Q : F × F ↦ (ψ Q.1, ψ Q.2)) ∘ (fun q ↦ (q.1, q.2.1)) from rfl,
      ← List.map_map]
    exact hnd.map (fun Q Q' h ↦ Prod.ext (hψinj (congrArg Prod.fst h))
      (hψinj (congrArg Prod.snd h)))
  have hdeg : S.p.natDegree = (toPoly f).natDegree := by
    rw [hf, natDegree_map_eq_of_injective φ.injective]
  have hpK : S.p.map (algebraMap C K) = (toPoly f).map ψ := by
    rw [hf, Polynomial.map_map]
  have hTvalid : ∀ Q ∈ (Γ.map key).toFinset, Q.2 ≠ 0 ∧
      Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := by
    intro Q hQ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hQ)
    obtain ⟨h1, h2⟩ := hΓ q hq
    refine ⟨(map_ne_zero_iff _ hψinj).mpr h1, ?_⟩
    rw [hpK, eval_map, eval₂_at_apply, ← h2, map_pow]
  have hΓF : ∀ q ∈ Γ, (S.n : F) * q.2.1 ^ (S.n - 1) ≠ 0 ∧ q.2.1 ^ S.n = (toPoly f).eval q.1 :=
    fun q hq ↦ ⟨mul_ne_zero (fun h ↦ S.hnC (by rw [← map_natCast φ, h, map_zero]))
        (pow_ne_zero _ (hΓ q hq).1),
      (hΓ q hq).2⟩
  have hmult : ∀ q ∈ Γ, ((Γ.filter fun q' ↦ key q' = key q).map fun q ↦ q.2.2).sum = q.2.2 :=
    mult_of_mem key (fun q ↦ q.2.2) Γ hndK
  constructor
  · intro h
    obtain ⟨⟨j, cs⟩, hjc⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨WF, hWF0, hsupp, hv⟩ := supPrincipalC_sound f S.n S.hn _ Γ _ hΓF hjc
    set WC := WF.map (mapRingHom φ)
    have hWC0 : WC ≠ 0 := (Polynomial.map_ne_zero_iff (Polynomial.map_injective _ φ.injective)).mpr
      hWF0
    refine S.cert_principal (K := K) hcop WC hWC0 _ (fun i a hia ↦ ?_) _ _ hTvalid
      (sum_mult key (fun q ↦ q.2.2) Γ hndK) (fun Q hQ ↦ ?_)
    · rw [hdeg]
      refine hsupp i a (fun h0 ↦ hia ?_)
      simp [WC, Polynomial.coeff_map, h0]
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hQ)
      rw [hmult q hq]
      have := vanishAtN_map ψ (hv q hq)
      rw [hpK, show WC.map (mapRingHom (algebraMap C K)) = WF.map (mapRingHom ψ) by
        simp [WC, Polynomial.map_map, ψ]]
      exact this
  · intro h
    obtain ⟨W, hW0, hsupp, hv⟩ := S.principal_cert (K := K) hcop _ _ hTvalid h
    refine supPrincipalC_complete ψ f S.n S.hn _ Γ _ hΓF (W.map (mapRingHom (algebraMap C K)))
      ((Polynomial.map_ne_zero_iff (Polynomial.map_injective _ (algebraMap C K).injective)).mpr hW0)
      (fun i a hia ↦ ?_) (fun q hq ↦ ?_)
    · have h1 : (W.coeff i).coeff a ≠ 0 := fun h0 ↦ hia (by simp [Polynomial.coeff_map, h0])
      have := hsupp i a h1
      rw [hdeg, sum_mult key (fun q ↦ q.2.2) Γ hndK] at this
      exact this
    · have := hv (key q) (List.mem_toFinset.mpr (List.mem_map_of_mem hq))
      rw [hmult q hq, hpK] at this
      exact this

end SuperData

end Differential
