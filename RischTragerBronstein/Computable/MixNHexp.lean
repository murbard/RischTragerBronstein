import RischTragerBronstein.Computable.MixNSound
import RischTragerBronstein.Computable.KerElim
import RischTragerBronstein.Computable.HexpDegenerateSpec

/-!
# Mixed towers: exponents with simple poles

`logIndep_of_hermKernelCert`: the certificate `hermKernelCert` proves that no non-zero
`ℚ`-combination `f = ∑ cⱼ bⱼ` of the exponents is a logarithmic derivative in `Kc(x)`.

Write `bⱼ = Gⱼ′ + Nⱼ / s` (Hermite part plus simple-pole part over the common squarefree `s`).
If `y′ + f y = 0`, `y ≠ 0`, then `f = (∑ cⱼ Gⱼ)′ + (∑ cⱼ Nⱼ) / s` is the logarithmic derivative of
`y⁻¹`, so `(∑ cⱼ Gⱼ)′ = 0` (`deriv_eq_zero_of_add_proper_eq_logDeriv`): a relation among the Hermite
numerators; and the residues `∑ cⱼ ρⱼ` are integers at every prime of `s`
(`residue_int_of_logDeriv`). The elimination (`kerElim_spec`) writes `∑ cⱼ ρⱼ = ∑ βₖ wₖ`, `β ≠ 0`,
which `nonRatVals` / `degenCertQ` refute.
-/

open Polynomial Differential CPoly

set_option linter.unusedSectionVars false

namespace Tower.MixN

namespace MixTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : List Kind} (T : MixTower Kc E ks)

open Tower.PrimN

/-- `ℚ[X] → F 0`, `X ↦ x`. -/
noncomputable abbrev psi0 : ℚ[X] →+* T.F 0 := T.phi0.comp (mapRingHom (algebraMap ℚ Kc))

lemma ratF0_eq (q : GFrac ℚ) :
    T.ratF 0 q = T.psi0 (CPoly.toPoly q.1) / T.psi0 (CPoly.toPoly q.2) :=
  (T.ratF_zero_eq q).trans ((T.model0_sem_eq q).trans rfl)

lemma toPoly_denProdQ (l : List (GFrac ℚ)) :
    CPoly.toPoly (denProdQ l) = (l.map fun q ↦ CPoly.toPoly q.2).prod := by
  induction l with
  | nil => simp [denProdQ, CPoly.toPoly]
  | cons q l ih =>
    simp only [denProdQ, List.foldr_cons, CPoly.toPoly_mul, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

lemma dvd_of_rem_zeroQ {s e : CPoly ℚ} (h : CPoly.isZero (divMod e s).2 = true) :
    toPoly e = toPoly (divMod e s).1 * toPoly s := by
  rw [divMod_spec e s, (isZero_iff _).mp h, add_zero]

/-- `∑ cⱼ gⱼ` in `F 0`. -/
noncomputable def gsum (cs : List ℚ) (bs : List (Code 1)) (g : Code 1 → T.F 0) : T.F 0 :=
  (List.zipWith (fun (c : ℚ) (b : Code 1) ↦ (c : T.F 0) * g b) cs bs).sum

lemma lcombF_eq_gsum (cs : List ℚ) (bs : List (Code 1)) :
    T.lcombF cs bs = T.gsum cs bs (T.ratF 0) := rfl

/-- **Linearity**: an identity `vⱼ = gⱼ′ + ψ Nⱼ / ψ s`, `gⱼ′ ψ D = ψ Pⱼ` for each `j` passes to
`ℚ`-combinations. -/
lemma gsum_decomp (s D : ℚ[X]) (hs : T.psi0 s ≠ 0) (g : Code 1 → T.F 0) (N P : Code 1 → CPoly ℚ)
    (bs : List (Code 1))
    (hv : ∀ b ∈ bs, T.ratF 0 b = (g b)′ + T.psi0 (toPoly (N b)) / T.psi0 s)
    (hp : ∀ b ∈ bs, (g b)′ * T.psi0 D = T.psi0 (toPoly (P b))) :
    ∀ cs : List ℚ, T.gsum cs bs (T.ratF 0) =
        (T.gsum cs bs g)′ + T.psi0 (lcomb cs (bs.map N)) / T.psi0 s ∧
      (T.gsum cs bs g)′ * T.psi0 D = T.psi0 (lcomb cs (bs.map P)) := by
  induction bs with
  | nil => intro cs; cases cs <;> simp [gsum, lcomb]
  | cons b bs ih =>
    intro cs
    cases cs with
    | nil => simp [gsum, lcomb]
    | cons c cs =>
      obtain ⟨ih1, ih2⟩ := ih (fun b' hb' ↦ hv b' (List.mem_cons_of_mem _ hb'))
        (fun b' hb' ↦ hp b' (List.mem_cons_of_mem _ hb')) cs
      have hvb := hv b List.mem_cons_self
      have hpb := hp b List.mem_cons_self
      have hC : T.psi0 (C c) = (c : T.F 0) := eq_ratCast (T.psi0.comp C) c
      have hdc : ((c : ℚ) : T.F 0)′ = 0 := T.deriv_ratCast0 c
      simp only [gsum, List.zipWith_cons_cons, List.sum_cons, List.map_cons, lcomb] at ih1 ih2 ⊢
      have hder : ((c : T.F 0) * g b + (List.zipWith (fun (c : ℚ) (b : Code 1) ↦
          (c : T.F 0) * g b) cs bs).sum)′ = (c : T.F 0) * (g b)′ +
          ((List.zipWith (fun (c : ℚ) (b : Code 1) ↦ (c : T.F 0) * g b) cs bs).sum)′ := by
        rw [map_add, Derivation.leibniz, hdc, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
      refine ⟨?_, ?_⟩
      · rw [ih1, hvb, hder, map_add T.psi0, map_mul T.psi0, hC]
        field_simp
        ring
      · rw [hder, map_add T.psi0, map_mul T.psi0, hC, add_mul, ← ih2, mul_assoc, hpb]

lemma degree_lcomb_lt (d : WithBot ℕ) : ∀ (cs : List ℚ) (vs : List (CPoly ℚ)),
    (∀ v ∈ vs, (toPoly v).degree < d) → ⊥ < d → (lcomb cs vs).degree < d
  | [], vs, _, hd => by simpa [lcomb] using hd
  | c :: cs, [], _, hd => by simpa [lcomb] using hd
  | c :: cs, v :: vs, h, hd => by
    have ih := degree_lcomb_lt d cs vs (fun w hw ↦ h w (List.mem_cons_of_mem _ hw)) hd
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ih)
    exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) (h v List.mem_cons_self)

lemma dvd_lcomb {s : ℚ[X]} : ∀ (cs : List ℚ) (vs : List (CPoly ℚ)), (∀ v ∈ vs, s ∣ toPoly v) →
    s ∣ lcomb cs vs
  | [], vs, _ => by simp [lcomb]
  | c :: cs, [], _ => by simp [lcomb]
  | c :: cs, v :: vs, h => by
    have ih := dvd_lcomb cs vs fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    exact dvd_add (dvd_mul_of_dvd_right (h v List.mem_cons_self) _) ih

lemma lcomb_sub_mul (f g : Code 1 → CPoly ℚ) (t : CPoly ℚ) : ∀ (cs : List ℚ) (bs : List (Code 1)),
    lcomb cs (bs.map fun b ↦ sub (mul (f b) t) (g b)) =
      lcomb cs (bs.map f) * toPoly t - lcomb cs (bs.map g)
  | [], bs => by simp [lcomb]
  | c :: cs, [] => by simp [lcomb]
  | c :: cs, b :: bs => by
    have ih := lcomb_sub_mul f g t cs bs
    simp only [lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons, toPoly_sub,
      toPoly_mul] at ih ⊢
    rw [ih]
    ring

lemma lcomb_all_zero : ∀ (cs : List ℚ) (bs : List (Code 1)), (∀ c ∈ cs, c = 0) →
    T.lcombF cs bs = 0
  | [], bs, _ => T.lcombF_nil_left bs
  | c :: cs, [], _ => T.lcombF_nil_right _
  | c :: cs, b :: bs, h => by
    rw [T.lcombF_cons, h c List.mem_cons_self, lcomb_all_zero cs bs
      fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]
    simp

lemma lcomb_map_ι (ι : ℚ →+* Kc) : ∀ (cs : List ℚ) (vs : List (CPoly ℚ)),
    (lcomb cs vs).map ι = (List.zipWith (fun c v ↦ C (ι c) * (toPoly v).map ι) cs vs).sum
  | [], vs => by simp [lcomb]
  | c :: cs, [] => by simp [lcomb]
  | c :: cs, v :: vs => by
    have ih := lcomb_map_ι ι cs vs
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [Polynomial.map_add, ih, Polynomial.map_mul, map_C]

set_option maxHeartbeats 1600000 in
/-- **Soundness of the Hermite-kernel certificate.** -/
theorem logIndep_of_hermKernelCert (h : hermKernelCert (allExps ks) = true) : T.LogIndep := by
  intro cs hl hne y hy0 hy
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  have hinj : Function.Injective T.psi0 := T.phi0_map_injective
  set ι := algebraMap ℚ Kc with hι
  set G := allExps ks with hG
  unfold hermKernelCert at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hs0, hsqf⟩, hall⟩, hmatch⟩ := h
  set s := sqDen G with hs
  set DH := denProdQ (G.map fun b ↦ ((hermNum b, hermDen b) : GFrac ℚ)) with hDH
  have hs0' : toPoly s ≠ 0 := fun h0 ↦ by simp [(isZero_iff _).mpr h0] at hs0
  have hψs : T.psi0 (toPoly s) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0'
  have hsep : ((toPoly s).map ι).Separable :=
    (PerfectField.separable_iff_squarefree.mpr (squarefreeCheck_sound hsqf)).map
  have hsqS : Squarefree ((toPoly s).map ι) := hsep.squarefree
  have hs0K : (toPoly s).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hs0'
  -- per-exponent data
  set g : Code 1 → T.F 0 := fun b ↦ T.model0.sem (ratPart (ratInt b)) with hgdef
  set N : Code 1 → CPoly ℚ := fun b ↦ mul (ratInt b).r (divMod s (ratInt b).s).1 with hNdef
  set P : Code 1 → CPoly ℚ := fun b ↦ (kerItem DH s b).1 with hPdef
  set ρ : Code 1 → CPoly ℚ := fun b ↦ (kerItem DH s b).2 with hρdef
  have hvals : ∀ b ∈ G, T.ratF 0 b = (g b)′ + T.psi0 (toPoly (N b)) / T.psi0 (toPoly s) ∧
      (g b)′ * T.psi0 (toPoly DH) = T.psi0 (toPoly (P b)) := by
    intro b hb
    obtain ⟨⟨hd0, hdiv⟩, hsdiv⟩ := (hall b hb).1
    have hd0' : toPoly (hermDen b) ≠ 0 := fun h0 ↦ by simp [(isZero_iff _).mpr h0] at hd0
    obtain ⟨hspec, -, -⟩ := T.ratInt_spec b
    have hnf := CPoly.normCoeff_spec _ T.phi0_map_injective (b : GFrac ℚ)
    simp only [RingHom.comp_apply, coe_mapRingHom] at hnf
    have hb0 : T.ratF 0 b = T.psi0 (toPoly (CPoly.normCoeff (R := ℚ) b).1) /
        T.psi0 (toPoly (CPoly.normCoeff (R := ℚ) b).2) := by
      exact (T.ratF0_eq b).trans hnf.symm
    have hden : toPoly (hermDen b) = toPoly (CPoly.normCoeff (R := ℚ) b).2 * toPoly (ratInt b).s := by
      simp [hermDen]
    have hn20 : T.psi0 (toPoly (CPoly.normCoeff (R := ℚ) b).2) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hd0' (by rw [hden, h0, zero_mul])
    have hss0 : T.psi0 (toPoly (ratInt b).s) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hd0' (by rw [hden, h0, mul_zero])
    have hgb : (g b)′ = T.ratF 0 b - T.psi0 (toPoly (ratInt b).r) / T.psi0 (toPoly (ratInt b).s) := by
      rw [T.ratF_zero_eq, hspec]
      simp only [psi0, RingHom.comp_apply, coe_mapRingHom]
      ring
    have e1 := dvd_of_rem_zeroQ hsdiv
    have e2 := dvd_of_rem_zeroQ hdiv
    have hq0 : T.psi0 (toPoly (divMod s (ratInt b).s).1) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hs0' (by rw [e1, h0, zero_mul])
    refine ⟨?_, ?_⟩
    · rw [hgb, hNdef]
      simp only [toPoly_mul, map_mul]
      rw [e1, map_mul]
      field_simp
      ring
    · rw [hgb, hb0, hPdef]
      simp only [kerItem, hermNum, toPoly_mul, toPoly_sub, map_mul, map_sub]
      rw [e2, map_mul, hden, map_mul]
      field_simp
  obtain ⟨hdec, hherm⟩ := T.gsum_decomp (toPoly s) (toPoly DH) hψs g N P G
    (fun b hb ↦ (hvals b hb).1) (fun b hb ↦ (hvals b hb).2) cs
  rw [← T.lcombF_eq_gsum] at hdec
  set W := T.gsum cs G g with hW
  set NN := lcomb cs (G.map N) with hNN
  -- `f` is the logarithmic derivative of `y⁻¹`
  have hyi0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have hlog : logDeriv y⁻¹ = T.lcombF cs G := by
    rw [logDeriv, Derivation.leibniz_inv, smul_eq_mul]
    field_simp
    linear_combination -hy
  -- the Hermite parts cancel
  have hdegN : (NN.map ι).degree < ((toPoly s).map ι).degree := by
    rw [degree_map, degree_map]
    refine degree_lcomb_lt _ cs _ (fun v hv ↦ ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      obtain ⟨-, -, hdr⟩ := T.ratInt_spec b
      rw [degree_map, degree_map] at hdr
      have e1 := dvd_of_rem_zeroQ ((hall b hb).1.2)
      have hq0 : toPoly (divMod s (ratInt b).s).1 ≠ 0 := fun h0 ↦ hs0' (by rw [e1, h0, zero_mul])
      simp only [hNdef, toPoly_mul]
      rw [e1, degree_mul, degree_mul, add_comm (degree (toPoly (divMod s (ratInt b).s).1))]
      exact WithBot.add_lt_add_right (degree_ne_bot.mpr hq0) hdr
    · exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hs0')
  have hW0 : W′ = 0 := deriv_eq_zero_of_add_proper_eq_logDeriv (K := T.F 0) hD (NN.map ι)
    ((toPoly s).map ι) hsqS hdegN W y⁻¹ hyi0 (by rw [hlog, hdec]; rfl)
  -- a relation among the Hermite numerators
  have hP0 : lcomb cs (G.map P) = 0 := hinj (by rw [← hherm, hW0, zero_mul, map_zero])
  -- integer residues
  have hy' : (y⁻¹)′ = algebraMap Kc[X] (T.F 0) (NN.map ι) /
      algebraMap Kc[X] (T.F 0) ((toPoly s).map ι) * y⁻¹ := by
    have h1 : logDeriv y⁻¹ = algebraMap Kc[X] (T.F 0) (NN.map ι) /
        algebraMap Kc[X] (T.F 0) ((toPoly s).map ι) := by
      rw [hlog, hdec, hW0, zero_add]; rfl
    rw [logDeriv] at h1
    field_simp at h1 ⊢
    linear_combination h1
  have hres := fun p hp hps ↦
    residue_int_of_logDeriv hD (NN.map ι) ((toPoly s).map ι) hs0K y⁻¹ hyi0 hy' p hp hps
  have hρs : toPoly s ∣ lcomb cs (G.map ρ) * derivative (toPoly s) - NN := by
    have := dvd_lcomb (s := toPoly s) cs (G.map fun b ↦ sub (mul (ρ b) (CPoly.deriv s)) (N b))
      (fun v hv ↦ by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
        exact ⟨_, (dvd_of_rem_zeroQ (hall b hb).2).trans (mul_comm _ _)⟩)
    rwa [lcomb_sub_mul, toPoly_deriv] at this
  -- the elimination
  have hfst : (G.map (kerItem DH s)).map Prod.fst = G.map P := by rw [List.map_map]; rfl
  have hsnd : (G.map (kerItem DH s)).map Prod.snd = G.map ρ := by rw [List.map_map]; rfl
  obtain ⟨β, hβl, hβ, hβ0⟩ := kerElim_spec (G.map (kerItem DH s)) cs (by simp [hl])
    (by rw [hfst]; exact hP0)
  rw [hsnd] at hβ
  have hβnz : ¬∀ b ∈ β, b = 0 := fun h0 ↦ hne (T.lcomb_all_zero cs G (hβ0 h0))
  have key : ∀ p : Kc[X], Irreducible p → p ∣ (toPoly s).map ι →
      ∃ q : ℚ, p ∣ (lcomb β ((G.map (kerItem DH s)).foldl kerStep ([], [])).2).map ι - C (ι q) := by
    intro p hp hps
    obtain ⟨k, hk⟩ := hres p hp hps
    have hρK := Polynomial.map_dvd ι hρs
    rw [Polynomial.map_sub, Polynomial.map_mul, ← derivative_map] at hρK
    have h1 : p ∣ ((lcomb cs (G.map ρ)).map ι - (k : Kc[X])) * derivative ((toPoly s).map ι) := by
      have e : ((lcomb cs (G.map ρ)).map ι - (k : Kc[X])) * derivative ((toPoly s).map ι) =
          ((lcomb cs (G.map ρ)).map ι * derivative ((toPoly s).map ι) - NN.map ι) +
            (NN.map ι - (k : Kc[X]) * derivative ((toPoly s).map ι)) := by ring
      rw [e]
      exact dvd_add (hps.trans hρK) hk
    have hpd : ¬p ∣ derivative ((toPoly s).map ι) := fun hd ↦
      hp.not_isUnit (hsep.isUnit_of_dvd' hps hd)
    have h2 := (hp.prime.dvd_or_dvd h1).resolve_right hpd
    refine ⟨k, ?_⟩
    have e : C (ι ((k : ℤ) : ℚ)) = ((k : ℤ) : Kc[X]) := by rw [map_intCast, C_eq_intCast]
    rw [← hβ, e]
    exact h2
  obtain ⟨ws, hws⟩ : ∃ ws, ws = ((G.map (kerItem DH s)).foldl kerStep ([], [])).2 := ⟨_, rfl⟩
  rw [← hws] at hmatch key hβl
  match ws, hmatch with
  | [], _ =>
    simp only [List.length_nil, List.length_eq_zero_iff] at hβl
    subst hβl
    exact hβnz (by simp)
  | [w], hw =>
    obtain ⟨β₁, rfl⟩ : ∃ β₁, β = [β₁] := List.length_eq_one_iff.mp hβl
    have hβ₁ : β₁ ≠ 0 := fun h0 ↦ hβnz (by simp [h0])
    have hβS : ι β₁ ≠ 0 := (map_ne_zero_iff _ ι.injective).mpr hβ₁
    refine nonRatVals_false ι hs0' hsqS hw fun p hp hps ↦ ?_
    obtain ⟨q, hq⟩ := key p hp hps
    refine ⟨q / β₁, ?_⟩
    have e : (lcomb [β₁] [w]).map ι - C (ι q) = C (ι β₁) * ((toPoly w).map ι - C (ι (q / β₁))) := by
      simp only [lcomb, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons,
        List.sum_nil, add_zero, Polynomial.map_mul, map_C]
      rw [mul_sub, ← C_mul, ← map_mul, mul_div_cancel₀ _ hβ₁]
    rw [e] at hq
    exact (hp.prime.dvd_or_dvd hq).resolve_left fun hd ↦
      hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.mpr hβS.isUnit))
  | [w₁, w₂], hw =>
    obtain ⟨β₁, β₂, rfl⟩ : ∃ β₁ β₂, β = [β₁, β₂] := by
      match β, hβl with
      | [β₁, β₂], _ => exact ⟨β₁, β₂, rfl⟩
    have hzc : β₁ ≠ 0 ∨ β₂ ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hβnz (by simp [h0.1, h0.2])
    refine degenCertQ_sound ι hw β₁ β₂ hzc fun p hp hps ↦ ?_
    obtain ⟨q, hq⟩ := key p hp hps
    refine ⟨q, ?_⟩
    simpa [lcomb, Polynomial.map_add, Polynomial.map_mul, map_C] using hq
  | w₁ :: w₂ :: w₃ :: ws', hw =>
    exact hβnz (CPoly.Kron.genResCert_sound ι s _ hw β hβl key)


end MixTower

end Tower.MixN
