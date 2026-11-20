import RischTragerBronstein.Algebraic.SupRedRF
import RischTragerBronstein.Algebraic.SupRedG
import RischTragerBronstein.Computable.NFK
import RischTragerBronstein.Elliptic.DV.GoodRed

/-!
# Reduction of simple algebraic extensions modulo `p`

For a computable field `K` with a reduction `R : RedFns p K` induced by `φ : K → ℚ_p`, and
`f ∈ K[y]` irreducible with integral coefficients whose reduction has a simple root `s ∈ 𝔽_p`,
`nfkFns R s` reduces `K[y]/(f)` by `y ↦ s`. It is induced by an embedding (`nfkFns_exists`): Hensel's
lemma lifts `s` to a root `ρ ∈ ℤ_p` of `φ(f)`, and `y ↦ ρ` extends `φ`.
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Hensel's lemma** over `ℤ_p`: a simple root modulo `p` lifts. -/
lemma hensel_root_padic (F : ℤ_[p][X]) (s : ZMod p)
    (hs : (F.map PadicInt.toZMod).eval s = 0)
    (hs' : ((derivative F).map PadicInt.toZMod).eval s ≠ 0) :
    ∃ z : ℤ_[p], F.eval z = 0 ∧ PadicInt.toZMod z = s := by
  set a : ℤ_[p] := (s.val : ℤ_[p])
  have ha : PadicInt.toZMod a = s := by
    simp only [a, map_natCast, ZMod.natCast_zmod_val]
  have hev : ∀ G : ℤ_[p][X], PadicInt.toZMod (G.aeval a) = (G.map PadicInt.toZMod).eval s := by
    intro G
    rw [aeval_def, eval_map, ← ha, hom_eval₂]
    congr 1
  have h1 : ‖(F.aeval a : ℚ_[p])‖ < 1 := by
    rw [EllDV.norm_lt_one_iff_toZMod, hev]; exact hs
  have h2 : ‖((derivative F).aeval a : ℚ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [EllDV.norm_lt_one_iff_toZMod, hev]; exact hs'
  obtain ⟨z, hz, hza, -⟩ := hensels_lemma (F := F) (a := a) (by
    change ‖(F.aeval a : ℚ_[p])‖ < ‖((derivative F).aeval a : ℚ_[p])‖ ^ 2
    rw [h2, one_pow]; exact h1)
  refine ⟨z, by rwa [Polynomial.coe_aeval_eq_eval] at hz, ?_⟩
  have hlt : ‖((z - a : ℤ_[p]) : ℚ_[p])‖ < 1 := by
    have : ‖z - a‖ < 1 := by
      calc ‖z - a‖ < ‖(derivative F).aeval a‖ := hza
        _ = 1 := h2
    exact this
  rw [EllDV.norm_lt_one_iff_toZMod, map_sub, sub_eq_zero, ha] at hlt
  exact hlt

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

/-- **The reduction of `K[y]/(f)` at `y ↦ s`.** -/
def nfkFns (R : RedFns p K) (f : CPoly K) (s : ZMod p) : RedFns p (NFK.NF f) :=
  ⟨fun z ↦ z.1.all R.ok, fun z ↦ evalC (z.1.map R.red) s⟩

/-- **`nfkFns` is induced by an embedding.** -/
theorem nfkFns_exists (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) (f : CPoly K)
    [Fact (Irreducible (toPoly f))] (hf : ∀ c ∈ f, R.ok c = true) (s : ZMod p)
    (hs : evalC (f.map R.red) s = 0) (hs' : evalC (CPoly.deriv (f.map R.red)) s ≠ 0) :
    ∃ φ' : NFK.NF f →+* ℚ_[p], RedValid p (nfkFns R f s) φ' := by
  classical
  -- integral lifts of the coefficients
  set zOf : K → ℤ_[p] := fun c ↦ if hc : R.ok c = true then Classical.choose (hR c hc) else 0
  have hzOf : ∀ c, R.ok c = true → φ c = (zOf c : ℚ_[p]) ∧ PadicInt.toZMod (zOf c) = R.red c :=
    fun c hc ↦ by
      simp only [zOf, dif_pos hc]
      exact Classical.choose_spec (hR c hc)
  set F : ℤ_[p][X] := toPoly (f.map zOf) with hF
  have hFmap : F.map (algebraMap ℤ_[p] ℚ_[p]) = (toPoly f).map φ := by
    rw [hF, ← toPoly_mapHom, ← toPoly_mapHom, List.map_map]
    congr 1
    refine List.map_congr_left fun c hc ↦ ?_
    exact ((hzOf c (hf c hc)).1).symm
  have hFred : F.map PadicInt.toZMod = toPoly (f.map R.red) := by
    rw [hF, ← toPoly_mapHom, List.map_map]
    congr 1
    refine List.map_congr_left fun c hc ↦ ?_
    exact (hzOf c (hf c hc)).2
  have hFd : (derivative F).map PadicInt.toZMod = toPoly (CPoly.deriv (f.map R.red)) := by
    rw [← derivative_map, hFred, toPoly_deriv]
  obtain ⟨ρ, hρ, hρs⟩ := hensel_root_padic F s (by rw [hFred, ← evalC_eq]; exact hs)
    (by rw [hFd, ← evalC_eq]; exact hs')
  have hroot : (toPoly f).eval₂ φ (ρ : ℚ_[p]) = 0 := by
    rw [← eval_map, ← hFmap, eval_map, show (ρ : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] ρ from rfl,
      eval₂_at_apply, hρ, map_zero]
  refine ⟨(AdjoinRoot.lift φ (ρ : ℚ_[p]) hroot).comp (NFK.toARHom f), fun z hz ↦ ?_⟩
  obtain ⟨w, hw, hwr⟩ := lift_list R φ hR ρ z.1 (List.all_eq_true.mp hz)
  refine ⟨w, ?_, ?_⟩
  · show AdjoinRoot.lift φ (ρ : ℚ_[p]) hroot (AdjoinRoot.mk _ (toPoly z.1)) = _
    rw [AdjoinRoot.lift_mk, hw]; rfl
  · rw [hwr, hρs]; rfl

end Sup
