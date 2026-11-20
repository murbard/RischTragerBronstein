import RischTragerBronstein.Torsion.NonSpec4

/-!
# Non-special base points exist (5): the certificate

* `AdmFib.perm`, `kerSp_perm`: reordering the points of each fibre so that the chosen one comes first;
* **`nsCheck_complete`**: if the kernel space at level `g` of `g` fibres (chosen index `0`) is spanned by
  `e0`, the evaluation at each chosen point is a combination of the evaluations at the non-chosen points
  on `Vsp g` (duality, `mem_span_of_iInf_ker_le_ker`), so a certificate `λ` passing `nsCheck` exists.
-/

open Polynomial Module

namespace Curves

open CPoly Sup GTors

section Perm

variable {K : Type*} [Field K] {n : ℕ} {B : Fin n → K[X][X]} (δ : Fin n → ℕ)

/-- Reordering the points of a fibre. -/
noncomputable def AdmFib.perm (fb : AdmFib B) (σ : Equiv.Perm (Fin n)) : AdmFib B where
  x := fb.x
  ys := fun k ↦ fb.ys (σ k)
  hdet := by
    have := Matrix.det_permute σ (Matrix.of fun (k j : Fin n) ↦ evalW (B j) fb.x (fb.ys k))
    rw [show (Matrix.of fun (k j : Fin n) ↦ evalW (B j) fb.x (fb.ys k)).submatrix σ id =
      Matrix.of fun (k j : Fin n) ↦ evalW (B j) fb.x (fb.ys (σ k)) by ext; simp] at this
    rw [this]
    exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])
      fb.hdet

variable (hn : 0 < n)

/-- Putting the chosen point first. -/
noncomputable def permF {r : ℕ} (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n) : Fin r → AdmFib B :=
  fun l ↦ (f l).perm (Equiv.swap ⟨0, hn⟩ (j₀ l))

lemma kerSp_perm (m r : ℕ) (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n) :
    kerSp δ m r (permF hn f j₀) (fun _ ↦ ⟨0, hn⟩) = kerSp δ m r f j₀ := by
  ext c
  rw [mem_kerSp, mem_kerSp]
  refine and_congr_right fun _ ↦ ⟨fun h l k hk ↦ ?_, fun h l k hk ↦ ?_⟩
  · have := h l (Equiv.swap ⟨0, hn⟩ (j₀ l) k) (by
      intro h'; apply hk
      have := congrArg (Equiv.swap ⟨0, hn⟩ (j₀ l)) h'
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this)
    simpa [permF, AdmFib.perm] using this
  · have := h l (Equiv.swap ⟨0, hn⟩ (j₀ l) k) (by
      intro h'; apply hk
      have := congrArg (Equiv.swap ⟨0, hn⟩ (j₀ l)) h'
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this)
    simpa [permF, AdmFib.perm] using this

lemma e0_perm {r : ℕ} (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n) :
    e0 hn (permF hn f j₀) = e0 hn f := rfl

end Perm

section Cert

lemma sum_subtype_dite {F α : Type*} [AddCommMonoid F] [Fintype α] (P : α → Prop) [DecidablePred P]
    [Fintype (Subtype P)] (h : Subtype P → F) :
    ∑ q, h q = ∑ p, if hp : P p then h ⟨p, hp⟩ else 0 := by
  rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
  exact Finset.sum_bij (fun q _ ↦ ⟨q.1, by simp [q.2]⟩) (by simp) (by simp [Subtype.ext_iff])
    (fun b _ ↦ ⟨⟨b.1, (Finset.mem_filter.mp b.2).2⟩, by simp⟩) (by simp)

variable {F : Type*} [Field F] [DecidableEq F]

lemma evPt_single {n : ℕ} (B : Fin n → F[X][X]) (x y : F) (j : Fin n) (d : ℕ) :
    evPt B x y (Pi.single j (X ^ d)) = x ^ d * evalW (B j) x y := by
  classical
  rw [evPt_apply, Finset.sum_eq_single j (fun j' _ hj ↦ by
    rw [Pi.single_eq_of_ne hj, eval_zero, zero_mul]) (by simp), Pi.single_eq_same, eval_pow, eval_X]

/-- **Duality**: on `Vsp g`, evaluation at a chosen point is a combination of the evaluations at the
non-chosen points. -/
theorem exists_comb {n g : ℕ} (hn : 0 < n) (B : Fin n → F[X][X]) (δ : Fin n → ℕ)
    (f : Fin g → AdmFib B) (h1 : kerSp δ g g f (fun _ ↦ ⟨0, hn⟩) ≤ F ∙ e0 hn f) (i0 : Fin g) :
    ∃ μ : QIdx (fun _ : Fin g ↦ (⟨0, hn⟩ : Fin n)) → F, ∀ c ∈ Vsp F δ g,
      evPt B (f i0).x ((f i0).ys ⟨0, hn⟩) c =
        ∑ q, μ q * evPt B (f q.1.1).x ((f q.1.1).ys q.1.2) c := by
  classical
  let L : QIdx (fun _ : Fin g ↦ (⟨0, hn⟩ : Fin n)) → Vsp F δ g →ₗ[F] F :=
    fun q ↦ evPt B (f q.1.1).x ((f q.1.1).ys q.1.2) ∘ₗ (Vsp F δ g).subtype
  have hμ : ∃ μ : QIdx (fun _ : Fin g ↦ (⟨0, hn⟩ : Fin n)) → F,
      ∑ q, μ q • L q = evPt B (f i0).x ((f i0).ys ⟨0, hn⟩) ∘ₗ (Vsp F δ g).subtype := by
    refine (Submodule.mem_span_range_iff_exists_fun F).mp (mem_span_of_iInf_ker_le_ker ?_)
    intro c hc
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hc
    have hk : (c : Fin n → F[X]) ∈ kerSp δ g g f (fun _ ↦ ⟨0, hn⟩) :=
      (mem_kerSp _ _ _ _ _ _).mpr ⟨c.2, fun l k hk ↦ hc ⟨(l, k), hk⟩⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h1 hk)
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← ha, map_smul,
      e0_evPt, smul_zero]
  obtain ⟨μ, hμ⟩ := hμ
  refine ⟨μ, fun c hc ↦ ?_⟩
  have := LinearMap.congr_fun hμ ⟨c, hc⟩
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.comp_apply, Submodule.subtype_apply, L] at this
  exact this.symm

/-- **Completeness of `nsCheck`.** -/
theorem nsCheck_complete {n g : ℕ} (hn : 0 < n) (δL : List ℕ) (Bc : List (BPoly F)) (xs : List F)
    (ys : List (List F)) (f : Fin g → AdmFib (fun j : Fin n ↦ toB (Bc.getD j [])))
    (hfx : ∀ l : Fin g, (f l).x = xs.getD l 0)
    (hfy : ∀ (l : Fin g) (k : Fin n), (f l).ys k = (ys.getD l []).getD k 0)
    (h1 : kerSp (fun j ↦ δL.getD j 0) g g f (fun _ ↦ ⟨0, hn⟩) ≤ F ∙ e0 hn f) :
    ∃ lam, nsCheck n g δL Bc xs ys lam = true := by
  classical
  have hrow : ∀ (i : Fin g) (k : Fin n) (j : Fin n) (d : ℕ), nsRow Bc xs ys i k j d =
      evPt (fun j : Fin n ↦ toB (Bc.getD j [])) (f i).x ((f i).ys k) (Pi.single j (X ^ d)) := by
    intro i k j d
    rw [evPt_single, nsRow, evalB_eq, hfx, hfy]
  have hμ := exists_comb hn _ (fun j ↦ δL.getD j 0) f h1
  choose μ hμ using hμ
  set lamF : ℕ → ℕ → ℕ → F := fun i0 i k ↦
    if h : i0 < g ∧ i < g ∧ k < n ∧ k ≠ 0 then
      μ ⟨i0, h.1⟩ ⟨(⟨i, h.2.1⟩, ⟨k, h.2.2.1⟩), fun h' ↦ h.2.2.2 (congrArg Fin.val h')⟩ else 0
  refine ⟨(List.range g).map fun i0 ↦ (List.range (g * n)).map fun idx ↦ lamF i0 (idx / n) (idx % n),
    ?_⟩
  have hlam : ∀ i0 i k, i0 < g → i < g → k < n →
      (((List.range g).map fun i0 ↦ (List.range (g * n)).map fun idx ↦
        lamF i0 (idx / n) (idx % n)).getD i0 []).getD (i * n + k) 0 = lamF i0 i k := by
    intro i0 i k hi0 hi hk
    have hlt : i * n + k < g * n := by
      calc i * n + k < i * n + n := by omega
        _ = (i + 1) * n := by ring
        _ ≤ g * n := Nat.mul_le_mul_right _ hi
    have hdiv : (i * n + k) / n = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk, zero_add]
    have hmod : (i * n + k) % n = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    simp [List.getD_eq_getElem?_getD, hi0, hlt, hdiv, hmod]
  simp only [nsCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq]
  intro i0 hi0 j hj d _
  by_cases hd : d + δL.getD j 0 ≤ g
  · right
    -- the test vector
    have hv : (Pi.single (⟨j, hj⟩ : Fin n) (X ^ d) : Fin n → F[X]) ∈ Vsp F (fun j ↦ δL.getD j 0) g := by
      rw [mem_Vsp]
      intro j'
      by_cases hj' : j' = ⟨j, hj⟩
      · subst hj'
        rw [Pi.single_eq_same, mem_degreeLT, degree_X_pow]
        exact_mod_cast (show d < g + 1 - δL.getD j 0 by omega)
      · rw [Pi.single_eq_of_ne hj']; exact Submodule.zero_mem _
    have he := hμ ⟨i0, hi0⟩ _ hv
    rw [show nsRow Bc xs ys i0 0 j d = nsRow Bc xs ys (⟨i0, hi0⟩ : Fin g) (⟨0, hn⟩ : Fin n)
      (⟨j, hj⟩ : Fin n) d from rfl, hrow, he]
    rw [sum_subtype_dite (fun p : Fin g × Fin n ↦ p.2 ≠ (⟨0, hn⟩ : Fin n)), Fintype.sum_prod_type,
      Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk0 : k = ⟨0, hn⟩
    · subst hk0
      simp
    · have hk0' : (k : ℕ) ≠ 0 := fun h ↦ hk0 (Fin.ext h)
      rw [dif_pos hk0, if_neg hk0', hlam i0 i k hi0 i.2 k.2,
        show nsRow Bc xs ys i k j d = nsRow Bc xs ys i k (⟨j, hj⟩ : Fin n) d from rfl, hrow]
      simp only [lamF, dif_pos (show i0 < g ∧ (i : ℕ) < g ∧ (k : ℕ) < n ∧ (k : ℕ) ≠ 0 from
        ⟨hi0, i.2, k.2, hk0'⟩)]
  · left; exact hd

end Cert

end Curves
