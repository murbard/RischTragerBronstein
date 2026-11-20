import RischTragerBronstein.Jacobian.CertCheck
import RischTragerBronstein.Computable.Hermite
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Non-elementarity from a checked certificate, any genus

For `y² = f(x)`, `f ∈ ℤ[x]` squarefree of degree `2g + 1`, and integer data `(aᵢ, bᵢ, zᵢ)` with
`bᵢ² = f(aᵢ)`, `bᵢ ≠ 0`, `zᵢ ≠ 0` and distinct `aᵢ`, consider

  `∫ (B(x) + ∑ᵢ zᵢ bᵢ / (x − aᵢ)) dx / y`

(residue `zᵢ` at `(aᵢ, bᵢ)`, `−zᵢ` at `(aᵢ, −bᵢ)`, and any `B` over the constants). By Abel's
direction (`hyp_principal_of_elementary`), if the integral is elementary then the residue
divisor `∑ zᵢ ([Pᵢ] − [σPᵢ])` is torsion. `nonElemCheck` certifies that it is not
(`nonTorsionCheck`), so `not_elementary_of_check` concludes that the integral is **not
elementary**. Certificates are found by `findCert` and re-checked by the kernel.
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

/-- The residue divisor of `∑ zᵢ bᵢ / ((x − aᵢ) y)` in `ψ`-form. -/
def ptsDiv (pts : List (ℤ × ℤ × ℤ)) : EDiv ℤ :=
  pts.map fun t ↦ (t.1, t.2.2.sign * t.2.1, 2 * t.2.2.natAbs)

/-- **The complete check**: well-formed data, `f` squarefree, and a non-torsion certificate. -/
def nonElemCheck (f : List ℤ) (g : ℕ) (pts : List (ℤ × ℤ × ℤ)) (p q : ℕ) [Fact p.Prime]
    [Fact q.Prime] (cp cq : LocalCert) (r k : ℕ) : Bool :=
  decide ((pts.map (·.1)).Nodup ∧ ∀ t ∈ pts, t.2.2 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.1 ^ 2 = evalC f t.1) &&
  squarefreeCheck (f.map (Int.castRingHom ℚ)) && nonTorsionCheck f g (ptsDiv pts) p q cp cq r k

/-- Principality only depends on the support and the degree of `Γ`. -/
lemma PrincipalMul.congr {K : Type*} [Field K] {f : K[X]} {g : ℕ} {Γ Γ' : EDiv K} {n : ℕ}
    (hmem : ∀ q, q ∈ Γ → q ∈ Γ') (hdeg : edeg Γ = edeg Γ') (h : PrincipalMul f g Γ' n) :
    PrincipalMul f g Γ n := by
  obtain ⟨ψ, h0, hp, hv⟩ := h
  refine ⟨ψ, h0, hdeg ▸ hp, fun q hq ↦ hv q ?_⟩
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q', hmem q' hq', rfl⟩

lemma toPoly_map_list {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : List R) :
    toPoly (l.map φ) = (toPoly l).map φ := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Soundness of `nonElemCheck`**: the integral is not elementary. -/
theorem not_elementary_of_check (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} {pts : List (ℤ × ℤ × ℤ)} {p q : ℕ} [hp : Fact p.Prime]
    [hq : Fact q.Prime] {cp cq : LocalCert} {r k : ℕ}
    (hcheck : nonElemCheck f g pts p q cp cq r k = true)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ)))
    (hgen : ∀ z : E, InHyp Kc x y z) (B : Kc[X]) :
    ¬ HasElementaryIntegral ((aeval x B + ∑ i : Fin pts.length,
      algebraMap Kc E ((pts[i].2.2 : Kc) * (pts[i].2.1 : Kc)) /
        (x - algebraMap Kc E (pts[i].1 : Kc))) / y) := by
  classical
  intro hel
  simp only [nonElemCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨hnd, hpt⟩, hsf⟩, hnt⟩ := hcheck
  have hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)) := by
    have := squarefreeCheck_sound hsf; rwa [toPoly_map_list] at this
  have hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1 := by
    have hP : localCheck p f g (ptsDiv pts) cp = true := by
      simp only [nonTorsionCheck, Bool.and_eq_true] at hnt; exact hnt.1.1
    have hdp := (localCheck_spec hP).1.hdeg
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _), ← hdp,
      natDegree_map_eq_of_injective (RingHom.injective_int _)]
  obtain ⟨Λ, hΛ1⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : Kc) ≠ 0)
  set n := pts.length
  let a : Fin n → ℚ := fun i ↦ (pts[i].1 : ℚ)
  let b : Fin n → ℚ := fun i ↦ (pts[i].2.1 : ℚ)
  let z : Fin n → ℤ := fun i ↦ pts[i].2.2
  have hel' : HasElementaryIntegral ((aeval x B + ∑ i ∈ (Finset.univ : Finset (Fin n)),
      algebraMap Kc E (((z i : ℤ) : Kc) * algebraMap ℚ Kc (b i)) /
        (x - algebraMap Kc E (algebraMap ℚ Kc (a i)))) / y) := by
    convert hel using 5 <;> simp [a, b, z]
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin n)), b i ≠ 0 := fun i _ ↦ by
    simpa [b] using (hpt _ (List.getElem_mem i.2)).2.1
  have hab : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      b i ^ 2 = (((toPoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ)).eval (a i) := by
    intro i _
    rw [Algebra.algebraMap_self, Polynomial.map_id, eval_map, show a i =
      Int.castRingHom ℚ pts[i].1 from rfl, eval₂_at_apply, ← evalC_eq]
    have h3 := congrArg (Int.cast : ℤ → ℚ) (hpt _ (List.getElem_mem i.2)).2.2
    simpa [b] using h3
  have hinj : Set.InjOn a (Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    have h1 : pts[i].1 = pts[j].1 := by simpa [a] using hij
    have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
      (hi := by simp [n]) (hj := by simp [n])).mp (by simpa using h1)
    exact Fin.ext this
  obtain ⟨m, hm1, hm⟩ := hyp_principal_of_elementary hC hCall x y hx _ hsq hdeg hy hgen
    (algebraMap ℚ Kc) Finset.univ a b hb hab hinj B (fun i ↦ ((z i : ℤ) : Kc)) hel' Λ z 1
    one_ne_zero (fun i _ ↦ by
      rw [show ((z i : ℤ) : Kc) = (z i) • (1 : Kc) by simp, map_zsmul, hΛ1]; simp)
  rw [Algebra.algebraMap_self, Polynomial.map_id] at hm
  refine not_torsion_of_check hnt m hm1 (PrincipalMul.congr ?_ ?_ hm)
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    unfold resDiv
    refine List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_filter.mpr ⟨Finset.mem_toList.mpr
      (Finset.mem_univ _), by simpa [z] using (hpt _ (List.getElem_mem hi)).1⟩, ?_⟩
    simp [a, b, z]
  · rw [edeg_emap, edeg_resDiv]
    simp only [edeg, ptsDiv, List.map_map, Function.comp_def]
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem (by simp [n])
    intro i h1 h2
    simp [z]
