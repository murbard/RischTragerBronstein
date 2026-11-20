import RischTragerBronstein.Computable.PrimNElem
import RischTragerBronstein.Liouville.Strong
import RischTragerBronstein.Differential.Constants

/-!
# Towers of `n` primitives over `ℚ(x)`: the decision theorem

`primN_decides`: let `E = Kc(x, t₀, …, t_{n-1})` (`Kc ⊇` all constants of `E`, `x′ = 1`,
`tₘ′ = ηₘ(x)` for rational functions `ηₘ ∈ ℚ(x)` given as codes) and suppose the independence
certificate `primCert ηs n` holds. Then for **every** code `A` of `ℚ(x)(t₀)…(t_{n-1})`,

  `A` has an elementary integral over `E`  ↔  `elemP ηs n A = true`.

Heights are arbitrary. The proof of `→` moves the whole tower into an elementary extension `L`
(`transport`), where the strong Liouville theorem gives a Liouville form over
`constants L (x, t₀, …)`, and `elemP_complete` applies there; `←` is `elemP_sound`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.PrimN

universe u v

/-- `evx` through `ℚ`-evaluation. -/
lemma evx_eq_eval₂ {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [CharZero Kc] [CharZero E]
    (x : E)
    (q : GFrac ℚ) : evx Kc x q = (CPoly.toPoly q.1).eval₂ (algebraMap ℚ E) x /
      (CPoly.toPoly q.2).eval₂ (algebraMap ℚ E) x := by
  have h : (algebraMap Kc E).comp (algebraMap ℚ Kc) = algebraMap ℚ E := RingHom.ext_rat _ _
  rw [evx, aeval_def, aeval_def, eval₂_map, eval₂_map, h]

/-- Evaluation of a coefficient list, Horner style. -/
def evalList {E : Type*} [Field E] (t : E) : List E → E
  | [] => 0
  | a :: l => a + t * evalList t l

lemma map_evalList {E L : Type*} [Field E] [Field L] (j : E →+* L) (t : E) :
    ∀ l : List E, j (evalList t l) = evalList (j t) (l.map j)
  | [] => by simp [evalList]
  | a :: l => by simp [evalList, map_evalList j t l]

lemma aeval_toPoly {α : Type*} {K E : Type*} [Field K] [Differential K] [Field E] [Algebra K E]
    {O : COps α} (M : CField α K O) (t : E) :
    ∀ p : GPoly α, aeval t (GPoly.toPoly M p) = evalList t (p.map fun a ↦ algebraMap K E (M.sem a))
  | [] => by simp [evalList]
  | a :: p => by
    rw [GPoly.toPoly_cons, map_add, map_mul, aeval_C, aeval_X, aeval_toPoly M t p]
    rfl

namespace PrimTower

variable {Kc : Type*} {E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
variable [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : List (Code 1)}
variable (T : PrimTower Kc E ηs)
variable {Kc' : Type*} {L : Type v} [Field Kc'] [Field L] [Algebra Kc' L] [Differential Kc']
variable [Differential L] [DifferentialAlgebra Kc' L] [CharZero Kc'] (T' : PrimTower Kc' L ηs)

/-- **Transport**: two towers related by a ring homomorphism `j` (`x ↦ x`, `tᵢ ↦ tᵢ`) give the
same values to every code. -/
theorem transport (j : E →+* L) (hx : T'.x = j T.x) (hts : ∀ i, T'.ts i = j (T.ts i)) :
    ∀ (m : ℕ) (h : T.Tr m) (h' : T'.Tr m) (q : Code (m + 1)),
      (((T'.MP m h').sem q : T'.F m) : L) = j (((T.MP m h).sem q : T.F m) : E)
  | 0, h, h', q => by
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap Kc' L).injective
    change ((T'.model0.sem q : T'.F 0) : L) = j ((T.model0.sem q : T.F 0) : E)
    rw [T'.sem_model0, T.sem_model0, evx_eq_eval₂ (Kc := Kc') T'.x (q : GFrac ℚ),
      evx_eq_eval₂ (Kc := Kc) T.x (q : GFrac ℚ), map_div₀, hom_eval₂,
      hom_eval₂, RingHom.ext_rat (j.comp (algebraMap ℚ E)) (algebraMap ℚ L), hx]
  | m + 1, h, h', q => by
    have ih := transport j hx hts m (fun i hi ↦ h i (by omega)) (fun i hi ↦ h' i (by omega))
    rw [sem_MP_succ, sem_MP_succ, IntermediateField.coe_div, IntermediateField.coe_div, coe_phi,
      coe_phi, coe_phi, coe_phi, map_div₀, aeval_toPoly, aeval_toPoly, aeval_toPoly,
      aeval_toPoly, map_evalList, map_evalList, List.map_map, List.map_map, hts]
    congr 2 <;> exact List.map_congr_left fun a _ ↦ ih a

/-- `j` maps each level into the corresponding level. -/
theorem map_mem_F (j : E →+* L) (hj : ∀ z : E, (j z)′ = j z′) (hx : T'.x = j T.x)
    (hts : ∀ i, T'.ts i = j (T.ts i)) : ∀ (m : ℕ) (z : E), z ∈ T.F m → j z ∈ T'.F m
  | 0, z, hz => by
    let S : IntermediateField Kc E :=
      { carrier := {w | j w ∈ T'.F 0}
        mul_mem' := fun {a b} ha hb ↦ by
          change j (a * b) ∈ T'.F 0; rw [map_mul]; exact mul_mem ha hb
        one_mem' := by change j 1 ∈ T'.F 0; rw [map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          change j (a + b) ∈ T'.F 0; rw [map_add]; exact add_mem ha hb
        zero_mem' := by change j 0 ∈ T'.F 0; rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun c ↦ T'.const_mem 0 _ (by
          rw [hj, deriv_algebraMap, T.hC, map_zero, map_zero])
        inv_mem' := fun a ha ↦ by
          change j a⁻¹ ∈ T'.F 0; rw [map_inv₀]; exact inv_mem ha }
    have hle : Kc⟮T.x⟯ ≤ S := by
      rw [adjoin_simple_le_iff]
      change j T.x ∈ T'.F 0
      rw [← hx]
      exact T'.x_mem 0
    exact hle hz
  | m + 1, z, hz => by
    have ih := map_mem_F j hj hx hts m
    let S : IntermediateField (T.F m) E :=
      { carrier := {w | j w ∈ T'.F (m + 1)}
        mul_mem' := fun {a b} ha hb ↦ by
          change j (a * b) ∈ T'.F (m + 1); rw [map_mul]; exact mul_mem ha hb
        one_mem' := by change j 1 ∈ T'.F (m + 1); rw [map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          change j (a + b) ∈ T'.F (m + 1); rw [map_add]; exact add_mem ha hb
        zero_mem' := by change j 0 ∈ T'.F (m + 1); rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun a ↦ T'.le_succ m (ih a a.2)
        inv_mem' := fun a ha ↦ by
          change j a⁻¹ ∈ T'.F (m + 1); rw [map_inv₀]; exact inv_mem ha }
    have hle : (T.F m)⟮T.ts m⟯ ≤ S := by
      rw [adjoin_simple_le_iff]
      change j (T.ts m) ∈ T'.F (m + 1)
      rw [← hts]
      exact T'.ts_mem m
    exact hle ((T.mem_F_succ).mp hz)

/-- **Towers of `n` primitives over `ℚ(x)` are decided**, for every `n`: when `E` is generated
by `x, t₀, …, t_{n-1}` over its constants and the independence certificate holds, a code `A`
has an elementary integral over `E` if and only if `elemP ηs n A = true`. -/
theorem primN_decides (n : ℕ) (hgen : T.F n = ⊤) (hcert : primCert ηs n = true)
    (A : Code (n + 1)) :
    HasElementaryIntegral ((((T.MP n (T.tr_of_ND (T.nd_of_primCert n hcert))).sem A : T.F n)) :
      E) ↔ elemP ηs n A = true := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  constructor
  · rintro ⟨L, _, _, _, _, hE, g, hg⟩
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
    -- the constants of `L`
    let Cc := constants L
    let _ : Differential Cc := ⟨0⟩
    have hDAc : DifferentialAlgebra Cc L := ⟨fun c ↦ c.2⟩
    have hcharC : CharZero Cc := ⟨fun a b h ↦ by
      have := congrArg (fun z : Cc ↦ (z : L)) h
      simpa using this⟩
    set j := algebraMap E L with hjdef
    have hj : ∀ z : E, (j z)′ = j z′ := fun z ↦ deriv_algebraMap z
    -- the same tower inside `L`
    let T' : PrimTower Cc L ηs :=
      { x := j T.x
        ts := fun i ↦ j (T.ts i)
        hC := fun _ ↦ rfl
        hx := by rw [hj, T.hx, map_one]
        ht := fun m ↦ by
          rw [hj, T.ht, evx_eq_eval₂ (Kc := Kc) T.x (eta ηs m),
            evx_eq_eval₂ (Kc := Cc) (j T.x) (eta ηs m), map_div₀, hom_eval₂, hom_eval₂,
            RingHom.ext_rat (j.comp (algebraMap ℚ E)) (algebraMap ℚ L)]
        hCall := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩ }
    have hnd' := T'.nd_of_primCert n hcert
    have htrans := T.transport T' j rfl (fun _ ↦ rfl) n (T.tr_of_ND (T.nd_of_primCert n hcert))
      (T'.tr_of_ND hnd') A
    -- the strong Liouville theorem
    obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
    have hcf : ∀ z ∈ constField E L, z ∈ T'.F n := by
      let N : IntermediateField E L :=
        { (T'.F n).toSubfield with
          algebraMap_mem' := fun e ↦ T.map_mem_F T' j hj rfl (fun _ ↦ rfl) n e
            (by rw [hgen]; trivial) }
      have : constField E L ≤ N := adjoin_le_iff.mpr fun z hz ↦ T'.const_mem n z hz
      exact fun z hz ↦ this hz
    refine T'.elemP_complete n hnd' A ⟨0, zero_mem _, ι, s, c, u, v, fun i hi ↦
      ⟨(hdata i hi).1, hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩, hcf _ hv, ?_⟩
    rw [sub_zero, htrans]
    exact heq
  · intro h
    exact (T.elemP_sound n (T.nd_of_primCert n hcert) A h).hasElementaryIntegral

end PrimTower

end Tower.PrimN
