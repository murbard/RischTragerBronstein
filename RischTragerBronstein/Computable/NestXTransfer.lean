import RischTragerBronstein.Computable.NestXBase

/-!
# Mixed towers: transfer into a differential extension

`map_mem_FX`: a differential embedding `E → L` carrying the tower `T` onto `T'` maps each level
into the corresponding level. `towerIn`: the image of a mixed tower in a differential field
extension `L` of `E` (over the constants of `L`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP

universe u v

namespace NestMTower

variable {Kc : Type*} {E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
variable [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

lemma x_memX (m : ℕ) : T.x ∈ T.F m :=
  T.F_mono (Nat.zero_le m) (mem_adjoin_simple_self Kc T.x)

lemma const_memX (m : ℕ) (z : E) (hz : z′ = 0) : z ∈ T.F m := by
  obtain ⟨κ, rfl⟩ := T.hCall z hz
  exact (T.F m).algebraMap_mem κ

variable {Kc' : Type*} {L : Type v} [Field Kc'] [Field L] [Algebra Kc' L] [Differential Kc']
variable [Differential L] [DifferentialAlgebra Kc' L] [CharZero Kc']
  (T' : NestMTower Kc' L ks)

/-- `j` maps each level into the corresponding level. -/
theorem map_mem_FX (j : E →+* L) (hj : ∀ z : E, (j z)′ = j z′) (hx : T'.x = j T.x)
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
        algebraMap_mem' := fun c ↦ T'.const_memX 0 _ (by
          rw [hj, deriv_algebraMap, T.hC, map_zero, map_zero])
        inv_mem' := fun a ha ↦ by
          change j a⁻¹ ∈ T'.F 0; rw [map_inv₀]; exact inv_mem ha }
    have hle : Kc⟮T.x⟯ ≤ S := by
      rw [adjoin_simple_le_iff]
      change j T.x ∈ T'.F 0
      rw [← hx]
      exact T'.x_memX 0
    exact hle hz
  | m + 1, z, hz => by
    have ih := map_mem_FX j hj hx hts m
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

/-- The derivative of a generator is transported by a differential embedding. -/
lemma map_kder {Cc : Type*} [Field Cc] [Algebra Cc L] [CharZero Cc] [CharZero E] [CharZero L]
    (j : E →+* L) (hj : ∀ z : E, (j z)′ = j z′) (x : E) (ts : ℕ → E) (m : ℕ) (k : KindN m) :
    j (kder Kc x ts m k) = kder Cc (j x) (fun i ↦ j (ts i)) m k := by
  cases k with
  | prim η => exact map_evN (Kc := Kc) (Cc := Cc) j x ts m η
  | exp a =>
    change j ((evN Kc x ts m a)′ * ts m) = (evN Cc (j x) (fun i ↦ j (ts i)) m a)′ * j (ts m)
    rw [map_mul, ← hj, map_evN (Kc := Kc) (Cc := Cc)]

end NestMTower

end Tower.NestM
