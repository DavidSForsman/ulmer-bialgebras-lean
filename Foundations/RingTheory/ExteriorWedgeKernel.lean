module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.RingTheory.Henselian

/-!
# The kernel of wedging with a decomposable exterior product

Let `V` be a vector space over a field `k` and let `w : Fin n → V` be a linearly independent
family.  Write `ω = w 0 ∧ ⋯ ∧ w (n-1)` for the associated element of the exterior algebra of `V`.
This file proves that

```
v ∧ ω = 0  ↔  v ∈ span k {w 0, …, w (n-1)},
```

i.e. that the kernel of the linear map `wedgeRight w : V → ⋀ V`, `v ↦ ι v * ω`, is exactly the
span of the family `w`.

This is the piece of linear algebra behind Takeuchi's Lemma 4.10(i) in *A correspondence between
Hopf ideals and sub-Hopf algebras*, manuscripta math. **7** (1972): the subspace `W ⊆ V` can be
recovered from the line `k · ω ⊆ ⋀ⁿ V` it spans.

## Main results

* `ExteriorAlgebra.ιMulti_ne_zero_of_linearIndependent`: the wedge product of a linearly
  independent family is nonzero;
* `ExteriorAlgebra.ι_mul_ιMulti_eq_zero_iff`: the criterion above;
* `ExteriorAlgebra.ker_wedgeRight`: the kernel of `wedgeRight w` is `span k (range w)`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Lemma
  4.10
-/

@[expose] public section

open scoped ExteriorAlgebra

section
namespace ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Wedging on the left: `ω ↦ v ∧ ω` on decomposable products. -/
theorem ιMulti_cons (n : ℕ) (v : V) (w : Fin n → V) :
    ιMulti k (n + 1) (Fin.cons v w) = ι k v * ιMulti k n w := by
  have hv : Matrix.vecTail (Fin.cons v w) = w := funext fun i => by simp [Matrix.vecTail]
  simp [hv]

/-- Wedging a member of a family with the wedge product of the family gives zero. -/
theorem ι_mul_ιMulti_self (n : ℕ) (w : Fin n → V) (i : Fin n) :
    ι k (w i) * ιMulti k n w = 0 := by
  rw [← ιMulti_cons]
  exact (ιMulti k (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ)
    (by simp) (fun h => (Fin.succ_ne_zero i) h.symm)

/-- Wedging an element of the span of a family with the wedge product of the family gives zero. -/
theorem ι_mul_ιMulti_eq_zero_of_mem_span {n : ℕ} {w : Fin n → V} {v : V}
    (hv : v ∈ Submodule.span k (Set.range w)) : ι k v * ιMulti k n w = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hv
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_mul_assoc, ι_mul_ιMulti_self, smul_zero]

/-- The wedge product of a linearly independent family of vectors over a field is nonzero. -/
theorem ιMulti_ne_zero_of_linearIndependent {m : ℕ} {u : Fin m → V}
    (hu : LinearIndependent k u) : ιMulti k m u ≠ 0 := by
  have hker : LinearMap.ker (Fintype.linearCombination k u) = ⊥ := by
    rw [Fintype.linearIndependent_iff] at hu
    ext c
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro h; funext i; exact hu c (by simpa [Fintype.linearCombination] using h) i
    · rintro rfl; simp
  obtain ⟨L, hL⟩ := (Fintype.linearCombination k u).exists_leftInverse_of_injective hker
  set f : Fin m → Module.Dual k V := fun i => (LinearMap.proj i) ∘ₗ L with hf
  have hfu : ∀ i j, f j (u i) = if j = i then (1 : k) else 0 := by
    intro i j
    have hLu : L (u i) = Pi.single i (1 : k) := by
      have := congrArg (fun g => g (Pi.single i (1 : k))) hL
      simpa [Fintype.linearCombination] using this
    simp [hf, hLu, Pi.single_apply, eq_comm]
  intro h0
  have h1 : exteriorPower.ιMulti k m u = 0 := by
    apply Subtype.ext
    rw [exteriorPower.ιMulti_apply_coe]
    simpa using h0
  have hp := exteriorPower.pairingDual_ιMulti_ιMulti (R := k) (M := V) (n := m) f u
  rw [h1] at hp
  simp only [map_zero] at hp
  rw [show (Matrix.of fun i j => (f j) (u i)) = (1 : Matrix (Fin m) (Fin m) k) by
    ext i j; simp [hfu, Matrix.one_apply, eq_comm]] at hp
  simp at hp

/-- A vector wedges to zero against the wedge product of a linearly independent family exactly
when it lies in the span of the family. -/
theorem ι_mul_ιMulti_eq_zero_iff {n : ℕ} {w : Fin n → V} (hw : LinearIndependent k w) (v : V) :
    ι k v * ιMulti k n w = 0 ↔ v ∈ Submodule.span k (Set.range w) := by
  refine ⟨fun h => ?_, ι_mul_ιMulti_eq_zero_of_mem_span⟩
  by_contra hv
  have hcons : LinearIndependent k (Fin.cons v w) := linearIndependent_finCons.2 ⟨hw, hv⟩
  exact ιMulti_ne_zero_of_linearIndependent hcons (by rw [ιMulti_cons]; exact h)

variable (k) in
/-- Wedging with the wedge product of the family `w`, as a `k`-linear map. -/
noncomputable def wedgeRight {n : ℕ} (w : Fin n → V) : V →ₗ[k] _root_.ExteriorAlgebra k V where
  toFun v := ι k v * ιMulti k n w
  map_add' x y := by rw [map_add, add_mul]
  map_smul' c x := by rw [map_smul, smul_mul_assoc, RingHom.id_apply]

/-- `wedgeRight k w v` is the exterior product `ι k v * ιMulti k n w`. -/
@[simp] theorem wedgeRight_apply {n : ℕ} (w : Fin n → V) (v : V) :
    wedgeRight k w v = ι k v * ιMulti k n w := rfl

/-- The kernel of wedging with the wedge product of a linearly independent family is the span of
the family. -/
theorem ker_wedgeRight {n : ℕ} {w : Fin n → V} (hw : LinearIndependent k w) :
    LinearMap.ker (wedgeRight k w) = Submodule.span k (Set.range w) := by
  ext v
  simpa using ι_mul_ιMulti_eq_zero_iff hw v

end ExteriorAlgebra
end
