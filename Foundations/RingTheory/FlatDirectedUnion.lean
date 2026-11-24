module

public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Flatness is a local property of finite families of elements

A module all of whose finite families of elements are contained in a flat submodule is flat.
This is the module-theoretic content of the (well-known) fact that a filtered union of flat
submodules is flat, and it is exactly what is needed to pass from Takeuchi's Corollary 2.3
(a relative Hopf module is the filtered union of its sub-Hopf-modules which are finitely
generated) to the flatness of an arbitrary relative Hopf module.

The proof is immediate from Mathlib's equational criterion for flatness: the triviality of a
relation only involves finitely many elements, and it is preserved by pushing forward along the
inclusion of a submodule.

## Main results

* `Module.Flat.flat_of_forall_finite_flat_submodule`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Corollary 2.3
-/

@[expose] public section

namespace Module.Flat

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If every finite family of elements of `M` is contained in a flat submodule, then `M` is
flat. -/
theorem flat_of_forall_finite_flat_submodule
    (h : ∀ (l : ℕ) (x : Fin l → M), ∃ N : Submodule R M, (∀ i, x i ∈ N) ∧ Module.Flat R ↥N) :
    Module.Flat R M := by
  refine Module.Flat.of_forall_isTrivialRelation ?_
  intro l f x hx
  obtain ⟨N, hxN, hN⟩ := h l x
  set x' : Fin l → ↥N := fun i => ⟨x i, hxN i⟩ with hx'def
  have hx' : ∑ i, f i • x' i = 0 := by
    apply Submodule.injective_subtype N
    rw [map_sum, map_zero]
    simpa using hx
  obtain ⟨j, a, y, hy1, hy2⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := ↥N) hx'
  refine ⟨j, a, fun i => (y i : M), fun i => ?_, hy2⟩
  have := congrArg (Submodule.subtype N) (hy1 i)
  simpa using this

end Module.Flat
