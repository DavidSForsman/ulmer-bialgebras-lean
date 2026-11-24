module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The descent equalizer of a faithfully flat ring map

For a faithfully flat morphism of commutative rings `A → B`, the sequence

```
A --> B ⇉ B ⊗[A] B
```

is an equalizer: an element `b : B` with `b ⊗ₜ 1 = 1 ⊗ₜ b` comes from `A`
(`Algebra.TensorProduct.mem_range_of_tmul_eq`). This is the first half of faithfully flat descent,
and it is what makes an injective morphism of commutative Hopf algebras a *regular* monomorphism.

We also record the variant `Algebra.TensorProduct.mem_range_of_tmul_eq_of_tower` in which the tensor
product is taken over a smaller ring `Y` mapping to `A`; this is the form needed when the two
projections come from the cokernel pair of a morphism whose image is `A`.

## Main results

* `Algebra.TensorProduct.mem_range_of_tmul_eq`: if `B` is faithfully flat over `A` and `b : B`
  satisfies `b ⊗ₜ 1 = 1 ⊗ₜ b` in `B ⊗[A] B`, then `b` lies in the image of `A`;
* `Algebra.TensorProduct.mem_range_of_tmul_eq_of_tower`: the same conclusion for a tower `Y → A → B`
  when `b ⊗ₜ 1 = 1 ⊗ₜ b` already holds in `B ⊗[Y] B`.

## References

* [A. Grothendieck, *Technique de descente et théorèmes d'existence en géométrie algébrique
  I*][GrothendieckDescent]
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Chapter 13
-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

universe u

section Base

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]

/-- **The descent equalizer.**  If `B` is faithfully flat over `A` and `b : B` satisfies
`b ⊗ₜ 1 = 1 ⊗ₜ b` in `B ⊗[A] B`, then `b` lies in the image of `A`. -/
theorem mem_range_of_tmul_eq (b : B) (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b := by
  set N : Submodule A B := LinearMap.range (Algebra.linearMap A B) with hN
  set π : B →ₗ[A] (B ⧸ N) := N.mkQ with hπ
  have hπ1 : π 1 = 0 := by
    rw [hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨1, by simp⟩
  have key : (1 : B) ⊗ₜ[A] (π b) = 0 := by
    have h1 : LinearMap.lTensor B π (b ⊗ₜ[A] (1 : B))
        = LinearMap.lTensor B π ((1 : B) ⊗ₜ[A] b) := by rw [hb]
    simp only [LinearMap.lTensor_tmul, hπ1, tmul_zero] at h1
    exact h1.symm
  have h2 :=
    (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := A) (M := B ⧸ N) (A := B) (π b)).mp key
  rw [hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

end Base

section Tower

variable {Y A B : Type u} [CommRing Y] [CommRing A] [CommRing B]
  [Algebra Y A] [Algebra Y B] [Algebra A B] [IsScalarTower Y A B]

/-- The canonical comparison morphism `B ⊗[Y] B → B ⊗[A] B` for a tower `Y → A → B`. -/
noncomputable def tensorComparison : B ⊗[Y] B →ₐ[Y] B ⊗[A] B :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).restrictScalars Y)
    ((Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).restrictScalars Y)
    (fun _ _ => Commute.all _ _)

/-- The comparison map `tensorComparison` sends `x ⊗ₜ[Y] y` to `x ⊗ₜ[A] y`. -/
@[simp] lemma tensorComparison_tmul (x y : B) :
    tensorComparison (Y := Y) (A := A) (x ⊗ₜ[Y] y) = x ⊗ₜ[A] y := by
  simp [tensorComparison, Algebra.TensorProduct.tmul_mul_tmul]

variable [Module.FaithfullyFlat A B]

/-- **The descent equalizer, relative version.**  If `B` is faithfully flat over `A`, `Y → A → B`
is a tower of commutative rings and `b : B` satisfies `b ⊗ₜ 1 = 1 ⊗ₜ b` already in `B ⊗[Y] B`,
then `b` lies in the image of `A`. -/
theorem mem_range_of_tmul_eq_of_tower (b : B) (hb : b ⊗ₜ[Y] (1 : B) = (1 : B) ⊗ₜ[Y] b) :
    ∃ a : A, algebraMap A B a = b := by
  refine mem_range_of_tmul_eq b ?_
  have := congrArg (tensorComparison (Y := Y) (A := A)) hb
  simpa using this

end Tower

end Algebra.TensorProduct
