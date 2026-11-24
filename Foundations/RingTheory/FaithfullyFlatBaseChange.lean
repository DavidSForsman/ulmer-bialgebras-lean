module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Descent of faithful flatness along a base field extension

This file contains a general commutative-algebra tool, independent of Hopf algebras.

The last of the main results is the standard first reduction in the proof of Takeuchi's
theorem: one may always assume the base field to be algebraically closed.

## Main results

* `Module.FaithfullyFlat.faithfullyFlat_of_retract`: if `B → B'` is a morphism of `A`-algebras which
  admits an `A`-linear retraction and `B'` is faithfully flat over `A`, then `B` is faithfully flat
  over `A`;
* `Module.FaithfullyFlat.faithfullyFlat_tensorRight`: for a field `k`, a nonzero `k`-algebra `K` and
  any `k`-algebra `A`, the ring `K ⊗[k] A` is faithfully flat over `A`;
* `Module.FaithfullyFlat.faithfullyFlat_of_baseChange`: **faithful flatness descends along a base
  field extension**. If `A → B` is a morphism of `k`-algebras (`k` a field) and the base changed
  morphism `K ⊗[k] A → K ⊗[k] B` is faithfully flat, then so is `A → B`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Theorem
  3.1
-/

@[expose] public section

namespace Module.FaithfullyFlat

open TensorProduct

section Retract

variable {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra B B']
  [Algebra A B'] [IsScalarTower A B B']

/-- If `B'` is faithfully flat over `A` and the structure map `B → B'` admits an `A`-linear
retraction, then `B` is faithfully flat over `A`. -/
theorem faithfullyFlat_of_retract [Module.FaithfullyFlat A B'] (r : B' →ₗ[A] B)
    (hr : ∀ b : B, r (algebraMap B B' b) = b) : Module.FaithfullyFlat A B := by
  have hflat : Module.Flat A B :=
    Module.Flat.of_retract (i := (Algebra.linearMap B B').restrictScalars A) (r := r)
      (by ext b; simpa using hr b)
  refine ⟨fun m hm hcon => ?_⟩
  have h1 : (1 : B) ∈ m • (⊤ : Submodule A B) := by rw [hcon]; trivial
  have h2 : (1 : B') ∈ m • (⊤ : Submodule A B') := by
    have key : ∀ x ∈ m • (⊤ : Submodule A B), algebraMap B B' x ∈ m • (⊤ : Submodule A B') := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha b _
        rw [show algebraMap B B' (a • b) = a • algebraMap B B' b by
          simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A B B']]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    simpa using key 1 h1
  refine Module.FaithfullyFlat.submodule_ne_top (R := A) (M := B') hm
    (eq_top_iff.2 fun x _ => ?_)
  rw [show (x : B') = x * 1 from (mul_one x).symm]
  rw [Ideal.smul_top_eq_map] at h2 ⊢
  exact Ideal.mul_mem_left _ _ h2

end Retract

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k K A : Type*) [CommRing k] [CommRing K] [Algebra k K] [CommRing A] [Algebra k A]

/-- For the right `A`-algebra structure on `K ⊗[k] A`, `a • (c ⊗ₜ b) = c ⊗ₜ (a * b)`. -/
theorem smul_tmul_right (a : A) (c : K) (b : A) :
    a • (c ⊗ₜ[k] b : K ⊗[k] A) = c ⊗ₜ[k] (a * b) := by
  rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp

/-- The swap `Algebra.TensorProduct.comm k K A` commutes with scalar multiplication by `a : A`,
where `K ⊗[k] A` carries its right `A`-algebra structure. -/
theorem comm_smul (a : A) (x : K ⊗[k] A) :
    (Algebra.TensorProduct.comm k K A) (a • x) = a • (Algebra.TensorProduct.comm k K A) x := by
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
      rw [smul_tmul_right]
      simp [Algebra.TensorProduct.comm_tmul, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end BaseChange

section BaseChangeField

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k K A : Type*) [Field k] [CommRing K] [Algebra k K] [Nontrivial K] [CommRing A]
  [Algebra k A]

/-- Base change along a nonzero algebra over a field is faithfully flat: `K ⊗[k] A` is a
faithfully flat `A`-algebra. -/
theorem faithfullyFlat_tensorRight :
    Module.FaithfullyFlat A (K ⊗[k] A) :=
  Module.FaithfullyFlat.of_linearEquiv A (A ⊗[k] K) (N := K ⊗[k] A)
    { (Algebra.TensorProduct.comm k K A).toLinearEquiv with map_smul' := comm_smul k K A }

end BaseChangeField

section Descent

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k K A B : Type*} [Field k] [CommRing K] [Algebra k K] [Nontrivial K]
  [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- **Faithful flatness descends along a base field extension.**

Let `k` be a field, `K` a nonzero `k`-algebra (e.g. a field extension of `k`) and `A → B` a
morphism of commutative `k`-algebras.  If the base change `K ⊗[k] A → K ⊗[k] B` is faithfully
flat, then `B` is faithfully flat over `A`.

The algebra structure of `K ⊗[k] B` over `K ⊗[k] A` is not assumed to be any particular instance;
it is only required to be given on pure tensors by `c ⊗ₜ a ↦ c ⊗ₜ (algebraMap A B a)`, which is
the case for all the standard constructions of the base changed morphism. -/
theorem faithfullyFlat_of_baseChange [Algebra (K ⊗[k] A) (K ⊗[k] B)]
    (hmap : ∀ (c : K) (a : A),
      algebraMap (K ⊗[k] A) (K ⊗[k] B) (c ⊗ₜ[k] a) = c ⊗ₜ[k] (algebraMap A B a))
    [Module.FaithfullyFlat (K ⊗[k] A) (K ⊗[k] B)] :
    Module.FaithfullyFlat A B := by
  -- the `A`-algebra structure on `K ⊗[k] B`, through `B`
  let : Algebra A (K ⊗[k] B) :=
    ((algebraMap B (K ⊗[k] B)).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B (K ⊗[k] B) := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A (K ⊗[k] A) (K ⊗[k] B) := by
    refine .of_algebraMap_eq fun a => ?_
    change algebraMap B (K ⊗[k] B) (algebraMap A B a) =
      algebraMap (K ⊗[k] A) (K ⊗[k] B) (algebraMap A (K ⊗[k] A) a)
    rw [show algebraMap A (K ⊗[k] A) a = (1 : K) ⊗ₜ[k] a from rfl, hmap]
    rfl
  have : Module.FaithfullyFlat A (K ⊗[k] A) := faithfullyFlat_tensorRight k K A
  have : Module.FaithfullyFlat A (K ⊗[k] B) :=
    Module.FaithfullyFlat.trans A (K ⊗[k] A) (K ⊗[k] B)
  -- a `k`-linear functional on `K` sending `1` to `1`
  obtain ⟨xi, hxi⟩ : ∃ xi : K →ₗ[k] k, xi.comp (Algebra.linearMap k K) = LinearMap.id :=
    LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
      (LinearMap.ker_eq_bot.2 (algebraMap k K).injective)
  have hxi1 : xi 1 = 1 := by
    have := LinearMap.congr_fun hxi 1
    simpa using this
  -- the induced `A`-linear retraction of `B → K ⊗[k] B`
  set r0 : K ⊗[k] B →ₗ[k] B := (TensorProduct.lid k B).toLinearMap ∘ₗ LinearMap.rTensor B xi
    with hr0
  have hr0_tmul : ∀ (c : K) (b : B), r0 (c ⊗ₜ[k] b) = xi c • b := by
    intro c b; simp [hr0]
  have hsmul : ∀ (a : A) (x : K ⊗[k] B), r0 (a • x) = a • r0 x := by
    intro a x
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
        have : a • (c ⊗ₜ[k] b : K ⊗[k] B) = c ⊗ₜ[k] (a • b) := by
          rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
            Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, Algebra.smul_def]
        rw [this, hr0_tmul, hr0_tmul, smul_comm]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  refine faithfullyFlat_of_retract (B' := K ⊗[k] B)
    { toFun := r0, map_add' := r0.map_add, map_smul' := hsmul } ?_
  intro b
  refine (hr0_tmul 1 b).trans ?_
  rw [hxi1, one_smul]

end Descent

end Module.FaithfullyFlat
