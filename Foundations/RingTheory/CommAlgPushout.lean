module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Pushouts of commutative algebras are tensor products

Let `k` be a commutative ring and let `A` be a commutative `k`-algebra with two commutative
`A`-algebras `X` and `B` (compatibly with `k`).  We show that

```
A ---> X
|      |
v      v
B ---> X ⊗[A] B
```

is a pushout square in `CommAlgCat k`, the category of commutative `k`-algebras.

This is the algebraic input for the description of pushouts of commutative Hopf algebras in
`AffineGroupSchemes/HopfPushout.lean`: pushouts of commutative Hopf algebras are computed on
underlying algebras, hence are given by the same tensor product.

## Main results

* `CommAlgCat.tensorCoconeIsColimit`: the tensor product cocone on `X ← A → B` is a colimit cocone
  in `CommAlgCat k`;
* `CommAlgCat.isPushout_tensorProduct`: the tensor product square is a pushout square in
  `CommAlgCat k`.

## References

* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

open TensorProduct CategoryTheory Limits

namespace CommAlgCat

universe u

variable (k A X B : Type u) [CommRing k] [CommRing A] [CommRing X] [CommRing B]
  [Algebra k A] [Algebra k X] [Algebra k B] [Algebra A X] [Algebra A B]
  [IsScalarTower k A X] [IsScalarTower k A B]

/-- The cocone on `X ← A → B` in `CommAlgCat k` given by the tensor product `X ⊗[A] B`. -/
noncomputable def tensorCocone :
    PushoutCocone (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A X))
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)) :=
  PushoutCocone.mk (W := CommAlgCat.of k (X ⊗[A] B))
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B))
    (CommAlgCat.ofHom ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k))
    (by
      ext a
      change (algebraMap A X a) ⊗ₜ[A] (1 : B) = (1 : X) ⊗ₜ[A] (algebraMap A B a)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul])

variable {k A X B}

/-- The morphism out of `X ⊗[A] B` induced by a cocone on `X ← A → B`. -/
noncomputable def tensorLift
    (s : PushoutCocone (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A X))
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B))) :
    CommAlgCat.of k (X ⊗[A] B) ⟶ s.pt :=
  letI : Algebra A s.pt := (s.inl.hom.comp (IsScalarTower.toAlgHom k A X)).toAlgebra
  letI : IsScalarTower k A s.pt := .of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra]
  let f : X →ₐ[A] s.pt := { s.inl.hom with commutes' := fun _ => rfl }
  let g : B →ₐ[A] s.pt :=
    { s.inr.hom with
      commutes' := fun a => by
        have := congr(($(s.condition)).hom a)
        simpa [RingHom.algebraMap_toAlgebra] using this.symm }
  CommAlgCat.ofHom ((Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).restrictScalars k)

/-- The morphism `tensorLift s` sends `x ⊗ₜ[A] b` to `s.inl x * s.inr b`. -/
@[simp] lemma tensorLift_tmul
    (s : PushoutCocone (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A X))
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B))) (x : X) (b : B) :
    (tensorLift s) (x ⊗ₜ[A] b) = s.inl x * s.inr b := rfl

/-- The morphism `tensorLift s` sends `x ⊗ₜ[A] 1` to `s.inl x`. -/
@[simp] lemma tensorLift_tmul_one
    (s : PushoutCocone (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A X))
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B))) (x : X) :
    (tensorLift s) (x ⊗ₜ[A] (1 : B)) = s.inl x := by
  rw [tensorLift_tmul]; simp

/-- The morphism `tensorLift s` sends `1 ⊗ₜ[A] b` to `s.inr b`. -/
@[simp] lemma tensorLift_one_tmul
    (s : PushoutCocone (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A X))
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B))) (b : B) :
    (tensorLift s) ((1 : X) ⊗ₜ[A] b) = s.inr b := by
  rw [tensorLift_tmul]; simp

omit [Algebra k B] [IsScalarTower k A B] in
/-- Two morphisms out of `X ⊗[A] B` agreeing on `X` and on `B` are equal. -/
lemma tensor_hom_ext {T : Type u} [CommRing T] [Algebra k T]
    {F G : X ⊗[A] B →ₐ[k] T}
    (hX : ∀ x : X, F (x ⊗ₜ[A] (1 : B)) = G (x ⊗ₜ[A] (1 : B)))
    (hB : ∀ b : B, F ((1 : X) ⊗ₜ[A] b) = G ((1 : X) ⊗ₜ[A] b)) : F = G := by
  ext t
  induction t with
  | tmul x b =>
      have h : (x ⊗ₜ[A] b : X ⊗[A] B) = (x ⊗ₜ[A] (1 : B)) * ((1 : X) ⊗ₜ[A] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h, map_mul, map_mul, hX, hB]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

variable (k A X B)

/-- **Pushouts of commutative algebras are tensor products.**  The square

```
A ---> X
|      |
v      v
B ---> X ⊗[A] B
```

is a pushout in `CommAlgCat k`. -/
noncomputable def tensorCoconeIsColimit : IsColimit (tensorCocone k A X B) := by
  refine PushoutCocone.IsColimit.mk _ (fun s => tensorLift s) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_)
  · ext x
    exact tensorLift_tmul_one s x
  · ext b
    exact tensorLift_one_tmul s b
  · refine CommAlgCat.hom_ext (tensor_hom_ext (fun x => ?_) (fun b => ?_))
    · rw [tensorLift_tmul_one]
      simpa using congr(($(h₁)).hom x)
    · rw [tensorLift_one_tmul]
      simpa using congr(($(h₂)).hom b)

/-- The tensor product square is a pushout square in `CommAlgCat k`. -/
lemma isPushout_tensorProduct :
    IsPushout (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A X))
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B))
      (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B))
      (CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)) :=
  IsPushout.of_isColimit (tensorCoconeIsColimit k A X B)

end CommAlgCat
