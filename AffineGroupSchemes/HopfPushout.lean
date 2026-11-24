module

public import Foundations.RingTheory.CommAlgPushout
public import Foundations.CategoryTheory.Grp.GrpObjIsPullback
public import AffineGroupSchemes.HopfGrpEquiv

/-!
# Pushouts of commutative Hopf algebras are tensor products

Let `A` be a commutative Hopf algebra over a commutative ring `k` and let `u : A →ₐc[k] X`,
`v : A →ₐc[k] B` be morphisms of commutative Hopf algebras.  Then the tensor product
`X ⊗[A] B` carries a (unique) Hopf algebra structure making the canonical maps `X → X ⊗[A] B`
and `B → X ⊗[A] B` morphisms of Hopf algebras, and the resulting square

```
A ---> X
|      |
v      v
B ---> X ⊗[A] B
```

is a pushout square in the category `CommHopfAlgCat k` of commutative Hopf `k`-algebras.

Geometrically this says that the fibre product of two morphisms of affine group schemes is
the fibre product of the underlying affine schemes, with its natural group structure.

The Hopf algebra structure is obtained without any computation: by
`Foundations/RingTheory/CommAlgPushout.lean` the tensor product square is a pushout square of
commutative algebras, hence a pullback square in the opposite category; the group object
structure on the apex of a pullback square of group objects
(`Foundations/CategoryTheory/Grp/GrpObjIsPullback.lean`) then transports, through the identification
of
commutative Hopf algebras with affine group schemes (`AffineGroupSchemes/HopfGrpEquiv.lean`),
to the required Hopf algebra structure.

## Main results

* `AffineGroupSchemes.hopfAlgebraTensor`: the Hopf algebra structure on `X ⊗[A] B`.
* `AffineGroupSchemes.liftBialgHom`: the morphism of Hopf algebras out of `X ⊗[A] B` induced by two
  compatible morphisms of Hopf algebras.
* `AffineGroupSchemes.isPushout_hopfTensor`: the tensor product square is a pushout square in
  `CommHopfAlgCat k`.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Section 1.4
-/

@[expose] public section

open TensorProduct CategoryTheory Limits Opposite MonObj

namespace AffineGroupSchemes

open CategoryTheory

universe u

section Tensor

variable {k A X B : Type u} [CommRing k] [CommRing A] [CommRing X] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k X] [HopfAlgebra k B]
  [Algebra A X] [Algebra A B] [IsScalarTower k A X] [IsScalarTower k A B]
  (u : A →ₐc[k] X) (v : A →ₐc[k] B)
  (hu : ∀ a, algebraMap A X a = u a) (hv : ∀ a, algebraMap A B a = v a)

include hu in
/-- If `algebraMap A X = u` pointwise, then `IsScalarTower.toAlgHom k A X = u` as algebra maps. -/
lemma toAlgHom_eq_of_bialgHom_left : IsScalarTower.toAlgHom k A X = (u : A →ₐ[k] X) := by
  ext a; exact hu a

include hv in
/-- If `algebraMap A B = v` pointwise, then `IsScalarTower.toAlgHom k A B = v` as algebra maps. -/
lemma toAlgHom_eq_of_bialgHom_right : IsScalarTower.toAlgHom k A B = (v : A →ₐ[k] B) := by
  ext a; exact hv a

include hu hv in
/-- The tensor product square of commutative algebras, read as a pullback square of affine
schemes. -/
theorem isPullback_op_tensorProduct :
    IsPullback
      ((CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)).op)
      ((CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B)).op)
      ((CommAlgCat.ofHom (v : A →ₐ[k] B)).op)
      ((CommAlgCat.ofHom (u : A →ₐ[k] X)).op) := by
  have := (CommAlgCat.isPushout_tensorProduct k A X B).op
  rwa [toAlgHom_eq_of_bialgHom_left u hu, toAlgHom_eq_of_bialgHom_right v hv] at this

/-- The affine group scheme structure on the fibre product. -/
@[instance_reducible]
noncomputable def grpObjTensor : GrpObj (op (CommAlgCat.of k (X ⊗[A] B))) :=
  grpObjOfIsPullback (isPullback_op_tensorProduct u v hu hv)

/-- **The Hopf algebra structure on `X ⊗[A] B`.** -/
@[instance_reducible]
noncomputable def hopfAlgebraTensor : HopfAlgebra k (X ⊗[A] B) :=
  letI := grpObjTensor u v hu hv
  instHopfAlgebraCarrierUnopCommAlgCatOfGrpObjOpposite (op (CommAlgCat.of k (X ⊗[A] B)))

/-- For the structure `hopfAlgebraTensor`, the counit of `X ⊗[A] B` composed with
`X → X ⊗[A] B` is the counit of `X`. -/
lemma counitAlgHom_comp_includeLeft :
    letI := hopfAlgebraTensor u v hu hv
    (Bialgebra.counitAlgHom k (X ⊗[A] B)).comp
        (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B) =
      Bialgebra.counitAlgHom k X := by
  let := grpObjTensor u v hu hv
  have := isMonHom_isPullback_snd (isPullback_op_tensorProduct u v hu hv)
  exact congr(($(IsMonHom.one_hom
    (f := (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B)).op))).unop.hom)

/-- For the structure `hopfAlgebraTensor`, the inclusion `X → X ⊗[A] B` commutes with
comultiplication. -/
lemma comulAlgHom_comp_includeLeft :
    letI := hopfAlgebraTensor u v hu hv
    (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B)
        (Algebra.TensorProduct.includeLeft)).comp (Bialgebra.comulAlgHom k X) =
      (Bialgebra.comulAlgHom k (X ⊗[A] B)).comp
        (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B) := by
  let := grpObjTensor u v hu hv
  have := isMonHom_isPullback_snd (isPullback_op_tensorProduct u v hu hv)
  exact congr(($((IsMonHom.mul_hom
    (f := (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B)).op)).symm)).unop.hom)

/-- For the structure `hopfAlgebraTensor`, the counit of `X ⊗[A] B` composed with
`B → X ⊗[A] B` is the counit of `B`. -/
lemma counitAlgHom_comp_includeRight :
    letI := hopfAlgebraTensor u v hu hv
    (Bialgebra.counitAlgHom k (X ⊗[A] B)).comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k) =
      Bialgebra.counitAlgHom k B := by
  let := grpObjTensor u v hu hv
  have := isMonHom_isPullback_fst (isPullback_op_tensorProduct u v hu hv)
  exact congr(($(IsMonHom.one_hom
    (f := (CommAlgCat.ofHom
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[A] X ⊗[A] B).restrictScalars k)).op))).unop.hom)

/-- For the structure `hopfAlgebraTensor`, the inclusion `B → X ⊗[A] B` commutes with
comultiplication. -/
lemma comulAlgHom_comp_includeRight :
    letI := hopfAlgebraTensor u v hu hv
    (Algebra.TensorProduct.map
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)).comp
        (Bialgebra.comulAlgHom k B) =
      (Bialgebra.comulAlgHom k (X ⊗[A] B)).comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k) := by
  let := grpObjTensor u v hu hv
  have := isMonHom_isPullback_fst (isPullback_op_tensorProduct u v hu hv)
  exact congr(($((IsMonHom.mul_hom
    (f := (CommAlgCat.ofHom
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[A] X ⊗[A] B).restrictScalars k)).op)).symm)).unop.hom)

/-- The canonical morphism of Hopf algebras `X →ₐc[k] X ⊗[A] B`. -/
noncomputable def inlBialgHom :
    letI := hopfAlgebraTensor u v hu hv
    X →ₐc[k] X ⊗[A] B :=
  letI := hopfAlgebraTensor u v hu hv
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B)
    (counitAlgHom_comp_includeLeft u v hu hv) (comulAlgHom_comp_includeLeft u v hu hv)

/-- The canonical morphism of Hopf algebras `B →ₐc[k] X ⊗[A] B`. -/
noncomputable def inrBialgHom :
    letI := hopfAlgebraTensor u v hu hv
    B →ₐc[k] X ⊗[A] B :=
  letI := hopfAlgebraTensor u v hu hv
  BialgHom.ofAlgHom
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)
    (counitAlgHom_comp_includeRight u v hu hv) (comulAlgHom_comp_includeRight u v hu hv)
/-- `inlBialgHom` sends `x` to `x ⊗ 1`. -/
@[simp] lemma inlBialgHom_apply (x : X) :
    letI := hopfAlgebraTensor u v hu hv
    inlBialgHom u v hu hv x = x ⊗ₜ[A] (1 : B) := rfl

/-- `inrBialgHom` sends `b` to `1 ⊗ b`. -/
@[simp] lemma inrBialgHom_apply (b : B) :
    letI := hopfAlgebraTensor u v hu hv
    inrBialgHom u v hu hv b = (1 : X) ⊗ₜ[A] b := rfl


/-- The counit of `X ⊗[A] B` (structure `hopfAlgebraTensor`) sends `x ⊗ 1` to `ε x`. -/
lemma counit_tmul_one (x : X) :
    letI := hopfAlgebraTensor u v hu hv
    Coalgebra.counit (R := k) (x ⊗ₜ[A] (1 : B)) = Coalgebra.counit (R := k) x := by
  let := hopfAlgebraTensor u v hu hv
  simpa using congr($(counitAlgHom_comp_includeLeft u v hu hv) x)

/-- The counit of `X ⊗[A] B` (structure `hopfAlgebraTensor`) sends `1 ⊗ b` to `ε b`. -/
lemma counit_one_tmul (b : B) :
    letI := hopfAlgebraTensor u v hu hv
    Coalgebra.counit (R := k) ((1 : X) ⊗ₜ[A] b) = Coalgebra.counit (R := k) b := by
  let := hopfAlgebraTensor u v hu hv
  simpa using congr($(counitAlgHom_comp_includeRight u v hu hv) b)

/-- The comultiplication of `X ⊗[A] B` on `x ⊗ 1` is `Δ x` pushed along `X → X ⊗[A] B` in
both factors. -/
lemma comul_tmul_one (x : X) :
    letI := hopfAlgebraTensor u v hu hv
    Coalgebra.comul (R := k) (x ⊗ₜ[A] (1 : B))
      = Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B)
          (Algebra.TensorProduct.includeLeft) (Coalgebra.comul (R := k) x) := by
  let := hopfAlgebraTensor u v hu hv
  simpa using congr($(comulAlgHom_comp_includeLeft u v hu hv) x).symm

/-- The comultiplication of `X ⊗[A] B` on `1 ⊗ b` is `Δ b` pushed along `B → X ⊗[A] B` in both
factors. -/
lemma comul_one_tmul (b : B) :
    letI := hopfAlgebraTensor u v hu hv
    Coalgebra.comul (R := k) ((1 : X) ⊗ₜ[A] b)
      = Algebra.TensorProduct.map
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)
          (Coalgebra.comul (R := k) b) := by
  let := hopfAlgebraTensor u v hu hv
  simpa using congr($(comulAlgHom_comp_includeRight u v hu hv) b).symm

end Tensor

section Aux

variable {k C D E : Type u} [CommRing k] [CommRing C] [CommRing D] [CommRing E]

/-- Composition of tensor products of algebra maps. -/
lemma algTensorMap_comp [Algebra k C] [Algebra k D] [Algebra k E] {C' D' : Type u} [CommRing C']
    [CommRing D'] [Algebra k C'] [Algebra k D'] (p : C →ₐ[k] C') (q : D →ₐ[k] D')
    (p' : E →ₐ[k] C) (q' : E →ₐ[k] D) (t : E ⊗[k] E) :
    Algebra.TensorProduct.map p q (Algebra.TensorProduct.map p' q' t)
      = Algebra.TensorProduct.map (p.comp p') (q.comp q') t := by
  induction t with
  | tmul a b => simp
  | add s t hs ht => simp [hs, ht]

/-- A morphism of bialgebras commutes with comultiplication, in tensor-product form. -/
lemma algTensorMap_comul [Bialgebra k C] [Bialgebra k D] (p : C →ₐc[k] D) (c : C) :
    Algebra.TensorProduct.map (p : C →ₐ[k] D) (p : C →ₐ[k] D) (Coalgebra.comul c)
      = Coalgebra.comul (p c) := by
  have h : ∀ t : C ⊗[k] C,
      Algebra.TensorProduct.map (p : C →ₐ[k] D) (p : C →ₐ[k] D) t
        = TensorProduct.map ((p : C →ₐ[k] D) : C →ₗ[k] D) ((p : C →ₐ[k] D) : C →ₗ[k] D) t := by
    intro t
    induction t with
    | tmul a b => simp
    | add s t hs ht => simp [hs, ht]
  rw [h]
  exact congr($(CoalgHomClass.map_comp_comul p) c)

end Aux

section Pushout

variable {k A X B : Type u} [CommRing k] [CommRing A] [CommRing X] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k X] [HopfAlgebra k B]
  [Algebra A X] [Algebra A B] [IsScalarTower k A X]
  (u : A →ₐc[k] X) (v : A →ₐc[k] B)
  (hu : ∀ a, algebraMap A X a = u a) (hv : ∀ a, algebraMap A B a = v a)
  {T : Type u} [CommRing T] [HopfAlgebra k T]
  (φ : X →ₐc[k] T) (ψ : B →ₐc[k] T) (hcomm : ∀ a, φ (u a) = ψ (v a))

include hu hv hcomm in
/-- The algebra morphism out of `X ⊗[A] B` induced by two compatible morphisms. -/
noncomputable def liftAlgHom : X ⊗[A] B →ₐ[k] T :=
  letI : Algebra A T := ((φ : X →ₐ[k] T).comp (u : A →ₐ[k] X)).toAlgebra
  letI : IsScalarTower k A T := .of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra]
  letI f : X →ₐ[A] T :=
    { (φ : X →ₐ[k] T) with
      commutes' := fun a => by simp [hu a, RingHom.algebraMap_toAlgebra] }
  letI g : B →ₐ[A] T :=
    { (ψ : B →ₐ[k] T) with
      commutes' := fun a => by simp [hv a, hcomm a, RingHom.algebraMap_toAlgebra] }
  (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).restrictScalars k

/-- `liftAlgHom` sends `x ⊗ b` to `φ x * ψ b`. -/
@[simp] lemma liftAlgHom_tmul (x : X) (b : B) :
    liftAlgHom u v hu hv φ ψ hcomm (x ⊗ₜ[A] b) = φ x * ψ b := rfl

include hu hv hcomm in
/-- `liftAlgHom` composed with `X → X ⊗[A] B` is `φ`. -/
lemma liftAlgHom_comp_includeLeft :
    (liftAlgHom u v hu hv φ ψ hcomm).comp
        (Algebra.TensorProduct.includeLeft : X →ₐ[k] X ⊗[A] B) = (φ : X →ₐ[k] T) := by
  ext x
  simp

variable [IsScalarTower k A B]

include hu hv hcomm in
/-- `liftAlgHom` composed with `B → X ⊗[A] B` is `ψ`. -/
lemma liftAlgHom_comp_includeRight :
    (liftAlgHom u v hu hv φ ψ hcomm).comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] X ⊗[A] B).restrictScalars k)
      = (ψ : B →ₐ[k] T) := by
  ext b
  simp

include hu hv hcomm in
/-- `liftAlgHom` preserves counits (for the structure `hopfAlgebraTensor` on `X ⊗[A] B`). -/
lemma counitAlgHom_comp_liftAlgHom :
    letI := hopfAlgebraTensor u v hu hv
    (Bialgebra.counitAlgHom k T).comp (liftAlgHom u v hu hv φ ψ hcomm)
      = Bialgebra.counitAlgHom k (X ⊗[A] B) := by
  let := hopfAlgebraTensor u v hu hv
  refine CommAlgCat.tensor_hom_ext (fun x => ?_) (fun b => ?_)
  · simp [counit_tmul_one u v hu hv x, CoalgHomClass.counit_comp_apply (R := k) φ x]
  · simp [counit_one_tmul u v hu hv b, CoalgHomClass.counit_comp_apply (R := k) ψ b]

include hu hv hcomm in
/-- `liftAlgHom` commutes with comultiplication (for the structure `hopfAlgebraTensor`). -/
lemma comulAlgHom_comp_liftAlgHom :
    letI := hopfAlgebraTensor u v hu hv
    (Algebra.TensorProduct.map (liftAlgHom u v hu hv φ ψ hcomm)
          (liftAlgHom u v hu hv φ ψ hcomm)).comp (Bialgebra.comulAlgHom k (X ⊗[A] B))
      = (Bialgebra.comulAlgHom k T).comp (liftAlgHom u v hu hv φ ψ hcomm) := by
  let := hopfAlgebraTensor u v hu hv
  set d := liftAlgHom u v hu hv φ ψ hcomm with hd
  refine CommAlgCat.tensor_hom_ext (fun x => ?_) (fun b => ?_)
  · simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    rw [comul_tmul_one u v hu hv x, algTensorMap_comp, hd,
      liftAlgHom_comp_includeLeft u v hu hv φ ψ hcomm, algTensorMap_comul, ← hd]
    congr 1
    rw [hd, liftAlgHom_tmul]
    simp
  · simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    rw [comul_one_tmul u v hu hv b, algTensorMap_comp, hd,
      liftAlgHom_comp_includeRight u v hu hv φ ψ hcomm, algTensorMap_comul, ← hd]
    congr 1
    rw [hd, liftAlgHom_tmul]
    simp

include hu hv hcomm in
/-- The morphism of Hopf algebras out of `X ⊗[A] B` induced by two compatible morphisms of
Hopf algebras. -/
noncomputable def liftBialgHom :
    letI := hopfAlgebraTensor u v hu hv
    X ⊗[A] B →ₐc[k] T :=
  letI := hopfAlgebraTensor u v hu hv
  BialgHom.ofAlgHom (liftAlgHom u v hu hv φ ψ hcomm)
    (counitAlgHom_comp_liftAlgHom u v hu hv φ ψ hcomm)
    (comulAlgHom_comp_liftAlgHom u v hu hv φ ψ hcomm)

include hu hv hcomm in
/-- `liftBialgHom` sends `x ⊗ b` to `φ x * ψ b`. -/
@[simp] lemma liftBialgHom_tmul (x : X) (b : B) :
    letI := hopfAlgebraTensor u v hu hv
    liftBialgHom u v hu hv φ ψ hcomm (x ⊗ₜ[A] b) = φ x * ψ b := rfl

end Pushout

section Cocone

variable {k A X B : Type u} [CommRing k] [CommRing A] [CommRing X] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k X] [HopfAlgebra k B] (u : A →ₐc[k] X) (v : A →ₐc[k] B)

/-- The compatibility condition carried by a cocone under `X ← A → B`. -/
lemma pushoutCocone_hcomm
    (s : PushoutCocone (CommHopfAlgCat.ofHom u) (CommHopfAlgCat.ofHom v)) (a : A) :
    s.inl.hom (u a) = s.inr.hom (v a) :=
  congr(($(s.condition)).hom a)

end Cocone

section IsPushoutHopf

variable {k A X B : Type u} [CommRing k] [CommRing A] [CommRing X] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k X] [HopfAlgebra k B]
  [Algebra A X] [Algebra A B] [IsScalarTower k A X] [IsScalarTower k A B]
  (u : A →ₐc[k] X) (v : A →ₐc[k] B)
  (hu : ∀ a, algebraMap A X a = u a) (hv : ∀ a, algebraMap A B a = v a)

/-- Two morphisms of bialgebras out of `X ⊗[A] B` agreeing on `X` and on `B` are equal. -/
lemma bialgHom_tensor_ext {T : Type u} [CommRing T] [HopfAlgebra k T]
    (F G : letI := hopfAlgebraTensor u v hu hv; X ⊗[A] B →ₐc[k] T)
    (hX : ∀ x : X, F (x ⊗ₜ[A] (1 : B)) = G (x ⊗ₜ[A] (1 : B)))
    (hB : ∀ b : B, F ((1 : X) ⊗ₜ[A] b) = G ((1 : X) ⊗ₜ[A] b)) : F = G := by
  let := hopfAlgebraTensor u v hu hv
  have h : ((F : X ⊗[A] B →ₐ[k] T)) = (G : X ⊗[A] B →ₐ[k] T) :=
    CommAlgCat.tensor_hom_ext hX hB
  exact DFunLike.ext _ _ fun t => congr($h t)

/-- The pushout cocone of two morphisms of commutative Hopf algebras, with apex the tensor
product. -/
noncomputable def hopfPushoutCocone :
    letI := hopfAlgebraTensor u v hu hv
    PushoutCocone (CommHopfAlgCat.ofHom u) (CommHopfAlgCat.ofHom v) :=
  letI := hopfAlgebraTensor u v hu hv
  PushoutCocone.mk (W := CommHopfAlgCat.of k (X ⊗[A] B))
    (CommHopfAlgCat.ofHom (inlBialgHom u v hu hv))
    (CommHopfAlgCat.ofHom (inrBialgHom u v hu hv))
    (by ext a; simp [← hu a, ← hv a, Algebra.algebraMap_eq_smul_one, smul_tmul])

/-- **Pushouts of commutative Hopf algebras are tensor products.** -/
noncomputable def hopfPushoutCoconeIsColimit :
    letI := hopfAlgebraTensor u v hu hv
    IsColimit (hopfPushoutCocone u v hu hv) := by
  letI := hopfAlgebraTensor u v hu hv
  refine PushoutCocone.IsColimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_)
  · exact CommHopfAlgCat.ofHom
      (liftBialgHom u v hu hv s.inl.hom s.inr.hom (pushoutCocone_hcomm u v s))
  · ext x
    simp
  · ext b
    simp
  · refine CommHopfAlgCat.hom_ext (bialgHom_tensor_ext u v hu hv _ _ (fun x => ?_) (fun b => ?_))
    · simpa using congr(($h₁).hom x)
    · simpa using congr(($h₂).hom b)

/-- The tensor product square is a pushout square of commutative Hopf algebras. -/
theorem isPushout_hopfTensor :
    letI := hopfAlgebraTensor u v hu hv
    IsPushout (CommHopfAlgCat.ofHom u) (CommHopfAlgCat.ofHom v)
      (CommHopfAlgCat.ofHom (inlBialgHom u v hu hv))
      (CommHopfAlgCat.ofHom (inrBialgHom u v hu hv)) :=
  letI := hopfAlgebraTensor u v hu hv
  IsPushout.of_isColimit (hopfPushoutCoconeIsColimit u v hu hv)

end IsPushoutHopf

end AffineGroupSchemes
