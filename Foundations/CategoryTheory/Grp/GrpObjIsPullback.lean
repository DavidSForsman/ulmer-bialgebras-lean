module

public import Foundations.CategoryTheory.Grp.GrpObjPullback

/-!
# Group object structures on arbitrary pullback squares

`Foundations/CategoryTheory/Grp/GrpObjPullback.lean` shows that the chosen pullback of two morphisms
of
group objects carries a group object structure.  Here we record the same construction for an
*arbitrary* pullback square: if

```
P ---p₁--> G
|          |
p₂         f
v          v
H ---g---> K
```

is a pullback square in a cartesian monoidal category and `f`, `g` are morphisms of group
objects, then `P` carries a group object structure for which `p₁` and `p₂` are morphisms of
group objects.

This is the form in which the construction is applied in
`AffineGroupSchemes/HopfPushout.lean`, where the pullback square is the (opposite of the) tensor
product square of commutative algebras: it endows the tensor product `X ⊗[A] B` of two
commutative Hopf algebras over a common commutative Hopf algebra `A` with its Hopf algebra
structure.

## Main results

* `CategoryTheory.grpObjOfIsPullback`: the group object structure on the apex of a pullback square
  of group objects;
* `CategoryTheory.isMonHom_isPullback_fst`, `CategoryTheory.isMonHom_isPullback_snd`: for this
  structure the two projections are morphisms of group objects.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Section 1.4
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
open CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section IsPullback

variable {P G H K : C} [GrpObj G] [GrpObj H] [GrpObj K]
  {f : G ⟶ K} [IsMonHom f] {g : H ⟶ K} [IsMonHom g] {p₁ : P ⟶ G} {p₂ : P ⟶ H}
  (hP : IsPullback p₁ p₂ f g)

/-- An arbitrary pullback square represents the presheaf of groups `pbPresheaf f g`. -/
noncomputable def isPullbackRepresentableBy :
    (pbPresheaf f g ⋙ forget _).RepresentableBy P where
  homEquiv {T} :=
    { toFun := fun u => ⟨(u ≫ p₁, u ≫ p₂), by
        rw [mem_pbSubgroup]; simp [Category.assoc, hP.w]⟩
      invFun := fun p => hP.lift p.1.1 p.1.2 ((mem_pbSubgroup p.1).1 p.2)
      left_inv := fun u => by apply hP.hom_ext <;> simp
      right_inv := fun p => Subtype.ext (Prod.ext (by simp) (by simp)) }
  homEquiv_comp := by
    intros
    exact Subtype.ext (Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- The group object structure on the apex of a pullback square of group objects. -/
@[instance_reducible]
noncomputable def grpObjOfIsPullback : GrpObj P :=
  GrpObj.ofRepresentableBy _ (pbPresheaf f g) (isPullbackRepresentableBy hP)

/-- For the group structure `grpObjOfIsPullback hP` on `P`, postcomposition with `p₁` is
multiplicative: `(u * v) ≫ p₁ = (u ≫ p₁) * (v ≫ p₁)`. -/
lemma isPullback_mul_fst {T : C} (u v : T ⟶ P) :
    letI := grpObjOfIsPullback hP
    (u * v) ≫ p₁ = (u ≫ p₁) * (v ≫ p₁) :=
  congr((pbVal (f := f) (g := g) $(homEquiv_mul P (pbPresheaf f g ⋙ forget₂ GrpCat MonCat)
      (isPullbackRepresentableBy hP) u v)).1)

/-- For the group structure `grpObjOfIsPullback hP` on `P`, postcomposition with `p₂` is
multiplicative: `(u * v) ≫ p₂ = (u ≫ p₂) * (v ≫ p₂)`. -/
lemma isPullback_mul_snd {T : C} (u v : T ⟶ P) :
    letI := grpObjOfIsPullback hP
    (u * v) ≫ p₂ = (u ≫ p₂) * (v ≫ p₂) :=
  congr((pbVal (f := f) (g := g) $(homEquiv_mul P (pbPresheaf f g ⋙ forget₂ GrpCat MonCat)
      (isPullbackRepresentableBy hP) u v)).2)

/-- For the group structure on a pullback `P` of group objects, the first projection `p₁` is a
morphism of group objects. -/
lemma isMonHom_isPullback_fst :
    letI := grpObjOfIsPullback hP
    IsMonHom p₁ :=
  letI := grpObjOfIsPullback hP
  isMonHom_of_mul' _ (fun _ u v => isPullback_mul_fst hP u v)

/-- For the group structure on a pullback `P` of group objects, the second projection `p₂` is a
morphism of group objects. -/
lemma isMonHom_isPullback_snd :
    letI := grpObjOfIsPullback hP
    IsMonHom p₂ :=
  letI := grpObjOfIsPullback hP
  isMonHom_of_mul' _ (fun _ u v => isPullback_mul_snd hP u v)

end IsPullback

end CategoryTheory
