module

public import Hopf.Cocommutative.GrpCocommHopf
public import InternalGroups.SubGrpObjAsGrp

/-!
# Morphisms of group objects of `Comon_k^coc` are bialgebra maps

The cartesian structure on `Comon_k^coc = CommComon (ModuleCat k)` is given by Fox's product cones
(`Foundations/CategoryTheory/Monoidal/CocommProducts.lean`). So the categorical product `A ⊗ B` *is*
the
tensor product of coalgebras and the projections are the counit projections, by definition. A group
object `H` is therefore a cocommutative Hopf algebra on the nose
(`Hopf/Cocommutative/GrpCocommHopf.lean`), and this file reads off morphisms:

* `HopfAlgebra.Cocommutative.GrpDict.tensorHom_hom_hom`: the product of two morphisms is their
  tensor product;
* `HopfAlgebra.Cocommutative.GrpDict.mulHom_eq`: the multiplication of `H` is `μ[H.X]`;
* `HopfAlgebra.Cocommutative.GrpDict.map_mul`, `map_one`: the underlying linear map of a morphism of
  group objects is multiplicative and unital, i.e. a morphism of bialgebras;
* `HopfAlgebra.Cocommutative.GrpDict.elemLinearMap`: the underlying linear map of a generalized
  element `T ⟶ H`, typed so that its values carry the Hopf algebra structure of `H`.

## Main results

* `HopfAlgebra.Cocommutative.GrpDict.tensorHom_hom_hom`: the categorical product of two morphisms of
  cocommutative coalgebras has underlying linear map their tensor product.
* `HopfAlgebra.Cocommutative.GrpDict.mulHom_eq`: the multiplication of a group object `H` is
  `μ[H.X]`.
* `HopfAlgebra.Cocommutative.GrpDict.map_mul`: the underlying linear map of a morphism of group
  objects is multiplicative.
* `HopfAlgebra.Cocommutative.GrpDict.map_one`: the underlying linear map of a morphism of group
  objects is unital.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 6.3 (`Hopf_k^coc = Grp(Comon_k^coc)`) and Corollary 6.11
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory TensorProduct
open scoped MonObj ComonObj

namespace HopfAlgebra.Cocommutative.GrpDict

open UlmerBialgebras

attribute [local instance_reducible] CommComon.toComon

variable {k : Type u} [CommRing k]

/-- **The categorical product of two morphisms of cocommutative coalgebras is their tensor
product.** -/
lemma tensorHom_hom_hom {A B A' B' : CommComon (ModuleCat.{u} k)} (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g).hom.hom = f.hom.hom ⊗ₘ g.hom.hom := by
  change Δ[(CommComon.tensorObj A B).X] ≫
      ((CocommComon.fst A.X B.X ≫ f.hom.hom) ⊗ₘ (CocommComon.snd A.X B.X ≫ g.hom.hom)) = _
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, ← Category.assoc, CocommComon.lift_fst_snd,
    Category.id_comp]

/-- The comparison `eHom` of `GrpCocommHopf.lean` is the identity for Fox's product. -/
lemma eHom_eq_id (X Y : CommComon (ModuleCat.{u} k)) : eHom X Y = 𝟙 _ :=
  CartesianMonoidalCategory.lift_fst_snd

/-- The multiplication of a group object is its structure morphism `μ`. -/
lemma mulHom_eq (H : Grp (CommComon (ModuleCat.{u} k))) : mulHom H = μ[H.X].hom.hom := by
  rw [mulHom, eHom_eq_id, Category.id_comp]

section Hom

variable {G H : Grp (CommComon (ModuleCat.{u} k))} (f : G ⟶ H)

/-- The underlying morphism of `k`-modules of a morphism of group objects. -/
abbrev modHom : (G.X.X : ModuleCat.{u} k) ⟶ H.X.X := f.hom.hom.hom.hom

/-- The underlying linear map of a morphism of group objects. -/
abbrev linearMap : (G.X.X : ModuleCat.{u} k) →ₗ[k] (H.X.X : ModuleCat.{u} k) := (modHom f).hom

/-- **A morphism of group objects intertwines the multiplications.** -/
lemma mulHom_comp : mulHom G ≫ modHom f = (modHom f ⊗ₘ modHom f) ≫ mulHom H := by
  have h : μ[G.X] ≫ f.hom.hom = (f.hom.hom ⊗ₘ f.hom.hom) ≫ μ[H.X] :=
    IsMonHom.mul_hom (f := f.hom.hom)
  have h2 := congr(($h).hom.hom)
  rw [CommComon.comp_hom, CommComon.comp_hom, tensorHom_hom_hom] at h2
  rw [mulHom_eq, mulHom_eq, modHom, h2]

/-- **A morphism of group objects preserves the units.** -/
lemma unitHom_comp : unitHom G ≫ modHom f = unitHom H := by
  have h : η[G.X] ≫ f.hom.hom = η[H.X] := IsMonHom.one_hom (f := f.hom.hom)
  have h1 : oneMor G ≫ f.hom.hom = oneMor H := by
    rw [oneMor, oneMor, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, h]
  exact congr(($h1).hom.hom)

/-- The underlying linear map of a morphism `f : G ⟶ H` of group objects in `Comon_k^coc` is
multiplicative for the Hopf algebra multiplications: `f (a * b) = f a * f b`. -/
lemma map_mul (a b : (G.X.X : ModuleCat.{u} k)) :
    linearMap f (a * b) = linearMap f a * linearMap f b := by
  simpa [mul_def] using congr(($(mulHom_comp f)).hom (a ⊗ₜ[k] b))

/-- The underlying linear map of a morphism `f : G ⟶ H` of group objects in `Comon_k^coc` is unital:
`f 1 = 1`. -/
lemma map_one : linearMap f 1 = 1 := by
  simpa [one_def] using congr(($(unitHom_comp f)).hom (1 : k))

end Hom

section Elem

variable {T : CommComon (ModuleCat.{u} k)} {H : Grp (CommComon (ModuleCat.{u} k))}

/-- The underlying linear map of a generalized element `x : T ⟶ H` of a group object, that is, of
a morphism of cocommutative coalgebras into the underlying coalgebra of `H`. Its codomain is
stated as `H.X.X`, so that its values carry the Hopf algebra structure of the dictionary. -/
abbrev elemLinearMap (x : T ⟶ H.X) : (T.X : ModuleCat.{u} k) →ₗ[k] (H.X.X : ModuleCat.{u} k) :=
  x.hom.hom.hom

end Elem

end HopfAlgebra.Cocommutative.GrpDict
