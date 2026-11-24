module

public import UlmerBialgebras.Models.CatPIE

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Components of 2-cells in `CAT`

The 2-cells of the strict 2-category `CAT` (`CategoryTheory.Cat.bicategory`) are natural
transformations, but their vertical composition, identities and whiskerings are those of the strict
2-category `CAT` (`Bicategory.Strict`), so the usual simp lemmas of `CategoryTheory.NatTrans` do not
fire on them. The components of composites, identities and whiskerings are Mathlib's
(`Cat.Hom₂.comp_app`, `Cat.Hom₂.id_app`, `Cat.whiskerLeft_app`, `Cat.whiskerRight_app`,
`Cat.eqToHom_app`), made simp lemmas here. This file records the rest of the (definitional)
dictionary, which turns any computation with 2-cells of `CAT` into a computation with components.

## Main results

* `UlmerBialgebras.cat_lift₂_app`: components of the 2-cell induced into a product of categories.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2
* [G. M. Kelly, *Basic concepts of enriched category theory*][Kelly:Enriched]
-/

universe v u

namespace UlmerBialgebras

open CategoryTheory

variable {A B D : Cat.{v, u}}

/- The component lemmas of Mathlib that this project's computations with 2-cells of `CAT` rewrite
with; `Cat.Hom₂.comp_app`, `Cat.Hom₂.id_app` and `Cat.Hom.comp_map` are simp lemmas already. -/
attribute [simp] Cat.whiskerLeft_app Cat.whiskerRight_app Cat.eqToHom_app Cat.Hom.comp_obj

/-- In `Cat`, the 2-cell induced into the chosen product by a family `γ` has components
`(γ i)_z` in each factor `i`. -/
@[simp] lemma cat_lift₂_app {ι : Type} {A : Cat.{v, max u v}} {c : ι → Cat.{v, max u v}}
    {f g : A ⟶ (HasChosenProductsOfSize.prod c).pt}
    (γ : ∀ i, (f ≫ (HasChosenProductsOfSize.prod c).π i) ⟶
      (g ≫ (HasChosenProductsOfSize.prod c).π i)) (z : A)
    (i : ι) :
    ((HasChosenProductsOfSize.prod c).lift₂ γ).toNatTrans.app z i = (γ i).toNatTrans.app z := rfl

/-- In `Cat`, the functor induced into the chosen product by `g` sends `z` to `(g i).toFunctor.obj
    z` in
each factor `i`. -/
@[simp] lemma cat_lift_obj {ι : Type} {A : Cat.{v, max u v}} {c : ι → Cat.{v, max u v}}
    (g : ∀ i, A ⟶ c i) (z : A) (i : ι) :
    ((HasChosenProductsOfSize.prod c).lift g).toFunctor.obj z i = (g i).toFunctor.obj z := rfl

/-- In `Cat`, the `i`-th projection of the chosen product sends `z` to its component `z i`. -/
@[simp] lemma cat_prod_π_obj {ι : Type} {c : ι → Cat.{v, max u v}}
    (z : (HasChosenProductsOfSize.prod c).pt) (i : ι) :
    ((HasChosenProductsOfSize.prod c).π i).toFunctor.obj z = z i := rfl

/-- In `Cat`, the `i`-th projection of the chosen product sends a morphism `f` to `f i`. -/
@[simp] lemma cat_prod_π_map {ι : Type} {c : ι → Cat.{v, max u v}}
    {z z' : (HasChosenProductsOfSize.prod c).pt} (f : z ⟶ z') (i : ι) :
    ((HasChosenProductsOfSize.prod c).π i).toFunctor.map f = f i := rfl

/-- In `Cat`, the functor induced into the chosen product by `g` sends a morphism `f` to
`(g i).toFunctor.map f` in each factor `i`. -/
@[simp] lemma cat_lift_map {ι : Type} {A : Cat.{v, max u v}} {c : ι → Cat.{v, max u v}}
    (g : ∀ i, A ⟶ c i) {z z' : A}
    (f : z ⟶ z') (i : ι) :
    ((HasChosenProductsOfSize.prod c).lift g).toFunctor.map f i = (g i).toFunctor.map f := rfl

/-- In `Cat`, the 2-cell induced into the chosen finite product by a family `γ` has components
`(γ i)_z` in each factor `i`. -/
@[simp] lemma cat_finProd_lift₂_app {n : ℕ} {c : Fin n → Cat.{v, u}}
    {f g : A ⟶ (HasChosenFinProducts.finProd c).pt}
    (γ : ∀ i, (f ≫ (HasChosenFinProducts.finProd c).π i) ⟶
      (g ≫ (HasChosenFinProducts.finProd c).π i)) (z : A) (i : Fin n) :
    ((HasChosenFinProducts.finProd c).lift₂ γ).toNatTrans.app z i = (γ i).toNatTrans.app z := rfl

/-- In `Cat`, the functor induced into the chosen finite product by `g` sends `z` to
`(g i).toFunctor.obj z` in each factor `i`. -/
@[simp] lemma cat_finProd_lift_obj {n : ℕ} {c : Fin n → Cat.{v, u}} (g : ∀ i, A ⟶ c i) (z : A)
    (i : Fin n) :
    ((HasChosenFinProducts.finProd c).lift g).toFunctor.obj z i = (g i).toFunctor.obj z :=
  rfl

/-- In `Cat`, the functor induced into the chosen finite product by `g` sends a morphism `f` to
`(g i).toFunctor.map f` in each factor `i`. -/
@[simp] lemma cat_finProd_lift_map {n : ℕ} {c : Fin n → Cat.{v, u}} (g : ∀ i, A ⟶ c i) {z z' : A}
    (f : z ⟶ z') (i : Fin n) :
    ((HasChosenFinProducts.finProd c).lift g).toFunctor.map f i = (g i).toFunctor.map f := rfl

/-- In `Cat`, the `i`-th projection of the chosen finite product sends `z` to its component
`z i`. -/
@[simp] lemma cat_finProd_π_obj {n : ℕ} {c : Fin n → Cat.{v, u}}
    (z : (HasChosenFinProducts.finProd c).pt) (i : Fin n) :
    ((HasChosenFinProducts.finProd c).π i).toFunctor.obj z = z i := rfl

/-- In `Cat`, the `i`-th projection of the chosen finite product sends a morphism `f` to `f i`. -/
@[simp] lemma cat_finProd_π_map {n : ℕ} {c : Fin n → Cat.{v, u}}
    {z z' : (HasChosenFinProducts.finProd c).pt} (f : z ⟶ z') (i : Fin n) :
    ((HasChosenFinProducts.finProd c).π i).toFunctor.map f = f i := rfl

end UlmerBialgebras
