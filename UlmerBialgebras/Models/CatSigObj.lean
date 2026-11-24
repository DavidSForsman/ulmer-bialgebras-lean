module

public import UlmerBialgebras.Models.Bialgebra
public import UlmerBialgebras.Models.CatCells

/-!
# Objects of operations of a model in `CAT`

For a model `M` in `CAT`, the object of operations `M^σ` is the inserter category
`Ins (M(t₁)) (M(t₂))` of `CatPIE.lean`, but only up to unfolding the chosen inserter. This file
gives the typed view `UlmerBialgebras.Model.catIns` of an object of `M^σ` as an object of that
inserter category, with the `rfl` lemmas that compute the inserter's 2-cell and the product
projections on it. Rewriting with them needs no transparency override.

## Main results

* `UlmerBialgebras.Model.catIns`: an object of `M^σ`, as an object of the inserter category.
* `UlmerBialgebras.Model.cat_sigIns_φ_app`: the component at `z` of the 2-cell of the inserter
  `M^σ` is the structure morphism of `catIns z`.
* `UlmerBialgebras.Model.cat_sigIns_u_obj`: the underlying object of `z` in `M₀`.
* `UlmerBialgebras.Model.cat_P_lift₂_app`: components of a 2-cell into an arity product.
* `UlmerBialgebras.Model.cat_Peq_hom_ext_iff`: morphisms into the product over the equations
  are equal iff their components are.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.13
-/

@[expose] public section

universe v u u₁ u₂ u₃

namespace UlmerBialgebras.Model

open CategoryTheory

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, max u v})
  (sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg)

/-- In `CAT`, an object of `M^σ` is an object of the inserter category
`Ins (M(t₁)) (M(t₂))`: a point `x` of `M₀` with its structure morphism `M(t₁)(x) ⟶ M(t₂)(x)`. -/
def catIns (z : (M.sigObj sg : Type (max u v))) :
    Ins (M.domCell sg).toFunctor (M.codCell sg).toFunctor := z

variable {M sg}

/-- The underlying object in `M₀` of an object `z` of `M^σ` is the point of `catIns z`. -/
@[simp] lemma cat_sigIns_u_obj (z : (M.sigObj sg : Type (max u v))) :
    (M.sigIns sg).u.toFunctor.obj z = (M.catIns sg z).pt := rfl

/-- The component at `z` of the 2-cell of the inserter `M^σ` is the structure morphism of
`catIns z`. -/
@[simp] lemma cat_sigIns_φ_app (z : (M.sigObj sg : Type (max u v))) :
    (M.sigIns sg).φ.toNatTrans.app z = (M.catIns sg z).cell := rfl

omit sg in
/-- In `CAT`, the component at `z` and `i` of a 2-cell induced into the arity product `M(B)` of a
function symbol is the component of its `i`-th factor. -/
lemma cat_P_lift₂_app (B : Sg.Fun) {A : Cat.{v, max u v}}
    {f g : A ⟶ (M.P B).pt} (γ : ∀ i, (f ≫ (M.P B).π i) ⟶ (g ≫ (M.P B).π i)) (z : A)
    (i : Fin (Sg.arn B)) :
    ((M.P B).lift₂ γ).toNatTrans.app z i = (γ i).toNatTrans.app z := rfl

/-- In `CAT`, two morphisms of the product `∏_r M_{c_r}` over the equations of a theory are equal
iff their components are. -/
lemma cat_Peq_hom_ext_iff (T : Theory.{u₁, u₂, u₃, 0, 0, 0} sg)
    {x y : ((M.Peq sg T).pt : Type (max u v))} (f g : x ⟶ y) :
    f = g ↔ ∀ r : T.Eqn, f r = g r :=
  funext_iff

end UlmerBialgebras.Model
