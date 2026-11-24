module

public import UlmerBialgebras.Models.BicatTwoCat
public import UlmerBialgebras.Models.LaxComp

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# 2-cells between lax morphisms of Σ-models

The Σ-models in a PIE-complete strict 2-category `K`, their lax morphisms
(`UlmerBialgebras.LaxMor`, Definition 3.10) and the 2-cells introduced here form a 2-category
`Lax(Σ, K)`: a 2-cell `α : H ⟹ H'` between lax morphisms `H, H' : M → N` is a family of
2-cells `α_c : H_c ⟹ H'_c` of `K`, compatible with the structure 2-cells of `H` and `H'`
(`UlmerBialgebras.LaxTwoCell`).

Identities and vertical composites of such 2-cells are computed componentwise, so that an
adjunction in `Lax(Σ, K)` amounts to a family of adjunctions in `K` whose units and counits
are 2-cells of lax morphisms.  Only the notion of 2-cell itself is formalized in this file.

## Main results

* `UlmerBialgebras.LaxTwoCell`: 2-cells between lax morphisms of Σ-models.
* `UlmerBialgebras.prodApp`: the 2-cell induced on the product of the arity of a functor symbol by a
  family of 2-cells `α_c`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Proposition 3.11 and the subsequent definition of
  transformations of lax morphisms
-/

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig}

section ProdApp

variable {M N : PreModel Sg Obj}

/-- The 2-cell induced on the product of the arity of a functor symbol by a family of
2-cells between the components of two morphisms of Σ-models. -/
def prodApp {Hc H'c : ∀ c : Sg.Cat, M.obj c ⟶ N.obj c} (app : ∀ c, Hc c ⟶ H'c c)
    (B : Sg.Fun) :
    (N.P B).lift (fun i => (M.P B).π i ≫ Hc (Sg.art B i)) ⟶
      (N.P B).lift (fun i => (M.P B).π i ≫ H'c (Sg.art B i)) :=
  (N.P B).lift₂ (fun i =>
    eqToHom ((N.P B).lift_π (fun i => (M.P B).π i ≫ Hc (Sg.art B i)) i) ≫
      ((M.P B).π i ◁ app (Sg.art B i)) ≫
      eqToHom ((N.P B).lift_π (fun i => (M.P B).π i ≫ H'c (Sg.art B i)) i).symm)

/-- The `i`-th projection of `prodApp app B` is the whiskering `π_i ◁ app_{c_i}`, up to
`eqToHom`. -/
@[simp] lemma prodApp_π {Hc H'c : ∀ c : Sg.Cat, M.obj c ⟶ N.obj c} (app : ∀ c, Hc c ⟶ H'c c)
    (B : Sg.Fun) (i : Fin (Sg.arn B)) :
    prodApp app B ▷ (N.P B).π i
      = eqToHom ((N.P B).lift_π (fun i => (M.P B).π i ≫ Hc (Sg.art B i)) i) ≫
        ((M.P B).π i ◁ app (Sg.art B i)) ≫
        eqToHom ((N.P B).lift_π (fun i => (M.P B).π i ≫ H'c (Sg.art B i)) i).symm :=
  (N.P B).lift₂_π _ i

end ProdApp

/-- A 2-cell between lax morphisms of Σ-models: a family of 2-cells between the components,
compatible with the structure 2-cells. -/
structure LaxTwoCell {M N : PreModel Sg Obj} (H H' : LaxData M N) where
  /-- The component of the 2-cell at a category symbol. -/
  app : ∀ c : Sg.Cat, H.cell c ⟶ H'.cell c
  /-- Compatibility with the structure 2-cells of `H` and `H'`. -/
  str_compat : ∀ B : Sg.Fun,
    (prodApp app B ▷ N.fn B) ≫ H'.str B = H.str B ≫ (M.fn B ◁ app (Sg.fcod B))

namespace LaxTwoCell

variable {M N : PreModel Sg Obj}

end LaxTwoCell

namespace LaxAdj

variable {M N : Model Sg Obj} {F : LaxMor N M} {G : LaxMor M N}

end LaxAdj

end UlmerBialgebras
