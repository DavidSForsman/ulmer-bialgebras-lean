module

public import UlmerBialgebras.Models.LaxCell
public import UlmerBialgebras.Models.OplaxComp

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# 2-cells between oplax morphisms of Σ-models

The formal dual of `LaxCell.lean`.  A 2-cell `α : H ⟹ H'` between oplax morphisms
`H, H' : M → N` of Σ-models is a family of 2-cells `α_c : H_c ⟹ H'_c` of the ambient
2-category, compatible with the (oplax) structure 2-cells (`UlmerBialgebras.OplaxTwoCell`).

Identities and vertical composites are computed componentwise, so that an adjunction in the
2-category `Oplax(Σ, K)` of Σ-models and oplax morphisms amounts to a family of adjunctions in
`K` whose units and counits are 2-cells of oplax morphisms.  Only the notion of 2-cell itself
is formalized in this file.

## Main results

* `UlmerBialgebras.OplaxTwoCell`: 2-cells between oplax morphisms of Σ-models.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Proposition 3.11 and the subsequent definition of
  transformations of lax and oplax morphisms
-/

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig}

/-- A 2-cell between oplax morphisms of Σ-models: a family of 2-cells between the
components, compatible with the structure 2-cells. -/
structure OplaxTwoCell {M N : PreModel Sg Obj} (H H' : OplaxData M N) where
  /-- The component of the 2-cell at a category symbol. -/
  app : ∀ c : Sg.Cat, H.cell c ⟶ H'.cell c
  /-- Compatibility with the structure 2-cells of `H` and `H'`. -/
  str_compat : ∀ B : Sg.Fun,
    (M.fn B ◁ app (Sg.fcod B)) ≫ H'.str B = H.str B ≫ (prodApp app B ▷ N.fn B)

namespace OplaxTwoCell

variable {M N : PreModel Sg Obj}

end OplaxTwoCell

namespace OplaxAdj

variable {M N : Model Sg Obj} {F : OplaxMor N M} {G : OplaxMor M N}

end OplaxAdj

end UlmerBialgebras
