module

public import UlmerBialgebras.Models.Co
public import UlmerBialgebras.Models.BicatTwoCat

/-!
# Adjunctions in `K^co`

Reversing 2-cells exchanges the unit and counit of an adjunction, so that `f ⊣ g` in `K`
is `g ⊣ f` in `K^co`.

## Main results

* `UlmerBialgebras.Co.adj`: an adjunction `f ⊣ g` in `K` as an adjunction `g ⊣ f` in `K^co`.
* `UlmerBialgebras.Co.unadj`: an adjunction `g ⊣ f` in `K^co` as an adjunction `f ⊣ g` in `K`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2
* [G. M. Kelly, R. Street,
  *Review of the elements of 2-categories*][kellyReviewElements2categories1974]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Co

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
variable {a b : Obj} {f : a ⟶ b} {g : b ⟶ a}

/-- An adjunction in `K`, with its unit and counit exchanged in `K^co`. -/
def adj (A : TwoAdj f g) : TwoAdj (Obj := Co Obj) (hom g) (hom f) :=
  TwoAdj.mk' (Obj := Co Obj) (cell A.counit') (cell A.unit')
    (by simpa only [comp_eq (Obj := Obj), eqToHom_eq (Obj := Obj), whiskerLeft_eq (Obj := Obj),
      whiskerRight_eq (Obj := Obj), cell, uncell, hom, Category.assoc] using A.right_triangle')
    (by simpa only [comp_eq (Obj := Obj), eqToHom_eq (Obj := Obj), whiskerLeft_eq (Obj := Obj),
      whiskerRight_eq (Obj := Obj), cell, uncell, hom, Category.assoc] using A.left_triangle')

/-- An adjunction in `K^co`, with its unit and counit exchanged in `K`. -/
def unadj (A : TwoAdj (Obj := Co Obj) (hom g) (hom f)) : TwoAdj f g :=
  TwoAdj.mk' (uncell A.counit') (uncell A.unit')
    (by simpa only [comp_eq (Obj := Obj), eqToHom_eq (Obj := Obj), whiskerLeft_eq (Obj := Obj),
      whiskerRight_eq (Obj := Obj), cell, uncell, hom, Category.assoc] using A.right_triangle')
    (by simpa only [comp_eq (Obj := Obj), eqToHom_eq (Obj := Obj), whiskerLeft_eq (Obj := Obj),
      whiskerRight_eq (Obj := Obj), cell, uncell, hom, Category.assoc] using A.left_triangle')

end UlmerBialgebras.Co
