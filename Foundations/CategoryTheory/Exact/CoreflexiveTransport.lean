module

public import Foundations.CategoryTheory.Exact.JointlyConservative

/-!
# Transporting conservativity and exactness along a jointly conservative family of squares

This file contains the purely categorical core of the following statement: *faithful flatness
of a morphism of monoids can be detected by a jointly conservative family of functors*.

The situation is a family of commutative squares of functors
```
   A --------- L --------> B
   |                       |
  G i                     H i
   |                       |
   v                       v
  A i ------- L i -------> B i
```
(commuting up to a natural isomorphism), where the families `G` and `H` are jointly
conservative.  Of the transport results along such squares, the file now only keeps one
auxiliary isomorphism.

## Main results

* `CategoryTheory.parallelPairComp`: composing a parallel pair with a functor gives the parallel
  pair of the images.

## References

* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes], Section 4
-/

@[expose] public section

universe v u v₂ u₂ w

open CategoryTheory Limits

namespace CategoryTheory

section Preserves

variable {A : Type u} [Category.{v} A] {B : Type u₂} [Category.{v₂} B]

/-- Composing a parallel pair with a functor gives the parallel pair of the images. -/
abbrev parallelPairComp (L : A ⥤ B) {X Y : A} (u v : X ⟶ Y) :
    parallelPair u v ⋙ L ≅ parallelPair (L.map u) (L.map v) :=
  diagramIsoParallelPair (parallelPair u v ⋙ L)

end Preserves

end CategoryTheory
