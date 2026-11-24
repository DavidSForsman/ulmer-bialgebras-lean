module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Foundations.CategoryTheory.Exact.SemiAbelian
public import Hopf.Basic.AntipodeBialgHom

/-!
# Bijective morphisms of Hopf algebras are isomorphisms

A bijective morphism of commutative Hopf algebras has an inverse which is again a morphism of
Hopf algebras (Mathlib's `BialgEquiv.ofBijective`), so that a bijective morphism induces an
isomorphism in the category `CommHopfAlgCat k` (`AffineGroupSchemes.CommHopfAlgCat.isoOfBijective`).

## Main results

* `AffineGroupSchemes.CommHopfAlgCat.isoOfBijective`: a bijective morphism of commutative Hopf
  algebras induces an isomorphism in `CommHopfAlgCat k`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.4
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra CategoryTheory

namespace AffineGroupSchemes


universe u

namespace CommHopfAlgCat

variable {k X Y : Type u} [CommRing k] [CommRing X] [CommRing Y]
  [HopfAlgebra k X] [HopfAlgebra k Y]

/-- A bijective morphism of commutative Hopf algebras is an isomorphism. -/
noncomputable def isoOfBijective (f : X →ₐc[k] Y) (hf : Function.Bijective f) :
    CommHopfAlgCat.of k X ≅ CommHopfAlgCat.of k Y :=
  CommHopfAlgCat.isoMk (BialgEquiv.ofBijective f hf)

end CommHopfAlgCat
end AffineGroupSchemes
