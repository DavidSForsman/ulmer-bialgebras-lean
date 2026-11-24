module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The antipode as a convolution inverse

The antipode `S` of a Hopf algebra is a two-sided convolution inverse of the identity; this is
Mathlib's `LinearMap.antipode_mul_id` and `LinearMap.id_mul_antipode`.

For a commutative Hopf algebra the antipode is an algebra homomorphism; this is Mathlib's
`HopfAlgebra.antipodeAlgHom` (with `HopfAlgebra.antipode_mul_distrib`), and the multiplication
of a bialgebra as a coalgebra map is Mathlib's `Bialgebra.mulCoalgHom`.  This file imports them,
so that the input needed to see a commutative Hopf `R`-algebra as a group object of
`(CommAlgCat R)ᵒᵖ` is available downstream.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 1.5
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 1.4
-/

@[expose] public section


