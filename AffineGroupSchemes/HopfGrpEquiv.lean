module

public import Mathlib.Algebra.Category.CommBialgCat
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Hopf.Basic.AntipodeAlgHom
public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Foundations.CategoryTheory.Exact.SemiAbelian

/-!
# Commutative Hopf algebras are the same thing as affine group schemes

Mathlib knows that a commutative Hopf `R`-algebra is the same thing as a *group* object of
`(CommAlgCat R)ᵒᵖ` — an affine group scheme over `R`.  The two directions are Mathlib's
instances `CommAlgCat.grpObjOpOf` (the inverse map of `op (CommAlgCat.of R A)` is the antipode
`HopfAlgebra.antipodeAlgHom`) and `HopfAlgebra R A.unop` for `[GrpObj A]` (the antipode is the
inverse map), which assemble into the equivalence
`commHopfAlgCatEquivCogrpCommAlgCat : CommHopfAlgCat R ≌ (Grp (CommAlgCat R)ᵒᵖ)ᵒᵖ`.

Here we record its opposite form
`AffineGroupSchemes.opCommHopfAlgCatEquivGrp : (CommHopfAlgCat R)ᵒᵖ ≌ Grp (CommAlgCat R)ᵒᵖ`,
which is the statement that the category of affine group `R`-schemes is the category of group
objects of the category of affine `R`-schemes.

## Main results

* `AffineGroupSchemes.opCommHopfAlgCatEquivGrp`: an equivalence
  `(CommHopfAlgCat R)ᵒᵖ ≌ Grp (CommAlgCat R)ᵒᵖ`.

## References

* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Section 1.4
* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AffineGroupSchemes


variable (R : Type u) [CommRing R]

/-- The opposite form of Mathlib's `commHopfAlgCatEquivCogrpCommAlgCat`: the category of affine
group `R`-schemes is the category of group objects of the category of affine `R`-schemes
(Waterhouse [waterhouseIntroductionAffineGroup1979], Section 1.4). -/
noncomputable def opCommHopfAlgCatEquivGrp :
    (CommHopfAlgCat.{u} R)ᵒᵖ ≌ Grp (CommAlgCat.{u} R)ᵒᵖ :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).op.trans (opOpEquivalence _)

end AffineGroupSchemes
