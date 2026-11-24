module

public import UlmerBialgebras.Paper.Sec6DefsGrp
public import UlmerBialgebras.Paper.Sec3DefsLoc
public import UlmerBialgebras.Paper.Sec6DefsLoc
public import Foundations.CategoryTheory.Monoidal.CocommProducts
public import Foundations.CategoryTheory.Factorization.RegularExact
public import Foundations.CategoryTheory.Exact.SemiAbelian
public import Foundations.CategoryTheory.Monoidal.MonadReflexive
public import Hopf.Cocommutative.CoreflexiveTensor
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite

/-!
# Challenge definitions for Corollary 6.11

The objects of Corollary 6.11 are already available:

* `CategoryTheory.CommComon A` (Mathlib): the cocommutative comonoids `Comon_A^coc` in a
  symmetric monoidal category `A`, with Fox's cartesian structure (the tensor product of `A` is
  the categorical product) from `Foundations.CategoryTheory.Monoidal.CocommProducts`;
* `Grp (CategoryTheory.CommComon A)`: the cocommutative Hopf monoids `Hopf_A^coc`;
* `UlmerBialgebras.Paper.Cart.cartModel B`: a cartesian category `B` as a `Σ_Cart`-model, and
  `UlmerBialgebras.Paper.Cart.grpExtSig`, `UlmerBialgebras.Paper.Cart.grpExtTheory`: a multi-sorted
  theory extending the theory of groups in each sort (`UlmerBialgebras/Paper/Sec6DefsGrp.lean`);
* `UlmerBialgebras.Paper.Loc.ModU R`: the symmetric monoidal category `Mod_R`
  (`UlmerBialgebras/Paper/Sec3DefsLoc.lean`).

The only new definition is the symmetric structure on `Cᵒᵖ`. Mathlib provides the braiding
`β_X,Y = (β_{Y,X})ᵒᵖ`; we record that it is symmetric when `C` is. This makes
`Comon^coc_{Mod_R^op} = CommComon (ModU R)ᵒᵖ` (affine `R`-schemes) a cartesian category.

## Main results

* `UlmerBialgebras.symmetricCategoryOp`: the opposite of a symmetric monoidal category is symmetric.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by Takeuchi*]
  [GRAN20194171]
* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory Opposite

/-- The opposite of a symmetric monoidal category is symmetric, with the braiding provided by
Mathlib (`β_X,Y = (β_{Y,X})ᵒᵖ`). -/
instance symmetricCategoryOp {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] : SymmetricCategory Cᵒᵖ where
  toBraidedCategory := inferInstance
  symmetry X Y := Quiver.Hom.unop_inj (SymmetricCategory.symmetry X.unop Y.unop)

end UlmerBialgebras
