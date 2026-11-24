module

public import UlmerBialgebras.Monadicity.AccTransfer
public import UlmerBialgebras.Monadicity.HomCatComp
public import UlmerBialgebras.Basic.PIE
public import UlmerBialgebras.Appendix.VCat
public import UlmerBialgebras.Basic.InsEqCat
public import UlmerBialgebras.Appendix.VCatUnit

/-!
# Representably accessible `V`-categories

This file concerns representable accessibility (Definition 7.2) in the 2-category `CAT_V` of
`V`-categories (`VCat.lean`), with the class of "small" objects taken to be the `V`-categories
whose type of objects is `w`-small:

* `UlmerBialgebras.IsSmallVCat` — the class of small `V`-categories.

A `V`-category `C` is **representably accessible** when for every small `V`-category `A` the
category `V`-`Fun(A, C)` of `V`-functors and `V`-natural transformations is accessible, and
restriction along a `V`-functor between small `V`-categories is an accessible functor.  The
case `A = 1` (through the equivalence `CAT_V(1, C) ≌ C` of `VCatUnit.lean`) shows that the
underlying ordinary category is then accessible.  These notions and results, and the
PIE-completeness of the resulting 2-category, are not formalized in this file.

## Main definitions

* `UlmerBialgebras.IsSmallVCat`: a `V`-category is small when its type of objects is `w`-small.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 7.2, Example 2.3 (2)
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
* [S. Lack, G. Tendas, *Virtual concepts in the theory of accessible
  categories*][LACK2023107196], Theorem 5.5, Theorem 5.9
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- A `V`-category is **small** when its type of objects is `w`-small, `w` being the universe
of the hom-sets of `V`. -/
def IsSmallVCat (A : VCat.{w, v, max u w} V) : Prop := Small.{w} A.carrier

end UlmerBialgebras
