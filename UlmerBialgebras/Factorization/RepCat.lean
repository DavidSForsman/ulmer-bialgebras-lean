module

public import UlmerBialgebras.Basic.CatTwoCat
public import Foundations.CategoryTheory.Factorization.FunctorOFS
public import UlmerBialgebras.Factorization.RepRegular

/-!
# Representable structure in `CAT` is ordinary structure

The notions of `Representable.lean` are *representable* versions of the ordinary ones: they
ask for
structure on all the hom-categories `K(x, c)`, compatibly with pre-composition.  In the
2-category `CAT` (see `CatTwoCat.lean`) the hom-category `K(X, C)` is the functor category
`X ⥤ C`, and this file makes the comparison with the ordinary notions on `C` explicit:

* `UlmerBialgebras.OFS.toRepOFS` — an orthogonal factorization system on `C` induces a representable
  one, given on `K(X, C) = X ⥤ C` by the pointwise factorization system;
* `UlmerBialgebras.RepOFS.toOFS` — conversely, a representable orthogonal factorization system on
  `C` restricts to an ordinary one along `K(1, C) ≃ C`.

That these two constructions are mutually inverse, and the corresponding comparison of
representable regularity (exactness) with regularity (exactness) of `C`, are not formalized in
this file.

## Main results

* `UlmerBialgebras.OFS.toRepOFS`: an orthogonal factorization system on a category `C` induces a
  representable one on `C` in `CAT`, given pointwise on `X ⥤ C`.
* `UlmerBialgebras.RepOFS.toOFS`: a representable orthogonal factorization system on `C` restricts
  to an orthogonal factorization system on `C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 6.1, 6.4, 7.2
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Cat.{v, u}}

/-! ## From an orthogonal factorization system to a representable one -/

/-- An orthogonal factorization system on a category `C` induces a representable one on `C`
viewed as an object of `CAT`: on the hom-category `K(X, C) = X ⥤ C` it is the pointwise
factorization system, and pre-composition acts pointwise. -/
noncomputable def OFS.toRepOFS (S : OFS C) : RepOFS C where
  ofs X := (S.functorOFS X).transport (catHomEquivalence X C).symm
  precomp_E := fun {_ _} f {_ _} _ hα x => hα (f.toFunctor.obj x)
  precomp_M := fun {_ _} f {_ _} _ hα x => hα (f.toFunctor.obj x)

/-! ## From a representable orthogonal factorization system to an ordinary one -/

/-- A representable orthogonal factorization system on an object `C` of `CAT` restricts,
along the equivalence `K(1, C) ≃ C`, to an orthogonal factorization system on `C`. -/
noncomputable def RepOFS.toOFS (R : RepOFS C) : OFS C :=
  (R.ofs One).transport ((catHomEquivalence One C).trans (oneEquiv C))

/-! ## The bijective correspondence -/

/-! ## Representable regularity and exactness -/

end UlmerBialgebras
