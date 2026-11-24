module

public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
public import Foundations.CategoryTheory.Bicategory.BiDense

/-!
# Challenge: definitions for the comparison of Definition 7.1 with Hofstra–Karvonen

The full sub-2-category of a strict 2-category `K` spanned by a class of objects `A`, as a
bicategory in Mathlib's sense, and its inclusion pseudofunctor into `K` (seen as a bicategory
through `UlmerBialgebras.AsBicat`). Hofstra–Karvonen bi-density of this pseudofunctor
(`CategoryTheory.Pseudofunctor.IsBiDense`, see
    the development repository's `Foundations/CategoryTheory/Bicategory/BiDense`)
is compared with the paper's bi-density of the class `A` (`UlmerBialgebras.Paper.IsBiDense`) in
`UlmerBialgebras/Paper/Sec7Variant.lean`.

## Main results

* `UlmerBialgebras.Paper.FullSubBicat`: the full sub-2-category of `K` spanned by `A`, as a
  bicategory.
* `UlmerBialgebras.Paper.fullSubBicatι`: its inclusion into `K`, as a pseudofunctor.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Bicategory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- The objects of `K` satisfying `A`, as objects of `K` seen as a bicategory. -/
def fullSubBicatObj (A : ObjectProperty Obj) : {x : Obj // A x} → AsBicat.{u, v, w} Obj :=
  fun x ↦ x.1

/-- The full sub-2-category of `K` spanned by a class of objects `A`, as a bicategory: its
objects are the objects of `K` satisfying `A`, and its 1- and 2-cells are those of `K`. -/
abbrev FullSubBicat (A : ObjectProperty Obj) : Type u :=
  InducedBicategory (AsBicat.{u, v, w} Obj) (fullSubBicatObj A)

/-- The inclusion of the full sub-2-category spanned by `A` into `K`, as a pseudofunctor. -/
abbrev fullSubBicatι (A : ObjectProperty Obj) : FullSubBicat A ⥤ᵖ AsBicat.{u, v, w} Obj :=
  (InducedBicategory.forget (F := fullSubBicatObj A)).toPseudofunctor

end UlmerBialgebras.Paper
