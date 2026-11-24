module

public import Companion.Statements.DefsAlgTranslations

/-!
# `Σ_Cart`-theories are universal algebra, and single-sorted universal algebra is first-order logic

Not a result of the paper. Isomorphisms of categories are stated as in
`modelCat_iso_cartThy_univ`: a pair of functors that are inverse up to equality of functors, and
that commute with the forgetful functors up to equality.

* `cartTheory_modelCat_iso`: for a 1-signature `sg` relative to `Σ_Cart` and a `sg`-theory `T`,
  the `T`-models `C^T` in a category `C` with finite products are isomorphic, over `C^S`, to the
  models of the equational theory `T' = CartToAlg.toMSTheory T` (the converse of
  `modelCat_iso_cartThy_univ`). `C^T` is computed for `AsSmall C`, as there, while `cartModel`
  needs a category whose objects and morphisms share a universe.
* `modelCat_type_iso_foModelCat`: for a single-sorted language, the models of an equational theory
  in `Type u` are isomorphic, over `Type u`, to the Mathlib models of its first-order theory
  `T.toFO` (universal closures of the equations), with Mathlib homomorphisms.

## Main results

* `UlmerBialgebras.Paper.cartTheory_modelCat_iso`
* `UlmerBialgebras.Paper.modelCat_type_iso_foModelCat`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19, Definition 3.14
-/

@[expose] public section

universe v u w s u₄ u₅

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Cart MSLanguage CartToAlg

/-- **`Σ_Cart`-theories are equational theories** (addition beyond [forsman2026syntactic]): for a
1-signature `sg` relative to `Σ_Cart` and a `sg`-theory `T`, and a cartesian monoidal category `C`
(objects in `Type (max s v w)`, morphisms in `Type (max s v)`), the models of the translated
equational theory `toMSTheory T` in `C` form a category isomorphic to `C^T` (Definition 3.14), over
`C^S`. -/
theorem cartTheory_modelCat_iso (C : Type (max s v w)) [Category.{max s v} C]
    [CartesianMonoidalCategory C]
    (sg : OneSig.{0, 0, 0, s, s} sigCart) (T : Theory.{0, 0, 0, s, s, s} sg) :
    ∃ (F : (toMSTheory T).ModelCat C ⥤ thyCat.{v, w, s} C sg T)
      (G : thyCat.{v, w, s} C sg T ⥤ (toMSTheory T).ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ thyCatForget.{v, w, s} C sg T = Theory.ModelCat.forget C (toMSTheory T) := sorry

/-- **Single-sorted equational theories are first-order theories** (addition beyond
[forsman2026syntactic]): for a language `L` with one sort, the models of an equational theory `T`
in `Type u` form a category isomorphic, over `Type u`, to the category of Mathlib models of the
first-order theory `T.toFO` (the universal closures of the equations of `T`) with Mathlib
homomorphisms. -/
theorem modelCat_type_iso_foModelCat {L : MSLanguage.{u₄, u₅}} [Unique L.Sorts] (T : L.Theory) :
    ∃ (F : T.ModelCat (Type u) ⥤ FOModelCat.{u} (toFOLanguage L) T.toFO)
      (G : FOModelCat.{u} (toFOLanguage L) T.toFO ⥤ T.ModelCat (Type u)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ FOModelCat.forget (toFOLanguage L) T.toFO =
          Theory.ModelCat.forget (Type u) T ⋙ Pi.eval (fun _ => Type u) default :=
  sorry

end UlmerBialgebras.Paper
