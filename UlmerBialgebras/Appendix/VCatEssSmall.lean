module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import UlmerBialgebras.Appendix.VCatIso
public import UlmerBialgebras.Appendix.VCatCellDense

/-!
# Choosing `A` in `CAT_V`, and choosing it as small as possible

`VCatCellDense.lean` verifies the local half of density for `CAT_V` with `A` the class of
**small `V`-categories**.  One would like to replace that proper class by a family indexed by
the `V`-categories with carrier in the universe `w` of the hom-objects (every small
`V`-category being equivalent in `CAT_V` to such a one), and, when the objects of `V` form a
`w`-small type, by a genuinely `w`-small family: the unit `V`-category together with the free
`V`-categories on an arrow `x`, one for each object `x` of `V`, are locally dense in `CAT_V`
(`UlmerBialgebras.isACellDense_of_probes`).

This file only provides the basic construction used for such replacements:

* `UlmerBialgebras.VInduced`, `UlmerBialgebras.vcatInduced` — the `V`-category induced on a type `ι`
  by a map `f : ι → C` into a `V`-category `C`, whose hom-object at `a, b` is that of `f a, f b`.

The universe-independence and smallness statements themselves are not formalized in this
file.

## Main definitions

* `UlmerBialgebras.VInduced`: the type `ι`, to carry the structure induced along a map `f : ι → C`.
* `UlmerBialgebras.vcatInduced`: the `V`-category induced on `ι` by a map `f : ι → C` into a
  `V`-category `C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1,
  Theorem A.5
* [P. Hofstra, M. Karvonen, *Inner Autoequivalences in General and Those of Monoidal Categories in
  Particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

universe w v u u₁ u₂

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-! ## `V`-categories induced along a map of object types -/

-- `VInduced` is a `def`, not an `abbrev`: if it were reducible, the instance
-- `inducedEnrichedCategory` would apply to the bare type `ι`, and the search for
-- `EnrichedCategory V ?X` would loop.
/-- The type `ι`, to be equipped with the structure of a `V`-category induced along a map
`f : ι → C` into a `V`-category `C`. -/
def VInduced {C : Type u₁} {ι : Type u₂} (_f : ι → C) : Type u₂ := ι

section Induced

variable {C : Type u₁} [Category.{w} C] [EnrichedOrdinaryCategory V C] {ι : Type u₂}
  (f : ι → C)

/-- The ordinary category induced on `ι` by a map `f : ι → C`. -/
instance inducedCategory : Category.{w} (VInduced f) where
  Hom a b := (f a ⟶ f b)
  id a := 𝟙 (f a)
  comp g h := g ≫ h
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

/-- The enrichment induced on `ι` by a map `f : ι → C` into a `V`-category: the hom-object
of `a, b` is the hom-object of `f a, f b`. -/
instance inducedEnrichedCategory : EnrichedCategory V (VInduced f) where
  Hom a b := (f a ⟶[V] f b)
  id a := eId V (f a)
  comp a b c := eComp V (f a) (f b) (f c)
  id_comp a b := EnrichedCategory.id_comp (f a) (f b)
  comp_id a b := EnrichedCategory.comp_id (f a) (f b)
  assoc a b c d := EnrichedCategory.assoc (f a) (f b) (f c) (f d)

/-- The induced enrichment represents the induced ordinary category. -/
instance inducedEnrichedOrdinaryCategory :
    EnrichedOrdinaryCategory V (VInduced f) where
  homEquiv {a b} := show (f a ⟶ f b) ≃ (𝟙_ V ⟶ (f a ⟶[V] f b)) from eHomEquiv V
  homEquiv_id a := eHomEquiv_id V (f a)
  homEquiv_comp := fun {a b c} g h =>
    eHomEquiv_comp (V := V) (X := f a) (Y := f b) (Z := f c) g h

end Induced

/-- The `V`-category induced on a type `ι` by a map `f : ι → C` into a `V`-category. -/
abbrev vcatInduced (C : VCat.{w, v, u₁} V) {ι : Type u₂} (f : ι → C.carrier) :
    VCat.{w, v, u₂} V :=
  VCat.of (VInduced f)

end UlmerBialgebras
