module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Thin shapes as objects of `Cat.{v, u}`

The universe conventions of `Cat.{v, u}` separate the object universe `u` from the hom universe
`v`. A diagram shape whose objects live in `Type u` and whose hom types are `v`-small is therefore
not literally an object of `Cat.{v, u}` when `u > v`. `ShrinkHoms` gives an equivalent category
with the same objects and `v`-small homs, and `thinShapeCat` packages it as an object of
`Cat.{v, u}`.

The main use is the constructed shapes in Theorem 6.6: the walking cospan and the walking parallel
pair are lifted to `Type (max u v)` by `AsSmall` and then shrunk to hom universe `v`.

## Main results

* `CategoryTheory.thinShapeCat`: `ShrinkHoms C` as an object of `Cat.{v, u}`.
* `CategoryTheory.thinShapeCat.forget`: the functor from the thin shape back to `C`.
* `CategoryTheory.thinShapeCat.equivalence`: `C` is equivalent to its thin shape.
* `CategoryTheory.cospanShapeCat`, `CategoryTheory.parallelPairShapeCat`: the walking cospan and
  walking parallel pair as objects of `Cat.{v, max u v}`, with their `forget` functors and
  equivalences to the standard shapes.

## Implementation notes

`ShrinkHoms` requires `[LocallySmall.{v} C]`. For the two shapes used here the hom types are finite
(they are `ULift` of the hom types of `WalkingCospan` and `WalkingParallelPair`, which live in
`Type 0`), so the instances are provided explicitly.

## References

* `Mathlib.CategoryTheory.EssentiallySmall` (`ShrinkHoms`, `LocallySmall`)
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

/-- `ShrinkHoms C` as an object of `Cat.{v, u}`: the same objects as `C`, with the hom types
shrunk to `Type v`. Requires `C` to be locally `v`-small. -/
noncomputable def thinShapeCat (C : Type u) [Category.{u} C] [LocallySmall.{v} C] : Cat.{v, u} :=
  Cat.of (ShrinkHoms C)

namespace thinShapeCat

/-- The functor from the thin shape back to the original category. -/
noncomputable def forget (C : Type u) [Category.{u} C] [LocallySmall.{v} C] :
    (thinShapeCat.{u, v} C : Type u) ⥤ C :=
  ShrinkHoms.inverse (C := C)

/-- The original category is equivalent to its thin shape. -/
noncomputable def equivalence (C : Type u) [Category.{u} C] [LocallySmall.{v} C] :
    C ≌ (thinShapeCat.{u, v} C : Type u) :=
  ShrinkHoms.equivalence (C := C)

end thinShapeCat

/-- The hom types of `AsSmall WalkingCospan` are finite, hence `v`-small. -/
instance locallySmallAsSmallWalkingCospan :
    LocallySmall.{v} (AsSmall.{max u v} WalkingCospan) where
  hom_small X Y := inferInstanceAs (Small.{v} (ULift (ULift.down X ⟶ ULift.down Y)))

/-- The hom types of `AsSmall WalkingParallelPair` are finite, hence `v`-small. -/
instance locallySmallAsSmallWalkingParallelPair :
    LocallySmall.{v} (AsSmall.{max u v} WalkingParallelPair) where
  hom_small X Y := inferInstanceAs (Small.{v} (ULift (ULift.down X ⟶ ULift.down Y)))

/-- The walking cospan, as an object of `Cat.{v, max u v}`. -/
noncomputable def cospanShapeCat : Cat.{v, max u v} :=
  thinShapeCat.{max u v, v} (AsSmall.{max u v} WalkingCospan)

/-- The walking parallel pair, as an object of `Cat.{v, max u v}`. -/
noncomputable def parallelPairShapeCat : Cat.{v, max u v} :=
  thinShapeCat.{max u v, v} (AsSmall.{max u v} WalkingParallelPair)

/-- The hom types of `AsSmall WalkingReflexivePair` are finite, hence `v`-small. -/
instance locallySmallAsSmallWalkingReflexivePair :
    LocallySmall.{v} (AsSmall.{max u v} WalkingReflexivePair) where
  hom_small X Y := inferInstanceAs (Small.{v} (ULift (ULift.down X ⟶ ULift.down Y)))

/-- The walking reflexive pair, as an object of `Cat.{v, max u v}`. -/
noncomputable def reflexivePairShapeCat : Cat.{v, max u v} :=
  thinShapeCat.{max u v, v} (AsSmall.{max u v} WalkingReflexivePair)

namespace cospanShapeCat

/-- The functor from the thin walking cospan to `AsSmall WalkingCospan`. -/
noncomputable def forget :
    (cospanShapeCat.{u, v} : Type (max u v)) ⥤ AsSmall.{max u v} WalkingCospan :=
  thinShapeCat.forget _

/-- The thin walking cospan is equivalent to `WalkingCospan`. -/
noncomputable def equivalence :
    WalkingCospan ≌ (cospanShapeCat.{u, v} : Type (max u v)) :=
  (AsSmall.equiv (C := WalkingCospan)).trans
    (ShrinkHoms.equivalence (C := AsSmall.{max u v} WalkingCospan))

end cospanShapeCat

namespace parallelPairShapeCat

/-- The functor from the thin walking parallel pair to `AsSmall WalkingParallelPair`. -/
noncomputable def forget :
    (parallelPairShapeCat.{u, v} : Type (max u v)) ⥤ AsSmall.{max u v} WalkingParallelPair :=
  thinShapeCat.forget _

/-- The thin walking parallel pair is equivalent to `WalkingParallelPair`. -/
noncomputable def equivalence :
    WalkingParallelPair ≌ (parallelPairShapeCat.{u, v} : Type (max u v)) :=
  (AsSmall.equiv (C := WalkingParallelPair)).trans
    (ShrinkHoms.equivalence (C := AsSmall.{max u v} WalkingParallelPair))

end parallelPairShapeCat

namespace reflexivePairShapeCat

/-- The functor from the thin walking reflexive pair to `AsSmall WalkingReflexivePair`. -/
noncomputable def forget :
    (reflexivePairShapeCat.{u, v} : Type (max u v)) ⥤ AsSmall.{max u v} WalkingReflexivePair :=
  thinShapeCat.forget _

/-- The thin walking reflexive pair is equivalent to `WalkingReflexivePair`. -/
noncomputable def equivalence :
    WalkingReflexivePair ≌ (reflexivePairShapeCat.{u, v} : Type (max u v)) :=
  (AsSmall.equiv (C := WalkingReflexivePair)).trans
    (ShrinkHoms.equivalence (C := AsSmall.{max u v} WalkingReflexivePair))

end reflexivePairShapeCat

end CategoryTheory
