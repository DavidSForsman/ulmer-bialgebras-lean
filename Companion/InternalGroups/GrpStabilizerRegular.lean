module

public import Companion.InternalGroups.EmbedsInGrpObj
public import InternalGroups.GrpStabilizerCoset
public import Companion.InternalGroups.GrpWreathRegular
public import InternalGroups.GrpStabilizerTwisted
public import InternalGroups.GrpStabilizerOps
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Stabilizers and regular monomorphisms

A regular monomorphism of internal groups is a stabilizer: the equalizer of two group
homomorphisms is the stabilizer of the identity for their twisted action
(`InternalGroups.grpIsStabilizer_of_regularMono`, in `InternalGroups/GrpStabilizerOps.lean`).
Conversely, stabilizers are regular when
objects embed into internal groups.

Let `C` be a cartesian closed category with pullbacks. The stabilizer of a module map
`f : G ⟶ V` of an internal group `G` is separated by `f` itself: right translation by a
generalized element `g` leaves `f` unchanged exactly when `g` lies in the stabilizer
(`InternalGroups.isCosetSeparator_stabOf`). Compose `f` with a monomorphism of `V` into an
internal group `A`; the composite is still a coset separator (`IsCosetSeparator.comp_mono`).
Since it now lands in an internal group, the wreath product `A^G ⋊ G` presents the stabilizer as
an equalizer (`InternalGroups.Internal.regularMonoOfCosetSeparator`).

So if every object of `C` embeds into an internal group (`InternalGroups.EmbedsInGrpObj`), every
stabilizer of `Grp C` is a regular monomorphism
(`InternalGroups.isRegularMono_of_grpIsStabilizer_of_embedsInGrpObj`).

## Main results

* `InternalGroups.isCosetSeparator_stabOf`: a module map separates the cosets of its stabilizer;
* `InternalGroups.isRegularMono_of_grpIsStabilizer_of_embedsInGrpObj`: in a cartesian closed
  category whose objects embed into internal groups, every stabilizer of `Grp C` is regular.

## References

* D. Forsman, exactness criterion for internal groups (unpublished, announced)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits MonObj

attribute [local instance] CategoryTheory.ModObj.regular

namespace InternalGroups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]


variable {G : C} [GrpObj G] {V : C} [ModObj G V]

/-- **A module map separates the cosets of its stabilizer**: `f (x * g) = f x` for the generic
`x` exactly when `g` lies in the stabilizer of `f`. -/
theorem isCosetSeparator_stabOf (f : G ⟶ V) [IsModHom G f] :
    Internal.IsCosetSeparator (stabOf f).i f := by
  intro T g
  rw [Internal.shear_fst_assoc]
  constructor
  · intro h
    refine (killsOf_iff_factors f g).1 ?_
    have h' := congrArg (lift (1 : T ⟶ G) (𝟙 T) ≫ ·) h
    simp only [← Category.assoc, Hom.mul_def, comp_lift, lift_fst, lift_snd,
      Category.id_comp] at h'
    rw [← Hom.mul_def, _root_.one_mul, Hom.one_def] at h'
    rw [KillsOf, h', stabBasePoint, Category.assoc]
  · rintro ⟨y, rfl⟩
    have := mul_stabSubIncl_comp (f := f) (fst G T) (snd G T ≫ y)
    rwa [Category.assoc] at this


variable [MonoidalClosed C]

/-- The inclusion of the stabilizer of a module map into a module that embeds into an internal
group is a regular monomorphism. -/
theorem isRegularMono_stabOf_of_mono {G : C} [GrpObj G] {V : C} [ModObj G V] (q : G ⟶ V)
    [IsModHom G q] (A : Grp C) (j : V ⟶ A.X) [Mono j] :
    IsRegularMono (InternalGroups.stabOf q).inclGrp := by
  have hu : Internal.IsCosetSeparator (InternalGroups.stabOf q).inclGrp.hom.hom (q ≫ j) :=
    (InternalGroups.isCosetSeparator_stabOf q).comp_mono j
  have : Mono (InternalGroups.stabOf q).inclGrp.hom.hom := (InternalGroups.stabOf q).mono_i
  exact ⟨⟨Internal.regularMonoOfCosetSeparator hu⟩⟩

/-- **In a cartesian closed category whose objects embed into internal groups, every stabilizer
of `Grp C` is a regular monomorphism.** -/
theorem isRegularMono_of_grpIsStabilizer_of_embedsInGrpObj (hemb : InternalGroups.EmbedsInGrpObj C)
    {X Y : Grp C} {m : X ⟶ Y} (hm : GrpIsStabilizer m) : IsRegularMono m := by
  obtain ⟨q, e, he⟩ := hm
  obtain ⟨A, j, hj⟩ := hemb q.right.X
  have hs := isRegularMono_stabOf_of_mono (G := Y.X) (V := q.right.X) q.hom.hom A j
  subst he
  exact MorphismProperty.RespectsIso.precomp (MorphismProperty.regularMono _) e.hom _ hs

end InternalGroups

/-! ## Regular monomorphisms are stabilizers -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj
attribute [local instance] CategoryTheory.ModObj.regular

namespace InternalGroups
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

end InternalGroups
