module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Creates
public import UlmerBialgebras.Kan.ColimKan

/-!
# Strict creation of left Kan extensions along `I → 1` and Mathlib's creation of colimits

A 1-cell `F : C ⟶ D` of `Cat` that strictly creates the left Kan extensions of every
`d : I ⟶ C` along `I ⟶ 1` (Definition 4.4 of [forsman2026syntactic]) creates the colimits of
shape `I` in Mathlib's sense (`CreatesColimitsOfShape`): a colimit cocone of `d ⋙ F` corresponds
to an initial left extension of `d ≫ F`, its unique preimage is an initial left extension of `d`,
that is, a colimit cocone of `d`, and a cocone of `d` whose image is a colimit is itself a colimit.

Mathlib's creation is transported along equivalences of shapes, so this also gives creation of
colimits of shape `J` for any category `J` equivalent to one with objects in `Type u` and
morphisms in `Type v`, in particular for any `J : Type w` with `[Category.{w} J]`,
`[Small.{u} J]` and `[LocallySmall.{v} J]` (`UlmerBialgebras.exists_smallShape_equiv`).

## Main results

* `UlmerBialgebras.createsColimitOfStrictlyCreatesLeftKan`
* `UlmerBialgebras.createsColimitsOfShapeOfStrictlyCreatesLeftKan`
* `UlmerBialgebras.nonempty_createsColimitsOfShape_of_strictlyCreatesLeftKan`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 4.2 and 4.4
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {I C D : Cat.{v, u}}

/-- A cocone and the cocone of its left extension along `I ⟶ 1` agree. -/
def coconeOfLeftExtOfCoconeIso {d : I ⟶ C} (c : Cocone d.toFunctor) :
    coconeOfLeftExt (leftExtOfCocone c) ≅ c :=
  Cocone.ext (Iso.refl _) (fun _ => Category.comp_id _)

/-- **Strict creation gives Mathlib's creation.** If `F` strictly creates the left Kan extension
of `d` along `I ⟶ 1`, then `F` creates the colimit of `d`. -/
@[instance_reducible]
noncomputable def createsColimitOfStrictlyCreatesLeftKan (F : C ⟶ D) (d : I ⟶ C)
    (h : StrictlyCreatesLeftKan (toOne I) d F) :
    CreatesColimit d.toFunctor F.toFunctor where
  reflects {c} hc := by
    let a := leftExtOfCocone c
    have hb : IsColimit (coconeOfLeftExt ((LeftExt.push (toOne I) d F).obj a)) :=
      hc.ofIsoColimit (((Cocone.functoriality _ F.toFunctor).mapIso
        (coconeOfLeftExtOfCoconeIso c).symm).trans
        (coconeOfLeftExtPushIso F a).symm)
    obtain ⟨hi⟩ := (h _ ⟨isInitialLeftExtOfIsColimit hb⟩).2 a rfl
    exact ⟨(isColimitCoconeOfLeftExt hi).ofIsoColimit (coconeOfLeftExtOfCoconeIso c)⟩
  lifts c hc :=
    let b : LeftExt (toOne I) (d ≫ F) := leftExtOfCocone c
    have hb : Nonempty (IsInitial b) :=
      ⟨isInitialLeftExtOfIsColimit (hc.ofIsoColimit (coconeOfLeftExtOfCoconeIso c).symm)⟩
    have ex := (h b hb).1.exists
    { liftedCocone := coconeOfLeftExt ex.choose
      validLift := (coconeOfLeftExtPushIso F ex.choose).symm ≪≫
        eqToIso (congrArg coconeOfLeftExt ex.choose_spec) ≪≫ coconeOfLeftExtOfCoconeIso c }

/-- **Strict creation gives Mathlib's creation**, for all diagrams of shape `I`. -/
@[instance_reducible]
noncomputable def createsColimitsOfShapeOfStrictlyCreatesLeftKan (F : C ⟶ D)
    (h : ∀ d : I ⟶ C, StrictlyCreatesLeftKan (toOne I) d F) :
    CreatesColimitsOfShape (I : Type u) F.toFunctor where
  CreatesColimit {K} := createsColimitOfStrictlyCreatesLeftKan F K.toCatHom (h _)

/-- A category `J : Type w` with `Category.{w}` that is `u`-small and locally `v`-small is
equivalent to a category with objects in `Type u` and morphisms in `Type v`, by an equivalence
that is a bijection on objects. -/
theorem exists_smallShape_equiv (J : Type w) [Category.{w} J] [Small.{u} J]
    [LocallySmall.{v} J] :
    ∃ (J' : Type u) (_ : Category.{v} J'), Nonempty (J ≌ J') ∧ Nonempty (J ≃ J') :=
  letI : Category.{v} (ShrinkHoms.{w} J) := ShrinkHoms.instCategory.{v} J
  have : Small.{u} (ShrinkHoms.{w} J) := inferInstanceAs (Small.{u} J)
  ⟨Shrink.{u} (ShrinkHoms.{w} J), inferInstance,
    ⟨(ShrinkHoms.equivalence.{v} J).trans (Shrink.equivalence _)⟩,
    ⟨equivShrink (ShrinkHoms.{w} J)⟩⟩

/-- **Small shapes.** If `F` strictly creates the left Kan extensions along `I ⟶ 1` for every
`I : Cat.{v, u}` equivalent to `J` (by an equivalence that is a bijection on objects), then `F`
creates the colimits of shape `J` (Mathlib's `CreatesColimitsOfShape`), for any `u`-small and
locally `v`-small `J : Type w`. -/
theorem nonempty_createsColimitsOfShape_of_strictlyCreatesLeftKan (F : C ⟶ D) (J : Type w)
    [Category.{w} J] [Small.{u} J] [LocallySmall.{v} J]
    (h : ∀ (J' : Type u) [Category.{v} J'], (J ≌ J') → (J ≃ J') →
      ∀ d : Cat.of J' ⟶ C, StrictlyCreatesLeftKan (toOne (Cat.of J')) d F) :
    Nonempty (CreatesColimitsOfShape J F.toFunctor) := by
  obtain ⟨J', _, ⟨e⟩, ⟨σ⟩⟩ := exists_smallShape_equiv.{w, v, u} J
  have i : CreatesColimitsOfShape J' F.toFunctor :=
    createsColimitsOfShapeOfStrictlyCreatesLeftKan (I := Cat.of J') F (h J' e σ)
  exact ⟨createsColimitsOfShapeOfEquiv e.symm F.toFunctor⟩

end UlmerBialgebras
