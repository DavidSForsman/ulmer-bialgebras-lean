module

public import Mathlib.CategoryTheory.Generator.StrongGenerator
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# Strong generators along a left adjoint

Let `adj : L ⊣ U` be an adjunction with `U : D ⥤ C` faithful and conservative (for example,
`U` monadic). If `P` is a strong generator of `C`, then its image `P.map L` is a strong generator
of `D`. If moreover `U` is `κ`-accessible and `P` consists of `κ`-presentable objects, then so
does `P.map L`. Combined with Adámek–Rosický 1.20 (Mathlib's
`IsCardinalLocallyPresentable.iff_exists_isStrongGenerator`), this shows that a cocomplete
category `D` with such a right adjoint `U` to a locally `κ`-presentable category `C` is locally
`κ`-presentable, for the same `κ`. In particular, the category of algebras of a `κ`-accessible
monad on a locally `κ`-presentable category is locally `κ`-presentable as soon as it is
cocomplete.

Unlike Mathlib's `Adjunction.isCardinalLocallyPresentable`, the right adjoint `U` need not be
full.

## Main results

* `CategoryTheory.ObjectProperty.IsStrongGenerator.of_le`: a property containing a strong
  generator is a strong generator;
* `CategoryTheory.Adjunction.isSeparating_map`: for `L ⊣ U` with `U` faithful, `L` maps a
  separating property to a separating property (for `strictMap`, this is Mathlib's
  `ObjectProperty.IsSeparating.strictMap_leftAdjoint`);
* `CategoryTheory.Adjunction.isStrongGenerator_strictMap`,
  `CategoryTheory.Adjunction.isStrongGenerator_map`: for `L ⊣ U` with `U` faithful and
  reflecting isomorphisms, `L` maps a strong generator to a strong generator;
* `CategoryTheory.Adjunction.map_le_isCardinalPresentable`,
  `CategoryTheory.Adjunction.strictMap_le_isCardinalPresentable`: if `U` is `κ`-accessible, `L`
  maps `κ`-presentable objects to `κ`-presentable objects;
* `CategoryTheory.Adjunction.isStrongGenerator_strictMap_and_le_isCardinalPresentable`: the two
  previous statements together;
* `CategoryTheory.Adjunction.preservesCardinalPresentable`: a left adjoint whose right adjoint is
  `κ`-accessible preserves `κ`-presentable objects;
* `CategoryTheory.Functor.preservesCardinalPresentable_of_isEquivalence`: an equivalence preserves
  `κ`-presentable objects;
* `CategoryTheory.Adjunction.isCardinalLocallyPresentable_of_reflectsIsomorphisms`: if `C` is
  locally `κ`-presentable, `D` is cocomplete and `U` is faithful, conservative and
  `κ`-accessible, then `D` is locally `κ`-presentable;
* `CategoryTheory.Monad.forget_isCardinalAccessible`,
  `CategoryTheory.MonadicRightAdjoint.isCardinalAccessible_of_monad`: the forgetful functor of
  the algebras of a `κ`-accessible monad (a monadic functor whose monad is `κ`-accessible) is
  `κ`-accessible;
* `CategoryTheory.MonadicRightAdjoint.isCardinalLocallyPresentable`: the same for a monadic
  `κ`-accessible functor `U : D ⥤ C`; monadic functors are faithful and conservative
  (`CategoryTheory.MonadicRightAdjoint.faithful`,
  `CategoryTheory.MonadicRightAdjoint.reflectsIsomorphisms`);
* `CategoryTheory.Monad.isCardinalLocallyPresentable_algebra`: the category of algebras of a
  `κ`-accessible monad on a locally `κ`-presentable category is locally `κ`-presentable if it is
  cocomplete.

## References

* [Adámek, J. and Rosický, J., *Locally presentable and accessible
  categories*][LPC], Theorem 1.20 (characterization by strong generators) and
  Chapter 2 (algebras of accessible monads)
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

namespace ObjectProperty

/-- A property containing a strong generator is a strong generator. -/
lemma IsStrongGenerator.of_le {P Q : ObjectProperty C} (hP : P.IsStrongGenerator) (h : P ≤ Q) :
    Q.IsStrongGenerator := by
  rw [isStrongGenerator_iff] at hP ⊢
  exact ⟨hP.1.of_le h, fun X Y i _ hi ↦ hP.2 i (fun G hG ↦ hi G (h G hG))⟩

end ObjectProperty

namespace Adjunction

variable {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U)

include adj

/-- If `L ⊣ U` and `U` is faithful, then the image under `L` of a separating property of `C` is
a separating property of `D`. -/
lemma isSeparating_map [U.Faithful] {P : ObjectProperty C} (hP : P.IsSeparating) :
    (P.map L).IsSeparating :=
  (hP.strictMap_leftAdjoint adj).of_le (P.strictMap_le_map L)

/-- If `L ⊣ U` and `U` is faithful and reflects isomorphisms, then the objects `L.obj G`, for `G`
in a strong generator `P` of `C`, form a strong generator of `D`. -/
lemma isStrongGenerator_strictMap [U.Faithful] [U.ReflectsIsomorphisms] {P : ObjectProperty C}
    (hP : P.IsStrongGenerator) : (P.strictMap L).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨hP.isSeparating.strictMap_leftAdjoint adj, fun X Y i _ hi ↦ ?_⟩
  have := adj.isRightAdjoint
  suffices IsIso (U.map i) from isIso_of_reflects_iso i U
  refine hP.isIso_of_mono (U.map i) (fun G hG a ↦ ?_)
  obtain ⟨b, hb⟩ := hi (L.obj G) (P.strictMap_obj L hG) ((adj.homEquiv _ _).symm a)
  refine ⟨adj.homEquiv _ _ b, ?_⟩
  dsimp at hb ⊢
  rw [← Adjunction.homEquiv_naturality_right, hb, Equiv.apply_symm_apply]

/-- If `L ⊣ U` and `U` is faithful and reflects isomorphisms, then the image under `L` of a
strong generator of `C` is a strong generator of `D`. -/
lemma isStrongGenerator_map [U.Faithful] [U.ReflectsIsomorphisms] {P : ObjectProperty C}
    (hP : P.IsStrongGenerator) : (P.map L).IsStrongGenerator :=
  (adj.isStrongGenerator_strictMap hP).of_le (P.strictMap_le_map L)

/-- If `L ⊣ U` and `U` is `κ`-accessible, then the image under `L` of a property of `C`
contained in the `κ`-presentable objects is contained in the `κ`-presentable objects of `D`. -/
lemma map_le_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [U.IsCardinalAccessible κ] {P : ObjectProperty C} (hP : P ≤ isCardinalPresentable C κ) :
    P.map L ≤ isCardinalPresentable D κ := by
  rintro Y ⟨X, hX, ⟨e⟩⟩
  have : IsCardinalPresentable X κ := hP X hX
  have := adj.isCardinalPresentable_leftAdjoint_obj κ X
  exact isCardinalPresentable_of_iso e κ

/-- If `L ⊣ U` and `U` is `κ`-accessible, then the objects `L.obj G`, for `G` in a property of
`C` contained in the `κ`-presentable objects, are `κ`-presentable. -/
lemma strictMap_le_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [U.IsCardinalAccessible κ] {P : ObjectProperty C} (hP : P ≤ isCardinalPresentable C κ) :
    P.strictMap L ≤ isCardinalPresentable D κ :=
  (P.strictMap_le_map L).trans (adj.map_le_isCardinalPresentable κ hP)

/-- If `L ⊣ U` and `U` is `κ`-accessible, then `L` preserves `κ`-presentable objects. -/
lemma preservesCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [U.IsCardinalAccessible κ] : L.PreservesCardinalPresentable κ where
  le_inverseImage_isCardinalPresentable X hX := by
    have : IsCardinalPresentable X κ := hX
    exact adj.isCardinalPresentable_leftAdjoint_obj κ X

/-- If `L ⊣ U` with `U` faithful, reflecting isomorphisms and `κ`-accessible, and `P` is a strong
generator of `C` consisting of `κ`-presentable objects, then the objects `L.obj G`, for `G`
satisfying `P`, form a strong generator of `D` consisting of `κ`-presentable objects. -/
lemma isStrongGenerator_strictMap_and_le_isCardinalPresentable (κ : Cardinal.{w})
    [Fact κ.IsRegular] [U.IsCardinalAccessible κ] [U.Faithful] [U.ReflectsIsomorphisms]
    {P : ObjectProperty C} (hP : P.IsStrongGenerator) (hPκ : P ≤ isCardinalPresentable C κ) :
    (P.strictMap L).IsStrongGenerator ∧ P.strictMap L ≤ isCardinalPresentable D κ :=
  ⟨adj.isStrongGenerator_strictMap hP, adj.strictMap_le_isCardinalPresentable κ hPκ⟩

/-- If `L ⊣ U` with `U` faithful, reflecting isomorphisms and `κ`-accessible, `C` is locally
`κ`-presentable and `D` is cocomplete, then `D` is locally `κ`-presentable. -/
lemma isCardinalLocallyPresentable_of_reflectsIsomorphisms (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ] [HasColimitsOfSize.{w, w} D] [U.IsCardinalAccessible κ]
    [U.Faithful] [U.ReflectsIsomorphisms] :
    IsCardinalLocallyPresentable D κ := by
  have : LocallySmall.{w} D := locallySmall_of_faithful U
  obtain ⟨P, _, hP, hPκ⟩ := (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator C κ).1
    inferInstance
  exact (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator D κ).2
    ⟨P.strictMap L, inferInstance,
      adj.isStrongGenerator_strictMap_and_le_isCardinalPresentable κ hP hPκ⟩

end Adjunction

/-- An equivalence of categories preserves `κ`-presentable objects. -/
lemma Functor.preservesCardinalPresentable_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : F.PreservesCardinalPresentable κ where
  le_inverseImage_isCardinalPresentable X hX := by
    have : IsCardinalPresentable X κ := hX
    exact isCardinalPresentable_of_isEquivalence X κ F

namespace Monad

/-- If `C` has `κ`-filtered colimits and the underlying functor of a monad `T` on `C` is
`κ`-accessible, then the forgetful functor of the category of `T`-algebras is `κ`-accessible. -/
lemma forget_isCardinalAccessible (T : Monad C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits.{w} C κ] [(T : C ⥤ C).IsCardinalAccessible κ] :
    T.forget.IsCardinalAccessible κ := ⟨fun J _ _ ↦ by
  have := (T : C ⥤ C).preservesColimitsOfShape_of_isCardinalAccessible κ J
  have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
  infer_instance⟩

/-- If `T` is a monad on a locally `κ`-presentable category `C` whose underlying functor is
`κ`-accessible, and the category of `T`-algebras is cocomplete, then the category of
`T`-algebras is locally `κ`-presentable. -/
lemma isCardinalLocallyPresentable_algebra (T : Monad C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ] [(T : C ⥤ C).IsCardinalAccessible κ]
    [HasColimitsOfSize.{w, w} T.Algebra] :
    IsCardinalLocallyPresentable T.Algebra κ := by
  have := T.forget_isCardinalAccessible κ
  exact T.adj.isCardinalLocallyPresentable_of_reflectsIsomorphisms κ

end Monad

namespace MonadicRightAdjoint

variable (U : D ⥤ C) [MonadicRightAdjoint U]

/-- A monadic functor is faithful. -/
lemma faithful : U.Faithful :=
  Functor.Faithful.of_iso (Monad.comparisonForget (monadicAdjunction U))

/-- A monadic functor reflects isomorphisms. -/
lemma reflectsIsomorphisms : U.ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_iso (Monad.comparisonForget (monadicAdjunction U))

/-- If `U : D ⥤ C` is monadic, `C` has `κ`-filtered colimits and the induced monad
`U ∘ (left adjoint)` is `κ`-accessible, then `U` is `κ`-accessible. -/
lemma isCardinalAccessible_of_monad (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits.{w} C κ]
    [((monadicAdjunction U).toMonad : C ⥤ C).IsCardinalAccessible κ] :
    U.IsCardinalAccessible κ := by
  have := (monadicAdjunction U).toMonad.forget_isCardinalAccessible κ
  exact Functor.isCardinalAccessible_of_natIso (Monad.comparisonForget (monadicAdjunction U)) κ

/-- If `U : D ⥤ C` is monadic and `κ`-accessible, `C` is locally `κ`-presentable and `D` is
cocomplete, then `D` is locally `κ`-presentable. -/
lemma isCardinalLocallyPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ] [HasColimitsOfSize.{w, w} D] [U.IsCardinalAccessible κ] :
    IsCardinalLocallyPresentable D κ := by
  have := faithful U
  have := reflectsIsomorphisms U
  exact (monadicAdjunction U).isCardinalLocallyPresentable_of_reflectsIsomorphisms κ

end MonadicRightAdjoint

end CategoryTheory
