module

public import InternalGroups.GrpObjSubgroupCorrespondenceCharacterization
public import InternalGroups.GrpKernelImage
public import InternalGroups.GrpStablyEpi
public import Foundations.CategoryTheory.Limits.MapRegularEpi
public import Foundations.CategoryTheory.Monoidal.ModObjPullbacks

/-!
# Newman's correspondence: the coset composite condition (S′)

Standing hypotheses, as in `InternalGroups/GrpKernelImage.lean`: `C` is cartesian monoidal with
finite limits and reflexive coequalizers, which the binary product preserves in each variable.

If every epi quotient of an internal group is a regular epimorphism of modules (the surjective
half of Newman's correspondence, `InternalGroups.subgroupCorrespondence_iff`), then the coset
composite condition (S′), `RegularEpiCosetCompHom C`, holds:

* let `f : X ⟶ Y` be a regular epimorphism of `Grp C` and `q : Y ⟶ Y / s` a coset quotient;
  regard `U f ≫ q` as a map of `X`-modules from the regular module `X` to `Y / s` restricted along
  `f` (`InternalGroups.compQuotMod`);
* `U f` is a regular epimorphism of `C` (`InternalGroups.isRegularEpi_hom_of_isRegularEpi`), and so
  is `q` (`InternalGroups.isRegularEpi_quot_p_hom`); their composite is an epimorphism of `C`,
  hence of `C^X`, since the forgetful functor `C^X ⥤ C` is faithful;
* so `U f ≫ q` is an epi quotient of `X`, which is regular in `C^X` by hypothesis; the forgetful
  functor preserves reflexive coequalizers and `C^X` has pullbacks, so it preserves regular
  epimorphisms, and `U f ≫ q` is a regular epimorphism of `C`.

The exactness of `Grp C` that follows is in
`InternalGroups/GrpObjSubgroupCorrespondenceStabilizer.lean`.

## Main results

* `InternalGroups.regularEpiCosetCompHom_of_everyEpiQuotientRegular`: (S′) from the regularity of
  epi quotients.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj MonObj

namespace InternalGroups


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section CompQuot

variable {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom f]

/-- A monoid morphism `f : X ⟶ Y` is a map of `X`-modules from the regular module `X` to the
regular module `Y` restricted along `f`. -/
noncomputable def selfModComap : selfMod X ⟶ (CategoryTheory.Mod.comap f).obj (selfMod Y) :=
  CategoryTheory.Mod.Hom.mk' f (by
    change μ ≫ f = (X ◁ f) ≫ (f ▷ Y) ≫ μ
    rw [← Category.assoc, ← tensorHom_def', IsMonHom.mul_hom])

/-- The underlying morphism of `selfModComap f` is `f`. -/
@[simp]
lemma selfModComap_hom : (selfModComap f).hom = f := rfl

end CompQuot

variable [HasFiniteLimits C] [HasReflexiveCoequalizers C]
  [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)] [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

/-- **The composite of a group morphism with a coset quotient, as an epi quotient.**  For a group
morphism `f : X ⟶ Y` whose underlying morphism is an epimorphism of `C` and a subgroup object `s`
of `Y`, the composite `U f ≫ (Y ⟶ Y / s)` is an epi quotient of the regular `X`-module. -/
noncomputable def compQuotMod {X Y : Grp C} (f : X ⟶ Y) [Epi f.hom.hom] (s : SubGrp Y.X) :
    QuotMod X.X :=
  haveI : IsMonHom f.hom.hom := f.hom.isMonHom_hom
  { V := (CategoryTheory.Mod.comap f.hom.hom).obj s.quot.V
    p := selfModComap f.hom.hom ≫ (CategoryTheory.Mod.comap f.hom.hom).map s.quot.p
    epi_p := by
      have : Epi s.quot.p.hom := RegularEpi.epi _ (isRegularEpi_quot_p_hom s).regularEpi.some
      constructor
      intro Z g h hgh
      ext
      have e := congrArg CategoryTheory.Mod.Hom.hom hgh
      simp only [CategoryTheory.Mod.comp_hom', selfModComap_hom, Mod.comap_map_hom] at e
      exact (cancel_epi (f.hom.hom ≫ s.quot.p.hom : X.X ⟶ _)).1 e }

omit [HasFiniteLimits C] [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)] in
/-- The quotient map of `compQuotMod f s` is `f` followed by the coset quotient map of `s`. -/
lemma compQuotMod_p_hom {X Y : Grp C} (f : X ⟶ Y) [Epi f.hom.hom] (s : SubGrp Y.X) :
    (compQuotMod f s).p.hom = f.hom.hom ≫ s.quot.p.hom := by
  rfl

/-- **(S′) from the regularity of epi quotients.**  If every epi quotient of an internal group is
a regular epimorphism of modules, then `U f ≫ q` is a regular epimorphism of `C` for every
regular epimorphism `f` of `Grp C` and every coset quotient `q`. -/
theorem regularEpiCosetCompHom_of_everyEpiQuotientRegular (hreg : EveryEpiQuotientRegular C) :
    RegularEpiCosetCompHom C := by
  intro X Y f hf s
  have : IsRegularEpi f.hom.hom := isRegularEpi_hom_of_isRegularEpi f hf
  have hq : IsRegularEpi (compQuotMod f s).p := hreg X.X (compQuotMod f s)
  have hpres := CategoryTheory.Mod_.preservesReflexiveCoequalizers_forget (A := X.X)
    (fun _ => inferInstance)
  have h := isRegularEpi_map_of_preservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) X.X)
    (compQuotMod f s).p
  rwa [Mod.forget_map, compQuotMod_p_hom] at h


end InternalGroups
