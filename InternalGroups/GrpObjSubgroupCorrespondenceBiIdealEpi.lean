module

public import InternalGroups.GrpObjSubgroupCorrespondenceBiIdeal

/-!
# Epimorphisms of modules in cocommutative comonoids

Let `A` be an abelian symmetric monoidal category whose tensor product preserves finite colimits
in each variable, and let `h` be an internal monoid of `C = CommComon A`.  The epimorphisms of
the category `C^h` of `h`-modules in `C` are exactly the morphisms whose underlying morphism of
`A` is an epimorphism (`InternalGroups.epi_iff_epi_modHomA`).

The forgetful functor `C^h ⥤ A` is faithful, so it reflects epimorphisms.  It preserves them
because it preserves pushouts:

* the forgetful functor `C ⥤ A` preserves the colimits that `A` has (comonoid colimits are
  computed in `A`), and it reflects isomorphisms, so it also reflects these colimits;
* hence tensoring in `C` preserves pushouts, because tensoring in `A` does
  (`UlmerBialgebras.CommComon.tensorLeftForgetIso`);
* hence the forgetful functor `C^h ⥤ C` creates pushouts
  (`CategoryTheory.Mod_.createsColimitForget`);
* a functor preserving the pushout of `f` along itself preserves the epimorphism `f`
  (`CategoryTheory.preserves_epi_of_preservesColimit`).

As a consequence, the surjectivity condition of Newman's bi-ideal correspondence
(`InternalGroups.biIdealMap_surjective_iff_epi`) is that every categorical epi quotient of `h` in
`C^h` is regular (`InternalGroups.biIdealMap_surjective_iff_isRegularEpi`).  So the bi-ideal
correspondence for `h` is bijective iff every subgroup object of `h` is a stabilizer and every epi
quotient of `h` in `C^h` is regular (`InternalGroups.biIdealMap_bijective_iff_isRegularEpi`).  It
is bijective for every `h` exactly when Newman's correspondence with quotient modules holds in
`C` (`InternalGroups.forall_biIdealMap_bijective_iff`).

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj MonObj ComonObj

namespace InternalGroups


section EpiTransfer

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [∀ X : A, PreservesFiniteColimits (tensorLeft X)]

omit [Abelian A] [∀ X : A, PreservesFiniteColimits (tensorLeft X)] in
/-- The forgetful functor from cocommutative comonoids preserves the colimits that `A` has:
they are computed on underlying objects. -/
lemma preservesColimitsOfShape_forgetV (J : Type) [SmallCategory J] [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (UlmerBialgebras.CommComon.forgetV A) := by
  have : PreservesColimitsOfShape J (CategoryTheory.CommComon.forget₂Comon A) :=
    ⟨fun {_} => inferInstance⟩
  exact comp_preservesColimitsOfShape _ _

attribute [local instance] preservesColimitsOfShape_forgetV

/-- **Tensoring with a cocommutative comonoid preserves pushouts**, as soon as tensoring in `A`
preserves finite colimits. -/
lemma preservesColimitsOfShape_walkingSpan_tensorLeft (Z : CommComon A) :
    PreservesColimitsOfShape WalkingSpan (tensorLeft Z : CommComon A ⥤ CommComon A) := by
  have : PreservesColimitsOfShape WalkingSpan
      (UlmerBialgebras.CommComon.forgetV A ⋙ tensorLeft Z.X) := inferInstance
  have : PreservesColimitsOfShape WalkingSpan
      (tensorLeft Z ⋙ UlmerBialgebras.CommComon.forgetV A) :=
    preservesColimitsOfShape_of_natIso (UlmerBialgebras.CommComon.tensorLeftForgetIso Z).symm
  have : ReflectsColimitsOfShape WalkingSpan (UlmerBialgebras.CommComon.forgetV A) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves (tensorLeft Z)
    (UlmerBialgebras.CommComon.forgetV A)

attribute [local instance] preservesColimitsOfShape_walkingSpan_tensorLeft

variable {h : CommComon A} [MonObj h]

/-- **The forgetful functor from `h`-modules in `CommComon A` to `A` preserves pushouts.** -/
lemma preservesColimitsOfShape_walkingSpan_forget :
    PreservesColimitsOfShape WalkingSpan
      (Mod.forget h ⋙ UlmerBialgebras.CommComon.forgetV A) := by
  have : PreservesColimitsOfShape WalkingSpan (Mod.forget (D := CommComon A) h) :=
    ⟨fun {K} =>
      have := Mod_.createsColimitForget K (fun _ => inferInstance)
      preservesColimit_of_createsColimit_and_hasColimit K _⟩
  infer_instance

/-- **The epimorphisms of `h`-modules in `CommComon A` are the morphisms whose underlying
morphism of `A` is an epimorphism.** -/
theorem epi_iff_epi_modHomA {N M : Mod (CommComon A) h} (f : N ⟶ M) :
    Epi f ↔ Epi (modHomA f) := by
  refine ⟨fun _ => ?_, fun _ => epi_of_epi_modHomA f⟩
  have := preservesColimitsOfShape_walkingSpan_forget (h := h)
  exact preserves_epi_of_preservesColimit (Mod.forget h ⋙ UlmerBialgebras.CommComon.forgetV A) f

end EpiTransfer

/-! ## Newman's bi-ideal correspondence with categorical epimorphisms -/

section Correspondence

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [∀ X : A, PreservesFiniteLimits (tensorLeft X)] [∀ X : A, PreservesFiniteColimits (tensorLeft X)]

attribute [local instance] preservesFiniteLimits_tensorRight_of_left
  preservesFiniteColimits_tensorRight_of_left
  tensorPreservesCoreflexiveEqualizers_of_preservesFiniteLimits
  preservesReflexiveCoeq_tensorLeft_of_preservesFiniteColimits

variable {h : CommComon A} [GrpObj h]

/-- **Surjectivity of Newman's bi-ideal correspondence is the property that every epi quotient
of `h` in `C^h` is a regular epimorphism.**  Here epi means epimorphism of `h`-modules in
`CommComon A`; by `InternalGroups.epi_iff_epi_modHomA` these are the quotients whose quotient map
is an epimorphism of `A`. -/
theorem biIdealMap_surjective_iff_isRegularEpi :
    Function.Surjective (biIdealMap h) ↔ ∀ q : QuotMod h, IsRegularEpi q.p :=
  biIdealMap_surjective_iff_epi.trans
    ⟨fun H q => H q ((epi_iff_epi_modHomA q.p).1 q.epi_p), fun H q _ => H q⟩

/-- **Newman's bi-ideal correspondence for `h` is bijective iff every subgroup object of `h` is a
stabilizer and every epi quotient of `h` in `C^h` is a regular epimorphism.** -/
theorem biIdealMap_bijective_iff_isRegularEpi :
    Function.Bijective (biIdealMap h) ↔
      (∀ s : SubGrp h, GrpIsStabilizer s.inclGrp) ∧ ∀ q : QuotMod h, IsRegularEpi q.p :=
  and_congr biIdealMap_injective_iff_grpIsStabilizer biIdealMap_surjective_iff_isRegularEpi

/-- **Newman's bi-ideal correspondence is bijective for every cocommutative Hopf monoid of `A`
iff Newman's correspondence with quotient modules holds in `CommComon A`**, that is
(`InternalGroups.subgroupCorrespondence_iff`), iff the coset relations of `CommComon A` are
effective and every epi quotient of an internal group in its module category is regular. -/
theorem forall_biIdealMap_bijective_iff :
    (∀ (h : CommComon A) [GrpObj h], Function.Bijective (biIdealMap h)) ↔
      SubgroupCorrespondence (CommComon A) := by
  rw [subgroupCorrespondence_iff]
  constructor
  · intro H
    exact ⟨fun G _ _ s => biIdealMap_injective_iff.1 (H G).1 s,
      fun G _ _ q => biIdealMap_surjective_iff_isRegularEpi.1 (H G).2 q⟩
  · rintro ⟨hinj, hreg⟩ G _
    exact ⟨biIdealMap_injective_iff.2 fun s => hinj G s,
      biIdealMap_surjective_iff_isRegularEpi.2 fun q => hreg G q⟩

end Correspondence


end InternalGroups
