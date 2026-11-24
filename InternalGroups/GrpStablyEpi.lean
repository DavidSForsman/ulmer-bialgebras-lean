module

public import InternalGroups.GrpExactFromCoset
public import Foundations.CategoryTheory.Factorization.LiftedFactorizationSystem

/-!
# Underlying epimorphisms of internal groups

Under the effective-coset hypotheses, a monomorphism of internal groups whose underlying
morphism is epimorphic is an isomorphism (`InternalGroups.isIso_of_mono_of_epi_hom`).  A morphism
with epimorphic underlying map is an extremal epimorphism
(`InternalGroups.isExtremalEpi_of_epi_hom`), and the underlying morphism of a regular
epimorphism of `Grp C` is a regular epimorphism of `C`
(`InternalGroups.isRegularEpi_hom_of_isRegularEpi`).

## Main results

* `InternalGroups.epi_of_epi_hom`: a morphism of `Grp C` whose underlying morphism is an
  epimorphism of `C` is an epimorphism.
* `InternalGroups.isIso_of_mono_of_epi_hom`: given effective coset relations, a monomorphism of
  `Grp C` whose underlying morphism is an epimorphism of `C` is an isomorphism.
* `InternalGroups.isExtremalEpi_of_epi_hom`: given effective coset relations, a morphism of
  `Grp C` whose underlying morphism is an epimorphism of `C` is an extremal epimorphism.
* `InternalGroups.isRegularEpi_hom_of_isRegularEpi`: the underlying morphism of a regular
  epimorphism of `Grp C` is a regular epimorphism of `C`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory CategoryTheory.LiftedOFS

open CategoryTheory.LiftedOFS

variable (D : Type u) [Category.{v} D]

variable {D}


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## `Grp C` is balanced over `C` -/

/-- A morphism of `Grp C` whose underlying morphism of `C` is an epimorphism is an
epimorphism. -/
theorem epi_of_epi_hom {A B : Grp C} (f : A ⟶ B) (he : Epi f.hom.hom) : Epi f :=
  ⟨fun _a _b hab =>
    Grp.hom_ext _ _ ((cancel_epi f.hom.hom).1 (congr(($hab).hom.hom)))⟩

variable [HasFiniteLimits C] [HasReflexiveCoequalizers C]
  [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

/-- **A monomorphism of `Grp C` whose underlying morphism of `C` is an epimorphism is an
isomorphism**, granting the injectivity of Newman's correspondence.  The subgroup object `m`
kills its own coset quotient `p : B ⟶ B / A`; as `m` is epimorphic in `C` this forces `p` to be
constant at the base point, so that `𝟙 B` is killed as well and therefore factors through `m`. -/
theorem isIso_of_mono_of_epi_hom (hinj : CosetInjective C) {A B : Grp C} (m : A ⟶ B) [Mono m]
    (he : Epi m.hom.hom) : IsIso m := by
  have : Mono m.hom.hom := mono_hom_of_mono m
  have := hasReflexiveCoequalizers_mod (C := C) B.X
  let s : SubGrp B.X := { N := A.X, i := m.hom.hom }
  -- the coset quotient of `m` kills `m`, hence, `m` being epi, the identity
  have hm : Kills s.quot s.i := kills_quot_i s
  have hid : Kills s.quot (𝟙 B.X) := by
    have hcomp : m.hom.hom ≫ (s.quot).p.hom = m.hom.hom ≫ pt s.quot B.X := by
      rw [show m.hom.hom ≫ (s.quot).p.hom = _ from hm, comp_pt]
    have hcancel := (cancel_epi m.hom.hom).1 hcomp
    change (𝟙 B.X) ≫ s.quot.p.hom = pt s.quot B.X
    exact (Category.id_comp _).trans hcancel
  -- so the identity factors through `m`
  obtain ⟨k, hk⟩ := factors_of_kills_quot s (hinj B.X s) hid
  have : IsIso m.hom.hom := by
    refine ⟨k, ?_, hk⟩
    rw [← cancel_mono m.hom.hom, Category.assoc, show k ≫ m.hom.hom = 𝟙 B.X from hk,
      Category.comp_id, Category.id_comp]
  exact isIso_of_isIso_hom m inferInstance

/-- **A morphism of `Grp C` whose underlying morphism of `C` is an epimorphism is an extremal
epimorphism.**  This is the form in which the previous result is used: the missing step in the
reduction of the development repository's
`Foundations/CategoryTheory/Protomodular/ExtremalBaseChange.lean` is exactly the
passage from "epimorphic" to "extremal epimorphic". -/
theorem isExtremalEpi_of_epi_hom (hinj : CosetInjective C) {A B : Grp C} (f : A ⟶ B)
    (he : Epi f.hom.hom) : IsExtremalEpi f := by
  refine IsExtremalEpi.mk (epi_of_epi_hom f he) (fun {Z} e m hm hfac => ?_)
  have := hm
  have : Epi (e.hom.hom ≫ m.hom.hom) := by
    have h : e.hom.hom ≫ m.hom.hom = f.hom.hom := congr(($hfac).hom.hom)
    rw [h]; exact he
  have : Epi m.hom.hom := epi_of_epi e.hom.hom m.hom.hom
  exact isIso_of_mono_of_epi_hom hinj m inferInstance

/-! ## The underlying form of the hypothesis -/

variable [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

/-- The underlying morphism of a regular epimorphism of `Grp C` is a regular epimorphism of `C`:
a regular epimorphism is the coequalizer of its kernel pair, which is a reflexive pair, and the
forgetful functor preserves both. -/
theorem isRegularEpi_hom_of_isRegularEpi {A B : Grp C} (f : A ⟶ B) (hf : IsRegularEpi f) :
    IsRegularEpi f.hom.hom := by
  have := hf
  have hk : IsKernelPair f (pullback.fst f f) (pullback.snd f f) := IsKernelPair.of_hasPullback f
  have hcolim : IsColimit (Cofork.ofπ f hk.w) := hk.toCoequalizer'
  have : IsReflexivePair (pullback.fst f f) (pullback.snd f f) := hk.isReflexivePair
  have h2 := (isColimitMapCoconeCoforkEquiv (Grp.forget C) hk.w)
    (isColimitOfPreserves (Grp.forget C) hcolim)
  exact ⟨⟨{ W := ((Grp.forget C).obj (pullback f f))
            left := (Grp.forget C).map (pullback.fst f f)
            right := (Grp.forget C).map (pullback.snd f f)
            w := congr(($(hk.w)).hom.hom)
            isColimit := h2 }⟩⟩


/-! ## Sufficiency -/

/-! ## Necessity -/

/-! ## The equivalence -/


end InternalGroups
