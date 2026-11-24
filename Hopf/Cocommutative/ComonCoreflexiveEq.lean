module

public import Foundations.CategoryTheory.Monoidal.CommComonEqualizers
public import Foundations.CategoryTheory.Monoidal.ComonTransport
public import Hopf.Cocommutative.CoreflexiveTensor

/-!
# Coreflexive equalizers of (cocommutative) comonoid objects are created in the base

Let `C` be a monoidal category in which tensoring on either side preserves the equalizers of
coreflexive pairs.  Dually to the development repository's
`Foundations/CategoryTheory/Monoidal/MonReflexiveCoequalizers.lean`,
the
equalizer of a coreflexive pair of morphisms of comonoid objects, computed in `C`, carries a
comonoid structure making the equalizer inclusion a morphism of comonoid objects; that is, the
forgetful functors `Comon C ⥤ C` and `CommComon C ⥤ C` **strictly create coreflexive
equalizers**.

This is the instance, for the prop of (cocommutative) comonoids and for the walking coreflexive
pair, of the general principle that a category of models of a theory in a monoidal category has
the `I`-limits strictly created from the base whenever `I` is cosifted and the tensor product
preserves `I`-limits in each variable.  The walking coreflexive pair is cosifted — its opposite,
the walking reflexive pair, is sifted — and over a field every vector space is flat, so the
tensor product of `Vect_k` is exact; this is why cocommutative coalgebras have their coreflexive
equalizers, and hence (with finite products) all their finite limits, computed in `Vect_k`
(`Hopf/Cocommutative/CocommFiniteLimits.lean`).  The dual statement for colimits — the
forgetful functor creates all colimits that exist in the base, in particular all sifted ones — is
`Foundations/CategoryTheory/Monoidal/ComonColimits.lean`.

Together with the fact that the tensor product of cocommutative comonoids is their categorical
product, and with `UlmerBialgebras.hasFiniteLimits_of_coreflexive`, this computes *all finite
limits* of cocommutative comonoids: general equalizers, and hence pullbacks, are obtained from
coreflexive ones by the standard trick `⟨𝟙, f⟩, ⟨𝟙, g⟩ : A ⟶ A × B`.

## Main results

* `UlmerBialgebras.ComonCoreflexiveEq.comonObj` — the comonoid structure on the equalizer;
* `UlmerBialgebras.ComonCoreflexiveEq.isComonHom_e` — the inclusion is a morphism of comonoid
  objects;
* `UlmerBialgebras.ComonCoreflexiveEq.isCommComonObj` — an equalizer of cocommutative comonoid
  objects is cocommutative;
* `UlmerBialgebras.ComonCoreflexiveEq.liftComon`,
  `UlmerBialgebras.ComonCoreflexiveEq.isComonHom_liftComon` — the lift of a comonoid morphism
  through the equalizer is a comonoid morphism;
* `UlmerBialgebras.ComonCoreflexiveEq.isLimitForkCommComon` — the equalizer computed in `C` is the
  equalizer of cocommutative comonoid objects;
* `UlmerBialgebras.ComonCoreflexiveEq.hasCoreflexiveEqualizers_commComon`,
  `UlmerBialgebras.ComonCoreflexiveEq.preservesCoreflexiveEq_commComonForget` — `CommComon C` has
  coreflexive equalizers, and the forgetful functor to `C` preserves them.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.17 (dual form)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits ComonObj

namespace UlmerBialgebras

namespace ComonCoreflexiveEq

section Construction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [∀ Z : C, PreservesCoreflexiveEq (tensorLeft Z)]
  [∀ Z : C, PreservesCoreflexiveEq (tensorRight Z)]

variable {M N E : C} [ComonObj M] [ComonObj N] {u v : M ⟶ N} [IsComonHom u] [IsComonHom v]
  (hr : IsCoreflexivePair u v) {e : E ⟶ M} {w : e ≫ u = e ≫ v}
  (he : IsLimit (Fork.ofι e w))

/-- The componentwise preservation hypotheses in the interface for the chosen equalizer. -/
theorem tensorPreserves : TensorPreservesCoreflexiveEqualizers C where
  preserves_left Z :=
    ⟨fun {_ _} f g h => PreservesCoreflexiveEq.preserves (F := tensorLeft Z) f g h⟩
  preserves_right Z :=
    ⟨fun {_ _} f g h => PreservesCoreflexiveEq.preserves (F := tensorRight Z) f g h⟩

include hr he

/-- Transport the comonoid on the chosen equalizer to the carrier of any limiting fork. -/
@[instance_reducible]
noncomputable def comonObj : ComonObj E :=
  letI : IsCoreflexivePair u v := hr
  letI : HasEqualizer u v := HasLimit.mk ⟨_, he⟩
  letI := tensorPreserves (C := C)
  letI := coreflexiveComonObj (f := u) (g := v)
  ComonObj.ofIso (limit.isoLimitCone ⟨_, he⟩)

/-- The inclusion of a coreflexive equalizer is a morphism of comonoid objects. -/
lemma isComonHom_e : letI := comonObj hr he; IsComonHom e := by
  let _ : IsCoreflexivePair u v := hr
  let _ : HasEqualizer u v := HasLimit.mk ⟨_, he⟩
  let _ := tensorPreserves (C := C)
  let _ := coreflexiveComonObj (f := u) (g := v)
  let t : LimitCone (parallelPair u v) := ⟨_, he⟩
  let i : equalizer u v ≅ E := limit.isoLimitCone t
  let _ := ComonObj.ofIso i
  have := ComonObj.isComonHom_ofIso_inv i
  have h : i.inv ≫ equalizer.ι u v = e := limit.isoLimitCone_inv_π t WalkingParallelPair.zero
  have hm : IsComonHom (i.inv ≫ equalizer.ι u v) := inferInstanceAs
    (IsComonHom (i.inv ≫ coreflexiveEqι (f := u) (g := v)))
  rwa [h] at hm

/-- A coreflexive equalizer of cocommutative comonoid objects is cocommutative. -/
lemma isCommComonObj [BraidedCategory C] [IsCommComonObj M] :
    letI := comonObj hr he; IsCommComonObj E :=
  letI : IsCoreflexivePair u v := hr
  letI : HasEqualizer u v := HasLimit.mk ⟨_, he⟩
  letI := tensorPreserves (C := C)
  letI := coreflexiveComonObj (f := u) (g := v)
  letI := isCommComonObj_coreflexiveEq (f := u) (g := v)
  ComonObj.isCommComonObj_ofIso (limit.isoLimitCone ⟨_, he⟩)

section Lift

variable {Z : C} [ComonObj Z] (h : Z ⟶ M) [IsComonHom h] (hh : h ≫ u = h ≫ v)

/-- The morphism induced into the equalizer by a morphism of comonoid objects equalizing the
pair. -/
noncomputable def liftComon : Z ⟶ E := Fork.IsLimit.lift he h hh

omit [∀ Z : C, PreservesCoreflexiveEq (tensorLeft Z)]
  [∀ Z : C, PreservesCoreflexiveEq (tensorRight Z)] [ComonObj M] [ComonObj N]
  [IsComonHom u] [IsComonHom v] [ComonObj Z] [IsComonHom h] [MonoidalCategory C] hr in
/-- `liftComon he h hh ≫ e = h`. -/
@[reassoc (attr := simp)]
lemma liftComon_comp : liftComon he h hh ≫ e = h :=
  Fork.IsLimit.lift_ι' he h hh

/-- The induced morphism is again a morphism of comonoid objects. -/
lemma isComonHom_liftComon : letI := comonObj hr he; IsComonHom (liftComon he h hh) :=
  letI := comonObj hr he
  haveI := isComonHom_e hr he
  haveI := CoreflexiveTensor.mono_tensorHom hr he
  isComonHom_of_factorization _ e h (liftComon_comp he h hh)

end Lift

end Construction

section CommComon

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [∀ Z : C, PreservesCoreflexiveEq (tensorLeft Z)]
  [∀ Z : C, PreservesCoreflexiveEq (tensorRight Z)]

-- `A.toComon.X` is `A.X` by definition; instance arguments are compared at instance
-- transparency, so the coercion to `Comon C` has to unfold there.
attribute [local instance_reducible] CommComon.toComon

/-- The underlying object of the comonoid object underlying a cocommutative comonoid object is
cocommutative. -/
instance isCommComonObj_toComon (A : CommComon C) : IsCommComonObj A.toComon.X := A.comm

variable {M N : CommComon C} {u v : M ⟶ N} (hr : IsCoreflexivePair u.hom.hom v.hom.hom)
  {E : C} {e : E ⟶ M.X} {w : e ≫ u.hom.hom = e ≫ v.hom.hom} (he : IsLimit (Fork.ofι e w))

include hr he

/-- The equalizer of a coreflexive pair of cocommutative comonoid objects. -/
@[instance_reducible]
noncomputable def eqCommComon : CommComon C :=
  letI := comonObj hr he
  letI := isCommComonObj hr he
  .mk E

/-- The inclusion of the equalizer, as a morphism of cocommutative comonoid objects. -/
noncomputable def eqCommComonι : eqCommComon hr he ⟶ M :=
  letI := comonObj hr he
  letI := isCommComonObj hr he
  letI := isComonHom_e hr he
  InducedCategory.homMk (F := CommComon.toComon) (Comon.Hom.mk e)
/-- The underlying morphism of `eqCommComonι hr he` is `e`. -/
@[simp]
lemma eqCommComonι_hom : (eqCommComonι hr he).hom.hom = e := rfl


/-- The equalizer inclusion of cocommutative comonoids equalizes `u` and `v`. -/
lemma eqCommComon_condition : eqCommComonι hr he ≫ u = eqCommComonι hr he ≫ v :=
  CommComon.hom_ext _ _ (by simpa using w)

/-- **Coreflexive equalizers of cocommutative comonoid objects are created in the base
category.** -/
noncomputable def isLimitForkCommComon :
    IsLimit (Fork.ofι (eqCommComonι hr he) (eqCommComon_condition hr he)) :=
  have : Mono ((eqCommComonι hr he).hom.hom ⊗ₘ (eqCommComonι hr he).hom.hom) :=
    CoreflexiveTensor.mono_tensorHom hr he
  isLimitForkOfUnderlying (eqCommComonι hr he) _ he

end CommComon

section Instances

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [∀ Z : C, PreservesCoreflexiveEq (tensorLeft Z)]
  [∀ Z : C, PreservesCoreflexiveEq (tensorRight Z)]
  [HasCoreflexiveEqualizers C]

variable [BraidedCategory C]

/-- The category of cocommutative comonoid objects has coreflexive equalizers, computed in the
base category. -/
instance hasCoreflexiveEqualizers_commComon : HasCoreflexiveEqualizers (CommComon C) :=
  letI := tensorPreserves (C := C)
  commComonHasCoreflexiveEqualizers

/-- The forgetful functor `CommComon C ⥤ C` preserves coreflexive equalizers. -/
instance preservesCoreflexiveEq_commComonForget :
    PreservesCoreflexiveEq (CommComon.forget₂Comon C ⋙ Comon.forget C) where
  preserves {M N} u v h := by
    let _ := tensorPreserves (C := C)
    exact preservesLimit_of_preserves_limit_cone (coreflexiveEqForkIsLimit u v)
      ((isLimitMapConeForkEquiv (CommComon.forget₂Comon C ⋙ Comon.forget C) _).symm
        (equalizerIsEqualizer u.hom.hom v.hom.hom))

end Instances

end ComonCoreflexiveEq

end UlmerBialgebras
