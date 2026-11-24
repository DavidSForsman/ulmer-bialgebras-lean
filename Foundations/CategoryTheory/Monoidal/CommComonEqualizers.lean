module

public import Foundations.CategoryTheory.Monoidal.CocommEqualizers

/-!
# Coreflexive equalizers in `CommComon A`

For a braided monoidal category `A` with coreflexive equalizers that tensoring preserves, the
coreflexive equalizer of cocommutative comonoids built in
`Foundations/CategoryTheory/Monoidal/CocommEqualizers.lean` is an equalizer in `CommComon A`.

## Main results

* `UlmerBialgebras.coreflexiveEqForkIsLimit`: the equalizer fork is a limit fork in
  `CommComon A`;
* `UlmerBialgebras.commComonHasCoreflexiveEqualizers`: `CommComon A` has coreflexive
  equalizers when `A` does and tensoring preserves them.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section
universe v u
open CategoryTheory MonoidalCategory Limits
open scoped ComonObj

namespace UlmerBialgebras

section CommComonEqualizer

variable {A : Type u} [Category.{v} A] [MonoidalCategory.{v} A] [BraidedCategory A]
variable [HasCoreflexiveEqualizers A] [TensorPreservesCoreflexiveEqualizers A]

/-- The underlying pair of a coreflexive pair of cocommutative comonoids is coreflexive. -/
instance isCoreflexivePair_hom_hom {X Y : CommComon A} {f g : X ⟶ Y}
    [IsCoreflexivePair f g] : IsCoreflexivePair f.hom.hom g.hom.hom := by
  obtain ⟨r, hf, hg⟩ := IsCoreflexivePair.common_retraction f g
  let U := CategoryTheory.CommComon.forget₂Comon A ⋙ Comon.forget A
  apply IsCoreflexivePair.mk' (f := U.map f) (g := U.map g) (U.map r)
  · rw [← U.map_comp, hf, U.map_id]
  · rw [← U.map_comp, hg, U.map_id]

/-- The underlying equalizer object, as a cocommutative comonoid. -/
noncomputable def coreflexiveEqCommComon {X Y : CommComon A} {f g : X ⟶ Y}
    [IsCoreflexivePair f g] : CommComon A :=
  let E := equalizer f.hom.hom g.hom.hom
  letI : IsCommComonObj X.toComon.X := X.comm
  CommComon.mk E

/-- The equalizer map, as a morphism of cocommutative comonoids. -/
noncomputable def coreflexiveEqCommComonι {X Y : CommComon A} {f g : X ⟶ Y}
    [IsCoreflexivePair f g] : coreflexiveEqCommComon (f := f) (g := g) ⟶ X :=
  let e : (coreflexiveEqCommComon (f := f) (g := g)).X ⟶ X.X :=
    coreflexiveEqι (f := f.hom.hom) (g := g.hom.hom)
  let h := isComonHom_coreflexiveEqι (f := f.hom.hom) (g := g.hom.hom)
  InducedCategory.homMk (F := CategoryTheory.CommComon.toComon)
    (Comon.Hom.mk' e h.hom_counit h.hom_comul)

/-- The equalizer fork in cocommutative comonoids. -/
noncomputable def coreflexiveEqFork {X Y : CommComon A} (f g : X ⟶ Y)
    [IsCoreflexivePair f g] : Fork f g :=
  Fork.ofι (coreflexiveEqCommComonι (f := f) (g := g)) (by
    ext
    exact equalizer.condition f.hom.hom g.hom.hom)

/-- A factor of a comonoid morphism through a comonoid morphism is a comonoid
morphism when the tensor square of the latter is monic. -/
theorem isComonHom_of_factorization {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P Q X : C} [ComonObj P] [ComonObj Q] [ComonObj X]
    (l : P ⟶ Q) (j : Q ⟶ X) (t : P ⟶ X) [IsComonHom j] [IsComonHom t]
    [Mono (j ⊗ₘ j)] (hl : l ≫ j = t) : IsComonHom l where
  hom_counit := by rw [← IsComonHom.hom_counit j, ← Category.assoc, hl, IsComonHom.hom_counit]
  hom_comul := by
    apply (cancel_mono (j ⊗ₘ j)).mp
    rw [Category.assoc, ← IsComonHom.hom_comul j, ← Category.assoc, hl,
      Category.assoc, tensorHom_comp_tensorHom, hl, IsComonHom.hom_comul]

/-- If the underlying fork is limiting and the tensor square of its inclusion is
monic, then the fork is limiting in commutative comonoids. -/
noncomputable def isLimitForkOfUnderlying {X Y Q : CommComon A} {f g : X ⟶ Y}
    (j : Q ⟶ X) (w : j ≫ f = j ≫ g)
    (h : IsLimit (Fork.ofι j.hom.hom (congrArg (fun t => t.hom.hom) w) :
      Fork f.hom.hom g.hom.hom)) [Mono (j.hom.hom ⊗ₘ j.hom.hom)] :
    IsLimit (Fork.ofι j w) := by
  refine Fork.IsLimit.mk' _ fun s => ?_
  obtain ⟨l, hl⟩ := Fork.IsLimit.lift' h s.ι.hom.hom (congr(($(s.condition)).hom.hom))
  change l ≫ j.hom.hom = s.ι.hom.hom at hl
  have hm := isComonHom_of_factorization (Q := Q.toComon.X) l j.hom.hom s.ι.hom.hom hl
  let m : s.pt ⟶ Q := InducedCategory.homMk (Comon.Hom.mk' l hm.hom_counit hm.hom_comul)
  refine ⟨m, CategoryTheory.CommComon.hom_ext _ _ hl, fun {n} hn => ?_⟩
  apply CategoryTheory.CommComon.hom_ext
  apply Fork.IsLimit.hom_ext h
  exact (congr(($(hn)).hom.hom)).trans hl.symm

/-- The equalizer fork in cocommutative comonoids is a limit fork. -/
noncomputable def coreflexiveEqForkIsLimit {X Y : CommComon A} (f g : X ⟶ Y)
    [IsCoreflexivePair f g] : IsLimit (coreflexiveEqFork f g) := by
  let j := coreflexiveEqCommComonι (f := f) (g := g)
  haveI : Mono (j.hom.hom ⊗ₘ j.hom.hom) :=
    mono_coreflexiveEqι_tensor (f := f.hom.hom) (g := g.hom.hom)
  exact isLimitForkOfUnderlying j _ (equalizerIsEqualizer f.hom.hom g.hom.hom)

/-- The coreflexive equalizer of a coreflexive pair of cocommutative comonoids. -/
theorem commComonHasEqualizer {X Y : CommComon A} (f g : X ⟶ Y)
    [IsCoreflexivePair f g] : HasEqualizer f g :=
  HasLimit.mk { cone := coreflexiveEqFork f g, isLimit := coreflexiveEqForkIsLimit f g }

/-- **`CommComon A` has coreflexive equalizers** when `A` has them and tensoring in either
variable preserves them. -/
noncomputable instance commComonHasCoreflexiveEqualizers :
    HasCoreflexiveEqualizers (CommComon A) where
  has_eq A B f g _ := commComonHasEqualizer (X := A) (Y := B) f g

end CommComonEqualizer

end UlmerBialgebras
