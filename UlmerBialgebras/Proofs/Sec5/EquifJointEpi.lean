module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Monadicity.BigMonadicity
public import UlmerBialgebras.Proofs.Sec5.ChainCofinality

/-!
# Free equifier algebras from joint epicness (Theorem 5.5 (2))

The development's reflection into an equifier
(`UlmerBialgebras/Monadicity/FreeEquifTransfinite.lean`)
assumes that `F` preserves the colimits of the reflection chain. The only place this is used is
to show that the colimit of the chain lies in the equifier, and for that it is enough that
`F ⋙ L` sends the colimiting cocone of the chain to a jointly epimorphic family. This file
redoes the last step of the construction under that weaker hypothesis, and transfers joint
epicness along a relative left adjoint.

## Main results

* `UlmerBialgebras.RelLeftAdjoint.preservesJointEpiOfShape`: a relative left adjoint `L` of `G`
  (relative to `F`) preserves the joint epicness of colimiting cocones of shape `J` that `F`
  preserves.
* `UlmerBialgebras.Equif.forget_isRightAdjoint_of_jointEpi`: for `L ⊣ G`, if `F ⋙ L` preserves joint
  epicness of colimiting cocones of a well-ordered shape `J`, the forgetful functor of the
  equifier of `η, θ : F ⟶ G` has a left adjoint.
* `UlmerBialgebras.Equif.monadicRightAdjointForgetOfJointEpi`: Theorem 5.5 (2), if `G` has an
  `F`-relative left adjoint and `F` preserves joint epicness of colimiting cocones of
  `κ`-chains, the forgetful functor `U : Eq(α, β) ⥤ C` is monadic.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5 (2)
* [F. Ulmer, *Properties of dense and relative adjoint
  functors*][ulmerPropertiesDenseRelative1968]
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits SmallObject

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A relative left adjoint `L` of `G` (relative to `F`) preserves the joint epicness of the
colimiting cocones that `F` preserves. -/
lemma RelLeftAdjoint.preservesJointEpiOfShape {F G : C ⥤ D} {L : C ⥤ C}
    (ra : RelLeftAdjoint F G L) (J : Type w) [Category.{w} J]
    (h : Paper.PreservesJointEpiOfShape J F) : Paper.PreservesJointEpiOfShape J L := by
  intro K c hc y p q hpq
  apply (ra.homEquiv c.pt y).injective
  refine h K c hc _ _ fun j => ?_
  have hj := congrArg (ra.homEquiv (K.obj j) y) (hpq j)
  rwa [ra.homEquiv_naturality_left, ra.homEquiv_naturality_left] at hj

namespace Equif

variable {F G : C ⥤ D} {L : D ⥤ C}

section Chain

variable (adj : L ⊣ G) (η θ : F ⟶ G) [HasCoequalizers C] (X : C)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]
  [HasIterationOfShape J C]

/-- The colimit of the reflection chain lies in the equifier as soon as `F ⋙ L` preserves
joint epicness of colimiting cocones of shape `J`. -/
lemma equifProp_reflPtOfShape_of_jointEpi (hJ : Paper.PreservesJointEpiOfShape J (F ⋙ L)) :
    η.app (reflPtOfShape adj η θ X (J := J)) = θ.app (reflPtOfShape adj η θ X (J := J)) := by
  rw [equifProp_iff_transpose adj]
  refine hJ _ _ (colimit.isColimit (reflChain adj η θ X (J := J))) _ _ fun j => ?_
  dsimp
  rw [equifTranspose_naturality, equifTranspose_naturality]
  rw [← colimit.w (reflChain adj η θ X) (homOfLE (Order.le_succ j)), ← Category.assoc,
    ← Category.assoc, transpose_reflChain_map_succ adj η θ X]

variable (hJ : Paper.PreservesJointEpiOfShape J (F ⋙ L))

/-- The reflection of `X` into the equifier. -/
noncomputable def reflJE : Equif η θ :=
  ⟨reflPtOfShape adj η θ X (J := J), equifProp_reflPtOfShape_of_jointEpi adj η θ X hJ⟩

/-- The unit of the reflection. -/
noncomputable def reflUnitJE : X ⟶ reflPtOfShape adj η θ X (J := J) :=
  (reflBotIso adj η θ X (J := J)).inv ≫ reflιOfShape adj η θ X ⊥

/-- The morphism induced on the reflection by a morphism `X ⟶ Z` into the equifier. -/
noncomputable def reflLiftJE (Z : Equif η θ) (h : X ⟶ Z.obj) :
    reflPtOfShape adj η θ X (J := J) ⟶ Z.obj :=
  colimit.desc _
    { pt := Z.obj
      ι :=
        { app := fun j => (existsUnique_descent adj η θ X Z h j).choose
          naturality := by
            intro i j f
            dsimp
            rw [Category.comp_id]
            exact (existsUnique_descent adj η θ X Z h i).choose_spec.2 _
              (descent_restrict (show i ≤ j from leOfHom f)
                (existsUnique_descent adj η θ X Z h j).choose_spec.1) } }

/-- The `j`-th colimit injection of the reflection chain followed by `reflLiftJE h` is the unique
descended morphism at stage `j`. -/
@[reassoc]
lemma reflι_reflLiftJE (Z : Equif η θ) (h : X ⟶ Z.obj) (j : J) :
    reflιOfShape adj η θ X j ≫ reflLiftJE adj η θ X Z h
      = (existsUnique_descent adj η θ X Z h j).choose :=
  colimit.ι_desc _ _

/-- The unit `X ⟶ reflPt X` followed by `reflLiftJE h` is `h`. -/
lemma reflUnit_reflLiftJE (Z : Equif η θ) (h : X ⟶ Z.obj) :
    reflUnitJE adj η θ X (J := J) ≫ reflLiftJE adj η θ X Z h = h := by
  have h0 := (existsUnique_descent adj η θ X Z h (⊥ : J)).choose_spec.1
  have h1 : (𝟙 ((reflChain adj η θ X (J := J)).obj ⊥)) ≫
      (existsUnique_descent adj η θ X Z h (⊥ : J)).choose
      = (reflBotIso adj η θ X (J := J)).hom ≫ h := by
    rw [← reflChain_map_refl adj η θ X (⊥ : J)]
    exact h0
  rw [Category.id_comp] at h1
  rw [reflUnitJE, Category.assoc, reflι_reflLiftJE, h1, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- `reflLiftJE h` is the unique morphism `m` out of the reflection with `reflUnitJE ≫ m = h`. -/
lemma reflLiftJE_uniq (Z : Equif η θ) (h : X ⟶ Z.obj)
    (m : reflPtOfShape adj η θ X (J := J) ⟶ Z.obj)
    (hm : reflUnitJE adj η θ X (J := J) ≫ m = h) :
    m = reflLiftJE adj η θ X Z h := by
  refine reflPt_hom_ext adj η θ X fun j => ?_
  rw [reflι_reflLiftJE]
  refine (existsUnique_descent adj η θ X Z h j).choose_spec.2 _ ?_
  change (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ (reflιOfShape adj η θ X j ≫ m)
      = (reflBotIso adj η θ X (J := J)).hom ≫ h
  rw [← Category.assoc, map_reflι]
  rw [reflUnitJE, Category.assoc] at hm
  rw [← hm, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The reflection is initial in `X ↓ Equif.forget η θ`. -/
noncomputable def isInitialStructuredArrowReflJE :
    IsInitial (StructuredArrow.mk (S := X) (T := Equif.forget η θ)
      (Y := reflJE adj η θ X hJ) (reflUnitJE adj η θ X (J := J))) := by
  refine IsInitial.ofUniqueHom (fun A => StructuredArrow.homMk
    (⟨reflLiftJE adj η θ X A.right A.hom⟩ : reflJE adj η θ X hJ ⟶ A.right) ?_) ?_
  · exact reflUnit_reflLiftJE adj η θ X A.right A.hom
  · intro A m
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    refine reflLiftJE_uniq adj η θ X A.right A.hom m.right.hom ?_
    exact StructuredArrow.w m

end Chain

/-- **The inclusion of an equifier has a left adjoint**, assuming only that `F ⋙ L` preserves
joint epicness of colimiting cocones of shape `J`. -/
theorem forget_isRightAdjoint_of_jointEpi (adj : L ⊣ G) (η θ : F ⟶ G) [HasCoequalizers C]
    (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]
    [HasIterationOfShape J C] (hJ : Paper.PreservesJointEpiOfShape J (F ⋙ L)) :
    (Equif.forget η θ).IsRightAdjoint := by
  have := fun X : C => (isInitialStructuredArrowReflJE adj η θ X hJ).hasInitial
  exact isRightAdjointOfStructuredArrowInitials _

/-- **Theorem 5.5 (2)** ([forsman2026syntactic]), **development form.** If `G` has an
`F`-relative left adjoint `L`, `κ` is infinite, `C` is chain cocomplete up to `κ` and has
coequalizers, and `F` preserves joint epicness of colimiting cocones of `κ`-chains, then
`U : Eq(α, β) ⥤ C` is monadic. -/
@[instance_reducible]
noncomputable def monadicRightAdjointForgetOfJointEpi {F G : C ⥤ D} {L : C ⥤ C}
    {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 ≤ κ) (ra : RelLeftAdjoint F G L) (α β : F ⟶ G)
    [HasCoequalizers C] (hch : HasChainColimitsLE κ C)
    (hF : Paper.PreservesJointEpiOfShape κ.ord.ToType F) :
    MonadicRightAdjoint (Equif.forget α β) := by
  letI := Kappa.orderBotOfPos hκ
  haveI := Cardinal.noMaxOrder hκ
  haveI := Kappa.hasIterationOfShape_of_chain hκ hch
  have hL : Paper.PreservesJointEpiOfShape (Kappa.shape κ) (L ⋙ 𝟭 C) :=
    ra.preservesJointEpiOfShape _ hF
  haveI : (Equif.forget α β).IsRightAdjoint :=
    ObjectProperty.isRightAdjoint_ι_of_eq (ra.equifProp_eq α β)
      (forget_isRightAdjoint_of_jointEpi (F := L) (G := 𝟭 C) (L := 𝟭 C) Adjunction.id
        (ra.transposeNat α) (ra.transposeNat β) (Kappa.shape κ) hL)
  exact Monad.monadicOfCreatesGSplitCoequalizers (Adjunction.ofIsRightAdjoint _)

end Equif

end UlmerBialgebras
