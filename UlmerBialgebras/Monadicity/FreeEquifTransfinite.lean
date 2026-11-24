module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import UlmerBialgebras.Monadicity.FreeEquif

/-!
# Reflection into an equifier, by a transfinite chain

Let `η, θ : F ⟶ G` be natural transformations between functors `F, G : C ⥤ D`, let
`L ⊣ G` be an adjunction and assume that `C` has coequalizers.  The reflection of an
object `X` into the equifier `Equif η θ` is the colimit of the transfinite chain of
successive quotients

  `X₀ = X`,  `X_{j+1} = coeq (η'ₓ, θ'ₓ : L (F X_j) ⇉ X_j)`,  `X_j = colim_{i<j} X_i`,

where `η'ₓ` is the transpose of `ηₓ` along `L ⊣ G`.  The chain converges at any
well-ordered stage `J` without maximal element such that `F` preserves colimits of shape
`J` (and `C` has the colimits needed to run the chain).

## Main results

* `UlmerBialgebras.Equif.hasInitial_structuredArrow_of_shape` — the comma category
  `X ↓ Equif.forget η θ` has an initial object;
* `UlmerBialgebras.Equif.forget_isRightAdjoint_of_shape` — the inclusion `Equif η θ ⥤ C` has a left
  adjoint.

This is Theorem 5.5 (2), for a general well-ordered chain.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits SmallObject

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Equif

variable {F G : C ⥤ D} {L : D ⥤ C}

/-- The successor structure of the reflection chain: one step is the coequalizer of the
two transposed components. -/
@[simps]
noncomputable def equifSuccStruct (adj : L ⊣ G) (η θ : F ⟶ G) [HasCoequalizers C] (X : C) :
    SuccStruct C where
  X₀ := X
  succ Y := equifStep adj η θ Y
  toSucc Y := equifStepMap adj η θ Y

/-- Any morphism into an object of the equifier coequalizes the two transposes. -/
lemma transposeComp_eq (adj : L ⊣ G) (η θ : F ⟶ G) (Z : Equif η θ) {x : C}
    (w : x ⟶ Z.obj) :
    equifTranspose adj η x ≫ w = equifTranspose adj θ x ≫ w := by
  rw [← equifTranspose_naturality adj η w, ← equifTranspose_naturality adj θ w,
    (equifProp_iff_transpose adj η θ Z.obj).1 Z.property]

section Chain

variable (adj : L ⊣ G) (η θ : F ⟶ G) [HasCoequalizers C] (X : C)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

/-- The transfinite reflection chain. -/
@[implicit_reducible]
noncomputable def reflChain : J ⥤ C := (equifSuccStruct adj η θ X).iterationFunctor J

/-- The reflection chain is continuous at limit stages. -/
instance : (reflChain adj η θ X (J := J)).IsWellOrderContinuous :=
  inferInstanceAs ((equifSuccStruct adj η θ X).iterationFunctor J).IsWellOrderContinuous

/-- The stage `⊥` of the chain is `X`. -/
noncomputable def reflBotIso : (reflChain adj η θ X (J := J)).obj (⊥ : J) ≅ X :=
  (equifSuccStruct adj η θ X).iterationFunctorObjBotIso J

section Succ

variable [NoMaxOrder J]

/-- The stage `j+1` of the chain is the coequalizer step applied to the stage `j`. -/
noncomputable def reflSuccIso (j : J) :
    (reflChain adj η θ X (J := J)).obj (Order.succ j)
      ≅ equifStep adj η θ ((reflChain adj η θ X (J := J)).obj j) :=
  (equifSuccStruct adj η θ X).iterationFunctorObjSuccIso j (not_isMax j)

/-- The transition `j ⟶ j+1` of the reflection chain is `equifStepMap` followed by
the inverse of `reflSuccIso`. -/
lemma reflChain_map_succ (j : J) :
    (reflChain adj η θ X (J := J)).map (homOfLE (Order.le_succ j))
      = equifStepMap adj η θ _ ≫ (reflSuccIso adj η θ X j).inv :=
  (equifSuccStruct adj η θ X).iterationFunctor_map_succ j (not_isMax j)

/-- Each successor transition `j ⟶ j+1` of the reflection chain is an epimorphism. -/
instance epi_reflChain_map_succ (j : J) :
    Epi ((reflChain adj η θ X (J := J)).map (homOfLE (Order.le_succ j))) := by
  rw [reflChain_map_succ adj η θ X]
  infer_instance

/-- The two transposes are coequalized by the transition to the successor stage. -/
@[reassoc]
lemma transpose_reflChain_map_succ (j : J) :
    equifTranspose adj η ((reflChain adj η θ X (J := J)).obj j) ≫
        (reflChain adj η θ X (J := J)).map (homOfLE (Order.le_succ j))
      = equifTranspose adj θ ((reflChain adj η θ X (J := J)).obj j) ≫
        (reflChain adj η θ X (J := J)).map (homOfLE (Order.le_succ j)) := by
  rw [reflChain_map_succ adj η θ X, ← Category.assoc, ← Category.assoc, equifStep_condition]

end Succ

/-- Functoriality of the reflection chain: the transitions `i ⟶ j ⟶ k` compose to `i ⟶ k`. -/
@[reassoc]
lemma reflChain_map_comp {i j k : J} (hij : i ≤ j) (hjk : j ≤ k) :
    (reflChain adj η θ X (J := J)).map (homOfLE hij) ≫
        (reflChain adj η θ X (J := J)).map (homOfLE hjk)
      = (reflChain adj η θ X (J := J)).map (homOfLE (hij.trans hjk)) := by
  rw [← Functor.map_comp, homOfLE_comp]

/-- The reflection chain maps `i ≤ i` to the identity. -/
@[simp]
lemma reflChain_map_refl (i : J) :
    (reflChain adj η θ X (J := J)).map (homOfLE (le_refl i)) = 𝟙 _ :=
  (reflChain adj η θ X (J := J)).map_id i

/-- The underlying object of the reflection of `X` into the equifier. -/
@[implicit_reducible]
noncomputable def reflPtOfShape : C := colimit (reflChain adj η θ X (J := J))

/-- The colimit inclusions of the reflection chain. -/
@[implicit_reducible]
noncomputable def reflιOfShape (j : J) :
    (reflChain adj η θ X (J := J)).obj j ⟶ reflPtOfShape adj η θ X (J := J) :=
  colimit.ι _ j

/-- Compatibility of the colimit injections of the reflection chain with its transitions. -/
@[reassoc (attr := simp)]
lemma map_reflι {i j : J} (hij : i ≤ j) :
    (reflChain adj η θ X (J := J)).map (homOfLE hij) ≫ reflιOfShape adj η θ X j
      = reflιOfShape adj η θ X i :=
  colimit.w _ _

/-- Morphisms out of the colimit of the reflection chain are determined by the injections. -/
lemma reflPt_hom_ext {Y : C} {f g : reflPtOfShape adj η θ X (J := J) ⟶ Y}
    (h : ∀ j : J, reflιOfShape adj η θ X j ≫ f = reflιOfShape adj η θ X j ≫ g) : f = g :=
  colimit.hom_ext h

section Colimit

variable [NoMaxOrder J] [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J L]

/-- The colimit of the reflection chain lies in the equifier. -/
lemma equifProp_reflPtOfShape :
    η.app (reflPtOfShape adj η θ X (J := J)) = θ.app (reflPtOfShape adj η θ X (J := J)) := by
  rw [equifProp_iff_transpose adj]
  refine (isColimitOfPreserves (F ⋙ L)
    (colimit.isColimit (reflChain adj η θ X (J := J)))).hom_ext ?_
  intro j
  dsimp
  rw [equifTranspose_naturality, equifTranspose_naturality]
  rw [← colimit.w _ (homOfLE (Order.le_succ j)), ← Category.assoc, ← Category.assoc,
    transpose_reflChain_map_succ adj η θ X]

/-- The reflection of `X` into the equifier. -/
@[implicit_reducible]
noncomputable def reflOfShape : Equif η θ :=
  ⟨reflPtOfShape adj η θ X (J := J), equifProp_reflPtOfShape adj η θ X⟩

/-- The unit of the reflection. -/
noncomputable def reflUnitOfShape : X ⟶ (reflOfShape adj η θ X (J := J)).obj :=
  (reflBotIso adj η θ X (J := J)).inv ≫ reflιOfShape adj η θ X ⊥

end Colimit

section Descent

variable (Z : Equif η θ) (h : X ⟶ Z.obj)

variable {adj η θ X Z h}

/-- A compatibility `k` at stage `j` with `h` at the bottom restricts to stage `i ≤ j`. -/
lemma descent_restrict {i j : J} (hij : i ≤ j)
    {k : (reflChain adj η θ X (J := J)).obj j ⟶ Z.obj}
    (hk : (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ k
      = (reflBotIso adj η θ X (J := J)).hom ≫ h) :
    (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫
        ((reflChain adj η θ X (J := J)).map (homOfLE hij) ≫ k)
      = (reflBotIso adj η θ X (J := J)).hom ≫ h := by
  rw [← Category.assoc, reflChain_map_comp]
  exact hk

variable (adj η θ X Z h)

/-- Limit step for `existsUnique_descent`: given unique compatible morphisms at all `i < j`,
assemble the unique compatible morphism at a successor-limit `j`. -/
private lemma existsUnique_descent_limit {j : J} (hj : Order.IsSuccLimit j)
    (IH : ∀ i < j, ∃! k : (reflChain adj η θ X (J := J)).obj i ⟶ Z.obj,
      (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ k
        = (reflBotIso adj η θ X (J := J)).hom ≫ h) :
    ∃! k : (reflChain adj η θ X (J := J)).obj j ⟶ Z.obj,
      (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ k
        = (reflBotIso adj η θ X (J := J)).hom ≫ h := by
  classical
  have hcolim := (reflChain adj η θ X (J := J)).isColimitOfIsWellOrderContinuous j hj
  set k : ∀ (i : J), i < j → ((reflChain adj η θ X (J := J)).obj i ⟶ Z.obj) :=
    fun i hi => (IH i hi).choose
  have hkc : ∀ (i : J) (hi : i < j),
      (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ k i hi
        = (reflBotIso adj η θ X (J := J)).hom ≫ h :=
    fun i hi => (IH i hi).choose_spec.1
  have hku : ∀ (i : J) (hi : i < j) (m : (reflChain adj η θ X (J := J)).obj i ⟶ Z.obj),
      (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ m
        = (reflBotIso adj η θ X (J := J)).hom ≫ h → m = k i hi :=
    fun i hi m hm => (IH i hi).choose_spec.2 m hm
  let cocone : Cocone ((Set.principalSegIio j).monotone.functor ⋙
      (reflChain adj η θ X (J := J))) :=
    { pt := Z.obj
      ι :=
        { app := fun i => k i.1 i.2
          naturality := by
            rintro ⟨i, hi⟩ ⟨i', hi'⟩ f
            dsimp
            rw [Category.comp_id]
            exact hku i hi _
              (descent_restrict (i := i) (j := i') (show i ≤ i' from leOfHom f) (hkc i' hi')) } }
  refine ⟨hcolim.desc cocone, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i : J, i < j := ⟨⊥, hj.bot_lt⟩
    have hfac : (reflChain adj η θ X (J := J)).map (homOfLE hi.le) ≫ hcolim.desc cocone
        = k i hi := hcolim.fac cocone ⟨i, hi⟩
    rw [← reflChain_map_comp adj η θ X (bot_le : (⊥ : J) ≤ i) hi.le, Category.assoc, hfac]
    exact hkc i hi
  · intro m hm
    refine hcolim.hom_ext fun i => ?_
    rw [hcolim.fac]
    exact hku i.1 i.2 _ (descent_restrict i.2.le hm)

variable [NoMaxOrder J]

/-- At every stage of the chain there is a unique morphism to `Z` compatible with `h`. -/
lemma existsUnique_descent (j : J) :
    ∃! k : (reflChain adj η θ X (J := J)).obj j ⟶ Z.obj,
      (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ k
        = (reflBotIso adj η θ X (J := J)).hom ≫ h := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      obtain rfl : j = ⊥ := hj.eq_bot
      have hid : (reflChain adj η θ X (J := J)).map (homOfLE (bot_le : (⊥ : J) ≤ ⊥)) = 𝟙 _ :=
        reflChain_map_refl adj η θ X ⊥
      refine ⟨(reflBotIso adj η θ X (J := J)).hom ≫ h, ?_, ?_⟩
      · beta_reduce
        rw [hid, Category.id_comp]
      · intro k hk
        have hk' : (reflChain adj η θ X (J := J)).map (homOfLE bot_le) ≫ k
            = (reflBotIso adj η θ X (J := J)).hom ≫ h := hk
        rw [hid, Category.id_comp] at hk'
        exact hk'
  | succ j hj IH =>
      obtain ⟨kj, hkj, huniq⟩ := IH
      have hcoeq : equifTranspose adj η ((reflChain adj η θ X (J := J)).obj j) ≫ kj
          = equifTranspose adj θ ((reflChain adj η θ X (J := J)).obj j) ≫ kj :=
        transposeComp_eq adj η θ Z kj
      have hres : (reflChain adj η θ X (J := J)).map (homOfLE (Order.le_succ j)) ≫
          ((reflSuccIso adj η θ X j).hom ≫ coequalizer.desc kj hcoeq) = kj := by
        rw [reflChain_map_succ adj η θ X, Category.assoc]
        exact (whisker_eq _ (Iso.inv_hom_id_assoc _ _)).trans (coequalizer.π_desc _ _)
      refine ⟨(reflSuccIso adj η θ X j).hom ≫ coequalizer.desc kj hcoeq, ?_, ?_⟩
      · beta_reduce
        rw [← reflChain_map_comp adj η θ X (bot_le : (⊥ : J) ≤ j) (Order.le_succ j),
          Category.assoc, hres]
        exact hkj
      · intro k hk
        have h1 : (reflChain adj η θ X (J := J)).map (homOfLE (Order.le_succ j)) ≫ k = kj :=
          huniq _ (descent_restrict (Order.le_succ j) hk)
        exact (cancel_epi ((reflChain adj η θ X (J := J)).map
          (homOfLE (Order.le_succ j)))).1 (h1.trans hres.symm)
  | isSuccLimit j hj IH =>
      exact existsUnique_descent_limit adj η θ X Z h hj IH

end Descent

section Universal

variable [NoMaxOrder J]

/-- The morphism induced on the reflection by a morphism `X ⟶ Z` into an object of the
equifier. -/
noncomputable def reflLiftOfShape (Z : Equif η θ) (h : X ⟶ Z.obj) :
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

/-- The colimit injection at `j` followed by `reflLiftOfShape` is the chosen compatible
morphism of `existsUnique_descent` at stage `j`. -/
@[reassoc]
lemma reflι_reflLiftOfShape (Z : Equif η θ) (h : X ⟶ Z.obj) (j : J) :
    reflιOfShape adj η θ X j ≫ reflLiftOfShape adj η θ X Z h
      = (existsUnique_descent adj η θ X Z h j).choose :=
  colimit.ι_desc _ _

variable [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J L]

/-- `reflLiftOfShape` extends `h` along the unit: `reflUnitOfShape ≫ reflLiftOfShape Z h = h`. -/
lemma reflUnit_reflLiftOfShape (Z : Equif η θ) (h : X ⟶ Z.obj) :
    reflUnitOfShape adj η θ X (J := J) ≫ reflLiftOfShape adj η θ X Z h = h := by
  have h0 := (existsUnique_descent adj η θ X Z h (⊥ : J)).choose_spec.1
  have h1 : (𝟙 ((reflChain adj η θ X (J := J)).obj ⊥)) ≫
      (existsUnique_descent adj η θ X Z h (⊥ : J)).choose
      = (reflBotIso adj η θ X (J := J)).hom ≫ h := by
    rw [← reflChain_map_refl adj η θ X (⊥ : J)]
    exact h0
  rw [Category.id_comp] at h1
  rw [reflUnitOfShape, Category.assoc, reflι_reflLiftOfShape, h1, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Any `m` with `reflUnitOfShape ≫ m = h` equals `reflLiftOfShape Z h`. -/
lemma reflLiftOfShape_uniq (Z : Equif η θ) (h : X ⟶ Z.obj)
    (m : reflPtOfShape adj η θ X (J := J) ⟶ Z.obj)
    (hm : reflUnitOfShape adj η θ X (J := J) ≫ m = h) :
    m = reflLiftOfShape adj η θ X Z h := by
  refine reflPt_hom_ext adj η θ X fun j => ?_
  rw [reflι_reflLiftOfShape]
  refine (existsUnique_descent adj η θ X Z h j).choose_spec.2 _ ?_
  beta_reduce
  rw [← Category.assoc, map_reflι]
  rw [reflUnitOfShape, Category.assoc] at hm
  rw [← hm, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **Reflections into an equifier**: the comma category `X ↓ Equif.forget η θ` has an
initial object. -/
noncomputable def isInitialStructuredArrowRefl :
    IsInitial (StructuredArrow.mk (S := X) (T := Equif.forget η θ)
      (Y := reflOfShape adj η θ X (J := J)) (reflUnitOfShape adj η θ X)) := by
  refine IsInitial.ofUniqueHom (fun A => StructuredArrow.homMk
    (⟨reflLiftOfShape adj η θ X A.right A.hom⟩ :
      reflOfShape adj η θ X (J := J) ⟶ A.right) ?_) ?_
  · simpa using reflUnit_reflLiftOfShape adj η θ X A.right A.hom
  · intro A m
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    refine reflLiftOfShape_uniq adj η θ X A.right A.hom m.right.hom ?_
    simpa using StructuredArrow.w m

end Universal

end Chain

/-- **Reflections into an equifier.** -/
theorem hasInitial_structuredArrow_of_shape {F G : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ G) (η θ : F ⟶ G)
    [HasCoequalizers C] (X : C)
    (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]
    [HasIterationOfShape J C] [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J L] :
    HasInitial (StructuredArrow X (Equif.forget η θ)) :=
  (isInitialStructuredArrowRefl adj η θ X (J := J)).hasInitial

/-- **The inclusion of an equifier has a left adjoint** (Theorem 5.5 (2) of
[forsman2026syntactic]). -/
theorem forget_isRightAdjoint_of_shape {F G : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ G) (η θ : F ⟶ G)
    [HasCoequalizers C]
    (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]
    [HasIterationOfShape J C] [PreservesColimitsOfShape J F] :
    (Equif.forget η θ).IsRightAdjoint := by
  have : PreservesColimitsOfShape J L :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := fun X : C => hasInitial_structuredArrow_of_shape adj η θ X J
  exact isRightAdjointOfStructuredArrowInitials _

end Equif

end UlmerBialgebras
